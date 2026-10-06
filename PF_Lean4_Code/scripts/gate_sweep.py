#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""Run pristine_gate.sh over the whole import closure of PF.lean.

Pablo, 2026-10-06: "You need to know what the goal line is. And so you know when
you reach it."

Step 1 of the recorded program is "the Lean corpus pristine, gate-enforced", and
it gates steps 2-4. The number that defines the goal line is therefore: how many
of the modules the root actually imports pass the full six-criterion gate? Only a
gate run can answer it -- criterion (c) being clean corpus-wide (measured
separately: 0 sorry, 0 native_decide, 0 axiom across all 1451) is necessary and
nowhere near sufficient.

Resumable: results append to the TSV, and modules already recorded are skipped,
so an interrupted sweep continues where it stopped.

Usage:
  gate_sweep.py [--limit N] [--out PATH]
"""
import io
import os
import re
import subprocess
import sys
import time

ROOT = "/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE/PF_Lean4_Code"
GATE = "scripts/pristine_gate.sh"
DEFAULT_OUT = ("/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE/"
               "codex/PRISTINE_SWEEP_2026-10-06.tsv")
CPUS = "0,1"


def strip_comments(s):
    out = []
    i = 0
    depth = 0
    n = len(s)
    while i < n:
        if s.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if s.startswith("-/", i) and depth > 0:
            depth -= 1
            i += 2
            continue
        if depth > 0:
            if s[i] == "\n":
                out.append("\n")
            i += 1
            continue
        if s.startswith("--", i):
            j = s.find("\n", i)
            if j == -1:
                break
            i = j
            continue
        out.append(s[i])
        i += 1
    return "".join(out)


def module_to_path(mod):
    return os.path.join(ROOT, mod.replace(".", "/") + ".lean")


def closure_of(entry):
    seen = set()
    stack = [entry]
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        seen.add(mod)
        p = module_to_path(mod)
        if not os.path.exists(p):
            continue
        try:
            s = io.open(p, encoding="utf-8").read()
        except (OSError, UnicodeDecodeError):
            continue
        for m in re.finditer(r"^import\s+(PF(?:\.[A-Za-z0-9_']+)*)\s*$",
                             strip_comments(s), re.MULTILINE):
            stack.append(m.group(1))
    return seen


# re.MULTILINE is load-bearing: without it "^" anchors only at the start
# of the whole captured output, so every FAIL line was missed and the
# first calibration run recorded 8 failures as "unparsed".
CRIT = re.compile(r"^\s*(PASS|FAIL)\s+\(([a-z0-9]+)\)", re.MULTILINE)


def run_gate(mod):
    t0 = time.time()
    try:
        r = subprocess.run(["bash", GATE, mod], cwd=ROOT,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                           timeout=900)
        out = r.stdout.decode("utf-8", "replace")
        code = r.returncode
    except subprocess.TimeoutExpired:
        return "TIMEOUT", "", time.time() - t0
    dt = time.time() - t0
    failed = ["(%s)" % m.group(2) for m in CRIT.finditer(out)
              if m.group(1) == "FAIL"]
    findings = re.findall(r"^\s+(DEAD|CONTAINED|VACUOUS)\s+(\S+)", out,
                          re.MULTILINE)
    detail = ";".join(sorted(set("%s:%s" % (kind, decl)
                                 for kind, decl in findings)))
    if code == 0 and "PRISTINE" in out:
        return "PRISTINE", "", dt
    if code == 2:
        return "ENVERROR", ",".join(failed), dt
    return "FAILED", (",".join(failed) if failed else "unparsed") + "|" + detail, dt


def main():
    limit = None
    out_path = DEFAULT_OUT
    args = sys.argv[1:]
    i = 0
    while i < len(args):
        if args[i] == "--limit":
            limit = int(args[i + 1]); i += 2
        elif args[i] == "--out":
            out_path = args[i + 1]; i += 2
        else:
            print("unknown arg %s" % args[i]); return 2
    os.environ["PATH"] = os.path.expanduser("~/.elan/bin") + ":" + os.environ.get("PATH", "")

    mods = sorted(m for m in closure_of("PF") if os.path.exists(module_to_path(m)))
    done = {}
    if os.path.exists(out_path):
        for line in io.open(out_path, encoding="utf-8"):
            parts = line.rstrip("\n").split("\t")
            if len(parts) >= 2 and parts[0] != "module":
                done[parts[0]] = parts[1]
    todo = [m for m in mods if m not in done]
    if limit:
        todo = todo[:limit]

    print("closure: %d modules | already recorded: %d | this run: %d"
          % (len(mods), len(done), len(todo)))
    sys.stdout.flush()

    new = os.path.exists(out_path)
    fh = io.open(out_path, "a", encoding="utf-8")
    if not new:
        fh.write("module\tverdict\tfailed_criteria\tseconds\n")
        fh.flush()

    tally = {}
    for k, v in done.items():
        tally[v] = tally.get(v, 0) + 1
    t_start = time.time()
    for n, mod in enumerate(todo, 1):
        verdict, failed, dt = run_gate(mod)
        tally[verdict] = tally.get(verdict, 0) + 1
        fh.write("%s\t%s\t%s\t%.1f\n" % (mod, verdict, failed, dt))
        fh.flush()
        elapsed = time.time() - t_start
        rate = elapsed / n
        remaining = (len(mods) - len(done) - n) * rate
        print("[%4d/%4d] %-9s %6.1fs  %-60s | avg %.1fs/mod, ETA %.1fh"
              % (n, len(todo), verdict, dt, mod[:60], rate, remaining / 3600.0))
        sys.stdout.flush()

    fh.close()
    print("")
    print("TALLY (cumulative over the TSV):")
    for k in sorted(tally):
        print("  %-9s %5d" % (k, tally[k]))
    tot = sum(tally.values())
    if tot:
        print("  PRISTINE share: %.1f%% of %d recorded"
              % (100.0 * tally.get("PRISTINE", 0) / tot, tot))
    return 0


sys.exit(main())
