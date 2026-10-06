#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""Measure the actual distance to the goal line.

Pablo, 2026-10-06: "You need to know what the goal line is. And so you know when
you reach it."

The recorded goal line (project_pf_mission): step 1 of 4 is "the Lean corpus
pristine, gate-enforced"; readiness is "detection power stable AND find-rate on
new work near zero". Step 1 gates steps 2-4. So the number that matters is: how
much of the corpus that the book actually depends on is pristine?

A raw grep said "445 files contain sorry". That is not the number -- it counts
the word inside comments and docstrings (every module of mine says "no sorry"),
and it counts files nothing imports. This computes the honest version:

  * the TRANSITIVE import closure of PF.lean (what the root actually pulls in),
  * with Lean comments and docstrings stripped,
  * counting sorry / native_decide / axiom only at real code positions,
  * reported inside the closure and outside it separately.

Read-only. Nothing is modified.
"""
import io
import os
import re
import sys

ROOT = "/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE/PF_Lean4_Code"


def strip_comments(s):
    """Remove Lean block comments (nestable, incl. /-- docstrings) and -- lines."""
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
            # keep newlines so line numbers stay meaningful
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
    """Transitive import closure, following only PF.* imports."""
    seen = set()
    stack = [entry]
    missing = []
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        seen.add(mod)
        p = module_to_path(mod)
        if not os.path.exists(p):
            missing.append(mod)
            continue
        try:
            s = io.open(p, encoding="utf-8").read()
        except (OSError, UnicodeDecodeError):
            continue
        for m in re.finditer(r"^import\s+(PF(?:\.[A-Za-z0-9_']+)*)\s*$",
                             strip_comments(s), re.MULTILINE):
            stack.append(m.group(1))
    return seen, missing


PATS = {
    "sorry": re.compile(r"(?<![A-Za-z0-9_'.])sorry(?![A-Za-z0-9_'])"),
    "sorryAx": re.compile(r"(?<![A-Za-z0-9_'.])sorryAx(?![A-Za-z0-9_'])"),
    "native_decide": re.compile(r"(?<![A-Za-z0-9_'.])native_decide(?![A-Za-z0-9_'])"),
    "axiom_decl": re.compile(r"^\s*axiom\s+", re.MULTILINE),
    "interval_tac": re.compile(r"(?<![A-Za-z0-9_'.])interval(?![A-Za-z0-9_'])"),
}


def scan(paths):
    hits = dict((k, []) for k in PATS)
    for mod, p in paths:
        if not os.path.exists(p):
            continue
        try:
            code = strip_comments(io.open(p, encoding="utf-8").read())
        except (OSError, UnicodeDecodeError):
            continue
        for k, rx in PATS.items():
            n = len(rx.findall(code))
            if n:
                hits[k].append((mod, n))
    return hits


def main():
    entry = "PF"
    if not os.path.exists(module_to_path(entry)):
        print("MISS: %s absent" % module_to_path(entry))
        return 1

    closure, missing = closure_of(entry)
    all_files = []
    for dirpath, dirnames, filenames in os.walk(os.path.join(ROOT, "PF")):
        for fn in filenames:
            if fn.endswith(".lean"):
                full = os.path.join(dirpath, fn)
                rel = os.path.relpath(full, ROOT)
                mod = rel[:-5].replace("/", ".")
                all_files.append((mod, full))

    in_closure = [(m, p) for m, p in all_files if m in closure]
    out_closure = [(m, p) for m, p in all_files if m not in closure]

    print("=" * 72)
    print("THE DENOMINATOR")
    print("=" * 72)
    print("  .lean files under PF/                 %5d" % len(all_files))
    print("  in the transitive closure of PF.lean  %5d   <-- what the root pulls in"
          % len(in_closure))
    print("  NOT imported by anything from PF      %5d   <-- not in the submission"
          % len(out_closure))
    if missing:
        print("  imported but absent on disk           %5d  %s"
              % (len(missing), missing[:5]))
    print("")

    hin = scan(in_closure)
    hout = scan(out_closure)

    print("=" * 72)
    print("BLOCKERS INSIDE THE CLOSURE  (comments and docstrings stripped)")
    print("=" * 72)
    for k in ("sorry", "sorryAx", "native_decide", "axiom_decl", "interval_tac"):
        files = hin[k]
        tot = sum(n for _, n in files)
        print("  %-14s  %4d files  %5d occurrences" % (k, len(files), tot))
    print("")
    print("  same patterns OUTSIDE the closure (informational only):")
    for k in ("sorry", "native_decide", "axiom_decl"):
        files = hout[k]
        tot = sum(n for _, n in files)
        print("    %-12s  %4d files  %5d occurrences" % (k, len(files), tot))
    print("")

    for k in ("sorry", "native_decide"):
        files = sorted(hin[k], key=lambda t: -t[1])
        if not files:
            continue
        print("  heaviest %s in closure:" % k)
        for mod, n in files[:12]:
            print("    %5d  %s" % (n, mod))
        if len(files) > 12:
            print("    ... %d more files" % (len(files) - 12))
        print("")

    clean = [m for m, p in in_closure
             if m not in set(x[0] for x in hin["sorry"])
             and m not in set(x[0] for x in hin["native_decide"])
             and m not in set(x[0] for x in hin["sorryAx"])
             and m not in set(x[0] for x in hin["axiom_decl"])]
    print("=" * 72)
    print("GATE-ELIGIBLE: modules in closure with no sorry/native_decide/axiom")
    print("=" * 72)
    print("  %d of %d  (%.1f%%)"
          % (len(clean), len(in_closure), 100.0 * len(clean) / max(1, len(in_closure))))
    print("")
    print("  NOTE: gate-eligible is necessary, not sufficient. PRISTINE also")
    print("  requires olean current, axioms subset-of the three, no unused")
    print("  binders, PremiseAudit clean, and non-vacuity witnesses -- criteria")
    print("  (a), (b), (d), (d2), (e). Only a gate run can assert PRISTINE.")
    return 0


sys.exit(main())
