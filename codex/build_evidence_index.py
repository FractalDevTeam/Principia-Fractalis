#!/usr/bin/env python3
"""Build the Riemann lane's evidence index: theorem -> commit -> axiom output.

Rio's P8 wants a per-lane evidence index at that shape. This produces it for the
march from the committed tree only -- no /tmp logs, which are ephemeral and
already missing for the early boxes. Every column is sourced from git:

  theorem   : the unconditional capstone's name, read out of the committed file
  interval  : the box it closes, read from the same statement
  commit    : git log for that path
  axiom bar : the commit message's recorded gate result, plus an independent
              re-grep of the committed file for contraband

The axiom OUTPUT itself is not in the tree -- `#print axioms` prints at build
time. So this index records (a) what the gate recorded when the box landed, and
(b) a fresh contraband scan of the bytes now committed. Where a box predates the
runner's gate, that is stated rather than inferred.
"""
import io
import os
import re
import subprocess
import sys
from fractions import Fraction as F

REPO = "/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE"


def git(args):
    return subprocess.run(["git"] + args, cwd=REPO, capture_output=True,
                           text=True, encoding="utf-8", errors="replace").stdout


files = [f for f in git(["ls-files",
                         "PF_Lean4_Code/PF/Analytic/PilotBoxes/"]).split("\n")
         if "UNCONDITIONAL" in f or "CLOSED" in f]

rows = []
for path in files:
    body = git(["show", "HEAD:%s" % path])
    if not body:
        continue
    m = re.search(r"theorem\s+(pilot_r1_box_\w*UNCONDITIONAL)\s*:", body)
    if not m:
        continue
    thm = m.group(1)
    iv = re.search(r"Icc\s*\(\(([-\d/\. ]+)\s*:\s*ℝ\)\)\s*\(([-\d/\. ]+)\)",
                   body)
    interval = ("[%s, %s]" % (iv.group(1).strip(), iv.group(2).strip())
                if iv else "?")
    log = git(["log", "--format=%h|%s", "-1", "--", path]).strip()
    sha, subj = (log.split("|", 1) if "|" in log else (log, ""))
    msg = git(["log", "--format=%B", "-1", "--", path])
    bar = "recorded" if "three-axiom bar" in msg else "not recorded in message"
    nth = re.search(r"(\d+)\s+theorems?, every one on exactly", msg)
    # independent contraband scan of the committed bytes
    bad = []
    for tok in ("sorry", "native_decide", "sorryAx"):
        for ln in body.split("\n"):
            s = ln.strip()
            if re.search(r"(^|[^A-Za-z_])%s([^A-Za-z_]|$)" % tok, s):
                if s.startswith("--") or s.startswith("/-") or "`" in s:
                    continue          # the file's own discipline docstring
                bad.append(tok)
                break
    rows.append((interval, thm, sha, bar,
                 nth.group(1) if nth else "-", sorted(set(bad))))


def key(r):
    m = re.match(r"\[([-\d/\.]+),", r[0])
    try:
        return float(F(m.group(1))) if m else 0.0
    except Exception:
        return 0.0


rows.sort(key=key)
print("# Riemann march — evidence index (theorem -> commit -> gate)")
print("")
print("%d boxes with an unconditional capstone in the committed tree." % len(rows))
print("")
print("| interval | theorem | commit | gate recorded | thms | contraband |")
print("|---|---|---|---|---|---|")
for interval, thm, sha, bar, nth, bad in rows:
    print("| `%s` | `%s` | `%s` | %s | %s | %s |"
          % (interval, thm.replace("pilot_r1_box_", ""), sha, bar, nth,
             ", ".join(bad) if bad else "none"))
print("")
clean = sum(1 for r in rows if not r[5])
print("contraband-free (independent scan of committed bytes): %d of %d"
      % (clean, len(rows)))
print("gate recorded in the landing commit: %d of %d"
      % (sum(1 for r in rows if r[3] == "recorded"), len(rows)))
