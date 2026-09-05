#!/usr/bin/env python3
"""Gate item E: MHI override table.

Every M certificate states its majorant as

    T_0 ~ ...   B0 = ...
    T_1 ~ ...   B1 = ...
    T_2 ~ ...   B2 = ...
    2*(B0+B1+B2) = <lhs> <= <rhs>

The default rule is MHI = 2 * sum(B_n) exactly. An "override" is any segment whose
declared MHI (the rhs, which is what the Lean statement uses) differs from that sum.
This scans all 18 boxes x 40 segments and reports every deviation.
"""
import os
import re
import sys
from fractions import Fraction as F

ROOT = sys.argv[1]
NUM = os.path.join(ROOT, "PF", "Numerics")

boxes = sorted({m.group(1) for m in
                (re.match(r"Box(\d+)Seg\d+M\.lean$", f) for f in os.listdir(NUM)) if m},
               key=int)

rows = []
overrides = []
missing = []
for K in boxes:
    for i in range(1, 41):
        fn = os.path.join(NUM, "Box%sSeg%02dM.lean" % (K, i))
        if not os.path.exists(fn):
            missing.append("Box%s Seg%02d" % (K, i))
            continue
        head = open(fn, encoding="utf-8").read()[:1500]
        m = re.search(r"2·\(B0\+B1\+B2\)\s*=\s*(\S+)\s*≤\s*(\S+)", head)
        if not m:
            m = re.search(r"2\*\(B0\+B1\+B2\)\s*=\s*(\S+)\s*<=\s*(\S+)", head)
        mh = re.search(r"MHI\s*=\s*(\S+?)\.", head)
        if not m:
            missing.append("Box%s Seg%02d (no majorant line)" % (K, i))
            continue
        lhs, rhs = F(m.group(1)), F(m.group(2))
        declared = F(mh.group(1)) if mh else rhs
        rows.append((K, i, lhs, rhs, declared))
        if lhs != rhs or declared != rhs:
            overrides.append((K, i, lhs, rhs, declared))

print("# MHI override table — gate item E")
print()
print("Scanned %d M certificates across %d boxes." % (len(rows), len(boxes)))
print()
print("Default rule: `MHI = 2 * (B0 + B1 + B2)` exactly, as emitted by")
print("`scripts/emit_box_segment.py`. An override is any segment whose Lean-facing")
print("MHI differs from that sum.")
print()
if missing:
    print("## Unreadable / missing")
    for x in missing[:10]:
        print("  - " + x)
    print()
if overrides:
    print("## OVERRIDES (%d)" % len(overrides))
    print()
    print("| box | seg | 2*sum(B) | declared MHI | direction |")
    print("|---|---|---|---|---|")
    for K, i, lhs, rhs, dec in overrides:
        d = "LOOSER (rhs > sum)" if rhs > lhs else "TIGHTER (rhs < sum) - UNSOUND"
        print("| %s | %d | %s | %s | %s |" % (K, i, lhs, rhs, d))
else:
    print("## OVERRIDES: **none**")
    print()
    print("Every one of the %d certificates uses `MHI = 2 * sum(B_n)` exactly," % len(rows))
    print("with the stated majorant equal to the declared bound. No segment was")
    print("hand-adjusted, tightened, or loosened. Gate items E1-E3 are therefore")
    print("vacuously satisfied: there is no override to justify.")
print()
print("## E4 — the Seg17 Stage-1 reference exception")
print()
print("`scripts/emit_stage2_segment.py` skips segment 17 (L=3/2, U=25/16, n=23) by")
print("default: it is the Stage-1 reference segment. Verify below that every box")
print("nonetheless carries a Seg17 M certificate (the box-parametric generator")
print("`emit_box_segment.py` emits it):")
print()
seg17 = [K for K in boxes if os.path.exists(os.path.join(NUM, "Box%sSeg17M.lean" % K))]
print("  boxes with Box<K>Seg17M.lean present: %d/%d  (%s)"
      % (len(seg17), len(boxes), " ".join(seg17)))
