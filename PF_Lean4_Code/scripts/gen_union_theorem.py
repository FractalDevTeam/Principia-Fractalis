# -*- coding: utf-8 -*-
"""Emit the top-edge union theorem from the frozen strip manifest.

Produces PF/Analytic/RiemannXiTopEdgeUnion.lean:

    theorem top15_re_lt_neg_1e4 {sigma : R} (h0 : 1/2 <= sigma) (h1 : sigma <= 1) :
        (riemannXiEntire (sigma + 15i)).re < -(1/10000)

by a right-nested case split over the certified strips.  Coverage is by
construction: strip k handles (prev_hi, hi_k], box 0 handles [1/2, 9/16], and
the final strip absorbs sigma <= 1.

Endpoint ownership: `rcases le_or_lt sigma c` gives `sigma <= c` on the left
branch and `c < sigma` on the right, so each interior endpoint belongs to the
LOWER strip and the strips are half-open upward.  Every strip theorem is stated
with closed hypotheses `a <= sigma`, `sigma <= b`, so a left branch supplies
`sigma <= c` directly and a right branch supplies `c < sigma` weakened by
`le_of_lt`.  No gap is possible; overlap at endpoints is harmless.
"""
import io
from fractions import Fraction as F

# frozen 17-strip manifest over [9/16, 1]  (greedy coarsest-passing)
STRIPS = [
    (F(9, 16), F(5, 8)), (F(5, 8), F(11, 16)),
    (F(11, 16), F(23, 32)), (F(23, 32), F(3, 4)), (F(3, 4), F(25, 32)),
    (F(25, 32), F(13, 16)), (F(13, 16), F(27, 32)),
    (F(27, 32), F(55, 64)), (F(55, 64), F(7, 8)), (F(7, 8), F(57, 64)),
    (F(57, 64), F(29, 32)), (F(29, 32), F(59, 64)), (F(59, 64), F(15, 16)),
    (F(15, 16), F(61, 64)), (F(61, 64), F(31, 32)), (F(31, 32), F(63, 64)),
    (F(63, 64), F(1)),
]
BOX0 = (F(1, 2), F(9, 16))


def r(f):
    return "%d/%d" % (f.numerator, f.denominator) if f.denominator != 1 else str(f.numerator)


# sanity: contiguous, covers [9/16,1], meets box 0
assert STRIPS[0][0] == BOX0[1], "strip 0 must start where box 0 ends"
assert STRIPS[-1][1] == F(1), "last strip must end at 1"
for i in range(len(STRIPS) - 1):
    assert STRIPS[i][1] == STRIPS[i + 1][0], "gap at strip %d" % i
assert sum(b - a for a, b in STRIPS) == F(7, 16)
assert (BOX0[1] - BOX0[0]) + sum(b - a for a, b in STRIPS) == F(1, 2)

L = []
L.append('''/-
# PF.Analytic.RiemannXiTopEdgeUnion

**Top-edge negativity on the whole of `[1/2, 1]` at `t = 15`.**

Case-splits over Box 0 `[1/2, 9/16]` plus the %d certified strips tiling
`[9/16, 1]`.  Coverage is exact and gap-free by construction: consecutive
endpoints are equal, the first strip begins where Box 0 ends, and the last
strip ends at `1`.

Endpoint ownership: each `rcases le_or_lt σ c` sends `σ = c` to the LOWER
strip, and every strip theorem has closed hypotheses, so endpoints are covered
(harmlessly twice at the seams, never zero times).

SPDX-License-Identifier: Apache-2.0
-/

import PF.Analytic.RiemannXiBox0Bridge''' % len(STRIPS))
for i, _ in enumerate(STRIPS):
    L.append("import PF.Analytic.RiemannXiStrip%02dBridge" % i)
L.append('''
namespace PrincipiaTractalis.RiemannXiTopEdgeUnion

open scoped Real
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.RiemannXiBox0Bridge''')
for i, _ in enumerate(STRIPS):
    L.append("open PrincipiaTractalis.RiemannXiStrip%02dBridge" % i)
L.append('''
/-- **★ TOP EDGE ★** — `Re ξ(σ + 15i) < -1/10000` for every `σ ∈ [1/2, 1]`. -/
theorem top15_re_lt_neg_1e4 {σ : ℝ}
    (h0 : (1 : ℝ) / 2 ≤ σ) (h1 : σ ≤ 1) :
    (riemannXiEntire (⟨σ, 15⟩ : ℂ)).re < -(1/10000 : ℝ) := by''')

ind = "  "
L.append(ind + "rcases le_or_lt σ (%s) with hb | hb" % r(BOX0[1]))
L.append(ind + "· exact top15_box0_re_lt_neg_1e4 h0 hb")

for i, (a, b) in enumerate(STRIPS):
    last = (i == len(STRIPS) - 1)
    L.append(ind + "· " + ("" if last else "rcases le_or_lt σ (%s) with hs%d | hs%d" % (r(b), i, i)))
    if last:
        L.append(ind + "  exact top15_strip%02d_re_lt_neg_1e4 (le_of_lt hb) h1" % i)
    else:
        L.append(ind + "  · exact top15_strip%02d_re_lt_neg_1e4 (le_of_lt hb) hs%d" % (i, i))
        L.append(ind + "  · " + "-- σ > %s, continue" % r(b))
        L.append(ind + "    rename_i hb")
    ind += "    "

L.append("")
L.append("end PrincipiaTractalis.RiemannXiTopEdgeUnion")

src = "\n".join(L)
io.open("/tmp/RiemannXiTopEdgeUnion.lean", "w", encoding="utf-8").write(src)
print("strips: %d" % len(STRIPS))
print("coverage assertions: PASS (contiguous, [1/2,1] exactly, measure 1/2)")
print("wrote /tmp/RiemannXiTopEdgeUnion.lean (%d lines)" % (src.count("\n") + 1))
print()
print("NOTE: nesting depth %d — if Lean's structured-tactic nesting is awkward at"
      % len(STRIPS))
print("this depth, the flat alternative is a list of `if h : σ ≤ c` guards or an")
print("interval_cases-style chain; will settle when the strips actually exist.")
