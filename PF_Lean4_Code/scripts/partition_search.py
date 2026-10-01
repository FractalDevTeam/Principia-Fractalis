#!/usr/bin/env python3
"""
partition_search.py — panel-count optimiser for the r331b Box-0 partition.

READ-ONLY with respect to the existing corpus. Imports `opt40tight` for the
frozen OPT-40-TIGHT geometry, writes nothing, deletes nothing, and modifies no
existing file. Output is a report on stdout plus an optional JSON file under
/tmp.

WHY THIS EXISTS

The Lean build cost of the xi-rectangle is (panel count) x (per-panel
elaboration cost). Per-panel cost is fixed by the generator; panel count is a
free design choice, currently 40 hand-tuned segments totalling sum(n_j) panels.

The generator's own docstring states the constraint:

    total midpoint error = sum_j MHI_j * (U_j - L_j)^3 / (24 * n_j^2)
                         ~ 1.78e-6   (reconnaissance)
                         = 1.9621020147e-06  (after MHI_OVERRIDE, per opt40tight)

So the design problem is

    minimise    sum_j n_j
    subject to  sum_j MHI_j * h_j^3 / (24 n_j^2)  <=  E_budget ,   h_j = U_j - L_j

with n_j positive integers.

For fixed segment boundaries this has a closed form. Writing
c_j = MHI_j * h_j^3 / 24 so E_j = c_j / n_j^2, the Lagrangian
sum n_j + lam (sum c_j / n_j^2 - E) gives

    1 - 2 lam c_j / n_j^3 = 0   =>   n_j proportional to c_j^(1/3).

That is the classical equidistribution rule: allocate panels in proportion to
the cube root of the local error coefficient. Any allocation that is NOT
proportional to c_j^(1/3) spends panels where they buy less error reduction
than they would elsewhere.

The current table is hand-tuned, so the first question is simply how far it sits
from equidistribution, and how many panels that costs at the SAME error budget.

No claim is made here about Lean, about the mathematics of the bound, or about
whether a smaller partition still certifies. This computes an allocation only.
Any candidate must then be run through the actual generator and the Lean kernel
before it means anything.
"""
from __future__ import annotations

import json
import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
for cand in (HERE, "/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE/PF_Lean4_Code/scripts",
             os.path.expanduser("~/pf-worker/Principia-Fractalis-ACTIVE/PF_Lean4_Code/scripts")):
    if os.path.isfile(os.path.join(cand, "opt40tight.py")):
        sys.path.insert(0, cand)
        break
else:
    print("FATAL: opt40tight.py not found on any candidate path")
    raise SystemExit(2)

import opt40tight as G  # read-only


def mhi_for(idx: int, m_ref: float) -> F:
    """Reproduce the generator's MHI choice, including the overrides."""
    ov = getattr(G, "MHI_OVERRIDE", {})
    if idx in ov:
        return ov[idx]
    return G.m_ceiling(m_ref)


def build_rows():
    rows = []
    for (idx, L, U, n, m_ref) in G.RAW:
        h = U - L
        mhi = mhi_for(idx, m_ref)
        c = F(mhi) * h ** 3 / 24          # E_j = c / n^2
        rows.append(dict(idx=idx, L=L, U=U, n=n, m_ref=m_ref, mhi=mhi, h=h, c=c))
    return rows


def total_error(rows, alloc):
    return sum(float(r["c"]) / (alloc[i] ** 2) for i, r in enumerate(rows))


def equidistribute(rows, budget):
    """Smallest integer allocation with sum(c_j/n_j^2) <= budget.

    Start from the continuous optimum n_j = (2 lam c_j)^(1/3), scaled so the
    constraint binds, then round up and greedily remove panels that still leave
    the constraint satisfied. Greedy removal is safe because each E_j is
    decreasing in n_j: dropping a panel only ever increases total error.
    """
    cs = [float(r["c"]) for r in rows]
    # continuous optimum shape
    shape = [c ** (1.0 / 3.0) for c in cs]
    # find scale s so that sum(c_j / (s*shape_j)^2) = budget
    # sum c_j/(s^2 shape_j^2) = budget  =>  s^2 = (1/budget) sum c_j/shape_j^2
    s2 = sum(c / (sh ** 2) for c, sh in zip(cs, shape)) / budget
    s = s2 ** 0.5
    alloc = [max(1, int(-(-(s * sh) // 1))) for sh in shape]   # ceil
    # greedy trim: repeatedly drop from the segment with the largest slack gain
    improved = True
    while improved:
        improved = False
        order = sorted(range(len(rows)), key=lambda i: -alloc[i])
        for i in order:
            if alloc[i] <= 1:
                continue
            alloc[i] -= 1
            if total_error(rows, alloc) <= budget:
                improved = True
            else:
                alloc[i] += 1
    return alloc


def main():
    rows = build_rows()
    cur = [r["n"] for r in rows]
    cur_panels = sum(cur)
    cur_err = total_error(rows, cur)

    print("=" * 78)
    print("CURRENT OPT-40-TIGHT")
    print("=" * 78)
    print(f"  segments      : {len(rows)}")
    print(f"  total panels  : {cur_panels}")
    print(f"  total E       : {cur_err:.10e}")

    # Use the current error as the budget: same certified quality, fewer panels.
    budget = cur_err
    opt = equidistribute(rows, budget)
    opt_panels = sum(opt)
    opt_err = total_error(rows, opt)

    print()
    print("=" * 78)
    print("EQUIDISTRIBUTED ALLOCATION, SAME ERROR BUDGET")
    print("=" * 78)
    print(f"  total panels  : {opt_panels}")
    print(f"  total E       : {opt_err:.10e}   (budget {budget:.10e})")
    print(f"  feasible      : {opt_err <= budget}")
    delta = cur_panels - opt_panels
    pct = 100.0 * delta / cur_panels if cur_panels else 0.0
    print(f"  panels saved  : {delta}  ({pct:.1f}%)")

    print()
    print("  idx      L        U       h        MHI        n_cur  n_opt  delta")
    print("  " + "-" * 72)
    for r, a, b in zip(rows, cur, opt):
        print(f"  {r['idx']:3d}  {float(r['L']):7.4f} {float(r['U']):7.4f} "
              f"{float(r['h']):7.5f} {float(r['mhi']):10.6g}  {a:5d}  {b:5d}  {b-a:+5d}")

    out = dict(
        current=dict(panels=cur_panels, error=cur_err, alloc=cur),
        equidistributed=dict(panels=opt_panels, error=opt_err, alloc=opt),
        saved=delta, saved_pct=pct,
        note="allocation only; must be re-run through the generator and the Lean "
             "kernel before it means anything",
    )
    dest = "/tmp/partition_search_result.json"
    with open(dest, "w") as f:
        json.dump(out, f, indent=2)
    print()
    print(f"  wrote {dest}")
    print()
    print("  NEXT, and none of it is implied by the above:")
    print("   1. re-run emit_stage2_segment.py on the candidate allocation")
    print("   2. confirm emit_M_certificate still certifies each MHI")
    print("   3. build the emitted panels and gate them")
    print("  Until (3) passes, this is a spreadsheet, not a result.")


if __name__ == "__main__":
    main()
