#!/usr/bin/env python3
"""
emit_centered_pilot_box.py — Rank-1.5 centered-form pilot-box Lean emitter.

Emits one `PF/Analytic/PilotBoxes/<kind>_c<c>_r<r>_<date>.lean` file per
invocation, consuming the certified producer's `(c, r, Mc_lb_or_ub, L)`
tuple plus the kind in {R1, R2, R3}, and emitting a Lean theorem that
specialises `CenteredFormBridge20261013.R{1,2,3}_box_centered_of_{lb,ub}`
at the concrete rational endpoints.

The emitted theorem is CONDITIONAL on the two certified-producer hypotheses
(`hvalue_lb`/`hvalue_ub`, `hbound`); the Lean file imports
`CenteredFormBridge_2026_10_13` and discharges the margin check with
`norm_num`. The eventual certified panel generator (the Rank-1.5 numerical
engineering) is what will supply the two hypotheses — this emitter is the
plumbing between the (future) certified numerics and the Lean capstone chain.

Author: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-13.
"""
import argparse
import os
import sys
from fractions import Fraction


TEMPLATE = r'''/-
# PilotBoxes/{kind}_c{c_tag}_r{r_tag}_{date} — pilot box of the Rank-1.5 campaign

Specialises `CenteredFormBridge20261013.{box_lemma}` at the concrete pilot
box `(c = {c_rat}, r = {r_rat})` on the {kind} segment.

CONDITIONAL theorem — the certified producer must discharge `hvalue_{lb_or_ub}`
and `hbound`. Margin check `L · r {margin_op} {thresh_desc}` holds by `norm_num`
on the chosen conservative rationals.

Emitted by `scripts/emit_centered_pilot_box.py`.

### No sorry, native_decide, axiom, Prop := True. autoImplicit off. Additive.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). {date}.
-/

import PF.Analytic.CenteredFormBridge_2026_10_13

set_option autoImplicit false

namespace PrincipiaTractalis
namespace PilotBox_{kind}_c{c_tag}_r{r_tag}_{date_ns}

open Complex Set
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.R1Neighborhood20261009
open PrincipiaTractalis.EdgeSignNeighborhoods20261013
open PrincipiaTractalis.CenteredFormBridge20261013

noncomputable section

/-- Pilot box: {kind} on `[{c_rat} - {r_rat}, {c_rat} + {r_rat}]` from the
certified producer's bound on `{part_name} ξ(1 + i·{c_rat})` plus the derivative
modulus bound. -/
theorem pilot_{kind_low}_box_c{c_tag}_r{r_tag}
    (hvalue_{lb_or_ub} : {hvalue_type})
    (hbound :
      ∀ x ∈ Icc (({c_rat} : ℝ) - {r_rat}) (({c_rat} : ℝ) + {r_rat}),
        |deriv {edge_fn} x| ≤ {L_rat}) :
    ∀ t ∈ Icc (({c_rat} : ℝ) - {r_rat}) (({c_rat} : ℝ) + {r_rat}),
      {goal} :=
  {box_lemma}
    (c := {c_rat}) (r := {r_rat}) (L := {L_rat}) ({mc_name} := {Mc_rat})
    (by norm_num : (0 : ℝ) ≤ {r_rat})
    hvalue_{lb_or_ub}
    hbound
    (by norm_num : {margin_statement})

end

/-! ## §Axiom check -/

#print axioms pilot_{kind_low}_box_c{c_tag}_r{r_tag}

end PilotBox_{kind}_c{c_tag}_r{r_tag}_{date_ns}
end PrincipiaTractalis
'''


def frac_to_tag(f):
    """`1/2` -> `1_2`, `3/40` -> `3_40`, `13` -> `13`."""
    if f.denominator == 1:
        return str(f.numerator)
    return f"{f.numerator}_{f.denominator}"


def frac_to_rat(f):
    """Lean rational literal."""
    if f.denominator == 1:
        return str(f.numerator)
    return f"{f.numerator} / {f.denominator}"


def emit(kind, c, r, Mc, L, date, out_dir):
    """kind ∈ {'R1','R2','R3'}; c, r, Mc, L are Fractions; emit Lean file."""
    assert kind in ('R1', 'R2', 'R3')
    c, r, Mc, L = Fraction(c), Fraction(r), Fraction(Mc), Fraction(L)
    c_tag, r_tag = frac_to_tag(c), frac_to_tag(r)
    c_rat, r_rat, Mc_rat, L_rat = (
        frac_to_rat(c), frac_to_rat(r), frac_to_rat(Mc), frac_to_rat(L))
    date_ns = date.replace('-', '_')

    if kind == 'R1':
        box_lemma = 'R1_box_centered_of_lb'
        lb_or_ub = 'lb'
        mc_name = 'Mc_lb'
        edge_fn = 'edgeRe'
        part_name = 'Re'
        goal = '0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re'
        hvalue_type = f'({Mc_rat} : ℝ) ≤ (riemannXiEntire (⟨1, {c_rat}⟩ : ℂ)).re'
        margin_statement = f'({L_rat} : ℝ) * ({r_rat}) < {Mc_rat}'
        margin_op = '<'
        thresh_desc = f'Mc_lb = {Mc_rat}'
    elif kind == 'R2':
        box_lemma = 'R2_box_centered_of_lb'
        lb_or_ub = 'lb'
        mc_name = 'Mc_lb'
        edge_fn = 'edgeIm'
        part_name = 'Im'
        goal = '0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).im'
        hvalue_type = f'({Mc_rat} : ℝ) ≤ (riemannXiEntire (⟨1, {c_rat}⟩ : ℂ)).im'
        margin_statement = f'({L_rat} : ℝ) * ({r_rat}) < {Mc_rat}'
        margin_op = '<'
        thresh_desc = f'Mc_lb = {Mc_rat}'
    else:  # R3
        box_lemma = 'R3_box_centered_of_ub'
        lb_or_ub = 'ub'
        mc_name = 'Mc_ub'
        edge_fn = 'edgeRe'
        part_name = 'Re'
        goal = '(riemannXiEntire (⟨1, t⟩ : ℂ)).re < 0'
        hvalue_type = f'(riemannXiEntire (⟨1, {c_rat}⟩ : ℂ)).re ≤ ({Mc_rat} : ℝ)'
        margin_statement = f'({Mc_rat} : ℝ) < -(({L_rat}) * ({r_rat}))'
        margin_op = '<'
        thresh_desc = f'Mc_ub = {Mc_rat}'

    body = TEMPLATE.format(
        kind=kind, kind_low=kind.lower(),
        c_tag=c_tag, r_tag=r_tag,
        c_rat=c_rat, r_rat=r_rat, Mc_rat=Mc_rat, L_rat=L_rat,
        box_lemma=box_lemma, lb_or_ub=lb_or_ub, mc_name=mc_name,
        edge_fn=edge_fn, part_name=part_name,
        goal=goal, hvalue_type=hvalue_type,
        margin_statement=margin_statement,
        margin_op=margin_op, thresh_desc=thresh_desc,
        date=date, date_ns=date_ns,
    )

    os.makedirs(out_dir, exist_ok=True)
    fname = f"{kind}_c{c_tag}_r{r_tag}_{date_ns}.lean"
    path = os.path.join(out_dir, fname)
    with open(path, 'w', encoding='utf-8') as fh:
        fh.write(body)

    # Sanity: Lean's `norm_num` must close the margin. Verify numerically here
    # before emitting (floating-point arithmetic suffices for the check).
    L_f, r_f, Mc_f = float(L), float(r), float(Mc)
    product = L_f * r_f
    if kind in ('R1', 'R2'):
        margin_ok = (product < Mc_f)
    else:  # R3
        margin_ok = (Mc_f < -product)
    return path, margin_ok


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--kind', required=True, choices=['R1', 'R2', 'R3'])
    ap.add_argument('--c', required=True, help='box center (rational, e.g. 1/2)')
    ap.add_argument('--r', required=True, help='box radius (rational, e.g. 1/20)')
    ap.add_argument('--mc', required=True,
                    help='Mc lower bound (R1/R2) or upper bound (R3), rational')
    ap.add_argument('--l', required=True, help='derivative modulus bound (rational)')
    ap.add_argument('--date', default='2026-10-13', help='YYYY-MM-DD tag')
    ap.add_argument('--out-dir',
                    default='PF/Analytic/PilotBoxes',
                    help='output directory (relative to PF_Lean4_Code)')
    args = ap.parse_args()

    path, margin_ok = emit(args.kind, args.c, args.r, args.mc, args.l,
                           args.date, args.out_dir)
    print(f"[{args.kind}] emitted {path}")
    print(f"  margin check (float sanity): {'OK' if margin_ok else '*** FAIL ***'}")
    if not margin_ok:
        sys.exit(2)


if __name__ == '__main__':
    main()
