/-
# PF.Analytic.R1BoxLocalLNumeric_2026_10_20

**A rational majorant for `L0`, so the parameterised box criterion can actually
be discharged by `norm_num`.**

`R1BoxLocalL_2026_10_20` gives `box_of_enclosure`, which needs

  `L0 (c − r) · r < (1 − c²·R_ub − c·I_ub)/2`,   `L0 c = 2·ω(1)·(1 + 1/c) + 1/(2c²)`

and that is where the parameterised route stalled: `ω(1)` is a transcendental
`∑' n, exp(−π(n+1)²)`, with no numeric bound anywhere in the tree, so the
margin hypothesis could not be closed and every emitted pilot fell back on the
old fixed shape (`Mc_lb = 1/8`, `L = 1`, `gate ≤ 3/4`) — which is FALSE from
`c = 29/4` on, and stopped the march there.

The bound is cheap, because the geometric majorant is already proved:
`omega_le_of_one_le : ω(x) ≤ (23/22)·exp(−πx)` for `x ≥ 1` (`FPlusSecondDerivative`)
and `exp_neg_pi_le_one_twentythird : exp(−π) ≤ 1/23` (`Lambda0TightestBoundsMellin`)
give `ω(1) ≤ 1/22` immediately.

That is loose — `ω(1) = 0.043217…` against `1/22 = 0.045454…`, about 5% — but
`L0` is only ~5% larger as a result, and the box criterion clears it with a
margin of 18× at the centres in question. Tightness is not what was missing; a
rational bound of any kind was.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-20.
-/

import PF.Analytic.R1BoxLocalL_2026_10_20
import PF.Analytic.FPlusSecondDerivative_2026_10_18
import PF.Analytic.Lambda0TightestBoundsMellin_2026_10_14

set_option autoImplicit false

namespace PrincipiaTractalis
namespace R1BoxLocalLNumeric20261020

open Complex Real Set
open PrincipiaTractalis.XiThetaIntegral
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.DerivEdgeReLocalL20261020
open PrincipiaTractalis.R1BoxLocalL20261020
open PrincipiaTractalis.FPlusSecondDerivative20261018
open PrincipiaTractalis.Lambda0TightestBoundsMellin20261014
open scoped Real

noncomputable section

/-! ## §1 — `ω(1) ≤ 1/22` -/

/-- `ω(1) ≤ 1/22`. From the geometric majorant `ω(x) ≤ (23/22)·exp(−πx)` at
`x = 1` together with `exp(−π) ≤ 1/23`. -/
theorem omega_one_le_inv_22 : omega 1 ≤ (1 : ℝ) / 22 := by
  have h := omega_le_of_one_le (le_refl (1 : ℝ))
  have hmul : -π * (1 : ℝ) = -π := by ring
  rw [hmul] at h
  have h23 : Real.exp (-π) ≤ (1 : ℝ) / 23 := exp_neg_pi_le_one_twentythird
  have : (23 / 22 : ℝ) * Real.exp (-π) ≤ (23 / 22 : ℝ) * (1 / 23) :=
    mul_le_mul_of_nonneg_left h23 (by norm_num)
  linarith

/-! ## §2 — A rational majorant for `L0` -/

/-- `L0 c ≤ (1/11)·(1 + 1/c) + 1/(2c²)` for `c > 0`: the same shape as `L0`
with `2·ω(1)` replaced by the rational `1/11`. Every coefficient is rational, so
for rational `c` the right-hand side is a rational number `norm_num` can
evaluate. -/
theorem L0_le_rat {c : ℝ} (hc : 0 < c) :
    L0 c ≤ (1 : ℝ) / 11 * (1 + 1 / c) + 1 / (2 * c ^ 2) := by
  have hω : omega 1 ≤ (1 : ℝ) / 22 := omega_one_le_inv_22
  have hinv : (0 : ℝ) ≤ 1 / c := by positivity
  have hfac : (0 : ℝ) ≤ 1 + 1 / c := by linarith
  have h2 : 2 * omega 1 ≤ (1 : ℝ) / 11 := by linarith
  have := mul_le_mul_of_nonneg_right h2 hfac
  simp only [L0]
  linarith

/-! ## §3 — The box, with a margin hypothesis `norm_num` can close -/

/-- **The parameterised box criterion, in rational form.**

Identical conclusion to `box_of_enclosure`, but the margin hypothesis is stated
against a rational majorant `Q` of `L0 (c − r)` rather than against `L0`
itself. For rational `c`, `r`, `R_ub`, `I_ub` both hypotheses `hQ` and
`hmargin` are rational inequalities, so the producer can emit
`by norm_num` for each.

This is what lets a generated pilot use the *local* `L0 ≈ 0.11` instead of
`L = 1`, and the *computed* `Mc_lb` instead of the fixed `1/8`. -/
theorem box_of_enclosure_rat {c r R_ub I_ub Q : ℝ}
    (hr : 0 ≤ r) (hcr : r < c)
    (hR_ub : (completedRiemannZeta₀ (⟨1, c⟩ : ℂ)).re ≤ R_ub)
    (hI_ub : (completedRiemannZeta₀ (⟨1, c⟩ : ℂ)).im ≤ I_ub)
    (hQ : (1 : ℝ) / 11 * (1 + 1 / (c - r)) + 1 / (2 * (c - r) ^ 2) ≤ Q)
    (hmargin : Q * r < (1 - c ^ 2 * R_ub - c * I_ub) / 2) :
    ∀ t ∈ Icc (c - r) (c + r), 0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re := by
  refine box_of_enclosure hr hcr hR_ub hI_ub ?_
  have hcr0 : (0 : ℝ) < c - r := by linarith
  have hL : L0 (c - r) ≤ Q := le_trans (L0_le_rat hcr0) hQ
  have : L0 (c - r) * r ≤ Q * r := mul_le_mul_of_nonneg_right hL hr
  linarith

end

end R1BoxLocalLNumeric20261020
end PrincipiaTractalis

/-! ## §Axiom check -/

#print axioms PrincipiaTractalis.R1BoxLocalLNumeric20261020.omega_one_le_inv_22
#print axioms PrincipiaTractalis.R1BoxLocalLNumeric20261020.L0_le_rat
#print axioms PrincipiaTractalis.R1BoxLocalLNumeric20261020.box_of_enclosure_rat
