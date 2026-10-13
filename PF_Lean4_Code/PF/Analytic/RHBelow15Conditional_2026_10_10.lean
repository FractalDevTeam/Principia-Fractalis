/-
Copyright (c) 2026 Pablo Cohen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Cohen
-/
import PF.Analytic.RiemannXiFullRectangleBoundary_r331e
import PF.Analytic.RightEdgeSigns_2026_10_08
import PF.Analytic.RHBelow15CountExhaustion_2026_10_10

/-!
# RH below height 15 — the fully-wired conditional theorem

This file composes the three verified layers into a single theorem whose only
open hypotheses are the three right-edge sign facts R1/R2/R3:

* **contour = 2 ⇐ R1 ∧ R2 ∧ R3** — `RightEdgeSigns_2026_10_08`'s
  `rectangleIntegral'_logDeriv_eq_of_three_right_edge_facts`
  (the rotated log-branch bridge r331g + the symmetry reduction).
* **contour = ∑ zero-orders** — `r331e`'s `xi_full_rectangle_zero_count_identity`
  (the argument principle on the rectangle `[0,1] × [-15,15]`).
* **∑ orders = 2 ⇒ RH on the box** — `RHBelow15CountExhaustion`'s
  `rh_below_15_of_zeroSum` (the multiplicity exhaustion + r331f).

`r331g`'s `zF`/`wF` are defined identically to `r331e`'s (`⟨0,-15⟩`, `⟨1,15⟩`),
so the two contour values are definitionally the same term and compose by `.trans`.

## Result

`rh_below_15_conditional` : if `0 < Re ξ(1+it)` on `[0,13]`, `0 < Im ξ(1+it)` on
`[13,29/2]`, and `Re ξ(1+it) < 0` on `[29/2,15]`, then every zero of `ξ` in
`[0,1] × [-15,15]` has `Re s = 1/2`.

## Scope — unchanged

`riemannHypothesis_below_15` is RH on one finite rectangle, classically known
since Riemann and Gram. This theorem bears NOTHING on the open Riemann Hypothesis.
The three hypotheses R1/R2/R3 are themselves still open (numerically confirmed
only; the certified t-boxed interval campaign is the remaining numerical work).
Its value is that the finite statement is now machine-checked down to exactly
those three sign facts, with no other open antecedent and no project axioms.
-/

set_option autoImplicit false

namespace PrincipiaTractalis
namespace RHBelow15Conditional

open Complex Set Finset
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.RHBelow15CountExhaustion
open PrincipiaTractalis.FullRectangleBoundaryR331e

/-- **★★★ RH below height 15, conditional on exactly the three right-edge sign
facts R1 ∧ R2 ∧ R3 ★★★**

Every `ξ`-zero in the closed rectangle `[0,1] × [-15,15]` lies on the critical
line `Re s = 1/2`. The three hypotheses are the right-edge sign facts; everything
else — the contour evaluation, the argument-principle count identity, the
multiplicity exhaustion, and the horizontal/left edges — is discharged. -/
theorem rh_below_15_conditional
    (hR1 : RightEdgeSigns20261008.RightEdgeR1)
    (hR2 : RightEdgeSigns20261008.RightEdgeR2)
    (hR3 : RightEdgeSigns20261008.RightEdgeR3) :
    ∀ σ t : ℝ, 0 ≤ σ → σ ≤ 1 → -15 ≤ t → t ≤ 15 →
      riemannXiEntire ⟨σ, t⟩ = 0 → σ = 1 / 2 := by
  -- contour = ∑ orders  (count identity), and contour = 2  (from R1∧R2∧R3);
  -- the two contour terms are defeq (identical zF/wF), so `.trans` composes them.
  have hsum := (xi_full_rectangle_zero_count_identity).symm.trans
    (RightEdgeSigns20261008.rectangleIntegral'_logDeriv_eq_of_three_right_edge_facts
      hR1 hR2 hR3)
  -- feed the exhaustion lemma; the zero-set Finset is inferred from `hsum`.
  refine rh_below_15_of_zeroSum _ ?_ hsum
  -- membership characterisation of r331e's rectangle zero set.
  intro ρ
  rw [Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_preimage,
    Set.mem_singleton_iff]
  simp only [Rectangle, zF_re, zF_im, wF_re, wF_im, Complex.mem_reProdIm,
    Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    Set.uIcc_of_le (show (-15 : ℝ) ≤ 15 by norm_num), Set.mem_Icc]
  tauto

/-- The same statement with the three sign facts spelled out inline (the
unfolded form of `RightEdgeR1/R2/R3`), for callers that want the bare inequalities
rather than the `Prop` abbreviations. -/
theorem rh_below_15_conditional'
    (hR1 : ∀ t ∈ Set.Icc (0 : ℝ) 13, 0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re)
    (hR2 : ∀ t ∈ Set.Icc (13 : ℝ) (29 / 2), 0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).im)
    (hR3 : ∀ t ∈ Set.Icc (29 / 2 : ℝ) 15, (riemannXiEntire (⟨1, t⟩ : ℂ)).re < 0) :
    ∀ σ t : ℝ, 0 ≤ σ → σ ≤ 1 → -15 ≤ t → t ≤ 15 →
      riemannXiEntire ⟨σ, t⟩ = 0 → σ = 1 / 2 :=
  rh_below_15_conditional hR1 hR2 hR3

end RHBelow15Conditional
end PrincipiaTractalis

/-! ## Axiom check -/

#print axioms PrincipiaTractalis.RHBelow15Conditional.rh_below_15_conditional
#print axioms PrincipiaTractalis.RHBelow15Conditional.rh_below_15_conditional'
