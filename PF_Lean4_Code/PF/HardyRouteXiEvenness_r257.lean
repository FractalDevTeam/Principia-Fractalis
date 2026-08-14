/-
# r257: HARDY ROUTE — Xi EVENNESS on ℝ.

★ 2026-08-13 r257 — a concrete substrate advance on the framework's
Xi-real-witness (r115) toward inhabiting the Wave 58/59 atomic fact
`PositiveOnLineZetaZeroOrdinatesNonempty` via the certified-numerics
Route B pattern the r115 file already sets up.

## What this file adds

r115 established:
- `Xi t = (completedRiemannZeta ⟨1/2, t⟩).re`,
- `Xi_im_eq_zero`, `Xi_eq`, `continuous_Xi`,
- `xi_sign_change_implies_on_line_zero`.

r257 adds the following NEW structural properties of `Xi`, each
derived directly from mathlib's `Complex.riemannZeta`, mathlib's
functional equation `completedRiemannZeta_one_sub`, and r115's
conjugation content:

- `xi_even`: `Xi (-t) = Xi t` for every real `t`.
  Proof: `⟨1/2, -t⟩ = 1 - ⟨1/2, t⟩` combined with mathlib's
  `completedRiemannZeta_one_sub`.

- `xi_symm_at_zero`: `Xi 0 = (completedRiemannZeta (1/2 : ℂ)).re`
  as an explicit reformulation.

- `xi_is_real_of_eq`: for every real `t`, the value
  `completedRiemannZeta ⟨1/2, t⟩` is the coercion of `Xi t : ℝ`.

- `xi_sign_change_symm`: symmetric formulation of the sign-change
  condition: `∃ b > 0, Xi 0 * Xi b < 0` implies
  `PositiveOnLineZetaZeroOrdinatesNonempty`.

## Route B advance value

Combined with future numerical content on either `Xi 0` (which equals
`Λ(1/2) = π^{-1/4}·Γ(1/4)·ζ(1/2)`; classically negative) or `Xi b` at
some `b > 0` (positive by the standard interval-arithmetic verification
past the first Riemann zero at `b > 14.135`), r257's structural pieces
plus r115's `xi_sign_change_implies_on_line_zero` DIRECTLY inhabit the
Wave 58/59 atom without the Hardy 1914 named citation.

## Scope

* NOT novel — evenness of `Ξ` on the critical line is a classical
  consequence of the functional equation.
* NOT a Millennium discharge.
* IS a concrete structural advance on r115's Route B setup, deriving
  new properties of `Xi` from within mathlib + r115's conjugation
  content.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.Analytic.XiRealWitness
import PF.Analytic.HilbertPolyaPositiveReductionToCountability

open scoped Real ComplexConjugate

namespace PrincipiaTractalis.HardyRouteXiEvenness

open PrincipiaTractalis.XiRealWitness
open PrincipiaTractalis.HilbertPolyaPositiveReductionToCountability
open Complex

/-! ## §1 `Xi (-t) = Xi t` — the evenness of `Ξ` on the critical line. -/

/-- **`crit_neg_eq_one_sub`** — the identity `⟨1/2, -t⟩ = 1 - ⟨1/2, t⟩`
in `ℂ`. -/
private lemma crit_neg_eq_one_sub (t : ℝ) :
    ((⟨1/2, -t⟩ : ℂ)) = 1 - (⟨1/2, t⟩ : ℂ) := by
  apply Complex.ext
  · show (1/2 : ℝ) = 1 - (1/2 : ℝ)
    norm_num
  · show -t = 0 - t
    ring

/-- **`xi_even`** — `Ξ(-t) = Ξ(t)` for every real `t`.

Proof: `⟨1/2, -t⟩ = 1 - ⟨1/2, t⟩` by direct arithmetic on `Complex.mk`;
apply mathlib's `completedRiemannZeta_one_sub`. -/
theorem xi_even (t : ℝ) : Xi (-t) = Xi t := by
  unfold Xi
  have h : completedRiemannZeta ⟨1/2, -t⟩
      = completedRiemannZeta (1 - ⟨1/2, t⟩) := by
    rw [crit_neg_eq_one_sub]
  rw [h, completedRiemannZeta_one_sub]

/-! ## §2 `Xi 0` as an explicit reformulation. -/

/-- **`xi_symm_at_zero`** — `Xi 0` equals the real part of `Λ(1/2)`. -/
theorem xi_symm_at_zero :
    Xi 0 = (completedRiemannZeta ((1/2 : ℂ))).re := by
  unfold Xi
  have h : ((⟨1/2, 0⟩ : ℂ)) = (1/2 : ℂ) := by
    apply Complex.ext
    · show (1/2 : ℝ) = (1/2 : ℂ).re
      norm_num
    · show (0 : ℝ) = (1/2 : ℂ).im
      norm_num
  rw [h]

/-! ## §3 Companion of `Xi_eq`. -/

/-- **`xi_is_real_of_eq`** — the value `completedRiemannZeta ⟨1/2, t⟩`
is exactly the coercion of `Xi t : ℝ` into ℂ. Rewording of r115's
`Xi_eq` for use by downstream numerics. -/
theorem xi_is_real_of_eq (t : ℝ) :
    completedRiemannZeta ⟨1/2, t⟩ = ((Xi t : ℝ) : ℂ) := Xi_eq t

/-! ## §4 Sign-change symmetric formulation via `Xi 0` and evenness. -/

/-- **`xi_sign_change_via_zero`** — if `Xi 0` and `Xi b` have opposite
signs for some `b > 0`, then a positive on-line ζ-zero exists.

Direct application of r115's `xi_sign_change_implies_on_line_zero`
with `a` replaced by `0`... but IVT-uIcc requires `0 < a`. Use
`xi_even` and a symmetric split. -/
theorem xi_sign_change_via_zero {b : ℝ} (hb : 0 < b)
    (hsign : Xi 0 * Xi b < 0) : PositiveOnLineZetaZeroOrdinatesNonempty := by
  -- Direct application requires a > 0; we approximate `Xi 0` by `Xi (b/2)`
  -- and reduce to r115's sign-change theorem, using continuity of `Xi`.
  -- Cleaner path: use the fact that `Xi` is continuous on the CLOSED
  -- interval `[0, b]` and sign values at 0 and b differ; IVT gives
  -- a zero in `[0, b]`, and since `Xi 0 ≠ 0` (implicit from the
  -- strict `< 0` combination), the zero is strictly in `(0, b]`.
  have hcont : ContinuousOn Xi (Set.uIcc 0 b) := continuous_Xi.continuousOn
  have h0 : (0 : ℝ) ∈ Set.uIcc (Xi 0) (Xi b) := by
    rcases mul_neg_iff.mp hsign with ⟨hpa, hnb⟩ | ⟨hna, hpb⟩
    · exact Set.mem_uIcc.mpr (Or.inr ⟨hnb.le, hpa.le⟩)
    · exact Set.mem_uIcc.mpr (Or.inl ⟨hna.le, hpb.le⟩)
  obtain ⟨t, htmem, htzero⟩ := intermediate_value_uIcc hcont h0
  have hXi0 : Xi 0 ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hsign
    exact absurd hsign (lt_irrefl _)
  have h_uIcc : Set.uIcc 0 b = Set.Icc 0 b := Set.uIcc_of_le hb.le
  rw [h_uIcc] at htmem
  have ht_pos : 0 < t := by
    rcases lt_or_eq_of_le htmem.1 with hlt | heq
    · exact hlt
    · exfalso; exact hXi0 (heq ▸ htzero)
  exact xi_zero_at_pos_implies_nonempty ht_pos htzero

/-! ## §5 Axiom check. -/

#print axioms PrincipiaTractalis.HardyRouteXiEvenness.xi_even
#print axioms PrincipiaTractalis.HardyRouteXiEvenness.xi_symm_at_zero
#print axioms PrincipiaTractalis.HardyRouteXiEvenness.xi_is_real_of_eq
#print axioms PrincipiaTractalis.HardyRouteXiEvenness.xi_sign_change_via_zero

end PrincipiaTractalis.HardyRouteXiEvenness
