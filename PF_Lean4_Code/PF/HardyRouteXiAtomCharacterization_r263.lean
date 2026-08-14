/-
# r263: HARDY ROUTE — Xi ZERO CHARACTERIZATION OF THE RH ATOM.

★ 2026-08-13 r263 — proves that the Wave 58/59 atomic RH residual
`PositiveOnLineZetaZeroOrdinatesNonempty` is EQUIVALENT to the
existence of a positive zero of the real function `Xi`.

r115's `xi_zero_at_pos_implies_nonempty` gives one direction. r263
supplies the reverse direction and bundles both into a biconditional.

## What r263 adds

- `xi_t_zero_iff_zeta_at_critical_zero`: for any real `t`,
  `Xi t = 0 ↔ riemannZeta ⟨1/2, t⟩ = 0`. This holds unconditionally
  (no `0 < t` hypothesis; the critical point `⟨1/2, t⟩` is always
  nonzero and always has `re = 1/2 > 0`, so mathlib's
  `Gammaℝ_ne_zero_of_re_pos` and the `Λ = Gammaℝ · ζ` factorization
  apply).

- `pos_ordinate_nonempty_iff_xi_pos_zero`:
  `PositiveOnLineZetaZeroOrdinatesNonempty ↔ ∃ t : ℝ, 0 < t ∧ Xi t = 0`.
  Bundles the two directions.

## Route B substrate value

Combined with the r255 Wave 58/59 one-fact reduction
`rh_wave59_one_fact_capstone: PF_T3SymIsHilbertPolyaOperator_Positive ↔
PositiveOnLineZetaZeroOrdinatesNonempty`, r263 gives a triple
equivalence:

  `PF_T3SymIsHilbertPolyaOperator_Positive`
    ↔  `PositiveOnLineZetaZeroOrdinatesNonempty`  (r255)
    ↔  `∃ t : ℝ, 0 < t ∧ Xi t = 0`                (r263)

So the framework's HP-positive Prop, the RH atomic Prop, and the
existence of a positive zero of `Xi` are the SAME Prop (up to
biconditional).

## Scope

* NOT novel — the biconditional is a direct consequence of the
  factorization `Λ = Gammaℝ · ζ` on the strip `re > 0`.
* NOT a Millennium discharge.
* IS a structural equivalence sharpening the r255-r261 reductions.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.HardyRouteBAlgebraicLayerCapstone_r262

open scoped Real ComplexConjugate

namespace PrincipiaTractalis.HardyRouteXiAtomCharacterization

open PrincipiaTractalis.XiRealWitness
open PrincipiaTractalis.HardyRouteXiEvenness
open PrincipiaTractalis.HardyRouteXiZeroFactored
open PrincipiaTractalis.HardyRouteGammaRHalfReal
open PrincipiaTractalis.HardyRouteXiZeroSignReduction
open PrincipiaTractalis.HardyRouteZetaHalfReal
open PrincipiaTractalis.HardyRouteBAlgebraicLayerCapstone
open PrincipiaTractalis.HilbertPolyaPositiveReductionToCountability
open PrincipiaTractalis.HilbertPolyaPositiveImageRigidity
open Complex

/-! ## §1 `Xi t = 0` iff `ζ(1/2 + it) = 0`. -/

/-- **`gammaR_critical_ne_zero`** — the archimedean Γ-factor at any
critical point `⟨1/2, t⟩ : ℂ` is nonzero, since `re ⟨1/2, t⟩ = 1/2 > 0`. -/
theorem gammaR_critical_ne_zero (t : ℝ) : Gammaℝ (⟨1/2, t⟩ : ℂ) ≠ 0 := by
  apply Gammaℝ_ne_zero_of_re_pos
  show (0 : ℝ) < (⟨1/2, t⟩ : ℂ).re
  norm_num

/-- **`completedRiemannZeta_critical_eq`** — the identity
`Λ ⟨1/2, t⟩ = ζ ⟨1/2, t⟩ · Gammaℝ ⟨1/2, t⟩` for every real `t`.
Rearrangement of mathlib's `riemannZeta_def_of_ne_zero`. -/
theorem completedRiemannZeta_critical_eq (t : ℝ) :
    completedRiemannZeta (⟨1/2, t⟩ : ℂ)
      = riemannZeta (⟨1/2, t⟩ : ℂ) * Gammaℝ (⟨1/2, t⟩ : ℂ) := by
  have hne : (⟨1/2, t⟩ : ℂ) ≠ 0 := critical_point_ne_zero t
  rw [riemannZeta_def_of_ne_zero hne,
      div_mul_cancel₀ _ (gammaR_critical_ne_zero t)]

/-- **`xi_t_zero_iff_zeta_at_critical_zero`** — the real function `Xi`
vanishes at `t` iff the Riemann zeta function vanishes at `⟨1/2, t⟩`,
for EVERY real `t`. Unconditional (no `0 < t` needed).

Forward direction: if `Xi t = 0` then `(Λ ⟨1/2, t⟩).re = 0`; combined
with r115's `Xi_im_eq_zero`, `Λ ⟨1/2, t⟩ = 0`; then
`ζ = Λ / Gammaℝ = 0`.

Reverse direction: if `ζ = 0` then `Λ = ζ · Gammaℝ = 0`; then
`Xi t = (Λ).re = 0`. -/
theorem xi_t_zero_iff_zeta_at_critical_zero (t : ℝ) :
    Xi t = 0 ↔ riemannZeta (⟨1/2, t⟩ : ℂ) = 0 := by
  have hne : (⟨1/2, t⟩ : ℂ) ≠ 0 := critical_point_ne_zero t
  constructor
  · intro hXi
    have hΛ_zero : completedRiemannZeta (⟨1/2, t⟩ : ℂ) = 0 := by
      apply Complex.ext
      · show (completedRiemannZeta (⟨1/2, t⟩ : ℂ)).re = 0
        exact hXi
      · exact Xi_im_eq_zero t
    rw [riemannZeta_def_of_ne_zero hne, hΛ_zero, zero_div]
  · intro hζ
    have hΛ_zero : completedRiemannZeta (⟨1/2, t⟩ : ℂ) = 0 := by
      rw [completedRiemannZeta_critical_eq, hζ, zero_mul]
    unfold Xi
    rw [hΛ_zero, Complex.zero_re]

/-! ## §2 Biconditional bundling. -/

/-- **`pos_ordinate_nonempty_iff_xi_pos_zero`** — the Wave 58/59 RH
atomic residual is EQUIVALENT to the existence of a positive zero of
the real function `Xi`. Bundles r115's forward direction with r263's
reverse. -/
theorem pos_ordinate_nonempty_iff_xi_pos_zero :
    PositiveOnLineZetaZeroOrdinatesNonempty
      ↔ ∃ t : ℝ, 0 < t ∧ Xi t = 0 := by
  constructor
  · rintro ⟨t, ht_pos, hζ⟩
    refine ⟨t, ht_pos, ?_⟩
    exact (xi_t_zero_iff_zeta_at_critical_zero t).mpr hζ
  · rintro ⟨t, ht_pos, hXi⟩
    exact xi_zero_at_pos_implies_nonempty ht_pos hXi

/-! ## §3 Axiom check. -/

#print axioms PrincipiaTractalis.HardyRouteXiAtomCharacterization.gammaR_critical_ne_zero
#print axioms PrincipiaTractalis.HardyRouteXiAtomCharacterization.completedRiemannZeta_critical_eq
#print axioms PrincipiaTractalis.HardyRouteXiAtomCharacterization.xi_t_zero_iff_zeta_at_critical_zero
#print axioms PrincipiaTractalis.HardyRouteXiAtomCharacterization.pos_ordinate_nonempty_iff_xi_pos_zero

end PrincipiaTractalis.HardyRouteXiAtomCharacterization
