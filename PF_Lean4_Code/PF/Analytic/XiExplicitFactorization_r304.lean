/-
# r304: Xi EXPLICIT FACTORIZATION — Xi t as Re(ζ · Gammaℝ) on the critical line
#      (strictly-necessary infrastructure for the Xi_Positive_At_15 discharge attempt)

★ 2026-08-20 r304 — first step toward discharging the aggregate's
Xi witness residual `Xi_Positive_At_15 := 0 < Xi 15`.

The classical value `Xi 15 = Λ(1/2 + 15i).re` is known to be positive
because `1/2 + 15i` lies between the first two Riemann zeros
(t₁ ≈ 14.135, t₂ ≈ 21.022) at which Λ vanishes on the critical line.
A rigorous discharge requires evaluating this complex-valued
expression numerically with certified error bounds — a substantial
downstream project.

r304 delivers the FIRST strictly-necessary reduction: on the critical
line, `Λ(s) = ζ(s) · Gammaℝ(s)` (mathlib's `riemannZeta_def_of_ne_zero`
rearranged, using `Gammaℝ_ne_zero_of_re_pos` since `re ⟨1/2, t⟩ = 1/2 > 0`).
This decomposes the Xi(15) target into two multiplicative factors
(`riemannZeta ⟨1/2, 15⟩` and `Gammaℝ ⟨1/2, 15⟩`) that FUTURE landings
can attack independently via mathlib's ζ- and Γ-evaluation
infrastructure.

## What r304 delivers

- `Gammaℝ_critical_ne_zero : ∀ t : ℝ, Gammaℝ ⟨1/2, t⟩ ≠ 0` —
  from `Gammaℝ_ne_zero_of_re_pos` at `re ⟨1/2, t⟩ = 1/2 > 0`.

- `completedRiemannZeta_critical_eq_zeta_mul_Gammaℝ : ∀ t : ℝ,
    completedRiemannZeta ⟨1/2, t⟩ = riemannZeta ⟨1/2, t⟩ * Gammaℝ ⟨1/2, t⟩`
  — rearrangement of mathlib's `riemannZeta_def_of_ne_zero`.

- `Xi_eq_re_zeta_mul_Gammaℝ : ∀ t : ℝ,
    Xi t = (riemannZeta ⟨1/2, t⟩ * Gammaℝ ⟨1/2, t⟩).re` — the general
  explicit-factorization form.

- `Xi_at_15_eq_re_product : Xi 15 = (riemannZeta ⟨1/2, 15⟩ * Gammaℝ ⟨1/2, 15⟩).re`
  — specialization to t = 15 (the discharge target).

- `Xi_Positive_At_15_iff_re_product_pos : Xi_Positive_At_15 ↔
    0 < (riemannZeta ⟨1/2, 15⟩ * Gammaℝ ⟨1/2, 15⟩).re` — the residual
  restated in mathlib-native primitives ready for numerical attack.

## Framework-first scope

Not a discharge. Strictly-necessary infrastructure that reduces the
aggregate's Xi witness residual to a form that:
- lives entirely in mathlib primitives (`riemannZeta`, `Gammaℝ`),
- exhibits the multiplicative structure (ζ · Gammaℝ) so that future
  numerical-evaluation landings can attack the two factors
  independently,
- eliminates the `completedRiemannZeta` layer of the definition,
  which is `noncomputable` and less-developed in mathlib than the
  underlying ζ and Γ APIs.

Book anchors: Ch 20 § 20.4 (RH via Fractal Resonance), Ch 34A § 34A.5.
Paper `principia_fractalis_alpha_skeleton_2026-07-13.pdf` § 6.
-/

import PF.Analytic.XiRealWitness
import PF.Analytic.UnifiedClayClosureViaRouteBSpecificXiAndFullPinning_r288

namespace PrincipiaTractalis.XiExplicitFactorization

open PrincipiaTractalis.XiRealWitness
open PrincipiaTractalis.UnifiedClayClosureViaRouteBSpecificXiAndFullPinning
open Complex

/-! ## §1 Gammaℝ is nonzero on the critical line. -/

/-- **`Gammaℝ_critical_ne_zero`** — for every real `t`, `Gammaℝ ⟨1/2, t⟩ ≠ 0`.

Direct from mathlib's `Gammaℝ_ne_zero_of_re_pos`: since
`(⟨1/2, t⟩ : ℂ).re = 1/2 > 0`, the Deligne-normalized real Gamma
factor is nonzero. -/
theorem Gammaℝ_critical_ne_zero (t : ℝ) : Gammaℝ ⟨1/2, t⟩ ≠ 0 := by
  apply Gammaℝ_ne_zero_of_re_pos
  show (0 : ℝ) < (1/2 : ℝ)
  norm_num

/-! ## §2 The critical-line factorization Λ = ζ · Gammaℝ. -/

/-- **`completedRiemannZeta_critical_eq_zeta_mul_Gammaℝ`** — on the
critical line, `Λ(1/2 + it) = ζ(1/2 + it) · Gammaℝ(1/2 + it)`.

Rearrangement of mathlib's `riemannZeta_def_of_ne_zero`
(`ζ s = Λ s / Gammaℝ s` for `s ≠ 0`) using `Gammaℝ_critical_ne_zero`
to justify the multiplication. -/
theorem completedRiemannZeta_critical_eq_zeta_mul_Gammaℝ (t : ℝ) :
    completedRiemannZeta ⟨1/2, t⟩
      = riemannZeta ⟨1/2, t⟩ * Gammaℝ ⟨1/2, t⟩ := by
  have hne0 : (⟨1/2, t⟩ : ℂ) ≠ 0 := critical_point_ne_zero t
  have hGne : Gammaℝ ⟨1/2, t⟩ ≠ 0 := Gammaℝ_critical_ne_zero t
  have hζ : riemannZeta ⟨1/2, t⟩
      = completedRiemannZeta ⟨1/2, t⟩ / Gammaℝ ⟨1/2, t⟩ :=
    riemannZeta_def_of_ne_zero hne0
  -- Multiply both sides by Gammaℝ ⟨1/2, t⟩ on the right and cancel.
  field_simp [hGne] at hζ
  exact hζ.symm

/-! ## §3 Xi as Re(ζ · Gammaℝ). -/

/-- **`Xi_eq_re_zeta_mul_Gammaℝ`** — for every real `t`,
`Xi t = (riemannZeta ⟨1/2, t⟩ * Gammaℝ ⟨1/2, t⟩).re`.

Unfolds `Xi` (defined as `(completedRiemannZeta ⟨1/2, t⟩).re`) via
`completedRiemannZeta_critical_eq_zeta_mul_Gammaℝ`. -/
theorem Xi_eq_re_zeta_mul_Gammaℝ (t : ℝ) :
    Xi t = (riemannZeta ⟨1/2, t⟩ * Gammaℝ ⟨1/2, t⟩).re := by
  unfold Xi
  rw [completedRiemannZeta_critical_eq_zeta_mul_Gammaℝ]

/-! ## §4 Specialization to t = 15. -/

/-- **`Xi_at_15_eq_re_product`** — `Xi 15 = (riemannZeta ⟨1/2, 15⟩ * Gammaℝ ⟨1/2, 15⟩).re`. -/
theorem Xi_at_15_eq_re_product :
    Xi 15
      = (riemannZeta ⟨(1 : ℝ)/2, (15 : ℝ)⟩ * Gammaℝ ⟨(1 : ℝ)/2, (15 : ℝ)⟩).re :=
  Xi_eq_re_zeta_mul_Gammaℝ 15

/-- **`Xi_Positive_At_15_iff_re_product_pos`** — the aggregate's Xi
witness residual `Xi_Positive_At_15` restated in mathlib-native
primitives ready for numerical attack:

  `Xi_Positive_At_15 ↔ 0 < (riemannZeta ⟨1/2, 15⟩ * Gammaℝ ⟨1/2, 15⟩).re`

Future landings can attack the two multiplicative factors
(`riemannZeta ⟨1/2, 15⟩` and `Gammaℝ ⟨1/2, 15⟩`) independently via
mathlib's ζ- and Γ-evaluation infrastructure. -/
theorem Xi_Positive_At_15_iff_re_product_pos :
    Xi_Positive_At_15 ↔
      0 < (riemannZeta ⟨(1 : ℝ)/2, (15 : ℝ)⟩ * Gammaℝ ⟨(1 : ℝ)/2, (15 : ℝ)⟩).re := by
  unfold Xi_Positive_At_15
  rw [Xi_at_15_eq_re_product]

/-! ## §5 Axiom checks. -/

#print axioms
  PrincipiaTractalis.XiExplicitFactorization.Gammaℝ_critical_ne_zero
#print axioms
  PrincipiaTractalis.XiExplicitFactorization.completedRiemannZeta_critical_eq_zeta_mul_Gammaℝ
#print axioms
  PrincipiaTractalis.XiExplicitFactorization.Xi_eq_re_zeta_mul_Gammaℝ
#print axioms
  PrincipiaTractalis.XiExplicitFactorization.Xi_at_15_eq_re_product
#print axioms
  PrincipiaTractalis.XiExplicitFactorization.Xi_Positive_At_15_iff_re_product_pos

end PrincipiaTractalis.XiExplicitFactorization
