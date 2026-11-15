/-
# NS Route A item 3 — pointwise Cauchy-Schwarz discharge.

★ 2026-11-15 — discharges the first of the three named residuals in
`PF/Analytic/YoungConvolutionL1L2_2026_11_15.lean`:

  `YoungL1L2_Pointwise_CauchySchwarz_Nat` (residual #1)
      — now closed unconditionally via mathlib Hölder at p = q = 2.

The two remaining named residuals
(`YoungL1L2_FubiniTonelliSwap`, `YoungL1L2_IntegrableConstantPull`)
remain as per `YoungConvolutionL1L2_2026_11_15.lean` and will be
discharged in subsequent passes against `MeasureTheory.lintegral_lintegral_swap`
+ `Measure.IsAddLeftInvariant` and `lintegral_const_mul''` +
`Measure.lintegral_prod_right'` respectively.

## Discharge technique

The named residual asserts:
    `(∫⁻ t, f t * F t ∂μ) ^ 2 ≤ (∫⁻ t, f t ∂μ) * (∫⁻ t, f t * F t ^ 2 ∂μ)`.

Proof: let `g₁ t := f t ^ ((1:ℝ)/2)` and `g₂ t := g₁ t · F t`.  Then
`g₁ · g₂ = f · F` and `g₁^2 = f`, `g₂^2 = f · F^2` (all ENNReal rpow
identities via `ENNReal.rpow_mul` + `ENNReal.rpow_one`).

Apply `ENNReal.lintegral_mul_le_Lp_mul_Lq` at `p = q = 2` (certified
by `Real.HolderConjugate.two_two`) to obtain
    `∫⁻ g₁ · g₂ ≤ (∫⁻ g₁²)^(1/2) · (∫⁻ g₂²)^(1/2)`
which rewrites to
    `∫⁻ f · F ≤ (∫⁻ f)^(1/2) · (∫⁻ f · F²)^(1/2)`.
Square both sides via `pow_le_pow_left'` and simplify
`((·)^(1/2))² = (·)` via `ENNReal.rpow_mul` to conclude.

Routine analytic calculation on `ENNReal.rpow`.  Three-axiom bar.

SPDX-License-Identifier: Apache-2.0
Author: Pablo Cohen.  2026-11-15.
-/

import PF.Analytic.YoungConvolutionL1L2_2026_11_15
import Mathlib.MeasureTheory.Integral.MeanInequalities

open MeasureTheory
open scoped ENNReal NNReal

namespace PF.Analytic.YoungConvolutionL1L2

variable {G : Type*} [MeasurableSpace G] [AddGroup G]

/-! ## §1 — Local rpow helpers. -/

/-- **`rpow_half_sq_self`** — `(x ^ (1/2)) ^ (2 : ℝ) = x` for ENNReal `x`. -/
private lemma rpow_half_sq_self (x : ℝ≥0∞) : (x ^ ((1 : ℝ)/2)) ^ (2 : ℝ) = x := by
  rw [← ENNReal.rpow_mul]
  norm_num

/-- **`rpow_half_mul_sq`** — `(x ^ (1/2) · y) ^ (2 : ℝ) = x · y^2` for ENNReal. -/
private lemma rpow_half_mul_sq (x y : ℝ≥0∞) :
    (x ^ ((1 : ℝ)/2) * y) ^ (2 : ℝ) = x * y ^ (2 : ℝ) := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2),
      rpow_half_sq_self]

/-- **`rpow_half_mul_half_self`** — `x^(1/2) · x^(1/2) = x` for ENNReal. -/
private lemma rpow_half_mul_half_self (x : ℝ≥0∞) :
    x ^ ((1 : ℝ)/2) * x ^ ((1 : ℝ)/2) = x := by
  rw [← ENNReal.rpow_add_of_nonneg (x := x) ((1:ℝ)/2) ((1:ℝ)/2)
        (by norm_num) (by norm_num)]
  norm_num

/-- **`rpow_sq_mul_rpow_sq`** — `(a^(1/2) · b^(1/2))^2 = a · b` for ENNReal. -/
private lemma rpow_sq_mul_rpow_sq (a b : ℝ≥0∞) :
    (a ^ ((1 : ℝ)/2) * b ^ ((1 : ℝ)/2)) ^ 2 = a * b := by
  rw [pow_two, mul_mul_mul_comm,
      rpow_half_mul_half_self, rpow_half_mul_half_self]

/-! ## §2 — Discharge of the pointwise Cauchy-Schwarz named residual. -/

/-- **`pointwise_cauchy_schwarz_discharge`** — unconditional discharge
of the named residual `YoungL1L2_Pointwise_CauchySchwarz_Nat`.

For any σ-finite measure `μ` and any non-negative measurable
`f F : G → ℝ≥0∞`,
    `(∫⁻ t, f t * F t ∂μ) ^ 2
      ≤ (∫⁻ t, f t ∂μ) * (∫⁻ t, f t * F t ^ 2 ∂μ)`.

Proof: write `f·F = f^(1/2) · (f^(1/2) · F)`, apply Hölder at
`p = q = 2` via `ENNReal.lintegral_mul_le_Lp_mul_Lq`, simplify the
`(·)^2` factors, then square. -/
theorem pointwise_cauchy_schwarz_discharge
    (μ : Measure G) (f F : G → ℝ≥0∞) :
    YoungL1L2_Pointwise_CauchySchwarz_Nat μ f F := by
  intro hf hF
  classical
  -- Set up `g₁ := f^(1/2)` and `g₂ := f^(1/2) · F`.
  set g1 : G → ℝ≥0∞ := fun t => f t ^ ((1:ℝ)/2) with hg1_def
  set g2 : G → ℝ≥0∞ := fun t => f t ^ ((1:ℝ)/2) * F t with hg2_def
  have hg1 : AEMeasurable g1 μ := hf.pow_const _
  have hg2 : AEMeasurable g2 μ := hg1.mul hF
  -- Hölder at p = q = 2.
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have hHolder :
      (∫⁻ t, (g1 * g2) t ∂μ)
        ≤ (∫⁻ t, g1 t ^ (2 : ℝ) ∂μ) ^ ((1:ℝ)/2)
          * (∫⁻ t, g2 t ^ (2 : ℝ) ∂μ) ^ ((1:ℝ)/2) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hg1 hg2
    -- Hölder result has `^ (1 / p)` with `p = 2`.  Normalize `1/2`.
    simpa using h
  -- Rewrite the LHS of Hölder: g1 * g2 = f^(1/2) · (f^(1/2) · F) = f · F.
  have hLHS : (∫⁻ t, (g1 * g2) t ∂μ) = ∫⁻ t, f t * F t ∂μ := by
    refine lintegral_congr_ae (Filter.Eventually.of_forall ?_)
    intro t
    simp only [g1, g2, Pi.mul_apply]
    rw [← mul_assoc, rpow_half_mul_half_self]
  -- Rewrite the first RHS factor: (f^(1/2))^(2:ℝ) = f.
  have hRHS1 : (∫⁻ t, g1 t ^ (2 : ℝ) ∂μ) = ∫⁻ t, f t ∂μ := by
    refine lintegral_congr_ae (Filter.Eventually.of_forall ?_)
    intro t
    simp only [g1]
    exact rpow_half_sq_self (f t)
  -- Rewrite the second RHS factor: (f^(1/2) · F)^(2:ℝ) = f · F^(2:ℝ).
  have hRHS2 : (∫⁻ t, g2 t ^ (2 : ℝ) ∂μ) = ∫⁻ t, f t * F t ^ 2 ∂μ := by
    refine lintegral_congr_ae (Filter.Eventually.of_forall ?_)
    intro t
    simp only [g2]
    rw [rpow_half_mul_sq]
    congr 1
    -- Convert `F t ^ (2 : ℝ)` to `F t ^ 2` (Monoid.npow).
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num,
        ENNReal.rpow_natCast]
  rw [hLHS, hRHS1, hRHS2] at hHolder
  -- Square both sides.
  have hSquared :
      (∫⁻ t, f t * F t ∂μ) ^ 2
        ≤ ((∫⁻ t, f t ∂μ) ^ ((1:ℝ)/2) * (∫⁻ t, f t * F t ^ 2 ∂μ) ^ ((1:ℝ)/2)) ^ 2 :=
    pow_le_pow_left' hHolder 2
  -- Simplify the RHS square via rpow_sq_mul_rpow_sq.
  rw [rpow_sq_mul_rpow_sq] at hSquared
  exact hSquared

/-! ## §3 — Axiom audit. -/

#check @pointwise_cauchy_schwarz_discharge

end PF.Analytic.YoungConvolutionL1L2
