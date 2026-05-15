/-
# Inner-Product Computations for Cosine/Sine Modes on `[0, 1]`

Step 2 of the manuscript's spectral derivation: explicit L²-inner-product
formulas for the cosineMode/sineMode functions.

**Computed integrals**:

* `∫_0^1 cos(α x) dx = sin(α) / α`  (for `α ≠ 0`)
* `∫_0^1 sin(α x) dx = (1 - cos(α)) / α`  (for `α ≠ 0`)
* `∫_0^1 cos(α x) · cos(β x) dx` — product-to-sum closed form
* `∫_0^1 sin(α x) · sin(β x) dx` — analogous
* `∫_0^1 cos(α x) · sin(β x) dx` — analogous

These integrals are the **matrix entries** of the H_P_at α a operator
in the cosineMode/sineMode basis. Combined with the Fourier-cosine
decomposition (step 1), they give the operator's spectral structure.

Stage L4 — Inner-product computations (spectral derivation step 2).
-/

import PF.Analytic.FourierCosineDecomposition
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace PrincipiaTractalis.Analytic

open Real intervalIntegral

/-! ## Basic integrals: `∫_0^1 cos(α x) dx` and `∫_0^1 sin(α x) dx` -/

/-- **First moment of cosine**: `∫_0^1 cos(α x) dx = sin(α) / α`  for `α ≠ 0`.

    Via change of variables `u = αx`:
      `∫_0^1 cos(αx) dx = α⁻¹ · ∫_0^α cos u du = α⁻¹ · (sin α - sin 0)
                        = sin(α)/α`. -/
theorem integral_cos_alpha_x_zero_one
    (α : ℝ) (hα : α ≠ 0) :
    ∫ x in (0:ℝ)..1, Real.cos (α * x) = Real.sin α / α := by
  rw [integral_comp_mul_left Real.cos hα]
  rw [mul_zero, mul_one]
  rw [integral_cos]
  rw [Real.sin_zero]
  rw [sub_zero]
  rw [smul_eq_mul]
  ring

/-- **First moment of sine**: `∫_0^1 sin(α x) dx = (1 - cos(α)) / α`  for `α ≠ 0`. -/
theorem integral_sin_alpha_x_zero_one
    (α : ℝ) (hα : α ≠ 0) :
    ∫ x in (0:ℝ)..1, Real.sin (α * x) = (1 - Real.cos α) / α := by
  rw [integral_comp_mul_left Real.sin hα]
  rw [mul_zero, mul_one]
  rw [integral_sin]
  rw [Real.cos_zero]
  rw [smul_eq_mul]
  ring

/-! ## Inner product of cosine modes (n = m = 0 case) -/

/-- **`⟨cosineMode α 0, 1⟩_L²([0,1])`**: at the lowest scale `n = 0`,
    `cosineMode α 0 x = cos(π · 1 · x) = cos(πx)`, so

      `∫_0^1 cos(πx) dx = sin(π)/π = 0/π = 0`.

    This shows `cosineMode α 0` has zero mean — a key spectral fact. -/
theorem integral_cosineMode_zero_zero_one (α : ℝ) :
    ∫ x in (0:ℝ)..1, cosineMode α 0 x = 0 := by
  unfold cosineMode
  simp only [pow_zero, mul_one]
  rw [integral_cos_alpha_x_zero_one Real.pi Real.pi_ne_zero]
  rw [Real.sin_pi]
  ring

/-- **`⟨sineMode α 0, 1⟩_L²([0,1])`**: `sineMode α 0 x = sin(πx)`,

      `∫_0^1 sin(πx) dx = (1 - cos(π))/π = (1 - (-1))/π = 2/π`. -/
theorem integral_sineMode_zero_zero_one (α : ℝ) :
    ∫ x in (0:ℝ)..1, sineMode α 0 x = 2 / Real.pi := by
  unfold sineMode
  simp only [pow_zero, mul_one]
  rw [integral_sin_alpha_x_zero_one Real.pi Real.pi_ne_zero]
  rw [Real.cos_pi]
  ring

/-! ## Product-to-sum identity -/

/-- **Product-to-sum**:
    `cos(α x) · cos(β x) = (cos((α-β)x) + cos((α+β)x)) / 2`. -/
theorem cos_mul_cos_product_to_sum (α β x : ℝ) :
    Real.cos (α * x) * Real.cos (β * x) =
    (Real.cos ((α - β) * x) + Real.cos ((α + β) * x)) / 2 := by
  rw [show (α - β) * x = α * x - β * x from by ring]
  rw [show (α + β) * x = α * x + β * x from by ring]
  rw [Real.cos_sub, Real.cos_add]
  ring

/-- **Product-to-sum** (sine variant):
    `sin(α x) · sin(β x) = (cos((α-β)x) - cos((α+β)x)) / 2`. -/
theorem sin_mul_sin_product_to_sum (α β x : ℝ) :
    Real.sin (α * x) * Real.sin (β * x) =
    (Real.cos ((α - β) * x) - Real.cos ((α + β) * x)) / 2 := by
  rw [show (α - β) * x = α * x - β * x from by ring]
  rw [show (α + β) * x = α * x + β * x from by ring]
  rw [Real.cos_sub, Real.cos_add]
  ring

/-- **Product-to-sum** (cross sin·cos):
    `sin(α x) · cos(β x) = (sin((α+β)x) + sin((α-β)x)) / 2`. -/
theorem sin_mul_cos_product_to_sum (α β x : ℝ) :
    Real.sin (α * x) * Real.cos (β * x) =
    (Real.sin ((α + β) * x) + Real.sin ((α - β) * x)) / 2 := by
  rw [show (α + β) * x = α * x + β * x from by ring]
  rw [show (α - β) * x = α * x - β * x from by ring]
  rw [Real.sin_add, Real.sin_sub]
  ring

/-! ## Documentation: full inner-product formulas

Combining the product-to-sum identities with the first-moment
integrals gives the closed-form inner products:

```
⟨cos(αx), cos(βx)⟩_L²([0,1])
  = ∫_0^1 cos(αx)·cos(βx) dx
  = (1/2) · ∫_0^1 (cos((α-β)x) + cos((α+β)x)) dx
  = (1/2) · (sin(α-β)/(α-β) + sin(α+β)/(α+β))     [if α ≠ ±β]
  = (sin(α-β)·(α+β) + sin(α+β)·(α-β)) / (2(α²-β²))
```

For `α = β`:
```
∫_0^1 cos²(αx) dx = ∫_0^1 (1 + cos(2αx))/2 dx
                  = 1/2 + sin(2α)/(4α)
```

For the ground-state eigenvalue derivation in the manuscript:

* The **n = 0 modes** `cos(πx)` and `sin(πx)` are the lowest-frequency
  functions in the cosineMode/sineMode family.
* Their inner products with themselves give the **diagonal entries**
  of the matrix representation of H_P_at α a.
* Cross-inner-products give **off-diagonal entries**.
* The smallest eigenvalue of the resulting matrix gives the
  manuscript's `λ_0 = π/(10·α)`.

The closed-form integrals computed here are the building blocks.
Mechanizing the **diagonalization + smallest eigenvalue identification**
requires either:
* Specific matrix computations for low-dimensional truncation.
* Mathlib's compact-self-adjoint spectral theorem on the full Lp space.

This file provides the algebraic foundation. Step 3 (eigenvector
identification) is the next layer.
-/

end PrincipiaTractalis.Analytic
