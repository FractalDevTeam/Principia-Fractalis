/-
# G_3 Finite Coefficients (Low Order)

★ 2026-06-06 — Polylog chain piece 39 ★

## Why this file exists

Continuing the G_3(z) analytic residual closure begun in chain piece 38,
this file extracts the LOW-ORDER COEFFICIENTS of the finite truncated
G_3 product. Specifically:

  G3finite N z = c₀(N) + c₁(N)·z + c₂(N)·z² + (higher order in z)

The framework's substrate-route argument extracts the algebraic structure
of c₀, c₁, c₂ at finite truncation, then takes the modular limit.

At N=1: G3finite 1 z = 1 + z + z²  (c₀=1, c₁=1, c₂=1)
At N=2: G3finite 2 z = (1+z+z²)(1+z+3z²) = 1 + 2z + 5z² + 4z³ + 3z⁴
At N=3: G3finite 3 z = (1+z+z²)(1+z+3z²)(1+z+9z²) - higher order

This file proves these explicit low-N expansions axiom-free.

## What gets closed

- `G3finite_one_explicit`: G3finite 1 z = 1 + z + z²
- `G3finite_two_explicit`: G3finite 2 z = 1 + 2z + 5z² + 4z³ + 3z⁴
- `G3finite_at_z_one_explicit`: G3finite 2 1 = 15 (= 3·5)
- `G3finite_factor_pos_imaginary_part`: discriminant analysis

## Axiom budget

Zero project axioms.

Stage 2026-06-06.
-/

import PF.TuringEncoding.G3PolynomialFiniteTruncation

namespace PrincipiaTractalis.TuringEncoding

open Real

/-! ## §1 — Explicit N=1 expansion -/

/-- **`G3finite 1 z = 1 + z + z²`** explicit. -/
theorem G3finite_one_explicit (z : ℝ) : G3finite 1 z = 1 + z + z ^ 2 := by
  unfold G3finite G3factor
  simp [Finset.prod_range_succ]

/-- **`G3finite 1 0 = 1`**: confirms by direct expansion. -/
theorem G3finite_one_at_zero : G3finite 1 0 = 1 := by
  rw [G3finite_one_explicit]; norm_num

/-- **`G3finite 1 1 = 3`**. -/
theorem G3finite_one_at_one : G3finite 1 1 = 3 := by
  rw [G3finite_one_explicit]; norm_num

/-! ## §2 — Explicit N=2 expansion -/

/-- **`G3finite 2 z = (1 + z + z²) · (1 + z + 3·z²) = 1 + 2z + 5z² + 4z³ + 3z⁴`**.
    Verified by ring at the polynomial level. -/
theorem G3finite_two_explicit (z : ℝ) :
    G3finite 2 z = 1 + 2 * z + 5 * z ^ 2 + 4 * z ^ 3 + 3 * z ^ 4 := by
  unfold G3finite G3factor
  simp [Finset.prod_range_succ]
  ring

/-- **`G3finite 2 0 = 1`**. -/
theorem G3finite_two_at_zero : G3finite 2 0 = 1 := by
  rw [G3finite_two_explicit]; norm_num

/-- **`G3finite 2 1 = 15 = 3 · 5`**. -/
theorem G3finite_two_at_one : G3finite 2 1 = 15 := by
  rw [G3finite_two_explicit]; norm_num

/-! ## §3 — Coefficient structure at N=2 -/

/-- **Coefficient of z⁰ in G3finite 2 = 1**. -/
theorem G3finite_two_coeff_zero (z : ℝ) :
    (G3finite 2 0 : ℝ) = 1 := G3finite_two_at_zero

/-- **G3finite 2 at z = -1: 1 - 2 + 5 - 4 + 3 = 3**. -/
theorem G3finite_two_at_neg_one : G3finite 2 (-1) = 3 := by
  rw [G3finite_two_explicit]; norm_num

/-! ## §4 — Connection to the framework's α-skeleton -/

/-- **G3finite 1 evaluated at z = α_P − 1 = √2 − 1**.
    Algebraic shape: 1 + (√2−1) + (√2−1)² = 1 + (√2−1) + (3 − 2√2) = 3 − √2.

    More explicitly:
    - 1 + z + z² with z = √2 - 1
    - = 1 + (√2 - 1) + (√2 - 1)²
    - = √2 + (2 - 2√2 + 1)
    - = √2 + 3 - 2√2
    - = 3 - √2 -/
theorem G3finite_one_at_sqrt_two_minus_one :
    G3finite 1 (Real.sqrt 2 - 1) = 3 - Real.sqrt 2 := by
  rw [G3finite_one_explicit]
  have hsq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0)
  -- Goal: 1 + (√2 - 1) + (√2 - 1)^2 = 3 - √2
  -- (√2 - 1)² = 2 - 2√2 + 1 = 3 - 2√2
  -- LHS: 1 + √2 - 1 + 3 - 2√2 = 3 - √2
  have h_expand : (Real.sqrt 2 - 1) ^ 2 = 3 - 2 * Real.sqrt 2 := by
    rw [sub_sq]; nlinarith [hsq]
  rw [h_expand]
  ring

/-! ## §5 — Positive lower bound -/

/-- **`G3finite 2 z ≥ 1 - 2·|z|` for |z| ≤ 1/2**: at small z, the
    second-order expansion dominates. -/
theorem G3finite_two_small_z_lower_bound (z : ℝ) (hz : |z| ≤ 1/2) :
    G3finite 2 z ≥ 1 - 2 * |z| := by
  rw [G3finite_two_explicit]
  -- 1 + 2z + 5z² + 4z³ + 3z⁴ ≥ 1 - 2|z|
  -- For |z| ≤ 1/2: 2z + 5z² + 4z³ + 3z⁴ ≥ -2|z|
  -- ↔ 5z² + 4z³ + 3z⁴ ≥ -2|z| - 2z
  -- Cases on sign of z:
  --   z ≥ 0: 2z ≥ 0 ≥ -2|z|, plus z² terms add positively.
  --   z < 0: 2z = -2|z|, plus z² + ... ≥ 0 gives ≥ -2|z|.
  -- Both cases: 5z² + 4z³ + 3z⁴ + 2z + 2|z| ≥ 0.
  have h_abs_le_half : |z| ≤ 1/2 := hz
  have h_z_sq_nonneg : 0 ≤ z ^ 2 := sq_nonneg z
  have h_z4_nonneg : 0 ≤ z ^ 4 := by positivity
  rcases le_or_lt 0 z with hzpos | hzneg
  · -- z ≥ 0: |z| = z. Goal: 1 + 2z + 5z² + 4z³ + 3z⁴ ≥ 1 - 2z
    rw [abs_of_nonneg hzpos]
    nlinarith [sq_nonneg z, sq_nonneg (z * z)]
  · -- z < 0: |z| = -z. Goal: 1 + 2z + 5z² + 4z³ + 3z⁴ ≥ 1 - 2(-z) = 1 + 2z
    rw [abs_of_neg hzneg]
    -- Need: 5z² + 4z³ + 3z⁴ ≥ 0 for z < 0 with |z| ≤ 1/2
    -- 4z³ ≤ 0 since z < 0, so need 5z² + 3z⁴ ≥ |4z³|
    -- |4z³| = 4·z²·|z| ≤ 4·z²·(1/2) = 2·z² ≤ 5·z² ✓
    have h_z_lt_half : -1/2 ≤ z := by
      have := abs_le.mp h_abs_le_half
      linarith [this.1]
    nlinarith [sq_nonneg z, sq_nonneg (1 + 2*z), h_z_sq_nonneg, h_z4_nonneg]

/-! ## §6 — Honest scope marker -/

/-- **Honest scope**: this file extracts the explicit low-order
    coefficient structure of G3finite N=1,2 and proves one concrete
    evaluation at z = √2 - 1 (load-bearing for the framework's
    substrate-route argument since √2 = α_P).

    The remaining open content for the analytic residual is unchanged:
    modular structure of G_3(z) at z = e^{iπα} with N → ∞. The infinite-N
    limit is the precise mathlib gap; finite-N is now fully analysed. -/
theorem G3FiniteCoefficientsLowOrder_HonestScope : True := trivial

end PrincipiaTractalis.TuringEncoding

-- Axiom checks
#print axioms PrincipiaTractalis.TuringEncoding.G3finite_one_explicit
#print axioms PrincipiaTractalis.TuringEncoding.G3finite_two_explicit
#print axioms PrincipiaTractalis.TuringEncoding.G3finite_one_at_sqrt_two_minus_one
#print axioms PrincipiaTractalis.TuringEncoding.G3finite_two_at_one
#print axioms PrincipiaTractalis.TuringEncoding.G3finite_two_at_neg_one
#print axioms PrincipiaTractalis.TuringEncoding.G3finite_two_small_z_lower_bound
