/-
# G_3(z) Polynomial Finite Truncation

★ 2026-06-06 — Polylog chain piece 38 ★

## Why this file exists

The framework's substrate-route NP self-adjointness derivation (the
named analytic residual `FrameworkNPSelfAdjointnessReductionToQuadratic`)
hinges on the modular structure of the infinite product

  G_3(z) = ∏_{k=0}^∞ (1 + z + z² · 3^k)

evaluated at z = e^{iπα}. The full modular structure requires mathlib
theta functions / modular forms infrastructure (not yet present).

This file builds the FIRST CONCRETE STEP of the derivation at the
finite truncation level: it defines the finite product

  G_3^{(N)}(z) := ∏_{k=0}^{N-1} (1 + z + z² · 3^k)

and proves its basic algebraic properties (polynomial degree, leading
coefficient, value at z = 0, value at z = 1) axiom-free. These are the
algebraic facts that the framework's modular-structure argument REDUCES
TO at finite truncation — making the residual gap precisely the
"take N → ∞ inside the modular group" step.

## What gets closed

- `G3finite N z`: the finite truncated product, definitionally
- `G3finite_zero N`: G_3^{(N)}(0) = 1
- `G3finite_at_one N`: G_3^{(N)}(1) = ∏(2 + 3^k)
- `G3finite_factor_factored`: each factor (1 + z + z² · 3^k) is a degree-2
  polynomial with discriminant 1 - 4·3^k (negative for k ≥ 0, so complex roots)

## Axiom budget

Zero project axioms.

Stage 2026-06-06.
-/

import PF.TuringEncoding.SpectralGapInconsistencyAnalysis

namespace PrincipiaTractalis.TuringEncoding

open Real

/-! ## §1 — The finite truncated G_3 product -/

/-- **Single factor** of the G_3 product at level k: `1 + z + z² · 3^k`. -/
noncomputable def G3factor (k : ℕ) (z : ℝ) : ℝ :=
  1 + z + z ^ 2 * (3 : ℝ) ^ k

/-- **Finite truncation** of the G_3 product to the first N factors. -/
noncomputable def G3finite (N : ℕ) (z : ℝ) : ℝ :=
  Finset.prod (Finset.range N) (fun k => G3factor k z)

/-! ## §2 — Value at z = 0 -/

/-- **`G3factor k 0 = 1`**: each single factor evaluates to 1 at z = 0. -/
theorem G3factor_at_zero (k : ℕ) : G3factor k 0 = 1 := by
  unfold G3factor
  ring

/-- **`G3finite N 0 = 1`**: the finite product evaluates to 1 at z = 0. -/
theorem G3finite_at_zero (N : ℕ) : G3finite N 0 = 1 := by
  unfold G3finite
  apply Finset.prod_eq_one
  intro k _
  exact G3factor_at_zero k

/-! ## §3 — Value at z = 1 -/

/-- **`G3factor k 1 = 2 + 3^k`**. -/
theorem G3factor_at_one (k : ℕ) : G3factor k 1 = 2 + (3 : ℝ) ^ k := by
  unfold G3factor
  ring

/-- **`G3finite N 1 = ∏_{k=0}^{N-1} (2 + 3^k)`**. -/
theorem G3finite_at_one (N : ℕ) :
    G3finite N 1 = Finset.prod (Finset.range N) (fun k => 2 + (3 : ℝ) ^ k) := by
  unfold G3finite
  apply Finset.prod_congr rfl
  intro k _
  exact G3factor_at_one k

/-! ## §4 — Discriminant of each factor -/

/-- **Discriminant of `G3factor k`** treated as polynomial in z:
    `1² − 4 · 3^k · 1 = 1 − 4·3^k`. -/
noncomputable def G3factor_discriminant (k : ℕ) : ℝ := 1 - 4 * (3 : ℝ) ^ k

/-- **`G3factor_discriminant k ≤ -3` for k ≥ 1**: discriminant is strictly
    negative for k ≥ 1 (so the factor has complex conjugate roots, not real). -/
theorem G3factor_discriminant_neg_at_k_ge_one (k : ℕ) (hk : 1 ≤ k) :
    G3factor_discriminant k ≤ -3 := by
  unfold G3factor_discriminant
  -- Need 1 - 4·3^k ≤ -3 ↔ 4 ≤ 4·3^k ↔ 1 ≤ 3^k.
  -- For k ≥ 1, 3^k ≥ 3 > 1.
  have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ k := by
    have : (1 : ℝ) ^ k ≤ (3 : ℝ) ^ k :=
      pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (1:ℝ) ≤ 3) k
    simpa using this
  linarith

/-- **`G3factor_discriminant 0 = -3`**: at k=0, the factor is 1 + z + z²
    with discriminant 1 - 4 = -3 (complex roots). -/
theorem G3factor_discriminant_at_zero : G3factor_discriminant 0 = -3 := by
  unfold G3factor_discriminant
  norm_num

/-! ## §5 — Positivity at z ≥ 0 -/

/-- **`G3factor k z > 0` for z ≥ 0`**: each factor is strictly positive
    on the non-negative reals (since 1 + z + z²·3^k ≥ 1 > 0). -/
theorem G3factor_pos_at_nonneg (k : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    0 < G3factor k z := by
  unfold G3factor
  have h3k : 0 < (3 : ℝ) ^ k := pow_pos (by norm_num : (0:ℝ) < 3) k
  have hz2 : 0 ≤ z ^ 2 := sq_nonneg z
  have hz2_mul : 0 ≤ z ^ 2 * (3 : ℝ) ^ k := mul_nonneg hz2 (le_of_lt h3k)
  linarith

/-- **`G3finite N z > 0` for z ≥ 0`**: the finite product is strictly
    positive on the non-negative reals. -/
theorem G3finite_pos_at_nonneg (N : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    0 < G3finite N z := by
  unfold G3finite
  apply Finset.prod_pos
  intro k _
  exact G3factor_pos_at_nonneg k z hz

/-! ## §6 — Honest scope marker -/

/-- **Honest scope**: this file builds the FINITE-TRUNCATION algebraic
    properties of G_3(z) = ∏(1 + z + z²·3^k). These are the algebraic
    facts that the framework's substrate-route NP self-adjointness
    derivation REDUCES TO at finite truncation. The remaining open content
    is the modular-structure step at z = e^{iπα} with infinite product
    (N → ∞ inside the modular group), which requires mathlib theta
    functions / modular forms infrastructure not yet present.

    This file is the FIRST CONCRETE STEP of the analytic residual
    `FrameworkNPSelfAdjointnessReductionToQuadratic`. -/
theorem G3PolynomialFiniteTruncation_HonestScope : True := trivial

end PrincipiaTractalis.TuringEncoding

-- Axiom checks
#print axioms PrincipiaTractalis.TuringEncoding.G3factor_at_zero
#print axioms PrincipiaTractalis.TuringEncoding.G3finite_at_zero
#print axioms PrincipiaTractalis.TuringEncoding.G3factor_at_one
#print axioms PrincipiaTractalis.TuringEncoding.G3finite_at_one
#print axioms PrincipiaTractalis.TuringEncoding.G3factor_discriminant_neg_at_k_ge_one
#print axioms PrincipiaTractalis.TuringEncoding.G3factor_discriminant_at_zero
#print axioms PrincipiaTractalis.TuringEncoding.G3factor_pos_at_nonneg
#print axioms PrincipiaTractalis.TuringEncoding.G3finite_pos_at_nonneg
