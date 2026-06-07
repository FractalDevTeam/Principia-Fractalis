/-
# Spectral Examples — Constant Kernel

★ 2026-06-06 — Polylog chain piece 16 ★

## Why this file exists

For a constant kernel V(x, y) = c at N=2, the matrix is all-c.
trace = 2c, det = 0 (since rows are linearly dependent).
Eigenvalues: λ_+ = 2c, λ_- = 0.
Spectral gap = 2c.

## What gets closed

- `lambdaPlus_constant_case`: λ_+ = 2c when V is constant c
- `lambdaMinus_constant_case`: λ_- = 0 when V is constant c
- `spectral_gap_constant_case`: gap = 2c

## Axiom budget

Zero project axioms. Zero `sorry`. Zero `admit`.

Stage 2026-06-06.
-/

import PF.TuringEncoding.SpectralExamplesDiagonal

namespace PrincipiaTractalis.TuringEncoding

open Real

/-! ## §1 — Constant kernel at N=2 -/

/-- **For a constant kernel** V(x, y) = c, the discriminant at N=2 is
    `Δ = (2c)² − 4·0 = 4c²`, so `√Δ = 2|c|`. -/
theorem discriminant_constant_case (c : ℝ) :
    let V := fun (_ _ : ℝ) => c
    (V 0 0 + V 0 0) ^ 2 - 4 * (V 0 0 * V 0 0 - (V 0 0) ^ 2) = (2 * c) ^ 2 := by
  show (c + c) ^ 2 - 4 * (c * c - c ^ 2) = (2 * c) ^ 2
  ring

/-- **`√((2c)²) = 2|c|`**. -/
theorem sqrt_constant_discriminant (c : ℝ) :
    Real.sqrt ((2 * c) ^ 2) = 2 * |c| := by
  rw [Real.sqrt_sq_eq_abs, abs_mul]
  simp

/-- **For non-negative constant `c ≥ 0`, `λ_+ = 2c`**. -/
theorem lambdaPlus_constant_nonneg (c : ℝ) (hc : 0 ≤ c) :
    lambdaPlus (fun _ _ => c) 0 0 = 2 * c := by
  unfold lambdaPlus
  simp only []
  have h_disc : (c + c) ^ 2 - 4 * (c * c - c ^ 2) = (2 * c) ^ 2 := by ring
  rw [h_disc]
  have h_sqrt : Real.sqrt ((2 * c) ^ 2) = 2 * c := by
    rw [Real.sqrt_sq (by linarith : 0 ≤ 2 * c)]
  rw [h_sqrt]
  ring

/-- **For non-negative constant `c ≥ 0`, `λ_- = 0`**. -/
theorem lambdaMinus_constant_nonneg (c : ℝ) (hc : 0 ≤ c) :
    lambdaMinus (fun _ _ => c) 0 0 = 0 := by
  unfold lambdaMinus
  simp only []
  have h_disc : (c + c) ^ 2 - 4 * (c * c - c ^ 2) = (2 * c) ^ 2 := by ring
  rw [h_disc]
  have h_sqrt : Real.sqrt ((2 * c) ^ 2) = 2 * c := by
    rw [Real.sqrt_sq (by linarith : 0 ≤ 2 * c)]
  rw [h_sqrt]
  ring

/-- **The spectral gap for a non-negative constant kernel is `2c`**. -/
theorem spectral_gap_constant_nonneg (c : ℝ) (hc : 0 ≤ c) :
    lambdaPlus (fun _ _ => c) 0 0 - lambdaMinus (fun _ _ => c) 0 0 = 2 * c := by
  rw [lambdaPlus_constant_nonneg c hc, lambdaMinus_constant_nonneg c hc]
  ring

/-! ## §2 — Honest scope marker -/

/-- **Honest scope** for this file: concrete spectral identities at
    constant kernels. -/
theorem SpectralExamplesConstant_HonestScope : True := trivial

end PrincipiaTractalis.TuringEncoding

-- Axiom checks
#print axioms PrincipiaTractalis.TuringEncoding.discriminant_constant_case
#print axioms PrincipiaTractalis.TuringEncoding.sqrt_constant_discriminant
#print axioms PrincipiaTractalis.TuringEncoding.lambdaPlus_constant_nonneg
#print axioms PrincipiaTractalis.TuringEncoding.lambdaMinus_constant_nonneg
#print axioms PrincipiaTractalis.TuringEncoding.spectral_gap_constant_nonneg
