/-
# Finite-Dim Spectral Determinant — Trace + Det Determine N=2 Spectrum

★ 2026-06-06 — Polylog chain piece 6 ★

## Why this file exists

Per `FiniteDimSpectralFrameworkOperator.lean` and `FiniteDimSpectralRealSpectrum.lean`,
the framework's V_P kernel matrix is symmetric (`IsSymm`) and self-adjoint as
a convolution operator. At N=2, the matrix is `2×2 symmetric over ℝ`, so its
spectrum is fully determined by trace + determinant.

This file proves the EXPLICIT 2×2 determinant formula axiom-free.

## What gets closed

- `kernelMatrix_two_det`: for the framework's V_P kernel at N=2,
  det(M) = V(x_0,x_0) · V(x_1,x_1) − V(x_0,x_1)².

- `kernelMatrix_two_characteristic_poly_form`: characteristic polynomial
  λ² − tr(M)·λ + det(M).

- `kernelMatrix_two_spectrum_real_via_discriminant`: the discriminant
  tr(M)² − 4·det(M) is non-negative (for symmetric kernels), confirming
  the spectrum is real (Ch 21 §5 claim 1 at N=2 EXPLICITLY).

## Axiom budget

Zero project axioms. Zero `sorry`. Zero `admit`.
Kernel-only `[propext, Classical.choice, Quot.sound]`.

Stage 2026-06-06.
-/

import PF.TuringEncoding.FiniteDimSpectralRealSpectrum
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace PrincipiaTractalis.TuringEncoding

open Matrix

/-! ## §1 — Explicit determinant at N = 2 -/

/-- **Determinant of the 2×2 kernel matrix** for the framework's V_P:
    `det(M) = V(x_0, x_0) · V(x_1, x_1) − V(x_0, x_1) · V(x_1, x_0)`. -/
theorem kernelMatrix_two_det (V : ℝ → ℝ → ℝ) (x_0 x_1 : ℝ) :
    Matrix.det (kernelMatrix V (fun i : Fin 2 => if i = 0 then x_0 else x_1)) =
    V x_0 x_0 * V x_1 x_1 - V x_0 x_1 * V x_1 x_0 := by
  rw [kernelMatrix_two_explicit]
  simp [Matrix.det_fin_two]

/-- **Determinant simplification for symmetric V**:
    `det(M) = V(x_0,x_0) · V(x_1,x_1) − V(x_0,x_1)²`. -/
theorem kernelMatrix_two_det_symmetric (V : ℝ → ℝ → ℝ)
    (hV : ∀ x y, V x y = V y x) (x_0 x_1 : ℝ) :
    Matrix.det (kernelMatrix V (fun i : Fin 2 => if i = 0 then x_0 else x_1)) =
    V x_0 x_0 * V x_1 x_1 - (V x_0 x_1) ^ 2 := by
  rw [kernelMatrix_two_det]
  congr 1
  rw [hV x_1 x_0]
  ring

/-! ## §2 — Characteristic polynomial form at N = 2 -/

/-- **The characteristic polynomial structure at N = 2**: for any 2×2 matrix
    `M = !![a, b; c, d]`, `det(λI - M) = λ² − tr(M)·λ + det(M)`.

    For the framework's V_P kernel matrix, this gives an explicit
    quadratic in λ whose roots are the eigenvalues. -/
theorem kernelMatrix_two_char_poly (V : ℝ → ℝ → ℝ) (x_0 x_1 : ℝ) (lam : ℝ) :
    let M := kernelMatrix V (fun i : Fin 2 => if i = 0 then x_0 else x_1)
    Matrix.det (lam • (1 : Matrix (Fin 2) (Fin 2) ℝ) - M) =
    lam ^ 2 - Matrix.trace M * lam + Matrix.det M := by
  rw [kernelMatrix_two_explicit]
  simp only [Matrix.det_fin_two, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
             Matrix.trace, Fin.sum_univ_two, smul_eq_mul, Matrix.cons_val',
             Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.head_fin_const, Matrix.cons_val_fin_one]
  -- Det of (λI - M) = (λ - V(x_0,x_0))·(λ - V(x_1,x_1)) - (-V(x_0,x_1))·(-V(x_1,x_0))
  -- = λ² - (V(x_0,x_0) + V(x_1,x_1))·λ + V(x_0,x_0)·V(x_1,x_1) - V(x_0,x_1)·V(x_1,x_0)
  -- = λ² - tr(M)·λ + det(M)
  show ((lam * 1 - V x_0 x_0) * (lam * 1 - V x_1 x_1) -
        (lam * 0 - V x_0 x_1) * (lam * 0 - V x_1 x_0)) =
       lam ^ 2 - (V x_0 x_0 + V x_1 x_1) * lam +
       (V x_0 x_0 * V x_1 x_1 - V x_0 x_1 * V x_1 x_0)
  ring

/-! ## §3 — Discriminant non-negativity for symmetric kernels -/

/-- **The discriminant of the characteristic polynomial** at N = 2:
    `Δ = tr(M)² − 4·det(M)`. For SYMMETRIC kernels, this equals
    `(V(x_0,x_0) − V(x_1,x_1))² + 4·V(x_0,x_1)²`, which is non-negative.

    This proves CONSTRUCTIVELY that the spectrum is real at N = 2:
    the characteristic polynomial has discriminant ≥ 0, so its roots
    (the eigenvalues) are real. -/
theorem kernelMatrix_two_discriminant_nonneg (V : ℝ → ℝ → ℝ)
    (hV : ∀ x y, V x y = V y x) (x_0 x_1 : ℝ) :
    0 ≤ (Matrix.trace (kernelMatrix V (fun i : Fin 2 => if i = 0 then x_0 else x_1))) ^ 2 -
        4 * Matrix.det (kernelMatrix V (fun i : Fin 2 => if i = 0 then x_0 else x_1)) := by
  rw [kernelMatrix_two_trace, kernelMatrix_two_det_symmetric V hV]
  nlinarith [sq_nonneg (V x_0 x_0 - V x_1 x_1), sq_nonneg (V x_0 x_1)]

/-! ## §4 — Honest scope marker -/

/-- **Honest scope** for this file:

    1. CLOSED axiom-free:
       - `kernelMatrix_two_det`: explicit 2×2 determinant
       - `kernelMatrix_two_det_symmetric`: symmetric simplification
       - `kernelMatrix_two_char_poly`: characteristic polynomial form
         `λ² − tr·λ + det` for any 2×2 matrix
       - `kernelMatrix_two_discriminant_nonneg`: discriminant ≥ 0 for
         SYMMETRIC kernels — CONSTRUCTIVE PROOF of real spectrum at N=2

    2. WHAT THIS UNLOCKS: at N=2, the framework's V_P spectrum is fully
       determined by trace + det, and the discriminant non-negativity
       gives an EXPLICIT CONSTRUCTIVE proof of real spectrum (not just
       via mathlib's spectral theorem black box). Eigenvalues are:
         λ_± = (tr(M) ± √Δ) / 2
       with Δ = (V(x_0,x_0) − V(x_1,x_1))² + 4·V(x_0,x_1)² ≥ 0.

    3. EXTENSION TO N > 2: standard linear algebra on real symmetric
       matrices gives real spectrum and complete eigenbasis at any
       finite N. The mathlib infrastructure (`Matrix.IsSymm` +
       spectral theorem) handles this; the explicit closed-form
       eigenvalue formulas exist for N ≤ 4 (Cardano + Ferrari) but
       are not needed for the framework's structural claims.

    4. CONTINUUM-LIMIT M3 RESIDUAL: the N → ∞ limit to L²(K_P, μ)
       and the convergence of finite-dim spectra to continuum
       spectra. Specific mathlib targets; not abstract open math. -/
theorem FiniteDimSpectralDeterminant_HonestScope : True := trivial

end PrincipiaTractalis.TuringEncoding

-- Axiom checks
#print axioms PrincipiaTractalis.TuringEncoding.kernelMatrix_two_det
#print axioms PrincipiaTractalis.TuringEncoding.kernelMatrix_two_det_symmetric
#print axioms PrincipiaTractalis.TuringEncoding.kernelMatrix_two_char_poly
#print axioms PrincipiaTractalis.TuringEncoding.kernelMatrix_two_discriminant_nonneg
