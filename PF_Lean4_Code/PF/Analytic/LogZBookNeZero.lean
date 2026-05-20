/-
# Discharge of `h_log_ne` (Input #1 of axiom_content_END_TO_END)

The `axiom_content_END_TO_END` wrapper takes `Complex.log z_book ≠ 0`
as Input #1. This file PROVES that hypothesis unconditionally,
reducing the wrapper's open inputs from 6 to 5.

**Proof strategy** (clean):

  z_book = exp(I · π · √2)
  Suppose log z_book = 0.
  Then z_book = exp(log z_book) = exp 0 = 1.
  So exp(I · π · √2) = 1.
  By Complex.exp_eq_one_iff, ∃ n : ℤ such that I · π · √2 = n · (2π · I).
  Equating: π · √2 = 2π · n, hence √2 = 2n with n : ℤ.
  This contradicts irrationality of √2 (mathlib's `irrational_sqrt_two`).

Stage L4 — Trivial input discharge.
-/

import PF.Analytic.EigenvalueIdentity
import Mathlib.Data.Real.Irrational

namespace PrincipiaTractalis.Analytic

open Complex

/-- **z_book ≠ 1**: from irrationality of √2.

    `z_book = exp(I π √2) = 1` would force `π √2 = 2π n` for some integer `n`,
    hence `√2 = 2n`, contradicting `irrational_sqrt_two`. -/
theorem z_book_ne_one : z_book ≠ 1 := by
  unfold z_book
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  -- hn : I * (π : ℂ) * (√2 : ℂ) = ↑n * (2 * π * I)
  -- Derive √2 = 2n as a complex equation, then extract real part.
  have h_pi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h_I_ne : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have h_I_pi_ne : I * (Real.pi : ℂ) ≠ 0 := mul_ne_zero h_I_ne h_pi_ne
  -- Rearrange both sides into (I·π) · K form
  have h_lhs : I * (Real.pi : ℂ) * (Real.sqrt 2 : ℂ) =
               (I * (Real.pi : ℂ)) * (Real.sqrt 2 : ℂ) := by ring
  have h_rhs : (n : ℂ) * (2 * (Real.pi : ℂ) * I) =
               (I * (Real.pi : ℂ)) * (2 * (n : ℂ)) := by ring
  rw [h_lhs, h_rhs] at hn
  -- Cancel I*π on both sides
  have h_sqrt2_eq : (Real.sqrt 2 : ℂ) = 2 * (n : ℂ) :=
    mul_left_cancel₀ h_I_pi_ne hn
  -- Extract real parts: √2 = 2n
  have h_re : Real.sqrt 2 = 2 * (n : ℝ) := by
    have := congr_arg Complex.re h_sqrt2_eq
    simp at this
    push_cast at this
    exact this
  -- Contradiction with irrationality of √2
  have h_irr : Irrational (Real.sqrt 2) := irrational_sqrt_two
  -- Show √2 ∈ Set.range ((↑·) : ℚ → ℝ) via 2n : ℚ
  apply h_irr
  refine ⟨(2 * n : ℤ), ?_⟩
  push_cast
  linarith

/-- **h_log_ne discharged**: `Complex.log z_book ≠ 0`.

    Direct: if `log z_book = 0`, then `z_book = exp(log z_book) = exp 0 = 1`,
    contradicting `z_book_ne_one`. -/
theorem log_z_book_ne_zero : Complex.log z_book ≠ 0 := by
  intro h
  apply z_book_ne_one
  -- z_book = exp(log z_book) since z_book ≠ 0
  have h_exp : Complex.exp (Complex.log z_book) = z_book :=
    Complex.exp_log z_book_ne_zero
  rw [h, Complex.exp_zero] at h_exp
  exact h_exp.symm

end PrincipiaTractalis.Analytic
