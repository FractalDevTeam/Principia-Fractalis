/-
# `z_book ≠ 1` via Irrationality of √2

Proves the non-trivial structural lemma `z_book ≠ 1` (where
`z_book := exp(I · π · √2)`), via:

* `Nat.Prime.irrational_sqrt` for `Irrational (Real.sqrt 2)`,
* `Complex.exp_eq_one_iff` for the criterion `exp z = 1 ↔ ∃ n : ℤ, z = n · 2πi`,
* Algebraic reduction `I · π · √2 = n · 2πi ⟹ √2 = 2n`,
* `Irrational.ne_int` for the irrationality contradiction.

Corollary: `Complex.log z_book ≠ 0`, which discharges the hypothesis
needed for `continuousAt_polyLogMonodromyShift_book` in
`BookEvaluationContinuity.lean`.

Stage L4 — `z_book ≠ 1` via irrationality.
-/

import PF.Analytic.BookEvaluationContinuity
import Mathlib.Data.Real.Irrational

namespace PrincipiaTractalis.Analytic

open Complex

/-! ## Irrationality of √2 -/

/-- **Irrationality of √2**: standard mathlib fact via
    `Nat.Prime.irrational_sqrt`. -/
theorem sqrt_two_irrational : Irrational (Real.sqrt 2) :=
  Nat.Prime.irrational_sqrt Nat.prime_two

/-! ## `z_book ≠ 1` -/

/-- **`z_book ≠ 1`**: would force `√2 = 2n` for some integer `n`,
    contradicting irrationality of `√2`. -/
theorem z_book_ne_one : z_book ≠ 1 := by
  unfold z_book
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  -- hn : I * π * √2 = n * (2 * π * I)
  -- Take imaginary parts: Im(I·π·√2) = π·√2; Im(n·2π·I) = 2π·n
  have h_im_eq : Real.pi * Real.sqrt 2 = 2 * Real.pi * (n : ℝ) := by
    have h_eq := congrArg Complex.im hn
    simp [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im,
          Complex.intCast_re, Complex.intCast_im] at h_eq
    linarith
  -- Cancel π (nonzero): √2 = 2 · n
  have h_pi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
  have h_div : Real.sqrt 2 = 2 * (n : ℝ) := by
    have h_factored : Real.pi * Real.sqrt 2 = Real.pi * (2 * (n : ℝ)) := by
      linarith
    exact mul_left_cancel₀ h_pi_ne h_factored
  -- √2 = ((2 * n : ℤ) : ℝ) contradicts irrationality
  have h_eq_int : Real.sqrt 2 = ((2 * n : ℤ) : ℝ) := by
    rw [h_div]; push_cast; ring
  exact sqrt_two_irrational.ne_int (2 * n) h_eq_int

/-! ## Corollary: `log z_book ≠ 0` -/

/-- **`Complex.log z_book ≠ 0`**: if `log z_book = 0`, then by
    `Complex.exp_log z_book ≠ 0` we'd get `z_book = exp(0) = 1`,
    contradicting `z_book ≠ 1`. -/
theorem log_z_book_ne_zero : Complex.log z_book ≠ 0 := by
  intro h
  have h_z_ne := z_book_ne_zero
  have h_eq : Complex.exp (Complex.log z_book) = z_book := Complex.exp_log h_z_ne
  rw [h, Complex.exp_zero] at h_eq
  exact z_book_ne_one h_eq.symm

/-! ## Unconditional monodromy-shift continuity -/

/-- **Unconditional monodromy-shift continuity** at any `s` with
    `Re s > 0`. Discharges the `log z_book ≠ 0` hypothesis from
    `continuousAt_polyLogMonodromyShift_book` using
    `log_z_book_ne_zero`. -/
theorem continuousAt_polyLogMonodromyShift_book_unconditional
    {s : ℂ} (hs : 0 < s.re) :
    ContinuousAt (fun s : ℂ => polyLogMonodromyShift (-1) s z_book) s :=
  continuousAt_polyLogMonodromyShift_book log_z_book_ne_zero hs

/-- **Unconditional bookEvaluation continuity** (modulo polylog
    continuity): given continuity of `s ↦ polyLog s z_book` at
    `(s_re : ℂ)`, `bookEvaluation` is continuous at `s_re`. -/
theorem continuousAt_bookEvaluation_unconditional
    {s_re : ℝ} (hs : 0 < s_re)
    (h_polyLog_cont : ContinuousAt (fun s : ℂ => polyLog s z_book) (s_re : ℂ)) :
    ContinuousAt bookEvaluation s_re :=
  continuousAt_bookEvaluation log_z_book_ne_zero hs h_polyLog_cont

end PrincipiaTractalis.Analytic
