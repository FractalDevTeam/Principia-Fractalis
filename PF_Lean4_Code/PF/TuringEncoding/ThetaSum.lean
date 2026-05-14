/-
# Truncated Theta-Sum and Reality Analysis

The book's Ch 21 Theorem 4.3 (Self-Adjointness Criterion) and Theorem 4.4
(Critical Parameter Values) express the self-adjointness of the discrete
H_P operator in terms of reality of a theta-sum:

  `Σ_m e^{iπα·m} N_m^(3) ∈ ℝ`

where `N_m^(3) = |{n ∈ ℕ : digitalSum3 n = m}|`. The book's claim is that
this is real precisely at `α = √2` (P-class) and `α = φ + 1/4` (NP-class).
However, `N_m^(3)` is generally infinite, so the literal infinite sum
doesn't converge — the book's identity must be a notational shorthand for
a specific limit or regularized sum.

The **finite, well-defined form** of the theta-sum is

  `Θ_N(α) = Σ_{n < 3^N} e^{iπα·digitalSum3 n}`

and this file establishes its key factorization (from `digitalSum3_generating_truncated`):

  `Θ_N(α) = (1 + e^{iπα} + e^{2iπα})^N`.

This is the foundational identity for the SA reality analysis. The full
derivation of `α = √2` and `α = φ + 1/4` (giving the algebraic equations
`α² = 2` and `16α² − 24α − 11 = 0`) requires Dirichlet L-function /
Dedekind eta machinery beyond the truncated GF alone — that is L4-proper
analytic-number-theory work.

Stage L4 — complex-valued truncated theta-sum + factorization framework.
-/

import PF.TuringEncoding.DigitalSum
import Mathlib.Analysis.Complex.Exponential

namespace PrincipiaTractalis.TuringEncoding

open Complex

/-! ## The truncated theta-sum -/

/-- **The truncated theta-sum** `Θ_N(α)` of Ch 21 Theorem 4.3:
    `Θ_N(α) = Σ_{n < 3^N} e^{iπα·digitalSum3 n}`. -/
noncomputable def truncatedThetaSum (α : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (3 ^ N),
    Complex.exp (Complex.I * Real.pi * α * (digitalSum3 n : ℂ))

/-- **Factorization of the truncated theta-sum**:
    `Θ_N(α) = (1 + e^{iπα} + e^{2iπα})^N`.

    Proof: substitute `z = e^{iπα}` into `digitalSum3_generating_truncated`;
    `e^{iπα·D(n)} = (e^{iπα})^(D(n))` via `Complex.exp_nat_mul`. -/
theorem truncatedThetaSum_factorization (α : ℝ) (N : ℕ) :
    truncatedThetaSum α N =
      (1 + Complex.exp (Complex.I * Real.pi * α) +
       Complex.exp (Complex.I * Real.pi * α) ^ 2) ^ N := by
  unfold truncatedThetaSum
  -- Convert each summand to (e^{iπα})^(D(n))
  have h_term : ∀ n : ℕ,
      Complex.exp (Complex.I * Real.pi * α * (digitalSum3 n : ℂ)) =
      Complex.exp (Complex.I * Real.pi * α) ^ (digitalSum3 n) := by
    intro n
    rw [show Complex.I * Real.pi * α * (digitalSum3 n : ℂ) =
        (digitalSum3 n : ℂ) * (Complex.I * Real.pi * α) from by ring]
    exact Complex.exp_nat_mul _ _
  simp_rw [h_term]
  -- Apply the truncated generating function with z = e^{iπα}
  exact digitalSum3_generating_truncated
    (Complex.exp (Complex.I * Real.pi * α)) N

/-! ## Base case and pointwise rephrasings -/

/-- `Θ_0(α) = 1` for every `α`. -/
theorem truncatedThetaSum_zero (α : ℝ) : truncatedThetaSum α 0 = 1 := by
  rw [truncatedThetaSum_factorization]
  simp

/-- The "factor" of the truncated theta-sum: the inner quantity
    `1 + e^{iπα} + e^{2iπα}` whose power gives `Θ_N(α)`. -/
noncomputable def thetaFactor (α : ℝ) : ℂ :=
  1 + Complex.exp (Complex.I * Real.pi * α) +
  Complex.exp (Complex.I * Real.pi * α) ^ 2

/-- Repackaging: `Θ_N(α) = thetaFactor(α)^N`. -/
theorem truncatedThetaSum_eq_factor_pow (α : ℝ) (N : ℕ) :
    truncatedThetaSum α N = (thetaFactor α) ^ N :=
  truncatedThetaSum_factorization α N

/-- If `thetaFactor α = 0`, then `Θ_N(α) = 0` for every `N ≥ 1`.
    (At `α = 2/3 + 2k` or `α = 4/3 + 2k`, `thetaFactor α = 0` since
    `e^{iπα}` is a primitive cube root of unity — this corresponds to the
    "trivial" SA values, distinct from the book's α = √2 / φ + 1/4.) -/
theorem truncatedThetaSum_succ_of_factor_zero {α : ℝ} (hα : thetaFactor α = 0)
    (N : ℕ) :
    truncatedThetaSum α (N + 1) = 0 := by
  rw [truncatedThetaSum_eq_factor_pow, hα, zero_pow (Nat.succ_ne_zero N)]

/-- If `thetaFactor α` is real, then `Θ_N(α)` is real for every `N`. -/
theorem truncatedThetaSum_re_of_factor_re {α : ℝ}
    (hα : (thetaFactor α).im = 0) (N : ℕ) :
    (truncatedThetaSum α N).im = 0 := by
  rw [truncatedThetaSum_eq_factor_pow]
  -- (x : ℂ) with x.im = 0 ⟹ x^N has im = 0
  have hα_re : thetaFactor α = ((thetaFactor α).re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [hα]
  rw [hα_re, ← Complex.ofReal_pow]
  exact Complex.ofReal_im _

end PrincipiaTractalis.TuringEncoding
