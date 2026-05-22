/-
# Digital-Sum Generating Function on the Unit Circle

This file evaluates the Ch 21 generating function

    G_N(z) = Σ_{n ∈ range (3^N)} z^(digitalSum3 n) = (1 + z + z²)^N

at points on the unit circle `z = exp(I·θ)`, deriving the closed factorization

    G_N(exp(I·θ)) = exp(I·N·θ) · (1 + 2·cos θ)^N.

This exposes the structural shape of the manuscript's "reality condition"
(Ch 21 Thm. `thm:critical-values`, lines 281-306): for the unweighted finite
generating function to be real, EITHER `1 + 2·cos θ = 0` (which has explicit
solutions in θ) OR `exp(I·N·θ)` is real (which requires `N·θ ∈ π·ℤ`).

For `θ = π·α` with `α` irrational (such as the manuscript's `α_P = √2`), the
second route is impossible for every `N ≥ 1`. So the unweighted finite
generating function CANNOT be the locus of the reality condition that pins
down `α_P = √2`: the weighted limit `Σ a^{-n} G_n(...)` is essential.

This is structural mathematical content directly from the manuscript that
was previously not formalized. It does not discharge `PolylogEigenvalueConjecture`
(which encodes a different, much deeper, conjectural mechanism), but it
clarifies what the unweighted version cannot do — making explicit the
necessity of the weighted construction.

Status: axiom-free.
-/

import PF.TuringEncoding.DigitalSum
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace PrincipiaTractalis.TuringEncoding

open Complex Real

/-! ## Unit-circle factorization of `1 + z + z²` -/

/-- **Unit-circle factorization.** For any real `θ`,

      `1 + exp(I·θ) + exp(2·I·θ) = exp(I·θ) · (1 + 2·cos θ)`.

    Derivation:
      `exp(I·θ) · (1 + 2·cos θ)
         = exp(I·θ) + 2·exp(I·θ)·cos θ
         = exp(I·θ) + exp(I·θ)·(exp(I·θ) + exp(-I·θ))
         = exp(I·θ) + exp(2·I·θ) + 1.` -/
theorem one_add_exp_add_exp_two_factor (θ : ℝ) :
    (1 : ℂ) + Complex.exp (Complex.I * (θ : ℂ)) +
      Complex.exp (2 * Complex.I * (θ : ℂ)) =
    Complex.exp (Complex.I * (θ : ℂ)) * (1 + 2 * (Real.cos θ : ℂ)) := by
  -- Step 1: 2·cos θ = exp(I·θ) + exp(-I·θ) over ℂ (Euler form).
  have h_two_cos :
      (2 : ℂ) * (Real.cos θ : ℂ) =
        Complex.exp (Complex.I * (θ : ℂ)) +
          Complex.exp (-(Complex.I * (θ : ℂ))) := by
    have h_cos_re : ((Real.cos θ : ℝ) : ℂ) = Complex.cos (θ : ℂ) :=
      Complex.ofReal_cos θ
    rw [h_cos_re, Complex.cos]
    have h_comm : (θ : ℂ) * Complex.I = Complex.I * (θ : ℂ) := by ring
    have h_comm_neg : -(θ : ℂ) * Complex.I = -(Complex.I * (θ : ℂ)) := by ring
    rw [h_comm, h_comm_neg]
    field_simp
  -- Step 2: exp(I·θ) · exp(I·θ) = exp(2·I·θ).
  have h_exp_two : Complex.exp (Complex.I * (θ : ℂ)) *
      Complex.exp (Complex.I * (θ : ℂ)) =
      Complex.exp (2 * Complex.I * (θ : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; ring
  -- Step 3: exp(I·θ) · exp(-I·θ) = exp(0) = 1.
  have h_exp_zero : Complex.exp (Complex.I * (θ : ℂ)) *
      Complex.exp (-(Complex.I * (θ : ℂ))) = 1 := by
    rw [← Complex.exp_add]
    rw [show Complex.I * (θ : ℂ) + -(Complex.I * (θ : ℂ)) = 0 from by ring]
    exact Complex.exp_zero
  -- Step 4: Combine. Compute RHS = LHS, then take symm.
  symm
  calc Complex.exp (Complex.I * (θ : ℂ)) * (1 + 2 * (Real.cos θ : ℂ))
      = Complex.exp (Complex.I * (θ : ℂ)) +
          Complex.exp (Complex.I * (θ : ℂ)) * (2 * (Real.cos θ : ℂ)) := by ring
    _ = Complex.exp (Complex.I * (θ : ℂ)) +
          Complex.exp (Complex.I * (θ : ℂ)) *
            (Complex.exp (Complex.I * (θ : ℂ)) +
              Complex.exp (-(Complex.I * (θ : ℂ)))) := by rw [h_two_cos]
    _ = Complex.exp (Complex.I * (θ : ℂ)) +
          (Complex.exp (Complex.I * (θ : ℂ)) *
              Complex.exp (Complex.I * (θ : ℂ)) +
            Complex.exp (Complex.I * (θ : ℂ)) *
              Complex.exp (-(Complex.I * (θ : ℂ)))) := by ring
    _ = Complex.exp (Complex.I * (θ : ℂ)) +
          (Complex.exp (2 * Complex.I * (θ : ℂ)) + 1) := by
            rw [h_exp_two, h_exp_zero]
    _ = (1 : ℂ) + Complex.exp (Complex.I * (θ : ℂ)) +
          Complex.exp (2 * Complex.I * (θ : ℂ)) := by ring

/-! ## Power form: `(1 + z + z²)^N` at `z = exp(I·θ)` -/

/-- **Powered factorization on the unit circle.** For any real `θ` and `N : ℕ`,

      `(1 + exp(I·θ) + exp(2·I·θ))^N = exp(I·N·θ) · (1 + 2·cos θ)^N`.

    Here `exp(I·N·θ)` is written `exp(N · (I · θ))` for clean coercion. -/
theorem one_add_exp_add_exp_two_pow_factor (θ : ℝ) (N : ℕ) :
    ((1 : ℂ) + Complex.exp (Complex.I * (θ : ℂ)) +
      Complex.exp (2 * Complex.I * (θ : ℂ))) ^ N =
    Complex.exp ((N : ℂ) * (Complex.I * (θ : ℂ))) *
      ((1 + 2 * (Real.cos θ : ℂ)) ^ N) := by
  rw [one_add_exp_add_exp_two_factor θ, mul_pow]
  congr 1
  -- exp(I·θ)^N = exp(N · (I·θ))
  rw [← Complex.exp_nat_mul]

/-! ## Evaluation of the Ch 21 generating function on the unit circle -/

/-- **Ch 21 generating function on the unit circle.** Combines
    `digitalSum3_generating_truncated` with the unit-circle factorization:

      `Σ_{n ∈ range (3^N)} (exp(I·θ))^(digitalSum3 n)
       = exp(N · (I·θ)) · (1 + 2·cos θ)^N`.

    This is the structural form of `G_N(e^(iθ))` referenced in Ch 21
    Thm. `thm:critical-values` (lines 281-306). Specializing `θ = π·α`
    yields the form the manuscript's "reality condition" is imposed on. -/
theorem digitalSum3_generating_at_exp_I (θ : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range (3 ^ N),
        (Complex.exp (Complex.I * (θ : ℂ))) ^ (digitalSum3 n) =
      Complex.exp ((N : ℂ) * (Complex.I * (θ : ℂ))) *
        ((1 + 2 * (Real.cos θ : ℂ)) ^ N) := by
  rw [digitalSum3_generating_truncated (Complex.exp (Complex.I * (θ : ℂ))) N]
  -- (1 + z + z²)^N at z = exp(I·θ) factors as exp(N·I·θ)·(1+2cos θ)^N.
  have h_zsq :
      Complex.exp (Complex.I * (θ : ℂ)) ^ 2 =
        Complex.exp (2 * Complex.I * (θ : ℂ)) := by
    rw [show Complex.exp (Complex.I * (θ : ℂ)) ^ 2 =
        Complex.exp (Complex.I * (θ : ℂ)) *
          Complex.exp (Complex.I * (θ : ℂ)) from sq _]
    rw [← Complex.exp_add]; congr 1; ring
  rw [h_zsq]
  exact one_add_exp_add_exp_two_pow_factor θ N

/-- **Specialization to `θ = π·α`** — the manuscript's exact form. -/
theorem digitalSum3_generating_at_exp_I_pi_alpha (α : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range (3 ^ N),
        (Complex.exp (Complex.I * ((Real.pi * α : ℝ) : ℂ))) ^ (digitalSum3 n) =
      Complex.exp ((N : ℂ) * (Complex.I * ((Real.pi * α : ℝ) : ℂ))) *
        ((1 + 2 * (Real.cos (Real.pi * α) : ℂ)) ^ N) :=
  digitalSum3_generating_at_exp_I (Real.pi * α) N

/-! ## Reality criterion for the unit-circle generating function

The manuscript's Thm. `thm:critical-values` asserts that the limit

    `Σ_n a^(-n) G_n(e^(iπα))`

is real at exactly `α ∈ {√2, φ + 1/4}` in `(1, 2)`. The chapter does not
execute this computation — it gestures at modular forms / theta functions
(Ch 21 line 305) but never works it out.

What CAN be done concretely: examine when the *unweighted* `G_N(e^(iπα))`
itself can be real. The factorization above implies that for `α` such that
`1 + 2·cos(πα) ≠ 0`, reality of `G_N(e^(iπα))` requires `exp(I·N·π·α)`
to be real (i.e., `N·α ∈ ℤ`). For irrational `α` (such as `√2`), this
fails for every `N ≥ 1`.

So the *unweighted* finite generating function is NEVER the locus of the
manuscript's reality condition for `α = √2`: the weighting `a^{-n}` and
the infinite sum are essential to whatever real-valued limit the manuscript
is invoking. This is a small but explicit structural finding from formalizing
the chapter's gestural argument.
-/

/-- The vanishing locus of `1 + 2·cos θ`: precisely the `θ` with
    `cos θ = -1/2`. (For `θ = π·α` with `α ∈ (1,2)`, this picks out
    `α = 4/3` only; neither `√2` nor `φ + 1/4` is among them.) -/
theorem one_add_two_cos_eq_zero_iff (θ : ℝ) :
    1 + 2 * Real.cos θ = 0 ↔ Real.cos θ = -1/2 := by
  constructor
  · intro h; linarith
  · intro h; linarith

/-- `cos(2π/3) = -1/2`. Derived from `cos(π - x) = -cos x` and
    `cos(π/3) = 1/2`. -/
theorem real_cos_two_pi_div_three : Real.cos (2 * Real.pi / 3) = -1/2 := by
  have h_rewrite : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  rw [h_rewrite]
  -- cos(π - x) = cos π · cos x + sin π · sin x = -cos x
  rw [Real.cos_sub, Real.cos_pi, Real.sin_pi]
  rw [Real.cos_pi_div_three]
  ring

/-- At `α = 2/3` (so `θ = π·α = 2π/3`), `1 + 2·cos(π·α) = 0`.
    This is one of the "trivial" reality points of the unweighted G_N. -/
theorem one_add_two_cos_pi_two_thirds :
    1 + 2 * Real.cos (Real.pi * (2/3)) = 0 := by
  rw [show Real.pi * (2/3) = 2 * Real.pi / 3 from by ring]
  rw [real_cos_two_pi_div_three]
  ring

/-- At `α = 4/3` (so `θ = π·α = 4π/3`), `1 + 2·cos(π·α) = 0`.
    The unique trivial reality point of the unweighted G_N inside the
    manuscript's range `α ∈ (1, 2)`. NOT equal to `α_P = √2` ≈ 1.414. -/
theorem one_add_two_cos_pi_four_thirds :
    1 + 2 * Real.cos (Real.pi * (4/3)) = 0 := by
  -- cos(4π/3) = cos(-2π/3 + 2π) = cos(-2π/3) = cos(2π/3) = -1/2
  have h_split : Real.pi * (4/3) = -(2 * Real.pi / 3) + 2 * Real.pi := by ring
  rw [h_split, Real.cos_add_two_pi, Real.cos_neg, real_cos_two_pi_div_three]
  ring

end PrincipiaTractalis.TuringEncoding
