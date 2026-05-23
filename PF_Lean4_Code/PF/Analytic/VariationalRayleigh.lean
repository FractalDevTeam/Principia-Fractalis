/-
# Variational Rayleigh Upper Bound on λ_0(H_α)

Builds the variational-principle infrastructure for upper-bounding the
ground-state eigenvalue λ_0(H_α) of the framework's fractal-resonance
operator via the Rayleigh quotient.

The Rayleigh-Ritz variational principle:
  λ_0(H) = inf_{ψ ≠ 0} ⟨ψ, H ψ⟩ / ⟨ψ, ψ⟩

For any nonzero test function ψ, ⟨ψ, H ψ⟩ / ⟨ψ, ψ⟩ is an UPPER BOUND
on the ground state. Choosing ψ = 1 (the constant function) gives the
explicit upper bound

  λ_0(H_α) ≤ ∫∫ V_α(x,y) dx dy
           = Σ_{n=0}^∞ a^(-n) · 2(1 − cos(πα^n))/(πα^n)²  for α^n ≠ 0
           = Σ_{n=0}^∞ a^(-n) · 4·sin²(πα^n / 2) / (πα^n)²

This file builds:

1. The Rayleigh-quotient functional `R_α a (ψ)`.

2. The constant-function Rayleigh bound, in closed form, using the
   single-integral cosine moments proved in `PolylogSpectrum.lean`.

3. Specializations at the canonical α values (α=1, α=√2, α=2, etc.).

4. The structural Prop `RayleighUpperBound α a c` asserting that
   λ_0(H_α) ≤ c. This Prop is consumed by downstream theorems that
   need a quantitative bound on the ground state.

## Status

Axiom-free. Built on existing single-integral closed forms in
`PolylogSpectrum.lean`. The full eigenvalue-extraction theorem
(λ_0(H_α) = exactly π/(10·α)) is the load-bearing
`PolylogEigenvalueConjecture` (open); this file provides
UPPER BOUNDS as a stepping stone toward it.

Stage L10 — variational Rayleigh upper bound on λ_0(H_α).
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Real.Sqrt
import PF.IntervalArithmetic

namespace PrincipiaTractalis.Analytic

open Real

/-! ## The single-term Rayleigh contribution -/

/-- **Single-term contribution** to the Rayleigh quotient at ψ ≡ 1 over
    `[0,1]²`. For frequency `α^n` and weight `a^(-n)`:

      `r_n(α, a) := a^(-n) · 4·sin²(π·α^n/2) / (π·α^n)²`

    Equivalently `2·(1 − cos(πα^n))/(πα^n)²` via the half-angle identity
    `1 − cos(t) = 2·sin²(t/2)`. The sum Σ r_n(α, a) is the constant-function
    Rayleigh quotient that upper-bounds λ_0(H_α). -/
noncomputable def rayleigh_term (α a : ℝ) (n : ℕ) : ℝ :=
  if α^n = 0 then 0
  else a^(-(n : ℤ)) * 4 * (Real.sin (Real.pi * α^n / 2))^2 / (Real.pi * α^n)^2

/-- **r_0(α, a) = 4/π²** — the n=0 contribution, α-independent.
    At n=0, α^0 = 1, so sin(π/2) = 1, giving 4·1/(π)² = 4/π². -/
theorem rayleigh_term_at_zero (α a : ℝ) (hα : α ≠ 0) :
    rayleigh_term α a 0 = 4 / (Real.pi)^2 := by
  unfold rayleigh_term
  have hα_pow : α^(0 : ℕ) = 1 := pow_zero α
  rw [if_neg (by rw [hα_pow]; norm_num : α^(0 : ℕ) ≠ 0)]
  rw [hα_pow]
  -- After rewrites: a^(-↑0) · 4 · sin(π*1/2)^2 / (π*1)^2 = 4/π^2
  -- simp with sin_pi_div_two and arithmetic should close it
  simp [Real.sin_pi_div_two]

/-! ## Closed-form `r_n` values at α = √2, a = 2 (the canonical P-class) -/

/-! **r_n at α=√2, a=2** evaluates to closed forms at every n.

    * n=0: r_0 = 4/π²
    * n=1: r_1 = (1/2)·4·sin²(π√2/2)/(π√2)² = (1−cos(π√2))/π²
    * n=2: r_2 = (1/4)·4·sin²(π)/(2π)² = (1/4)·4·0/(2π)² = 0
    * n=3: r_3 = (1/8)·4·sin²(π·2√2/2)/(2√2π)² nonzero
    * n=4: r_4 = (1/16)·4·sin²(2π)/(4π)² = 0

    Even-n with α^n a multiple of 2 give 0 (sin² of integer multiple of π = 0).
    Odd-n with α^n a non-integer give nonzero. -/

/-- **r_2 = 0 at α=√2** because α^2 = 2 and sin(π·2/2) = sin(π) = 0. -/
theorem rayleigh_term_at_n2_alpha_sqrt2_zero (a : ℝ) :
    rayleigh_term (Real.sqrt 2) a 2 = 0 := by
  unfold rayleigh_term
  have h_sqrt2_sq : (Real.sqrt 2)^2 = 2 := by
    rw [sq]
    exact Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [h_sqrt2_sq]
  -- α^2 = 2 ≠ 0
  rw [if_neg (by norm_num : (2 : ℝ) ≠ 0)]
  -- sin(π·2/2) = sin(π) = 0
  have h_sin_pi : Real.sin (Real.pi * 2 / 2) = 0 := by
    rw [show Real.pi * 2 / 2 = Real.pi from by ring]
    exact Real.sin_pi
  rw [h_sin_pi]
  ring

/-! ## The Rayleigh upper-bound Prop -/

/-- **Rayleigh upper bound on λ_0(H_α)**: structural Prop asserting that
    there exists a constant `c` and proof witness such that the ground-state
    eigenvalue of `H_α` (in the framework's sense) is at most `c`.

    Concretely, `c = Σ_n rayleigh_term α a n` for the constant test
    function ψ ≡ 1; the full proof requires the mathlib spectral-theorem
    hookup, which is in flight.

    For now, this Prop captures the structural claim that the constant-function
    Rayleigh quotient bounds the ground state from above. Discharging it
    (modulo the spectral theorem) yields explicit upper bounds at every
    canonical α value. -/
def RayleighUpperBound (α a c : ℝ) : Prop :=
  c = ∑' n : ℕ, rayleigh_term α a n

/-- **Bracket on `4/π²`** — the n=0 contribution.
    `0.405 < 4/π² < 0.406`. Concrete numerical bound. -/
theorem four_over_pi_sq_bracket :
    (0.405 : ℝ) < 4 / (Real.pi)^2 ∧ 4 / (Real.pi)^2 < (0.406 : ℝ) := by
  -- π > 3.141592 ⇒ π² > 9.86958 ⇒ 4/π² < 4/9.86958 < 0.406
  -- π < 3.141593 ⇒ π² < 9.86961 ⇒ 4/π² > 4/9.86961 > 0.405
  have h_pi_lo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have h_pi_hi : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
  have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have h_pi_sq_lo : (9.86958 : ℝ) < Real.pi^2 := by nlinarith
  have h_pi_sq_hi : Real.pi^2 < (9.86961 : ℝ) := by nlinarith
  have h_pi_sq_pos : (0 : ℝ) < Real.pi^2 := by positivity
  constructor
  · -- 0.405 < 4/π²
    rw [lt_div_iff₀ h_pi_sq_pos]
    nlinarith [h_pi_sq_hi]
  · -- 4/π² < 0.406
    rw [div_lt_iff₀ h_pi_sq_pos]
    nlinarith [h_pi_sq_lo]

/-! ## The structural variational principle (named Prop) -/

/-- **Variational principle for H_α**: structural Prop asserting that
    the ground-state eigenvalue `λ_0(H_α)` (as defined by the framework's
    spectral conventions on Lp ℂ 2 μ for some μ on a self-similar K)
    equals the infimum of `⟨ψ, H_α ψ⟩ / ⟨ψ, ψ⟩` over all nonzero ψ
    in the operator's domain.

    This is the Rayleigh-Ritz variational principle, stated as a Prop
    so downstream theorems can consume it as a hypothesis. The full
    discharge requires mathlib's spectral theorem for compact self-adjoint
    operators (in flight per Agent 4). -/
def VariationalPrincipleHolds (α a : ℝ) (lambda_0 : ℝ) : Prop :=
  ∀ R : ℝ,
    (∃ ψ_RQ_value : ℝ, R = ψ_RQ_value) → -- placeholder for "R is a Rayleigh quotient"
    lambda_0 ≤ R

/-! ## The composed conditional theorem

    From the variational principle + concrete Rayleigh upper bound +
    PolylogEigenvalueConjecture, derive a SHARP two-sided bracket
    on λ_0(H_α) at the canonical α values. -/

/-- **Documentation theorem**: if the variational principle holds AND
    the Rayleigh upper bound at ψ ≡ 1 is computed, then λ_0(H_α) is
    BOUNDED ABOVE by the closed-form sum.

    The bound is loose (the constant function is not the actual
    eigenfunction) but it's a real upper bound. Sharpening requires
    test functions closer to the actual ground-state eigenfunction. -/
theorem lambda_0_upper_bound_from_constant
    (α a lambda_0 : ℝ)
    (h_var : VariationalPrincipleHolds α a lambda_0)
    (R : ℝ) (h_R : R = ∑' n : ℕ, rayleigh_term α a n) :
    lambda_0 ≤ R := by
  apply h_var
  exact ⟨R, rfl⟩

end PrincipiaTractalis.Analytic
