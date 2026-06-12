/-
# Double Integral of `cos(π · c · (x − y))` — Closed Form

The framework's `PF/Analytic/PolylogSpectrum.lean` documents the
following double-integral identity as "proof deferred":

  ∫_0^1 ∫_0^1 cos(π · c · (x − y)) dx dy
    = (sin(π·c)/(π·c))² + ((1 − cos(π·c))/(π·c))²
    = 4 · sin²(π·c/2) / (π·c)²    (for c ≠ 0)

This is the foundational closed form for **variational eigenvalue
upper bounds** on `H_P^α` via Rayleigh-Ritz with constant test function:

  ⟨1, H_P^α · 1⟩_{L²[0,1]} = ∫_0^1 ∫_0^1 V_P(x, y) dx dy
    = Σ_{n ≥ 0} a^{-n} · 4·sin²(π·αⁿ/2) / (π·αⁿ)²

By Rayleigh-Ritz: `λ_0(H_P^α) ≤ ⟨1, H_P^α · 1⟩ / ⟨1, 1⟩`.

This file delivers the per-term identity (axiom-free), closing the
"proof deferred" gap in `PolylogSpectrum.lean` for the single
double-integral identity. The per-summand structure that lifts this
to the full variational identity is the Mercer rank-2-per-scale
decomposition already in the kernel infrastructure.

## Proof strategy

Inner-then-outer integration using:
* `Real.cos_sub` — `cos(a − b) = cos a · cos b + sin a · sin b`.
* `integral_cosine_pi_c`, `integral_sine_pi_c` — first cosine/sine
  moments on `[0, 1]` (already in `PolylogSpectrum.lean`).
* `intervalIntegral` linearity.
* Pythagorean identity `sin² + cos² = 1` + half-angle identity.

No Fubini interchange needed.

All theorems kernel-only `[propext, Classical.choice, Quot.sound]`;
zero project axioms.

Author: Pablo Cohen + Claude Opus 4.7. 2026-06-12.
-/

import PF.Analytic.PolylogSpectrum

namespace PrincipiaTractalis.Analytic

open Real MeasureTheory

/-! ## §1 — Inner integral closed form (over y, for fixed x) -/

/-- **Inner integral closed form**: for `c ≠ 0` and fixed `x : ℝ`,

      `∫_0^1 cos(π · c · (x − y)) dy
        = cos(π · c · x) · (sin(π · c) / (π · c))
          + sin(π · c · x) · ((1 − cos(π · c)) / (π · c))`.

    Via `cos(a − b) = cos a · cos b + sin a · sin b` and linearity of
    the integral over `y`. -/
theorem integral_cos_pi_c_x_sub_y_inner
    {c : ℝ} (hc : c ≠ 0) (x : ℝ) :
    (∫ y in (0:ℝ)..1, Real.cos (Real.pi * c * (x - y)))
    = Real.cos (Real.pi * c * x) * (Real.sin (Real.pi * c) / (Real.pi * c))
      + Real.sin (Real.pi * c * x)
        * ((1 - Real.cos (Real.pi * c)) / (Real.pi * c)) := by
  have h_expand : ∀ y : ℝ, Real.cos (Real.pi * c * (x - y))
      = Real.cos (Real.pi * c * x) * Real.cos (Real.pi * c * y)
        + Real.sin (Real.pi * c * x) * Real.sin (Real.pi * c * y) := by
    intro y
    have h_rewrite : Real.pi * c * (x - y) = Real.pi * c * x - Real.pi * c * y := by ring
    rw [h_rewrite, Real.cos_sub]
  conv => lhs; rw [show (fun y => Real.cos (Real.pi * c * (x - y))) =
    (fun y => Real.cos (Real.pi * c * x) * Real.cos (Real.pi * c * y)
              + Real.sin (Real.pi * c * x) * Real.sin (Real.pi * c * y))
    from by funext y; exact h_expand y]
  have h_cont_cos : Continuous (fun y : ℝ =>
      Real.cos (Real.pi * c * x) * Real.cos (Real.pi * c * y)) :=
    continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  have h_cont_sin : Continuous (fun y : ℝ =>
      Real.sin (Real.pi * c * x) * Real.sin (Real.pi * c * y)) :=
    continuous_const.mul (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  rw [intervalIntegral.integral_add
        (h_cont_cos.intervalIntegrable _ _)
        (h_cont_sin.intervalIntegrable _ _)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [integral_cosine_pi_c hc, integral_sine_pi_c hc]

/-! ## §2 — Outer integral closed form -/

/-- **Outer integral closed form** (the cos-of-difference double
    integral identity):

      `∫_0^1 ∫_0^1 cos(π · c · (x − y)) dy dx
        = (sin(π · c) / (π · c))² + ((1 − cos(π · c)) / (π · c))²`

    for `c ≠ 0`. Direct from the inner identity (§1) integrated over
    `x ∈ [0, 1]` using cosine/sine first-moment formulas. -/
theorem integral_integral_cos_pi_c_diff_eq_sq
    {c : ℝ} (hc : c ≠ 0) :
    (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, Real.cos (Real.pi * c * (x - y)))
    = (Real.sin (Real.pi * c) / (Real.pi * c)) ^ 2
      + ((1 - Real.cos (Real.pi * c)) / (Real.pi * c)) ^ 2 := by
  have h_inner_eq :
      (fun x : ℝ => ∫ y in (0:ℝ)..1, Real.cos (Real.pi * c * (x - y)))
      = (fun x : ℝ =>
          Real.cos (Real.pi * c * x)
            * (Real.sin (Real.pi * c) / (Real.pi * c))
          + Real.sin (Real.pi * c * x)
            * ((1 - Real.cos (Real.pi * c)) / (Real.pi * c))) := by
    funext x; exact integral_cos_pi_c_x_sub_y_inner hc x
  rw [h_inner_eq]
  -- Outer integral splits into two products.
  set A := Real.sin (Real.pi * c) / (Real.pi * c)
  set B := (1 - Real.cos (Real.pi * c)) / (Real.pi * c)
  have h_cont_cos_term : Continuous (fun x : ℝ => Real.cos (Real.pi * c * x) * A) :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul continuous_const
  have h_cont_sin_term : Continuous (fun x : ℝ => Real.sin (Real.pi * c * x) * B) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).mul continuous_const
  rw [intervalIntegral.integral_add
        (h_cont_cos_term.intervalIntegrable _ _)
        (h_cont_sin_term.intervalIntegrable _ _)]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
  rw [integral_cosine_pi_c hc, integral_sine_pi_c hc]
  show A * A + B * B = A ^ 2 + B ^ 2
  ring

/-! ## §3 — Half-angle closed form -/

/-- **Half-angle simplification**: for any `t : ℝ`,

      `sin²(t) + (1 − cos(t))² = 2 · (1 − cos(t)) = 4 · sin²(t/2)`.

    Standard identity. -/
theorem sq_sin_add_sq_one_sub_cos_eq_four_sq_sin_half
    (t : ℝ) :
    Real.sin t ^ 2 + (1 - Real.cos t) ^ 2 = 4 * Real.sin (t / 2) ^ 2 := by
  have h_pyth : Real.sin t ^ 2 + Real.cos t ^ 2 = 1 := Real.sin_sq_add_cos_sq t
  -- cos(t) = cos(2·(t/2)) = 1 - 2 sin²(t/2) (via cos_two_mul + pyth identity)
  have h_half : 1 - Real.cos t = 2 * Real.sin (t / 2) ^ 2 := by
    have h_full : t = 2 * (t / 2) := by ring
    have h_two_mul : Real.cos (2 * (t / 2))
        = 2 * Real.cos (t / 2) ^ 2 - 1 := Real.cos_two_mul (t / 2)
    have h_sin_sq : Real.sin (t / 2) ^ 2 + Real.cos (t / 2) ^ 2 = 1 :=
      Real.sin_sq_add_cos_sq (t / 2)
    rw [h_full, h_two_mul]
    have h_cos_sq : Real.cos (t / 2) ^ 2 = 1 - Real.sin (t / 2) ^ 2 := by
      linarith
    rw [h_cos_sq]; ring
  -- Final step: sin²t + (1-cos t)² = 4 sin²(t/2)
  -- Plan: rewrite using h_pyth and h_half to reduce both sides.
  have h_step1 : Real.sin t ^ 2 + (1 - Real.cos t) ^ 2
      = 2 * (1 - Real.cos t) := by
    have h_expand : (1 - Real.cos t) ^ 2
        = 1 - 2 * Real.cos t + Real.cos t ^ 2 := by ring
    have : Real.sin t ^ 2 + (1 - 2 * Real.cos t + Real.cos t ^ 2)
        = (Real.sin t ^ 2 + Real.cos t ^ 2) + (1 - 2 * Real.cos t) := by ring
    rw [h_expand, this, h_pyth]; ring
  rw [h_step1, h_half]; ring

/-! ## §4 — Capstone -/

/-- **★ DOUBLE INTEGRAL OF cos(π · c · (x − y)) CLOSED FORM ★** —
    `integral_integral_cos_pi_c_diff_closed_form`.

    The cleanly stated closed-form double integral over `[0, 1]²`:

      `∫_0^1 ∫_0^1 cos(π · c · (x − y)) dy dx = 4 · sin²(π · c / 2) / (π · c)²`

    for `c ≠ 0`. Closes the explicit "proof deferred" gap in
    `PolylogSpectrum.lean`.

    Application: by the Mercer rank-2-per-scale kernel decomposition,

      `⟨1, H_P^α · 1⟩_{L²[0,1]} = ∫_0^1 ∫_0^1 V_P(x, y) dx dy
        = Σ_{n ≥ 0} a^{-n} · 4 · sin²(π · αⁿ / 2) / (π · αⁿ)²`

    By Rayleigh-Ritz with constant test function, this gives an
    UPPER BOUND on the smallest eigenvalue of `H_P^α`. -/
theorem integral_integral_cos_pi_c_diff_closed_form
    {c : ℝ} (hc : c ≠ 0) :
    (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, Real.cos (Real.pi * c * (x - y)))
    = 4 * Real.sin (Real.pi * c / 2) ^ 2 / (Real.pi * c) ^ 2 := by
  rw [integral_integral_cos_pi_c_diff_eq_sq hc]
  have hpc_ne : Real.pi * c ≠ 0 := mul_ne_zero Real.pi_ne_zero hc
  have h_id := sq_sin_add_sq_one_sub_cos_eq_four_sq_sin_half (Real.pi * c)
  -- LHS: (sin(πc)/(πc))² + ((1-cos(πc))/(πc))²
  --    = [sin²(πc) + (1-cos(πc))²] / (πc)²
  --    = 4·sin²(πc/2)/(πc)²  by h_id
  have h_combine : (Real.sin (Real.pi * c) / (Real.pi * c)) ^ 2
      + ((1 - Real.cos (Real.pi * c)) / (Real.pi * c)) ^ 2
      = (Real.sin (Real.pi * c) ^ 2 + (1 - Real.cos (Real.pi * c)) ^ 2)
        / (Real.pi * c) ^ 2 := by
    field_simp
  rw [h_combine, h_id]

end PrincipiaTractalis.Analytic

#print axioms
  PrincipiaTractalis.Analytic.integral_integral_cos_pi_c_diff_closed_form
