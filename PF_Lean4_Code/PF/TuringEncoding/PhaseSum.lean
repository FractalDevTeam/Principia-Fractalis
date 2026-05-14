/-
# Phase-Weighted Theta-Sum: Closed Form via Geometric Series

The book's V_P kernel uses a convergence factor `a^{-n}` (with `a > 1`) to
weight the theta-sum. The phase-weighted theta-sum corresponds to
PART 3 of `alpha_sqrt2_derivation.py` — the sum

  Φ_a(α) = Σ_{n=0}^∞ a^{-n} · G_n(e^{iπα})
        = Σ_{n=0}^∞ (thetaFactor α / a)^n

where `G_n(z) = (1 + z + z²)^n` is the truncated GF factored via
`truncatedThetaSum_factorization` and `thetaFactor α = 1 + e^{iπα} + e^{2iπα}`.

This is a **geometric series in `thetaFactor α / a`**, which converges
absolutely when `‖thetaFactor α‖ < a`. In that regime it has the closed
form

  Φ_a(α) = a / (a − thetaFactor α).

This is the substantive analytic content underlying the book's
phase-weighted SA criterion: the reality of `Φ_a(α)` reduces to the
reality of `thetaFactor α` (the denominator's structure).

Stage L4 — phase-weighted theta-sum + closed-form analytic identity.
-/

import PF.TuringEncoding.ThetaSum
import Mathlib.Analysis.SpecificLimits.Normed

namespace PrincipiaTractalis.TuringEncoding

open Complex

/-! ## The phase-weighted sum -/

/-- **The phase-weighted theta-sum** with convergence factor `a^{-n}`:
    `Φ_a(α) = Σ_{n=0}^∞ a^{-n} · (1 + e^{iπα} + e^{2iπα})^n`. -/
noncomputable def phaseWeightedThetaSum (α : ℝ) (a : ℝ) : ℂ :=
  ∑' n : ℕ, ((1 / a : ℂ))^n * (thetaFactor α)^n

/-- The summand `(1/a)^n · (thetaFactor α)^n` equals `(thetaFactor α / a)^n`. -/
theorem phaseWeightedThetaSum_eq_geom (α : ℝ) (a : ℝ) :
    phaseWeightedThetaSum α a = ∑' n : ℕ, (thetaFactor α / a) ^ n := by
  unfold phaseWeightedThetaSum
  congr 1
  ext n
  rw [div_pow]
  ring

/-- **Closed form**: when `‖thetaFactor α‖ < a`, the phase-weighted sum
    equals `a / (a − thetaFactor α)`. -/
theorem phaseWeightedThetaSum_closed_form
    (α : ℝ) {a : ℝ} (ha_pos : 0 < a) (ha : ‖thetaFactor α‖ < a) :
    phaseWeightedThetaSum α a = a / ((a : ℂ) - thetaFactor α) := by
  rw [phaseWeightedThetaSum_eq_geom]
  -- ‖thetaFactor α / a‖ < 1
  have h_norm_a : ‖(a : ℂ)‖ = a := by
    have h_abs : |a| = a := abs_of_pos ha_pos
    have h_norm : ‖((a : ℝ) : ℂ)‖ = |a| := RCLike.norm_ofReal (K := ℂ) a
    rw [h_norm, h_abs]
  have h_lt_one : ‖thetaFactor α / (a : ℂ)‖ < 1 := by
    rw [norm_div, h_norm_a]
    exact (div_lt_one ha_pos).mpr ha
  rw [tsum_geometric_of_norm_lt_one h_lt_one]
  -- (1 - thetaFactor α / a)⁻¹ = a / (a - thetaFactor α)
  have h_a_ne : (a : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]
    exact ne_of_gt ha_pos
  field_simp

/-! ## Reality of the phase-weighted sum

The substantive analytic content: when the denominator is real, the
phase-weighted theta-sum is real. -/

/-- **Reality (sufficient direction)**: if `thetaFactor α` is real and the
    sum converges, then the phase-weighted theta-sum is real. This is the
    substantive content of the V_P kernel's SA reality criterion at the
    phase-sum level. -/
theorem phaseWeightedThetaSum_im_eq_zero_of_factor_im_zero
    (α : ℝ) {a : ℝ} (ha_pos : 0 < a) (ha : ‖thetaFactor α‖ < a)
    (h_tf_im : (thetaFactor α).im = 0) :
    (phaseWeightedThetaSum α a).im = 0 := by
  rw [phaseWeightedThetaSum_closed_form α ha_pos ha]
  -- a / (a - thetaFactor α): numerator real, denominator real (by hypothesis),
  -- so the quotient is real.
  -- Compute: (a / w).im = (a.im * w.re - a.re * w.im) / ‖w‖²
  --        = (0 * w.re - a * w.im) / ‖w‖²
  --        = -a * w.im / ‖w‖²
  -- With w.im = (a - tF α).im = -tF α.im = 0, the whole thing is 0.
  have h_a_im : ((a : ℂ)).im = 0 := Complex.ofReal_im _
  have h_a_re : ((a : ℂ)).re = a := Complex.ofReal_re _
  have h_diff_im : ((a : ℂ) - thetaFactor α).im = 0 := by
    simp [Complex.sub_im, h_tf_im]
  rw [Complex.div_im, h_a_im, h_a_re, h_diff_im]
  simp

/-! ## Connection to the truncated theta-sum

The phase-weighted sum `Φ_a(α)` is the `n → ∞` limit (with convergence
factor `a^{-n}`) of partial sums of the truncated theta-sums `Θ_N(α)`.
Specifically, each truncated `Θ_N(α) = thetaFactor(α)^N`, so

  Φ_a(α) = Σ_N a^{-N} · Θ_N(α) = Σ_N (thetaFactor α / a)^N.

This is the bridge between the finite GF/theta-sum framework (L3, L4
foundation) and the asymptotic SA reality criterion. -/

/-- The phase-weighted sum can be expressed as a power series in
    `truncatedThetaSum α N` (each term being `(thetaFactor α)^N`). -/
theorem phaseWeightedThetaSum_eq_thetaSum_series (α : ℝ) (a : ℝ) :
    phaseWeightedThetaSum α a =
      ∑' N : ℕ, ((1 / a : ℂ))^N * truncatedThetaSum α N := by
  unfold phaseWeightedThetaSum
  congr 1
  ext N
  rw [truncatedThetaSum_eq_factor_pow]

end PrincipiaTractalis.TuringEncoding
