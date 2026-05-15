/-
# Hankel Contour Small-Loop: Bound-by-Integration

The bound-by-integration step for the small-loop integral, proving
that the magnitude of the parameterized loop integral is bounded by
an explicit expression that vanishes as `ε → 0⁺` for `Re s > 0`.

**Parameterization** (full small circle of radius `ε`):
  `t(θ) := ε · exp(iθ)`,  `θ ∈ [-π, π]`,  derivative `t'(θ) = iε · exp(iθ)`.

**Parametric integrand**: `f(θ) := t(θ)^(s-1) · exp(-t(θ)) · t'(θ)`.

**Pointwise modulus bound**: for `θ ∈ [-π, π]` and `ε > 0`,
  `‖f(θ)‖ ≤ ε^(Re s) · exp(|Im s|·π + ε)`.

**Integral bound**: arc-length `2π` gives
  `‖∫_{-π}^{π} f(θ) dθ‖ ≤ 2π · ε^(Re s) · exp(|Im s|·π + ε)`.

This bound → 0 as `ε → 0⁺` for `Re s > 0` (the `ε^(Re s)` factor
dominates, the others stay bounded).

Stage L4 — Small-loop bound-by-integration.
-/

import PF.Analytic.HankelLowerEdgeDCTProof
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Complex.Trigonometric

namespace PrincipiaTractalis.Analytic

open Complex Filter Topology MeasureTheory

/-! ## Parametric small-loop integrand -/

/-- **Parametric integrand** of the small-loop integral, including the
    derivative factor `iε·exp(iθ)`:

      `f(θ) := (ε · exp(iθ))^(s-1) · exp(-(ε · exp(iθ))) · (i · ε · exp(iθ))`. -/
noncomputable def hankelLoopParametricIntegrand (s : ℂ) (ε : ℝ) (θ : ℝ) : ℂ :=
  ((ε : ℂ) * Complex.exp (I * (θ : ℂ))) ^ (s - 1) *
  Complex.exp (-((ε : ℂ) * Complex.exp (I * (θ : ℂ)))) *
  (I * (ε : ℂ) * Complex.exp (I * (θ : ℂ)))

/-! ## Norm of `ε · exp(iθ)` -/

/-- `‖ε · exp(iθ)‖ = ε` for `ε > 0`. -/
theorem norm_eps_exp_Itheta (ε : ℝ) (hε : 0 < ε) (θ : ℝ) :
    ‖(ε : ℂ) * Complex.exp (I * (θ : ℂ))‖ = ε := by
  rw [norm_mul]
  rw [show I * (θ : ℂ) = ((θ : ℝ) : ℂ) * I from by ring]
  rw [Complex.norm_exp_ofReal_mul_I, mul_one]
  rw [show ‖((ε : ℝ) : ℂ)‖ = |ε| from RCLike.norm_ofReal (K := ℂ) ε]
  exact abs_of_pos hε

/-- `ε · exp(iθ) ≠ 0` for `ε > 0`. -/
theorem eps_exp_Itheta_ne_zero (ε : ℝ) (hε : 0 < ε) (θ : ℝ) :
    (ε : ℂ) * Complex.exp (I * (θ : ℂ)) ≠ 0 := by
  apply mul_ne_zero
  · exact Complex.ofReal_ne_zero.mpr hε.ne'
  · exact Complex.exp_ne_zero _

/-! ## Pointwise modulus bound -/

/-- **Pointwise bound on the parametric integrand**:

      `‖hankelLoopParametricIntegrand s ε θ‖ ≤ ε^(Re s) · exp(|Im s|·π + ε)`

    for `θ ∈ [-π, π]` and `ε > 0`. Combines:
    * `Complex.norm_cpow_le` for the `cpow` factor (no slit-plane needed)
    * `Complex.norm_exp` for the exp factor (Re argument)
    * `‖ε · exp(iθ)‖ = ε` for the derivative factor
    * `|arg z| ≤ π` (universal bound). -/
theorem norm_hankelLoopParametricIntegrand_le
    (s : ℂ) (ε : ℝ) (hε : 0 < ε) (θ : ℝ) :
    ‖hankelLoopParametricIntegrand s ε θ‖ ≤
    ε ^ s.re * Real.exp (|s.im| * Real.pi + ε) := by
  set z : ℂ := (ε : ℂ) * Complex.exp (I * (θ : ℂ)) with hz_def
  have h_z_norm : ‖z‖ = ε := norm_eps_exp_Itheta ε hε θ
  have h_z_ne : z ≠ 0 := eps_exp_Itheta_ne_zero ε hε θ
  -- Unfold and break into three factors
  unfold hankelLoopParametricIntegrand
  rw [← hz_def]
  rw [norm_mul, norm_mul]
  -- Factor 1: ‖z^(s-1)‖ ≤ ‖z‖^(Re(s-1)) / exp(arg z · Im(s-1))
  have h_cpow_norm_le := Complex.norm_cpow_le z (s - 1)
  -- Re(s-1) = Re s - 1, Im(s-1) = Im s
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
             sub_zero] at h_cpow_norm_le
  rw [h_z_norm] at h_cpow_norm_le
  -- h_cpow_norm_le: ‖z^(s-1)‖ ≤ ε^(Re s - 1) / exp(arg z · Im s)
  -- Use 1/exp(arg z · Im s) ≤ exp(|Im s|·π):
  have h_arg_bound : |Complex.arg z| ≤ Real.pi := Complex.abs_arg_le_pi z
  have h_exp_factor :
      ε ^ (s.re - 1) / Real.exp (Complex.arg z * s.im) ≤
      ε ^ (s.re - 1) * Real.exp (|s.im| * Real.pi) := by
    rw [div_eq_mul_inv, ← Real.exp_neg]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hε.le _)
    apply Real.exp_le_exp.mpr
    calc -(Complex.arg z * s.im)
        ≤ |Complex.arg z * s.im| := neg_le_abs _
      _ = |Complex.arg z| * |s.im| := abs_mul _ _
      _ ≤ Real.pi * |s.im| :=
          mul_le_mul_of_nonneg_right h_arg_bound (abs_nonneg _)
      _ = |s.im| * Real.pi := by ring
  have h_cpow_final : ‖z ^ (s - 1)‖ ≤ ε ^ (s.re - 1) * Real.exp (|s.im| * Real.pi) :=
    le_trans h_cpow_norm_le h_exp_factor
  -- Factor 2: ‖exp(-z)‖ = exp(-Re z) = exp(-ε cos θ) ≤ exp(ε)
  have h_exp_neg : ‖Complex.exp (-z)‖ ≤ Real.exp ε := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    -- Compute (exp(I·θ)).re = cos θ
    have h_exp_re : (Complex.exp (I * (θ : ℂ))).re = Real.cos θ := by
      rw [show I * (θ : ℂ) = ((θ : ℝ) : ℂ) * I from by ring]
      rw [Complex.exp_mul_I]
      simp [Complex.cos_ofReal_re]
    -- Re(-z) = -ε · cos θ
    have h_re_neg_z : (-z).re = -ε * Real.cos θ := by
      show (-((ε : ℂ) * Complex.exp (I * (θ : ℂ)))).re = -ε * Real.cos θ
      rw [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero, h_exp_re]
      ring
    rw [h_re_neg_z]
    have h_cos_ge : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
    nlinarith [hε.le]
  -- Factor 3: ‖I · ε · exp(iθ)‖ = ε
  have h_factor3 : ‖I * (ε : ℂ) * Complex.exp (I * (θ : ℂ))‖ = ε := by
    rw [show I * (ε : ℂ) * Complex.exp (I * (θ : ℂ)) =
            I * ((ε : ℂ) * Complex.exp (I * (θ : ℂ))) from by ring]
    rw [norm_mul, Complex.norm_I, one_mul]
    rw [← hz_def, h_z_norm]
  rw [h_factor3]
  -- Combine: ‖z^(s-1)‖ * ‖exp(-z)‖ * ε ≤ ε^(Re s) · exp(|Im s|·π + ε)
  have h_cpow_nn : 0 ≤ ‖z ^ (s - 1)‖ := norm_nonneg _
  have h_exp_neg_nn : 0 ≤ ‖Complex.exp (-z)‖ := norm_nonneg _
  have h_eps_nn : 0 ≤ ε := hε.le
  calc ‖z ^ (s - 1)‖ * ‖Complex.exp (-z)‖ * ε
      ≤ (ε ^ (s.re - 1) * Real.exp (|s.im| * Real.pi)) *
        Real.exp ε * ε := by
        gcongr
    _ = ε ^ (s.re - 1) * ε * (Real.exp (|s.im| * Real.pi) * Real.exp ε) := by ring
    _ = ε ^ (s.re - 1) * ε^(1 : ℝ) * Real.exp (|s.im| * Real.pi + ε) := by
        rw [← Real.exp_add]
        rw [show ε^(1 : ℝ) = ε from Real.rpow_one ε]
    _ = ε ^ (s.re - 1 + 1) * Real.exp (|s.im| * Real.pi + ε) := by
        rw [← Real.rpow_add hε]
    _ = ε ^ s.re * Real.exp (|s.im| * Real.pi + ε) := by
        congr 2; ring

/-! ## Integral norm bound -/

/-- **Integral norm bound** for the small-loop parametric integral:

      `‖∫_{-π}^{π} hankelLoopParametricIntegrand s ε θ dθ‖
       ≤ 2π · ε^(Re s) · exp(|Im s|·π + ε)`.

    Direct application of `intervalIntegral.norm_integral_le_of_norm_le_const`
    with the pointwise bound proven above. -/
theorem hankelLoopParametric_integral_norm_le
    (s : ℂ) (ε : ℝ) (hε : 0 < ε) :
    ‖∫ θ in (-Real.pi)..Real.pi, hankelLoopParametricIntegrand s ε θ‖ ≤
    ε ^ s.re * Real.exp (|s.im| * Real.pi + ε) * (2 * Real.pi) := by
  have h_le := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -Real.pi) (b := Real.pi)
    (f := fun θ => hankelLoopParametricIntegrand s ε θ)
    (C := ε ^ s.re * Real.exp (|s.im| * Real.pi + ε))
    (fun θ _ => norm_hankelLoopParametricIntegrand_le s ε hε θ)
  -- |b - a| = |π - (-π)| = 2π
  have h_abs : |Real.pi - (-Real.pi)| = 2 * Real.pi := by
    rw [show Real.pi - (-Real.pi) = 2 * Real.pi from by ring]
    exact abs_of_pos (by positivity)
  rwa [h_abs] at h_le

/-! ## The integral bound vanishes as ε → 0⁺ -/

/-- **Full-circle loop bound** as a function of `ε`. -/
noncomputable def hankelLoopFullCircleBound (s : ℂ) (ε : ℝ) : ℝ :=
  ε ^ s.re * Real.exp (|s.im| * Real.pi + ε) * (2 * Real.pi)

/-- **Bound vanishes as ε → 0⁺** for `Re s > 0`. -/
theorem hankelLoopFullCircleBound_tendsto_zero {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun ε : ℝ => hankelLoopFullCircleBound s ε)
            (𝓝[>] 0) (𝓝 0) := by
  unfold hankelLoopFullCircleBound
  have h_rpow : Tendsto (fun ε : ℝ => ε ^ s.re) (𝓝[>] 0) (𝓝 0) :=
    rpow_re_tendsto_zero_of_pos hs
  have h_exp : Tendsto (fun ε : ℝ => Real.exp (|s.im| * Real.pi + ε))
                       (𝓝[>] 0) (𝓝 (Real.exp (|s.im| * Real.pi))) := by
    have h_in : Tendsto (fun ε : ℝ => |s.im| * Real.pi + ε) (𝓝 0)
                        (𝓝 (|s.im| * Real.pi + 0)) :=
      tendsto_const_nhds.add tendsto_id
    simp at h_in
    exact ((Real.continuous_exp.tendsto _).comp h_in).mono_left nhdsWithin_le_nhds
  have h_mid : Tendsto (fun ε : ℝ => ε ^ s.re * Real.exp (|s.im| * Real.pi + ε))
                       (𝓝[>] 0) (𝓝 (0 * Real.exp (|s.im| * Real.pi))) :=
    h_rpow.mul h_exp
  rw [zero_mul] at h_mid
  have h_const : Tendsto
      (fun ε : ℝ => ε ^ s.re * Real.exp (|s.im| * Real.pi + ε) * (2 * Real.pi))
      (𝓝[>] 0) (𝓝 (0 * (2 * Real.pi))) :=
    h_mid.mul_const _
  rw [zero_mul] at h_const
  exact h_const

end PrincipiaTractalis.Analytic
