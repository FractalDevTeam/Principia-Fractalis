/-
# Hankel Lower-Edge DCT — Unified Theorem (all `Re s > 0`)

The lower-edge DCT invocation for the `Re s ≥ 1` regime, combined with
the previously-proven `Re s ≤ 1` case into a unified theorem covering
all `Re s > 0`, including the boundary `Re s = 1`.

Mirrors `HankelUpperEdgeDCTUnified.lean`, adapted to the wrapped-branch
lower-edge integrand with constant branch factor `e^(2πi(s-1))`.

Stage L4 — Lower-edge DCT unified (all `Re s > 0`).
-/

import PF.Analytic.HankelUpperEdgeDCTUnified

namespace PrincipiaTractalis.Analytic

open Complex Filter Topology MeasureTheory Set

/-! ## Lower-edge rpow bound for `Re s ≥ 1` -/

/-- **Rpow bound for `Re s ≥ 1`** on the lower edge:
    `‖t - iε‖^(Re s - 1) ≤ (1 + t)^(Re s - 1)`.
    Combines `norm_lower_eq_upper` with the upper-edge version. -/
theorem norm_rpow_lower_edge_le_one_plus_t_of_re_ge_one
    (t ε : ℝ) (ht : 0 < t) (hε : |ε| ≤ 1) (s : ℂ) (hs : 1 ≤ s.re) :
    ‖(t : ℂ) - (ε : ℂ) * I‖ ^ (s.re - 1) ≤ (1 + t) ^ (s.re - 1) := by
  rw [norm_lower_eq_upper]
  exact norm_rpow_upper_edge_le_one_plus_t_of_re_ge_one t ε ht hε s hs

/-! ## ε-uniform bound for `Re s ≥ 1` on the lower edge -/

/-- **ε-uniform integrand bound for `1 ≤ Re s`, `|ε| ≤ 1`** on the
    lower edge:

      `‖F ε t‖ ≤ exp(-2π·Im s) · exp(|Im s|·π/2) ·
                  (1 + t)^(Re s - 1) · exp(-t)`. -/
theorem hankelLowerEdgeIntegrand_norm_le_of_re_ge_one
    {s : ℂ} (hs1 : 1 ≤ s.re) (t ε : ℝ) (ht : 0 < t) (hε : |ε| ≤ 1) :
    ‖hankelLowerEdgeIntegrand s ε t‖ ≤
    Real.exp (-(2 * Real.pi * s.im)) *
    Real.exp (|s.im| * Real.pi / 2) *
    (1 + t) ^ (s.re - 1) * Real.exp (-t) := by
  have h_main := norm_hankelLowerEdgeIntegrand_le t ε ht s
  rw [norm_lower_eq_upper] at h_main
  have h_rpow := norm_rpow_upper_edge_le_one_plus_t_of_re_ge_one t ε ht hε s hs1
  have h_branch_nn : 0 ≤ Real.exp (-(2 * Real.pi * s.im)) := Real.exp_nonneg _
  have h_const_nn : 0 ≤ Real.exp (|s.im| * Real.pi / 2) := Real.exp_nonneg _
  have h_exp_nn : 0 ≤ Real.exp (-t) := Real.exp_nonneg _
  calc ‖hankelLowerEdgeIntegrand s ε t‖
      ≤ Real.exp (-(2 * Real.pi * s.im)) *
          (‖(t : ℂ) + (ε : ℂ) * I‖ ^ (s.re - 1) *
           Real.exp (|s.im| * Real.pi / 2)) *
          Real.exp (-t) := h_main
    _ ≤ Real.exp (-(2 * Real.pi * s.im)) *
          ((1 + t) ^ (s.re - 1) * Real.exp (|s.im| * Real.pi / 2)) *
          Real.exp (-t) := by
        apply mul_le_mul_of_nonneg_right _ h_exp_nn
        apply mul_le_mul_of_nonneg_left _ h_branch_nn
        exact mul_le_mul_of_nonneg_right h_rpow h_const_nn
    _ = Real.exp (-(2 * Real.pi * s.im)) *
          Real.exp (|s.im| * Real.pi / 2) *
          (1 + t) ^ (s.re - 1) * Real.exp (-t) := by ring

/-! ## DCT invocation for `Re s ≥ 1` on the lower edge -/

/-- **Lower-edge integral converges to `e^(2πi(s-1)) · Γ(s)`** for
    `Re s ≥ 1`. Same DCT pattern as the upper edge, with the
    wrapped-branch integrand and constant branch factor. -/
theorem hankelLowerEdge_integral_tends_to_branch_Gamma_of_re_ge_one
    {s : ℂ} (hs : 0 < s.re) (hs1 : 1 ≤ s.re) :
    Tendsto (fun ε : ℝ => ∫ t in Ioi (0 : ℝ), hankelLowerEdgeIntegrand s ε t)
            (𝓝[>] 0)
            (𝓝 (Complex.exp (2 * (Real.pi : ℂ) * I * (s - 1)) *
                 Complex.Gamma s)) := by
  rw [← integral_gammaLowerLimitIntegrand_eq hs]
  set bound : ℝ → ℝ := fun t =>
    Real.exp (-(2 * Real.pi * s.im)) *
    Real.exp (|s.im| * Real.pi / 2) *
    (1 + t) ^ (s.re - 1) * Real.exp (-t)
  have h_within : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := by
    apply mem_nhdsWithin.mpr
    refine ⟨Set.Iio 1, isOpen_Iio, by norm_num, ?_⟩
    intro x ⟨hx_lt, hx_pos⟩
    exact ⟨hx_pos, hx_lt⟩
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence bound
    (Filter.Eventually.of_forall (fun _ =>
      hankelLowerEdgeIntegrand_aestronglyMeasurable s _))
    ?_ ?_ ?_
  · -- ε-uniform bound
    filter_upwards [h_within] with ε hε
    have hε_pos : 0 < ε := hε.1
    have hε_lt : ε < 1 := hε.2
    have h_abs : |ε| ≤ 1 := by rw [abs_of_pos hε_pos]; linarith
    refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    exact hankelLowerEdgeIntegrand_norm_le_of_re_ge_one hs1 t ε
      (Set.mem_Ioi.mp ht) h_abs
  · -- Bound integrability
    have h := ((one_plus_t_rpow_mul_exp_integrable hs hs1).const_mul
                (Real.exp (|s.im| * Real.pi / 2))).const_mul
                (Real.exp (-(2 * Real.pi * s.im)))
    refine h.congr ?_
    filter_upwards with t
    show Real.exp (-(2 * Real.pi * s.im)) *
         (Real.exp (|s.im| * Real.pi / 2) *
          ((1 + t) ^ (s.re - 1) * Real.exp (-t))) = bound t
    show Real.exp (-(2 * Real.pi * s.im)) *
         (Real.exp (|s.im| * Real.pi / 2) *
          ((1 + t) ^ (s.re - 1) * Real.exp (-t))) =
         Real.exp (-(2 * Real.pi * s.im)) *
         Real.exp (|s.im| * Real.pi / 2) *
         (1 + t) ^ (s.re - 1) * Real.exp (-t)
    ring
  · -- Pointwise convergence
    refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    exact hankelLowerEdgeIntegrand_tendsto_pointwise_pos (Set.mem_Ioi.mp ht)

/-! ## Unified lower-edge theorem for all `Re s > 0` -/

/-- **★ Unified lower-edge integral convergence**:

      `Tendsto (fun ε => ∫ t in Ioi 0, hankelLowerEdgeIntegrand s ε t)
              (𝓝[>] 0) (𝓝 (e^(2πi(s-1)) · Γ(s)))`

    for **all** `Re s > 0`. Case-splits on `Re s ≤ 1` vs `1 ≤ Re s`,
    with the boundary `Re s = 1` covered by either branch. -/
theorem hankelLowerEdge_integral_tends_to_branch_Gamma
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun ε : ℝ => ∫ t in Ioi (0 : ℝ), hankelLowerEdgeIntegrand s ε t)
            (𝓝[>] 0)
            (𝓝 (Complex.exp (2 * (Real.pi : ℂ) * I * (s - 1)) *
                 Complex.Gamma s)) := by
  rcases le_or_gt s.re 1 with h1 | h1
  · exact hankelLowerEdge_integral_tends_to_branch_Gamma_of_re_le_one hs h1
  · exact hankelLowerEdge_integral_tends_to_branch_Gamma_of_re_ge_one hs h1.le

/-! ## Unified Cauchy capstone for all `Re s > 0` -/

/-- **★ UNIFIED CAUCHY CAPSTONE** for all `Re s > 0` (incl. `Re s = 1`):

      `Tendsto (fun ε => ∫ upper − ∫ lower) (𝓝[>] 0)
              (𝓝 ((1 - e^(2πi(s-1))) · Γ(s)))`

    Direct `Tendsto.sub` of the unified upper- and lower-edge limits. -/
theorem hankelEdgeDifference_integral_tends_to_factor_Gamma
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun ε : ℝ =>
      (∫ t in Ioi (0 : ℝ), hankelUpperEdgeIntegrand s ε t) -
      (∫ t in Ioi (0 : ℝ), hankelLowerEdgeIntegrand s ε t))
      (𝓝[>] 0)
      (𝓝 ((1 - Complex.exp (2 * (Real.pi : ℂ) * I * (s - 1))) *
           Complex.Gamma s)) := by
  have h_upper := hankelUpperEdge_integral_tends_to_Gamma hs
  have h_lower := hankelLowerEdge_integral_tends_to_branch_Gamma hs
  have h_eq : Complex.Gamma s -
              Complex.exp (2 * (Real.pi : ℂ) * I * (s - 1)) * Complex.Gamma s =
              (1 - Complex.exp (2 * (Real.pi : ℂ) * I * (s - 1))) * Complex.Gamma s := by
    ring
  rw [← h_eq]
  exact h_upper.sub h_lower

/-- **Unified Cauchy capstone in trig form** (via `hankel_branch_jump_identity`). -/
theorem hankelEdgeDifference_integral_tends_to_trig_Gamma
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun ε : ℝ =>
      (∫ t in Ioi (0 : ℝ), hankelUpperEdgeIntegrand s ε t) -
      (∫ t in Ioi (0 : ℝ), hankelLowerEdgeIntegrand s ε t))
      (𝓝[>] 0)
      (𝓝 (2 * I * Complex.exp ((Real.pi : ℂ) * I * (s - 1)) *
           Complex.sin ((Real.pi : ℂ) * s) * Complex.Gamma s)) := by
  have h := hankelEdgeDifference_integral_tends_to_factor_Gamma hs
  have h_jump := hankel_branch_jump_identity s
  have h_eq :
      (1 - Complex.exp (2 * (Real.pi : ℂ) * I * (s - 1))) * Complex.Gamma s =
      2 * I * Complex.exp ((Real.pi : ℂ) * I * (s - 1)) *
      Complex.sin ((Real.pi : ℂ) * s) * Complex.Gamma s := by
    rw [h_jump]
  rw [← h_eq]
  exact h

/-- **★ Unified Cauchy capstone connecting to `gammaHankelTarget`**
    (Euler reflection):
    For all `Re s > 0` with `sin(πs) ≠ 0` and `Γ(s) ≠ 0`,

      `∫ upper − ∫ lower → e^(iπ(s-1)) · (2πi / Γ(1-s))`. -/
theorem hankelEdgeDifference_integral_tends_to_phased_target
    {s : ℂ} (hs : 0 < s.re)
    (h_sin_ne : Complex.sin ((Real.pi : ℂ) * s) ≠ 0)
    (h_Gamma_ne : Complex.Gamma s ≠ 0) :
    Tendsto (fun ε : ℝ =>
      (∫ t in Ioi (0 : ℝ), hankelUpperEdgeIntegrand s ε t) -
      (∫ t in Ioi (0 : ℝ), hankelLowerEdgeIntegrand s ε t))
      (𝓝[>] 0)
      (𝓝 (Complex.exp ((Real.pi : ℂ) * I * (s - 1)) *
           gammaHankelTarget s)) := by
  have h := hankelEdgeDifference_integral_tends_to_trig_Gamma hs
  have h_collapsed := gammaHankelCollapsed_eq_target h_sin_ne h_Gamma_ne
  unfold gammaHankelCollapsed gammaHankelTarget at h_collapsed
  have h_eq :
      Complex.exp ((Real.pi : ℂ) * I * (s - 1)) * gammaHankelTarget s =
      2 * I * Complex.exp ((Real.pi : ℂ) * I * (s - 1)) *
      Complex.sin ((Real.pi : ℂ) * s) * Complex.Gamma s := by
    unfold gammaHankelTarget
    rw [← h_collapsed]
    ring
  rw [h_eq]
  exact h

end PrincipiaTractalis.Analytic
