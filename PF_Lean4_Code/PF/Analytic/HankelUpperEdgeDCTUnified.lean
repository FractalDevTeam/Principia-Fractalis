/-
# Hankel Upper-Edge DCT — Unified Theorem (all `Re s > 0`)

The full upper-edge DCT invocation for the `Re s ≥ 1` regime, combined
with the previously-proven `Re s ≤ 1` case (in `HankelUpperEdgeDCTProof`)
into a UNIFIED theorem covering all `Re s > 0`, including the
boundary case `Re s = 1`.

**Strategy**: case-split on `s.re ≤ 1` vs `1 ≤ s.re`. These overlap
at exactly `Re s = 1`, where either branch handles the case. Together
they cover all `Re s > 0`.

This file:
* Proves the DCT invocation for `Re s ≥ 1` (mirrors the `Re s ≤ 1`
  proof in `HankelUpperEdgeDCTProof.lean`).
* Combines the two regimes into a single theorem for all `Re s > 0`.

Stage L4 — Upper-edge DCT unified (all `Re s > 0`).
-/

import PF.Analytic.HankelUpperEdgeDCTProofReGeOne

namespace PrincipiaTractalis.Analytic

open Complex Filter Topology MeasureTheory Set

/-! ## DCT invocation for `Re s ≥ 1` -/

/-- **Upper-edge integral converges to `Γ(s)`** for `Re s ≥ 1`.

    Applies `tendsto_integral_filter_of_dominated_convergence` with the
    `(1 + t)^(Re s - 1) · exp(-t)` dominating function (suitable when
    the integrand has no singularity at `t = 0`).

    The ε-uniform bound requires `|ε| ≤ 1`. We get this eventually in
    `𝓝[>] 0` by restricting to `Ioo 0 1`, which is in `𝓝[>] 0` (using
    `Iio 1 ∈ 𝓝 0` intersected with `Ioi 0`). -/
theorem hankelUpperEdge_integral_tends_to_Gamma_of_re_ge_one
    {s : ℂ} (hs : 0 < s.re) (hs1 : 1 ≤ s.re) :
    Tendsto (fun ε : ℝ => ∫ t in Ioi (0 : ℝ), hankelUpperEdgeIntegrand s ε t)
            (𝓝[>] 0) (𝓝 (Complex.Gamma s)) := by
  rw [← integral_gammaPrincipalIntegrand_eq_Gamma hs]
  set bound : ℝ → ℝ := fun t =>
    Real.exp (|s.im| * Real.pi / 2) * (1 + t) ^ (s.re - 1) * Real.exp (-t)
  -- `Ioo 0 1 ∈ 𝓝[>] 0`: take open `U = Iio 1` containing 0; then `U ∩ Ioi 0 = Ioo 0 1`.
  have h_within : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := by
    apply mem_nhdsWithin.mpr
    refine ⟨Set.Iio 1, isOpen_Iio, by norm_num, ?_⟩
    intro x ⟨hx_lt, hx_pos⟩
    exact ⟨hx_pos, hx_lt⟩
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence bound
    (Filter.Eventually.of_forall (fun _ =>
      hankelUpperEdgeIntegrand_aestronglyMeasurable s _))
    ?_ ?_ ?_
  · -- ε-uniform bound: eventually for `ε ∈ Ioo 0 1`
    filter_upwards [h_within] with ε hε
    have hε_pos : 0 < ε := hε.1
    have hε_lt : ε < 1 := hε.2
    have h_abs : |ε| ≤ 1 := by rw [abs_of_pos hε_pos]; linarith
    refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    exact hankelUpperEdgeIntegrand_norm_le_of_re_ge_one hs1 t ε
      (Set.mem_Ioi.mp ht) h_abs
  · -- Integrability of bound: pull constant out
    have h := (one_plus_t_rpow_mul_exp_integrable hs hs1).const_mul
                (Real.exp (|s.im| * Real.pi / 2))
    refine h.congr ?_
    filter_upwards with t
    show Real.exp (|s.im| * Real.pi / 2) *
         ((1 + t) ^ (s.re - 1) * Real.exp (-t)) = bound t
    show Real.exp (|s.im| * Real.pi / 2) *
         ((1 + t) ^ (s.re - 1) * Real.exp (-t)) =
         Real.exp (|s.im| * Real.pi / 2) *
         (1 + t) ^ (s.re - 1) * Real.exp (-t)
    ring
  · -- Pointwise convergence
    refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    exact hankelUpperEdgeIntegrand_tendsto_pointwise_pos (Set.mem_Ioi.mp ht)

/-! ## Unified theorem for all `Re s > 0` -/

/-- **★ Unified upper-edge integral convergence**:

      `Tendsto (fun ε => ∫ t in Ioi 0, hankelUpperEdgeIntegrand s ε t)
              (𝓝[>] 0) (𝓝 (Γ(s)))`

    for **all** `Re s > 0`. Case-splits on `Re s ≤ 1` vs `1 ≤ Re s`,
    with the boundary case `Re s = 1` covered by either branch.

    This theorem unifies the previously-separate regimes:
    * `hankelUpperEdge_integral_tends_to_Gamma_of_re_le_one`  (Re s ≤ 1)
    * `hankelUpperEdge_integral_tends_to_Gamma_of_re_ge_one`  (Re s ≥ 1)
    into a single statement covering the entire half-plane `Re s > 0`. -/
theorem hankelUpperEdge_integral_tends_to_Gamma
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun ε : ℝ => ∫ t in Ioi (0 : ℝ), hankelUpperEdgeIntegrand s ε t)
            (𝓝[>] 0) (𝓝 (Complex.Gamma s)) := by
  rcases le_or_gt s.re 1 with h1 | h1
  · exact hankelUpperEdge_integral_tends_to_Gamma_of_re_le_one hs h1
  · exact hankelUpperEdge_integral_tends_to_Gamma_of_re_ge_one hs h1.le

/-! ## Boundary case `Re s = 1` -/

/-- **Re s = 1 boundary case** (direct corollary of the unified theorem). -/
theorem hankelUpperEdge_integral_tends_to_Gamma_of_re_eq_one
    {s : ℂ} (hs : s.re = 1) :
    Tendsto (fun ε : ℝ => ∫ t in Ioi (0 : ℝ), hankelUpperEdgeIntegrand s ε t)
            (𝓝[>] 0) (𝓝 (Complex.Gamma s)) := by
  apply hankelUpperEdge_integral_tends_to_Gamma
  rw [hs]; exact zero_lt_one

end PrincipiaTractalis.Analytic
