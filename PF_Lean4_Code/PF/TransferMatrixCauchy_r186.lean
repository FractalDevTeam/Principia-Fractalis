/-
# PF.TransferMatrixCauchy_r186

★★★ 2026-08-03 — M3 STONE 4: THE CAUCHY BRIDGE ★★★

The last link of the M3 chain.  r185 proved: double-geometric entry decay
`‖A m n‖ ≤ C·r^m·ρ^n` implies Hilbert–Schmidt, hence a compact operator on ℓ²
(r183/r184).  This stone produces that decay for the **transfer-operator
coefficient matrix** of a weighted composition system, from its contraction
geometry alone:

  branches `φ k` mapping the circle `|z−c| = R₁` into the closed ball
  `|z−c| ≤ τ` with `τ < R < R₁`, weights `w k` bounded by `W` on that circle
    ⟹  the Cauchy coefficient matrix at basis scale `R` satisfies
        `‖A m n‖ ≤ (K·W)·(R/R₁)^m·(τ/R)^n`.

**No analyticity is assumed anywhere**: mathlib's
`norm_cauchyPowerSeries_le` is a pure integral estimate, so continuity on
the circle suffices.  The row decay `(R/R₁)^m` is the Cauchy decay of
coefficients extracted on the larger circle; the column decay `(τ/R)^n` is
the contraction of the branches measured in the basis scale.

This is exactly the geometry of the Mayer/Möbius systems of M1/M2: for the
depth-3 system, `c = 1`, `R = 3/2`, the branches `1/(x+k)` map the circle
`|z−1| = R₁` (any `R₁ < 2`) into `|z−1| ≤ τ` with `τ < 3/2`, and the weights
`(z+k)^{-2s}` are bounded on the circle.  The instantiation with those
concrete branch bounds is the H²-dictionary arc; nothing here depends on it.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-08-03.
-/
import PF.HilbertSchmidtGeometric_r185
import Mathlib.MeasureTheory.Integral.CircleIntegral

set_option maxHeartbeats 800000

namespace PrincipiaTractalis.HilbertSchmidtL2

open scoped Real
open intervalIntegral

noncomputable section

/-- The transfer-operator coefficient matrix: entry `(m, n)` is the `m`-th
Cauchy coefficient (extracted on the circle of radius `R₁` about `c`,
rescaled to basis scale `R`) of the image of the `n`-th basis element
`((z−c)/R)^n` under the weighted composition system. -/
def transferMatrix (c : ℂ) (R R₁ : ℝ) (K : ℕ) (w φ : Fin K → ℂ → ℂ) :
    ℕ → ℕ → ℂ := fun m n =>
  (R : ℂ) ^ m •
    (cauchyPowerSeries
      (fun z => ∑ k : Fin K, w k z * (((φ k z) - c) / (R : ℂ)) ^ n)
      c R₁ m (fun _ => 1))

variable {c : ℂ} {R R₁ τ W : ℝ} {K : ℕ} {w φ : Fin K → ℂ → ℂ}

/-- Pointwise bound for the image functions on the extraction circle. -/
theorem image_norm_le (hR : 0 < R) (hτ0 : 0 ≤ τ)
    (hw : ∀ k, ∀ z ∈ Metric.sphere c R₁, ‖w k z‖ ≤ W)
    (hφ : ∀ k, ∀ z ∈ Metric.sphere c R₁, φ k z ∈ Metric.closedBall c τ)
    (hW : 0 ≤ W) {z : ℂ} (hz : z ∈ Metric.sphere c R₁) (n : ℕ) :
    ‖∑ k : Fin K, w k z * (((φ k z) - c) / (R : ℂ)) ^ n‖
      ≤ (K : ℝ) * W * (τ / R) ^ n := by
  calc ‖∑ k : Fin K, w k z * (((φ k z) - c) / (R : ℂ)) ^ n‖
      ≤ ∑ k : Fin K, ‖w k z * (((φ k z) - c) / (R : ℂ)) ^ n‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _k : Fin K, W * (τ / R) ^ n := by
        apply Finset.sum_le_sum
        intro k _
        rw [norm_mul, norm_pow, norm_div]
        have hnum : ‖(φ k z) - c‖ ≤ τ := by
          have := hφ k z hz
          rwa [Metric.mem_closedBall, dist_eq_norm] at this
        have hden : ‖(R : ℂ)‖ = R := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
        rw [hden]
        apply mul_le_mul (hw k z hz)
        · apply pow_le_pow_left₀ (by positivity)
          exact div_le_div_of_nonneg_right hnum hR.le
        · positivity
        · exact hW
    _ = (K : ℝ) * W * (τ / R) ^ n := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        ring

/-- **The Cauchy bridge**: the transfer-operator coefficient matrix of a
weighted composition system whose branches contract the extraction circle
into a strictly smaller ball satisfies the double-geometric bound. -/
theorem geomBound_transferMatrix (hR : 0 < R) (hRR : R < R₁)
    (hτ0 : 0 ≤ τ) (hτR : τ < R) (hW : 0 ≤ W)
    (hwc : ∀ k, ContinuousOn (w k) (Metric.sphere c R₁))
    (hφc : ∀ k, ContinuousOn (φ k) (Metric.sphere c R₁))
    (hw : ∀ k, ∀ z ∈ Metric.sphere c R₁, ‖w k z‖ ≤ W)
    (hφ : ∀ k, ∀ z ∈ Metric.sphere c R₁, φ k z ∈ Metric.closedBall c τ) :
    GeomBound (transferMatrix c R R₁ K w φ) ((K : ℝ) * W) (R / R₁) (τ / R) := by
  intro m n
  have hR₁ : (0 : ℝ) < R₁ := hR.trans hRR
  set F : ℂ → ℂ :=
    fun z => ∑ k : Fin K, w k z * (((φ k z) - c) / (R : ℂ)) ^ n with hF
  -- Step 1: |entry| ≤ R^m · ‖p m‖
  have h1 : ‖transferMatrix c R R₁ K w φ m n‖
      ≤ R ^ m * ‖cauchyPowerSeries F c R₁ m‖ := by
    rw [transferMatrix]
    rw [norm_smul]
    have hnR : ‖(R : ℂ) ^ m‖ = R ^ m := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    rw [hnR]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc ‖cauchyPowerSeries F c R₁ m (fun _ => 1)‖
        ≤ ‖cauchyPowerSeries F c R₁ m‖ * ∏ _i : Fin m, ‖(1 : ℂ)‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖cauchyPowerSeries F c R₁ m‖ := by simp
  -- Step 2: mathlib's integral estimate for the Cauchy coefficients
  have h2 : ‖cauchyPowerSeries F c R₁ m‖
      ≤ ((2 * π)⁻¹ * ∫ θ : ℝ in (0 : ℝ)..2 * π, ‖F (circleMap c R₁ θ)‖)
        * |R₁|⁻¹ ^ m :=
    norm_cauchyPowerSeries_le F c R₁ m
  -- Step 3: bound the circle integral by the sup bound
  have hFcont : Continuous fun θ : ℝ => ‖F (circleMap c R₁ θ)‖ := by
    apply Continuous.norm
    have hmem : ∀ θ : ℝ, circleMap c R₁ θ ∈ Metric.sphere c R₁ :=
      fun θ => circleMap_mem_sphere c hR₁.le θ
    apply continuous_finset_sum
    intro k _
    apply Continuous.mul
    · exact (hwc k).comp_continuous (continuous_circleMap c R₁) hmem
    · apply Continuous.pow
      apply Continuous.div_const
      apply Continuous.sub _ continuous_const
      exact (hφc k).comp_continuous (continuous_circleMap c R₁) hmem
  have h3 : (∫ θ : ℝ in (0 : ℝ)..2 * π, ‖F (circleMap c R₁ θ)‖)
      ≤ 2 * π * ((K : ℝ) * W * (τ / R) ^ n) := by
    have hle : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
        ‖F (circleMap c R₁ θ)‖ ≤ (K : ℝ) * W * (τ / R) ^ n := by
      intro θ _
      exact image_norm_le hR hτ0 hw hφ hW
        (circleMap_mem_sphere c hR₁.le θ) n
    calc (∫ θ : ℝ in (0 : ℝ)..2 * π, ‖F (circleMap c R₁ θ)‖)
        ≤ ∫ _θ : ℝ in (0 : ℝ)..2 * π, (K : ℝ) * W * (τ / R) ^ n := by
          apply intervalIntegral.integral_mono_on Real.two_pi_pos.le
            (hFcont.intervalIntegrable _ _) (intervalIntegrable_const)
          exact hle
      _ = 2 * π * ((K : ℝ) * W * (τ / R) ^ n) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          ring
  -- Assemble
  have hpi : (0 : ℝ) < 2 * π := Real.two_pi_pos
  have hint_nonneg : (0 : ℝ) ≤ ∫ θ : ℝ in (0 : ℝ)..2 * π, ‖F (circleMap c R₁ θ)‖ :=
    intervalIntegral.integral_nonneg Real.two_pi_pos.le (fun θ _ => norm_nonneg _)
  have hR₁abs : |R₁|⁻¹ = R₁⁻¹ := by rw [abs_of_pos hR₁]
  calc ‖transferMatrix c R R₁ K w φ m n‖
      ≤ R ^ m * ‖cauchyPowerSeries F c R₁ m‖ := h1
    _ ≤ R ^ m * (((2 * π)⁻¹
          * ∫ θ : ℝ in (0 : ℝ)..2 * π, ‖F (circleMap c R₁ θ)‖) * |R₁|⁻¹ ^ m) := by
        apply mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ R ^ m * (((2 * π)⁻¹ * (2 * π * ((K : ℝ) * W * (τ / R) ^ n)))
          * |R₁|⁻¹ ^ m) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (K : ℝ) * W * (R / R₁) ^ m * (τ / R) ^ n := by
        rw [hR₁abs]
        field_simp
        ring

/-- **The transfer-operator matrix is Hilbert–Schmidt** — from the contraction
geometry alone. -/
theorem hsSummable_transferMatrix (hR : 0 < R) (hRR : R < R₁)
    (hτ0 : 0 ≤ τ) (hτR : τ < R) (hW : 0 ≤ W)
    (hwc : ∀ k, ContinuousOn (w k) (Metric.sphere c R₁))
    (hφc : ∀ k, ContinuousOn (φ k) (Metric.sphere c R₁))
    (hw : ∀ k, ∀ z ∈ Metric.sphere c R₁, ‖w k z‖ ≤ W)
    (hφ : ∀ k, ∀ z ∈ Metric.sphere c R₁, φ k z ∈ Metric.closedBall c τ) :
    HSSummable (transferMatrix c R R₁ K w φ) := by
  have hR₁ : (0 : ℝ) < R₁ := hR.trans hRR
  exact hsSummable_of_geometric
    (geomBound_transferMatrix hR hRR hτ0 hτR hW hwc hφc hw hφ)
    (by positivity)
    (by positivity)
    ((div_lt_one hR₁).mpr hRR)
    (by positivity)
    ((div_lt_one hR).mpr hτR)

/-- **THE M3 THEOREM: the transfer operator of a contracting weighted
composition system is a compact operator on ℓ²** — kernel-checked, from the
geometry alone.  This is the operator class whose determinants reproduced the
PSL(2,ℤ) Maass spectrum, the first Riemann zero, and the Γ₀(3) spectrum in
M1/M2. -/
theorem isCompactOperator_transferMatrix (hR : 0 < R) (hRR : R < R₁)
    (hτ0 : 0 ≤ τ) (hτR : τ < R) (hW : 0 ≤ W)
    (hwc : ∀ k, ContinuousOn (w k) (Metric.sphere c R₁))
    (hφc : ∀ k, ContinuousOn (φ k) (Metric.sphere c R₁))
    (hw : ∀ k, ∀ z ∈ Metric.sphere c R₁, ‖w k z‖ ≤ W)
    (hφ : ∀ k, ∀ z ∈ Metric.sphere c R₁, φ k z ∈ Metric.closedBall c τ) :
    IsCompactOperator
      (hsOperator (hsSummable_transferMatrix hR hRR hτ0 hτR hW hwc hφc hw hφ)) :=
  isCompactOperator_hsOperator _

end

end PrincipiaTractalis.HilbertSchmidtL2

#print axioms PrincipiaTractalis.HilbertSchmidtL2.geomBound_transferMatrix
#print axioms PrincipiaTractalis.HilbertSchmidtL2.hsSummable_transferMatrix
#print axioms PrincipiaTractalis.HilbertSchmidtL2.isCompactOperator_transferMatrix
