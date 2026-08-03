/-
# PF.TransferTrace_r188

★★★ 2026-08-03 — THE TRACE OF THE TRANSFER MATRIX IS A FIXED-POINT CONTOUR ★★★

Stone 1 of the Lefschetz arc.  The cross-front measurement of
`codex/BSD_TRACE_RANK_2026-08-03.md` — rank read from the trace of the
corrected ch24 operator — rests on the classical fixed-point trace formula.
This stone proves its first half in the kernel, for the r186 matrix:

  `Σ'_m (transferMatrix c R R₁ K w φ) m m
     = (2πi)⁻¹ · ∮_{|z−c|=R₁} Σ_k w_k(z) / (z − φ_k(z)) dz`

**Mechanism.**  The diagonal entry is a Cauchy integral of
`Σ_k w_k(z)·q_k(z)^m` with `q_k = (φ_k z − c)/(z − c)`; on the circle
`|q_k| ≤ τ/R₁ < 1`, so summing the diagonal sums a geometric series under the
integral, and `(z−c)⁻¹·(1−q_k)⁻¹ = (z − φ_k z)⁻¹`.  The basis scale `R`
cancels exactly — the trace is scale-free, as it must be.  The denominator
never vanishes: `‖z − φ_k z‖ ≥ R₁ − τ > 0` directly from the contraction.

Still ahead (stone 2): evaluating the contour by residues —
`Σ_k w_k(x*_k)/(1 − φ'_k(x*_k))` — which needs analyticity of the `w_k, φ_k`
on the disc and is NOT assumed here; this stone, like r186, needs only
continuity on the circle.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-08-03.
-/
import PF.TransferMatrixCauchy_r186

set_option maxHeartbeats 1000000

namespace PrincipiaTractalis.HilbertSchmidtL2

open scoped Real
open intervalIntegral MeasureTheory

noncomputable section

variable {c : ℂ} {R R₁ τ W : ℝ} {K : ℕ} {w φ : Fin K → ℂ → ℂ}

/-! ### The denominator never vanishes on the circle -/

theorem sub_apply_ne_zero (hτR₁ : τ < R₁)
    (hφ : ∀ k, ∀ z ∈ Metric.sphere c R₁, φ k z ∈ Metric.closedBall c τ)
    (k : Fin K) {z : ℂ} (hz : z ∈ Metric.sphere c R₁) :
    z - φ k z ≠ 0 := by
  have h1 : ‖z - c‖ = R₁ := by
    rw [← dist_eq_norm]; exact hz
  have h2 : ‖φ k z - c‖ ≤ τ := by
    have := hφ k z hz
    rwa [Metric.mem_closedBall, dist_eq_norm] at this
  have h3 : R₁ - τ ≤ ‖z - φ k z‖ := by
    calc R₁ - τ ≤ ‖z - c‖ - ‖φ k z - c‖ := by rw [h1]; linarith
      _ ≤ ‖(z - c) - (φ k z - c)‖ := norm_sub_norm_le _ _
      _ = ‖z - φ k z‖ := by ring_nf
  intro h0
  rw [h0, norm_zero] at h3
  linarith

/-! ### The geometric resolvent identity, pointwise on the circle -/

theorem tsum_ratio_pow (hR₁ : 0 < R₁) (hτ0 : 0 ≤ τ) (hτR₁ : τ < R₁)
    (hφ : ∀ k, ∀ z ∈ Metric.sphere c R₁, φ k z ∈ Metric.closedBall c τ)
    (k : Fin K) {z : ℂ} (hz : z ∈ Metric.sphere c R₁) :
    ∑' m : ℕ, ((φ k z - c) / (z - c)) ^ m = (z - c) / (z - φ k z) := by
  have hzc : ‖z - c‖ = R₁ := by rw [← dist_eq_norm]; exact hz
  have hzc0 : z - c ≠ 0 := by
    intro h; rw [h, norm_zero] at hzc; linarith
  have hq : ‖(φ k z - c) / (z - c)‖ < 1 := by
    rw [norm_div, hzc]
    have h2 : ‖φ k z - c‖ ≤ τ := by
      have := hφ k z hz
      rwa [Metric.mem_closedBall, dist_eq_norm] at this
    rw [div_lt_one hR₁]
    linarith
  rw [tsum_geometric_of_norm_lt_one hq]
  have hden : (1 : ℂ) - (φ k z - c) / (z - c) = (z - φ k z) / (z - c) := by
    field_simp
    ring
  rw [hden, inv_div]

/-! ### Summability of the diagonal -/

theorem diag_summable (hR : 0 < R) (hRR : R < R₁)
    (hτ0 : 0 ≤ τ) (hτR : τ < R) (hW : 0 ≤ W)
    (hwc : ∀ k, ContinuousOn (w k) (Metric.sphere c R₁))
    (hφc : ∀ k, ContinuousOn (φ k) (Metric.sphere c R₁))
    (hw : ∀ k, ∀ z ∈ Metric.sphere c R₁, ‖w k z‖ ≤ W)
    (hφ : ∀ k, ∀ z ∈ Metric.sphere c R₁, φ k z ∈ Metric.closedBall c τ) :
    Summable fun m => transferMatrix c R R₁ K w φ m m := by
  have hR₁ : (0 : ℝ) < R₁ := hR.trans hRR
  have hgb := geomBound_transferMatrix hR hRR hτ0 hτR hW hwc hφc hw hφ
  apply Summable.of_norm
  have hbound : ∀ m, ‖transferMatrix c R R₁ K w φ m m‖
      ≤ (K : ℝ) * W * (τ / R₁) ^ m := by
    intro m
    calc ‖transferMatrix c R R₁ K w φ m m‖
        ≤ (K : ℝ) * W * (R / R₁) ^ m * (τ / R) ^ m := hgb m m
      _ = (K : ℝ) * W * (τ / R₁) ^ m := by
          rw [mul_assoc, ← mul_pow]
          congr 2
          field_simp
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) hbound ?_
  have hτR₁' : τ / R₁ < 1 := by
    rw [div_lt_one hR₁]; linarith
  exact ((summable_geometric_of_lt_one (by positivity) hτR₁').mul_left _)

/-! ### Interval-integral / tsum interchange (helper) -/

/-- Interchange of a sum and an interval integral, for continuous summands
with a summable uniform bound.  Assembled from `MeasureTheory.integral_tsum`;
mathlib has no interval-integral version. -/
theorem intervalIntegral_tsum {u : ℕ → ℝ → ℂ} {b : ℕ → ℝ}
    (hu : ∀ m, Continuous (u m)) (hb : Summable b)
    (hub : ∀ m θ, ‖u m θ‖ ≤ b m) :
    (∫ θ in (0 : ℝ)..2 * π, ∑' m, u m θ)
      = ∑' m, ∫ θ in (0 : ℝ)..2 * π, u m θ := by
  have h2π : (0 : ℝ) ≤ 2 * π := Real.two_pi_pos.le
  rw [intervalIntegral.integral_of_le h2π]
  have hswap : (∫ θ in Set.Ioc (0 : ℝ) (2 * π), ∑' m, u m θ)
      = ∑' m, ∫ θ in Set.Ioc (0 : ℝ) (2 * π), u m θ := by
    rw [← MeasureTheory.integral_tsum]
    · exact fun m => ((hu m).aestronglyMeasurable).restrict
    · -- Σ' of the lintegrals is finite: each ≤ 2π · b m
      have hfin : ∀ m, (∫⁻ θ in Set.Ioc (0 : ℝ) (2 * π), ‖u m θ‖ₑ)
          ≤ ENNReal.ofReal (b m) * ENNReal.ofReal (2 * π) := by
        intro m
        calc (∫⁻ θ in Set.Ioc (0 : ℝ) (2 * π), ‖u m θ‖ₑ)
            ≤ ∫⁻ _θ in Set.Ioc (0 : ℝ) (2 * π), ENNReal.ofReal (b m) := by
              apply MeasureTheory.lintegral_mono
              intro θ
              simp only [← ofReal_norm_eq_enorm]
              exact ENNReal.ofReal_le_ofReal (hub m θ)
          _ = ENNReal.ofReal (b m) * ENNReal.ofReal (2 * π) := by
              rw [MeasureTheory.lintegral_const, MeasureTheory.Measure.restrict_apply
                MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc]
              congr 1
              rw [ENNReal.ofReal_eq_ofReal_iff (by linarith) h2π]
              ring
      apply ne_of_lt
      calc (∑' m, ∫⁻ θ in Set.Ioc (0 : ℝ) (2 * π), ‖u m θ‖ₑ)
          ≤ ∑' m, ENNReal.ofReal (b m) * ENNReal.ofReal (2 * π) :=
            ENNReal.tsum_le_tsum hfin
        _ = (∑' m, ENNReal.ofReal (b m)) * ENNReal.ofReal (2 * π) :=
            ENNReal.tsum_mul_right
        _ < ⊤ := by
            apply ENNReal.mul_lt_top _ ENNReal.ofReal_lt_top
            have hb0 : ∀ m, 0 ≤ b m := fun m => (norm_nonneg _).trans (hub m 0)
            rw [← ENNReal.ofReal_tsum_of_nonneg hb0 hb]
            exact ENNReal.ofReal_lt_top
  rw [hswap]
  congr 1
  funext m
  rw [intervalIntegral.integral_of_le h2π]

end

end PrincipiaTractalis.HilbertSchmidtL2

#print axioms PrincipiaTractalis.HilbertSchmidtL2.sub_apply_ne_zero
#print axioms PrincipiaTractalis.HilbertSchmidtL2.tsum_ratio_pow
#print axioms PrincipiaTractalis.HilbertSchmidtL2.diag_summable
#print axioms PrincipiaTractalis.HilbertSchmidtL2.intervalIntegral_tsum
