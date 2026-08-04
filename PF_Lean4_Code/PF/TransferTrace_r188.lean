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

/-! ### Stone 2 — the assembly: trace = fixed-point contour integral -/

/-- The rescaled diagonal integrand: `G m z = (z−c)⁻¹ · Σ_k w_k(z)·q_k(z)^m`
with `q_k = (φ_k z − c)/(z − c)`.  The basis scale `R` has already cancelled. -/
def diagIntegrand (c : ℂ) (K : ℕ) (w φ : Fin K → ℂ → ℂ) (m : ℕ) (z : ℂ) : ℂ :=
  (z - c)⁻¹ * ∑ k : Fin K, w k z * ((φ k z - c) / (z - c)) ^ m

theorem norm_diagIntegrand_le (hR₁ : 0 < R₁) (hτ0 : 0 ≤ τ) (hW : 0 ≤ W)
    (hw : ∀ k, ∀ z ∈ Metric.sphere c R₁, ‖w k z‖ ≤ W)
    (hφ : ∀ k, ∀ z ∈ Metric.sphere c R₁, φ k z ∈ Metric.closedBall c τ)
    (m : ℕ) {z : ℂ} (hz : z ∈ Metric.sphere c R₁) :
    ‖diagIntegrand c K w φ m z‖ ≤ R₁⁻¹ * ((K : ℝ) * W * (τ / R₁) ^ m) := by
  have hzc : ‖z - c‖ = R₁ := by rw [← dist_eq_norm]; exact hz
  rw [diagIntegrand, norm_mul, norm_inv, hzc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc ‖∑ k : Fin K, w k z * ((φ k z - c) / (z - c)) ^ m‖
      ≤ ∑ k : Fin K, ‖w k z * ((φ k z - c) / (z - c)) ^ m‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin K, W * (τ / R₁) ^ m := by
        apply Finset.sum_le_sum
        intro k _
        rw [norm_mul, norm_pow, norm_div, hzc]
        have hnum : ‖φ k z - c‖ ≤ τ := by
          have := hφ k z hz
          rwa [Metric.mem_closedBall, dist_eq_norm] at this
        apply mul_le_mul (hw k z hz)
        · apply pow_le_pow_left₀ (by positivity)
          exact div_le_div_of_nonneg_right hnum hR₁.le
        · positivity
        · exact hW
    _ = (K : ℝ) * W * (τ / R₁) ^ m := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- Step A: each diagonal entry is the Cauchy contour of `diagIntegrand` —
the basis scale `R` cancels exactly. -/
theorem diag_eq_contour (hR : 0 < R) (hRR : R < R₁) (m : ℕ) :
    transferMatrix c R R₁ K w φ m m
      = (2 * ↑π * Complex.I)⁻¹ •
          ∮ z in C(c, R₁), diagIntegrand c K w φ m z := by
  have hR₁ : (0 : ℝ) < R₁ := hR.trans hRR
  have hRC : (R : ℂ) ≠ 0 := by
    simpa using ne_of_gt (show (0:ℝ) < R from hR)
  rw [transferMatrix, cauchyPowerSeries_apply, smul_comm]
  congr 1
  rw [← circleIntegral.integral_smul]
  apply circleIntegral.integral_congr hR₁.le
  intro z hz
  have hzc : ‖z - c‖ = R₁ := by
    rw [← dist_eq_norm]
    simpa [abs_of_pos hR₁] using hz
  have hzc0 : z - c ≠ 0 := by
    intro h; rw [h, norm_zero] at hzc; linarith
  simp only [diagIntegrand, smul_eq_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  field_simp
  rw [show (↑R : ℂ) ^ m * (1 / (z - c)) ^ m * w k z * ((φ k z - c) / ↑R) ^ m
        = w k z * ((↑R * (1 / (z - c)) * ((φ k z - c) / ↑R)) ^ m) from by
      rw [mul_pow, mul_pow]; ring]
  congr 2
  rw [mul_one_div, div_mul_div_comm, mul_comm (z - c) (↑R : ℂ),
    mul_div_mul_left _ _ hRC]

/-- Step B: the pointwise resolvent identification on the circle. -/
theorem tsum_diagIntegrand (hR₁ : 0 < R₁) (hτ0 : 0 ≤ τ) (hτR₁ : τ < R₁)
    (hw : ∀ k, ∀ z ∈ Metric.sphere c R₁, ‖w k z‖ ≤ W)
    (hφ : ∀ k, ∀ z ∈ Metric.sphere c R₁, φ k z ∈ Metric.closedBall c τ)
    {z : ℂ} (hz : z ∈ Metric.sphere c R₁) :
    ∑' m : ℕ, diagIntegrand c K w φ m z
      = ∑ k : Fin K, w k z / (z - φ k z) := by
  have hzc : ‖z - c‖ = R₁ := by rw [← dist_eq_norm]; exact hz
  have hzc0 : z - c ≠ 0 := by
    intro h; rw [h, norm_zero] at hzc; linarith
  have hq : ∀ k : Fin K, ‖(φ k z - c) / (z - c)‖ < 1 := by
    intro k
    rw [norm_div, hzc, div_lt_one hR₁]
    have := hφ k z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at this
    linarith
  have hsummand : ∀ k : Fin K,
      Summable fun m : ℕ => w k z * ((φ k z - c) / (z - c)) ^ m :=
    fun k => (summable_geometric_of_norm_lt_one (hq k)).mul_left _
  calc ∑' m : ℕ, diagIntegrand c K w φ m z
      = (z - c)⁻¹ * ∑' m : ℕ, ∑ k : Fin K,
          w k z * ((φ k z - c) / (z - c)) ^ m := by
        rw [← tsum_mul_left]
        exact tsum_congr fun m => rfl
    _ = (z - c)⁻¹ * ∑ k : Fin K, ∑' m : ℕ,
          w k z * ((φ k z - c) / (z - c)) ^ m := by
        congr 1
        exact Summable.tsum_finsetSum (fun k _ => hsummand k)
    _ = (z - c)⁻¹ * ∑ k : Fin K, w k z * ((z - c) / (z - φ k z)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        rw [tsum_mul_left, tsum_ratio_pow hR₁ hτ0 hτR₁ hφ k hz]
    _ = ∑ k : Fin K, w k z / (z - φ k z) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        have hne := sub_apply_ne_zero hτR₁ hφ k hz
        field_simp

/-- **THE TRACE FORMULA, stone 2**: the trace of the transfer matrix is the
fixed-point contour integral.  Scale-free, no analyticity assumed. -/
theorem trace_eq_contour (hR : 0 < R) (hRR : R < R₁)
    (hτ0 : 0 ≤ τ) (hτR : τ < R) (hW : 0 ≤ W)
    (hwc : ∀ k, ContinuousOn (w k) (Metric.sphere c R₁))
    (hφc : ∀ k, ContinuousOn (φ k) (Metric.sphere c R₁))
    (hw : ∀ k, ∀ z ∈ Metric.sphere c R₁, ‖w k z‖ ≤ W)
    (hφ : ∀ k, ∀ z ∈ Metric.sphere c R₁, φ k z ∈ Metric.closedBall c τ) :
    (∑' m : ℕ, transferMatrix c R R₁ K w φ m m)
      = (2 * ↑π * Complex.I)⁻¹ •
          ∮ z in C(c, R₁), ∑ k : Fin K, w k z / (z - φ k z) := by
  have hR₁ : (0 : ℝ) < R₁ := hR.trans hRR
  have hτR₁ : τ < R₁ := hτR.trans hRR
  have hmem : ∀ θ : ℝ, circleMap c R₁ θ ∈ Metric.sphere c R₁ :=
    fun θ => circleMap_mem_sphere c hR₁.le θ
  -- continuity of the parametrized diagonal integrands
  have hGcont : ∀ m : ℕ, Continuous fun θ : ℝ =>
      deriv (circleMap c R₁) θ • diagIntegrand c K w φ m (circleMap c R₁ θ) := by
    intro m
    apply Continuous.smul
    · exact ((continuous_circleMap 0 R₁).mul continuous_const).congr
        fun θ => (deriv_circleMap c R₁ θ).symm
    · apply Continuous.mul
      · apply Continuous.inv₀
        · exact (continuous_circleMap c R₁).sub continuous_const
        · intro θ
          have := hmem θ
          rw [Metric.mem_sphere, dist_eq_norm] at this
          intro h0
          rw [sub_eq_zero] at h0
          rw [h0, sub_self, norm_zero] at this
          linarith
      · apply continuous_finset_sum
        intro k _
        apply Continuous.mul
        · exact (hwc k).comp_continuous (continuous_circleMap c R₁) hmem
        · apply Continuous.pow
          apply Continuous.div
          · exact ((hφc k).comp_continuous (continuous_circleMap c R₁) hmem).sub
              continuous_const
          · exact (continuous_circleMap c R₁).sub continuous_const
          · intro θ
            have := hmem θ
            rw [Metric.mem_sphere, dist_eq_norm] at this
            intro h0
            rw [sub_eq_zero] at h0
            rw [h0, sub_self, norm_zero] at this
            linarith
  -- the summable uniform bound
  have hτR₁' : τ / R₁ < 1 := by rw [div_lt_one hR₁]; linarith
  have hbsum : Summable fun m : ℕ =>
      R₁ * (R₁⁻¹ * ((K : ℝ) * W * (τ / R₁) ^ m)) := by
    apply Summable.mul_left
    apply Summable.mul_left
    exact (summable_geometric_of_lt_one (by positivity) hτR₁').mul_left _
  have hub : ∀ (m : ℕ) (θ : ℝ),
      ‖deriv (circleMap c R₁) θ • diagIntegrand c K w φ m (circleMap c R₁ θ)‖
        ≤ R₁ * (R₁⁻¹ * ((K : ℝ) * W * (τ / R₁) ^ m)) := by
    intro m θ
    rw [norm_smul]
    have hd : ‖deriv (circleMap c R₁) θ‖ = R₁ := by
      simp [deriv_circleMap, abs_of_pos hR₁]
    rw [hd]
    exact mul_le_mul_of_nonneg_left
      (norm_diagIntegrand_le hR₁ hτ0 hW hw hφ m (hmem θ)) hR₁.le
  -- assemble
  calc (∑' m : ℕ, transferMatrix c R R₁ K w φ m m)
      = ∑' m : ℕ, (2 * ↑π * Complex.I)⁻¹ •
          ∮ z in C(c, R₁), diagIntegrand c K w φ m z := by
        congr 1; funext m; exact diag_eq_contour hR hRR m
    _ = (2 * ↑π * Complex.I)⁻¹ •
          ∑' m : ℕ, ∮ z in C(c, R₁), diagIntegrand c K w φ m z := by
        rw [tsum_const_smul'']
    _ = (2 * ↑π * Complex.I)⁻¹ •
          ∮ z in C(c, R₁), ∑ k : Fin K, w k z / (z - φ k z) := by
        congr 1
        -- unfold both circle integrals to interval integrals and interchange
        simp only [circleIntegral]
        rw [← intervalIntegral_tsum hGcont hbsum hub]
        apply intervalIntegral.integral_congr
        intro θ _
        dsimp only
        rw [tsum_const_smul'']
        congr 1
        exact tsum_diagIntegrand hR₁ hτ0 hτR₁ hw hφ (hmem θ)

end

end PrincipiaTractalis.HilbertSchmidtL2

#print axioms PrincipiaTractalis.HilbertSchmidtL2.sub_apply_ne_zero
#print axioms PrincipiaTractalis.HilbertSchmidtL2.tsum_ratio_pow
#print axioms PrincipiaTractalis.HilbertSchmidtL2.diag_summable
#print axioms PrincipiaTractalis.HilbertSchmidtL2.intervalIntegral_tsum
#print axioms PrincipiaTractalis.HilbertSchmidtL2.diag_eq_contour
#print axioms PrincipiaTractalis.HilbertSchmidtL2.tsum_diagIntegrand
#print axioms PrincipiaTractalis.HilbertSchmidtL2.trace_eq_contour
