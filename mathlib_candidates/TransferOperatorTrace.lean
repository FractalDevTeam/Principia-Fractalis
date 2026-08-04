/-
Copyright (c) 2026 Pablo Cohen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Cohen
-/
import TransferOperatorCompact
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The holomorphic Lefschetz trace formula for transfer operators

The trace of the Cauchy coefficient matrix of a weighted composition
(transfer) operator whose branches contract the extraction circle is a
fixed-point contour integral, and — under holomorphy inside the disc — a
finite sum of fixed-point residues:

* `HilbertSchmidt.trace_eq_contour` :
  `∑' m, A m m = (2πi)⁻¹ • ∮_{|z-c|=R₁} ∑ k, w k z / (z - φ k z)`.
  Needs only continuity on the circle and the contraction geometry
  `0 ≤ τ < R < R₁`; the basis scale `R` cancels exactly.

* `HilbertSchmidt.trace_eq_residues` :
  `∑' m, A m m = ∑ k, w k (x k) / (1 - deriv (φ k) (x k))`,
  given `DiffContOnCl` of weights and branches and the simple-zero
  factorization `z - φ k z = (z - x k) * g k z` with `g k` holomorphic and
  nonvanishing on the closed disc.

Auxiliary results of independent interest:

* `HilbertSchmidt.intervalIntegral_tsum` — dominated interchange of `tsum`
  with an interval integral under a summable uniform bound;
* `HilbertSchmidt.contour_eq_residue_single` — the one-branch residue
  evaluation via the Cauchy integral formula;
* `HilbertSchmidt.cofactor_eq_one_sub_deriv` — `g x = 1 - φ' x` at the
  fixed point.

This is the trace half of the Ruelle/Mayer transfer-operator program
(Mayer, Bull. AMS 25 (1991)); the compactness half is
`TransferOperatorCompact`.
-/

set_option maxHeartbeats 1600000

namespace HilbertSchmidt


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

/-! ## Residue evaluation -/


open Complex Metric Real
open scoped Real

noncomputable section

variable {c : ℂ} {R R₁ τ W : ℝ} {K : ℕ}

/-! ### The factorization interface -/

/-- The factorization `z − φ z = (z − x)·g z` forces `x` to be a fixed point
of `φ`. -/
theorem fixedPoint_of_factor {x : ℂ} {φ g : ℂ → ℂ}
    (hx : x ∈ Metric.ball c R₁)
    (hfactor : ∀ z ∈ Metric.closedBall c R₁, z - φ z = (z - x) * g z) :
    φ x = x := by
  have h := hfactor x (Metric.ball_subset_closedBall hx)
  rw [sub_self, zero_mul, sub_eq_zero] at h
  exact h.symm

/-! ### One branch: the residue at the fixed point -/

/-- **Single-branch residue evaluation**: if `w` and the cofactor `g` are
holomorphic on the disc and continuous up to the boundary, `g` nonvanishing,
then the contour of `w/(z−φ)` picks up exactly the residue `w(x)/g(x)` at the
(unique, simple) zero `x` of `z − φ z`. -/
theorem contour_eq_residue_single (hR₁ : 0 < R₁) {x : ℂ}
    (hx : x ∈ Metric.ball c R₁) {w φ g : ℂ → ℂ}
    (hfactor : ∀ z ∈ Metric.closedBall c R₁, z - φ z = (z - x) * g z)
    (hwd : DiffContOnCl ℂ w (Metric.ball c R₁))
    (hgd : DiffContOnCl ℂ g (Metric.ball c R₁))
    (hg0 : ∀ z ∈ Metric.closedBall c R₁, g z ≠ 0) :
    (2 * ↑π * Complex.I)⁻¹ • (∮ z in C(c, R₁), w z / (z - φ z))
      = w x / g x := by
  -- the Cauchy-formula integrand
  have hcont : ContinuousOn (fun z => w z * (g z)⁻¹) (Metric.closedBall c R₁) :=
    hwd.continuousOn_ball.mul (hgd.continuousOn_ball.inv₀ hg0)
  have hdiff : ∀ z ∈ Metric.ball c R₁ \ (∅ : Set ℂ),
      DifferentiableAt ℂ (fun z => w z * (g z)⁻¹) z := by
    intro z hz
    have hz' : z ∈ Metric.ball c R₁ := hz.1
    have hd : DifferentiableOn ℂ (fun z => w z * (g z)⁻¹) (Metric.ball c R₁) :=
      hwd.differentiableOn.mul (hgd.differentiableOn.inv
        fun y hy => hg0 y (Metric.ball_subset_closedBall hy))
    exact hd.differentiableAt (Metric.isOpen_ball.mem_nhds hz')
  -- rewrite the integrand via the factorization
  have hcong : (∮ z in C(c, R₁), w z / (z - φ z))
      = ∮ z in C(c, R₁), (z - x)⁻¹ • (w z * (g z)⁻¹) := by
    apply circleIntegral.integral_congr hR₁.le
    intro z hz
    have hz' : z ∈ Metric.sphere c R₁ := by
      simpa [abs_of_pos hR₁] using hz
    dsimp only
    rw [hfactor z (Metric.sphere_subset_closedBall hz'), smul_eq_mul,
      div_eq_mul_inv, mul_inv]
    ring
  rw [hcong,
    Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      Set.countable_empty hx hcont hdiff, div_eq_mul_inv]

/-- **The cofactor at the fixed point is `1 − φ'(x)`**: differentiate the
factorization at `x`. -/
theorem cofactor_eq_one_sub_deriv {x : ℂ} (hx : x ∈ Metric.ball c R₁)
    {φ g : ℂ → ℂ}
    (hfactor : ∀ z ∈ Metric.closedBall c R₁, z - φ z = (z - x) * g z)
    (hφd : DifferentiableAt ℂ φ x)
    (hgd : DiffContOnCl ℂ g (Metric.ball c R₁)) :
    g x = 1 - deriv φ x := by
  have hgx : DifferentiableAt ℂ g x :=
    hgd.differentiableOn.differentiableAt (Metric.isOpen_ball.mem_nhds hx)
  -- left side: d/dz (z − φ z) at x
  have hL : HasDerivAt (fun z => z - φ z) (1 - deriv φ x) x :=
    (hasDerivAt_id x).sub hφd.hasDerivAt
  -- right side: d/dz ((z − x)·g z) at x is g x
  have hRt : HasDerivAt (fun z => (z - x) * g z) (g x) x := by
    have h1 : HasDerivAt (fun z => z - x) 1 x := (hasDerivAt_id x).sub_const x
    simpa using h1.mul hgx.hasDerivAt
  -- the two functions agree near x, so the derivatives agree
  have heq : (fun z => (z - x) * g z) =ᶠ[nhds x] fun z => z - φ z := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with z hz
    exact (hfactor z (Metric.ball_subset_closedBall hz)).symm
  have hL' : HasDerivAt (fun z => (z - x) * g z) (1 - deriv φ x) x :=
    hL.congr_of_eventuallyEq heq
  exact hRt.unique hL'

/-! ### The trace formula -/

/-- **THE HOLOMORPHIC LEFSCHETZ TRACE FORMULA** for the transfer matrix:
under the r186 contraction geometry plus holomorphy of the weights and
branches inside the disc, with each branch's simple-zero factorization,

`Σ'_m A[m,m] = Σ_k w_k(x_k) / (1 − φ_k'(x_k))`.

The trace of the transfer operator is the sum of fixed-point residues. -/
theorem trace_eq_residues (hR : 0 < R) (hRR : R < R₁)
    (hτ0 : 0 ≤ τ) (hτR : τ < R) (hW : 0 ≤ W) {w φ : Fin K → ℂ → ℂ}
    (hw : ∀ k, ∀ z ∈ Metric.sphere c R₁, ‖w k z‖ ≤ W)
    (hφ : ∀ k, ∀ z ∈ Metric.sphere c R₁, φ k z ∈ Metric.closedBall c τ)
    {x : Fin K → ℂ} (hx : ∀ k, x k ∈ Metric.ball c R₁)
    {g : Fin K → ℂ → ℂ}
    (hfactor : ∀ k, ∀ z ∈ Metric.closedBall c R₁,
      z - φ k z = (z - x k) * g k z)
    (hwd : ∀ k, DiffContOnCl ℂ (w k) (Metric.ball c R₁))
    (hφd : ∀ k, DiffContOnCl ℂ (φ k) (Metric.ball c R₁))
    (hgd : ∀ k, DiffContOnCl ℂ (g k) (Metric.ball c R₁))
    (hg0 : ∀ k, ∀ z ∈ Metric.closedBall c R₁, g k z ≠ 0) :
    (∑' m : ℕ, transferMatrix c R R₁ K w φ m m)
      = ∑ k : Fin K, w k (x k) / (1 - deriv (φ k) (x k)) := by
  have hR₁ : (0 : ℝ) < R₁ := hR.trans hRR
  have hτR₁ : τ < R₁ := hτR.trans hRR
  have hmem : ∀ θ : ℝ, circleMap c R₁ θ ∈ Metric.sphere c R₁ :=
    fun θ => circleMap_mem_sphere c hR₁.le θ
  have hwc : ∀ k, ContinuousOn (w k) (Metric.sphere c R₁) :=
    fun k => (hwd k).continuousOn_ball.mono Metric.sphere_subset_closedBall
  have hφc : ∀ k, ContinuousOn (φ k) (Metric.sphere c R₁) :=
    fun k => (hφd k).continuousOn_ball.mono Metric.sphere_subset_closedBall
  rw [trace_eq_contour hR hRR hτ0 hτR hW hwc hφc hw hφ]
  -- split the contour over the finite branch sum
  have hsplit : (∮ z in C(c, R₁), ∑ k : Fin K, w k z / (z - φ k z))
      = ∑ k : Fin K, ∮ z in C(c, R₁), w k z / (z - φ k z) := by
    simp only [circleIntegral]
    rw [← intervalIntegral.integral_finset_sum]
    · apply intervalIntegral.integral_congr
      intro θ _
      dsimp only
      rw [Finset.smul_sum]
    · intro k _
      apply Continuous.intervalIntegrable
      apply Continuous.smul
      · exact ((continuous_circleMap 0 R₁).mul continuous_const).congr
          fun θ => (deriv_circleMap c R₁ θ).symm
      · apply Continuous.div
        · exact (hwc k).comp_continuous (continuous_circleMap c R₁) hmem
        · exact (continuous_circleMap c R₁).sub
            ((hφc k).comp_continuous (continuous_circleMap c R₁) hmem)
        · intro θ
          exact sub_apply_ne_zero hτR₁ hφ k (hmem θ)
  rw [hsplit, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hφdAt : DifferentiableAt ℂ (φ k) (x k) :=
    (hφd k).differentiableOn.differentiableAt
      (Metric.isOpen_ball.mem_nhds (hx k))
  rw [contour_eq_residue_single hR₁ (hx k) (hfactor k) (hwd k) (hgd k) (hg0 k),
    cofactor_eq_one_sub_deriv (hx k) (hfactor k) hφdAt (hgd k)]

/-- **Non-vacuity witness** (audit rule 2026-08-01): every hypothesis of
`trace_eq_residues` is satisfiable and the formula computes.  One constant
branch `φ = 0` at center `0`, weight `w = 1`, cofactor `g = 1`, fixed point
`x = 0`: the trace of the resulting rank-one averaging operator is
`1/(1 − 0) = 1`. -/
example : (∑' m : ℕ, transferMatrix (0 : ℂ) (1/2) 1 1
    (fun _ _ => 1) (fun _ _ => (0 : ℂ)) m m) = 1 := by
  have h := trace_eq_residues (c := 0) (R := 1/2) (R₁ := 1) (τ := 0) (W := 1)
    (w := fun _ _ => 1) (φ := fun _ _ => (0 : ℂ)) (K := 1)
    (by norm_num) (by norm_num) le_rfl (by norm_num) zero_le_one
    (fun k z _ => by simp)
    (fun k z _ => by simp)
    (x := fun _ => 0) (fun k => by simp)
    (g := fun _ _ => 1) (fun k z _ => by ring)
    (fun k => diffContOnCl_const)
    (fun k => diffContOnCl_const)
    (fun k => diffContOnCl_const)
    (fun k z _ => one_ne_zero)
  rw [h]
  simp

end

end HilbertSchmidt

#print axioms HilbertSchmidt.intervalIntegral_tsum
#print axioms HilbertSchmidt.trace_eq_contour
#print axioms HilbertSchmidt.contour_eq_residue_single
#print axioms HilbertSchmidt.trace_eq_residues
