/-
# PF.YangMills.WilsonL2GramEntryTendsto_2026_11_12

**Step 5a of the L² extension lane**: bilinear convergence of Gram
entries under L² convergence of test functions.

Delivers `wilsonL2GramEntryTendsto_holds : WilsonL2GramEntryTendsto L β`.

Given two pairs `(F, F_n)` and `(G, G_n)` with `F_n → F` and `G_n → G`
in `L²(μ_Gibbs)`, the Gram entry

   `∫ star(F_n(θU)) * G_n U ∂μ_Gibbs`

converges to `∫ star(F(θU)) * G U ∂μ_Gibbs`.

Proof uses ε/2 decomposition through a mixed term:
    `∫ star(F_n θ) · G_n - ∫ star(F θ) · G
      = ∫ star((F_n - F) θ) · G_n + ∫ star(F θ) · (G_n - G)`
each bounded via `wilson_rp_gram_bound` + eventual bound on
`‖G_n‖_{L²}` from triangle.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-12.
-/

import PF.YangMills.WilsonRPL2Extension_2026_11_12
import PF.YangMills.WilsonRPGramBound_2026_11_11

namespace PF.YangMills

open MeasureTheory Filter
open scoped Topology ComplexOrder ENNReal

noncomputable section

variable {L : ℕ} [NeZero L]

/-- Real `L²`-seminorm shortcut for `MemLp f 2 μ`:
`L2NormReal f μ = (∫ ‖f‖² dμ)^(1/2)`.  Matches `wilson_rp_gram_bound`
which uses `^ 2` (nat-pow) on reals. -/
private noncomputable def L2NormReal (f : GaugeField L → ℂ) (μ : Measure (GaugeField L)) : ℝ :=
  (∫ U, ‖f U‖ ^ 2 ∂μ) ^ ((1 : ℝ) / 2)

private lemma L2NormReal_nonneg (f : GaugeField L → ℂ) (μ : Measure (GaugeField L)) :
    0 ≤ L2NormReal f μ := by
  unfold L2NormReal
  refine Real.rpow_nonneg ?_ _
  refine integral_nonneg fun U => ?_
  positivity

private lemma L2NormReal_eq_toReal_eLpNorm
    (μ : Measure (GaugeField L)) (f : GaugeField L → ℂ) (hf : MemLp f 2 μ) :
    L2NormReal f μ = (eLpNorm f 2 μ).toReal := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hf]
  have h_nonneg : 0 ≤ ∫ a, ‖f a‖ ^ ((2 : ℝ≥0∞).toReal) ∂μ :=
    integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg h_nonneg _)]
  unfold L2NormReal
  have h2 : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num
  rw [h2]
  have h_inv : ((2 : ℝ))⁻¹ = (1 : ℝ) / 2 := by norm_num
  rw [h_inv]
  -- Now: (∫ ‖f U‖^2 dμ)^(1/2) = (∫ ‖f a‖^(2:ℝ) dμ)^(1/2).
  congr 1
  refine integral_congr_ae ?_
  filter_upwards with U
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num,
      Real.rpow_natCast]

/-- `L2NormReal` tendsto 0 from `eLpNorm` tendsto 0. -/
private lemma L2NormReal_tendsto_zero
    (μ : Measure (GaugeField L)) [IsFiniteMeasure μ]
    (F : GaugeField L → ℂ) (F_n : ℕ → GaugeField L → ℂ)
    (hF : MemLp F 2 μ) (hF_n : ∀ n, MemLp (F_n n) 2 μ)
    (h : Tendsto (fun n => eLpNorm (fun U => F U - F_n n U) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => L2NormReal (fun U => F U - F_n n U) μ) atTop (𝓝 0) := by
  have h_toReal : Tendsto (fun n =>
      (eLpNorm (fun U => F U - F_n n U) 2 μ).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal (by norm_num : (0 : ℝ≥0∞) ≠ ∞)).comp h
    simpa using this
  refine h_toReal.congr' ?_
  filter_upwards with n
  exact (L2NormReal_eq_toReal_eLpNorm _ _ (hF.sub (hF_n n))).symm

/-- Triangle inequality on `L2NormReal`: `‖f‖ ≤ ‖g‖ + ‖f - g‖`. -/
private lemma L2NormReal_triangle
    (μ : Measure (GaugeField L)) [IsFiniteMeasure μ]
    (f g : GaugeField L → ℂ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    L2NormReal f μ ≤ L2NormReal g μ + L2NormReal (fun U => f U - g U) μ := by
  have h_tri_eLpNorm :
      eLpNorm f 2 μ ≤ eLpNorm g 2 μ + eLpNorm (fun U => f U - g U) 2 μ := by
    calc eLpNorm f 2 μ
        = eLpNorm (fun U => g U + (f U - g U)) 2 μ := by
          congr 1; funext U; ring
      _ ≤ eLpNorm g 2 μ + eLpNorm (fun U => f U - g U) 2 μ :=
          eLpNorm_add_le hg.aestronglyMeasurable
            (hf.aestronglyMeasurable.sub hg.aestronglyMeasurable)
            (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_sub_memLp : MemLp (fun U => f U - g U) 2 μ := hf.sub hg
  rw [L2NormReal_eq_toReal_eLpNorm _ _ hf,
      L2NormReal_eq_toReal_eLpNorm _ _ hg,
      L2NormReal_eq_toReal_eLpNorm _ _ h_sub_memLp]
  have h_add_ne_top :
      eLpNorm g 2 μ + eLpNorm (fun U => f U - g U) 2 μ ≠ ∞ := by
    refine ENNReal.add_ne_top.mpr ⟨hg.eLpNorm_ne_top, ?_⟩
    exact h_sub_memLp.eLpNorm_ne_top
  have h_mono := ENNReal.toReal_mono h_add_ne_top h_tri_eLpNorm
  rw [ENNReal.toReal_add hg.eLpNorm_ne_top h_sub_memLp.eLpNorm_ne_top] at h_mono
  exact h_mono

/-- **Step 5a**: bilinear Gram entry convergence. -/
theorem wilsonL2GramEntryTendsto_holds (β : ℝ) :
    WilsonL2GramEntryTendsto L β := by
  intro F G F_n G_n hF hG hF_n hG_n hF_tendsto hG_tendsto
  set μ := wilsonGibbsMeasure L β with hμ_def
  haveI : IsFiniteMeasure μ := wilsonGibbsMeasure_isFiniteMeasure β
  set NF := L2NormReal F μ with hNF_def
  set NG := L2NormReal G μ with hNG_def
  have hNG_nonneg : 0 ≤ NG := L2NormReal_nonneg G μ
  have hNF_nonneg : 0 ≤ NF := L2NormReal_nonneg F μ
  -- Transfer tendsto hypotheses to L2NormReal form.
  have hF_tendsto_real :
      Tendsto (fun n => L2NormReal (fun U => F U - F_n n U) μ) atTop (𝓝 0) :=
    L2NormReal_tendsto_zero μ F F_n hF hF_n hF_tendsto
  have hG_tendsto_real :
      Tendsto (fun n => L2NormReal (fun U => G U - G_n n U) μ) atTop (𝓝 0) :=
    L2NormReal_tendsto_zero μ G G_n hG hG_n hG_tendsto
  -- `L2NormReal (G_n n) μ` is eventually ≤ NG + 1.
  have h_NG_bound :
      ∀ᶠ n in atTop, L2NormReal (G_n n) μ ≤ NG + 1 := by
    have h_lt_one :
        ∀ᶠ n in atTop, L2NormReal (fun U => G U - G_n n U) μ < 1 :=
      hG_tendsto_real.eventually (eventually_lt_nhds zero_lt_one)
    filter_upwards [h_lt_one] with n hn
    have h_tri := L2NormReal_triangle μ (G_n n) G (hG_n n) hG
    -- `L2NormReal G_n n ≤ NG + L2NormReal (G_n n - G) μ`.
    have h_abs : L2NormReal (fun U => G_n n U - G U) μ
        = L2NormReal (fun U => G U - G_n n U) μ := by
      unfold L2NormReal
      congr 1
      refine integral_congr_ae ?_
      filter_upwards with U
      rw [show (G_n n U - G U) = -(G U - G_n n U) from by ring, norm_neg]
    rw [h_abs] at h_tri
    linarith
  -- Begin the ε/N argument.
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ := ε / 2 with hδ_def
  have hδ : 0 < δ := by positivity
  have hNG1_pos : 0 < NG + 1 := by linarith
  -- Find N₁ so `L2NormReal (F - F_n n) μ * (NG + 1) < δ` for n ≥ N₁.
  have h_tendsto_prod_F : Tendsto (fun n =>
      L2NormReal (fun U => F U - F_n n U) μ * (NG + 1)) atTop (𝓝 0) := by
    simpa using hF_tendsto_real.mul_const (NG + 1)
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp h_tendsto_prod_F δ hδ
  -- Find N₂ so `NF * L2NormReal (G - G_n n) μ < δ` for n ≥ N₂.
  have h_tendsto_prod_G : Tendsto (fun n =>
      NF * L2NormReal (fun U => G U - G_n n U) μ) atTop (𝓝 0) := by
    simpa using hG_tendsto_real.const_mul NF
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp h_tendsto_prod_G δ hδ
  -- Find N₃ so `L2NormReal (G_n n) μ ≤ NG + 1` for n ≥ N₃.
  obtain ⟨N₃, hN₃⟩ := h_NG_bound.exists_forall_of_atTop
  refine ⟨max (max N₁ N₂) N₃, fun n hn => ?_⟩
  have hn₁ : n ≥ N₁ := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
  have hn₂ : n ≥ N₂ := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)
  have hn₃ : n ≥ N₃ := le_trans (le_max_right _ _) hn
  -- Target: `dist (A_n n) A < ε`.
  set A_n := ∫ U, star (F_n n (timeReflectionGaugeField U)) * G_n n U ∂μ
    with hA_n_def
  set A := ∫ U, star (F (timeReflectionGaugeField U)) * G U ∂μ with hA_def
  -- Integrability pieces.
  have h_Ftheta : MemLp (fun U => F (timeReflectionGaugeField U)) 2 μ :=
    hF.comp_measurePreserving
      (wilsonGibbsMeasure_measurePreserving_timeReflection β)
  have h_Fntheta : MemLp (fun U => F_n n (timeReflectionGaugeField U)) 2 μ :=
    (hF_n n).comp_measurePreserving
      (wilsonGibbsMeasure_measurePreserving_timeReflection β)
  have h_starFtheta : MemLp (fun U => star (F (timeReflectionGaugeField U))) 2 μ :=
    h_Ftheta.star
  have h_starFntheta : MemLp (fun U =>
      star (F_n n (timeReflectionGaugeField U))) 2 μ := h_Fntheta.star
  -- Integrability of the four product forms we need.
  have h_An_int : Integrable
      (fun U => star (F_n n (timeReflectionGaugeField U)) * G_n n U) μ :=
    h_starFntheta.integrable_mul (hG_n n)
  have h_A_int : Integrable
      (fun U => star (F (timeReflectionGaugeField U)) * G U) μ :=
    h_starFtheta.integrable_mul hG
  have h_mix_int : Integrable
      (fun U => star (F (timeReflectionGaugeField U)) * G_n n U) μ :=
    h_starFtheta.integrable_mul (hG_n n)
  -- A_n - A = ∫ star(F_n θ)·G_n - ∫ star(F θ)·G
  --        = (∫ star(F_n θ)·G_n - ∫ star(F θ)·G_n) + (∫ star(F θ)·G_n - ∫ star(F θ)·G)
  --        = ∫ star((F_n - F)θ)·G_n + ∫ star(F θ)·(G_n - G).
  have h_An_sub_mix : A_n - ∫ U, star (F (timeReflectionGaugeField U)) * G_n n U ∂μ
      = ∫ U, star ((F_n n (timeReflectionGaugeField U)) -
                    (F (timeReflectionGaugeField U))) * G_n n U ∂μ := by
    rw [hA_n_def, ← integral_sub h_An_int h_mix_int]
    refine integral_congr_ae ?_
    filter_upwards with U
    rw [← sub_mul, ← star_sub]
  have h_mix_sub_A : (∫ U, star (F (timeReflectionGaugeField U)) * G_n n U ∂μ) - A
      = ∫ U, star (F (timeReflectionGaugeField U)) * (G_n n U - G U) ∂μ := by
    rw [hA_def, ← integral_sub h_mix_int h_A_int]
    refine integral_congr_ae ?_
    filter_upwards with U
    rw [mul_sub]
  -- Apply gram_bound to the two pieces.
  have h_bd1 :
      ‖∫ U, star ((F_n n (timeReflectionGaugeField U)) -
                   (F (timeReflectionGaugeField U))) * G_n n U ∂μ‖
        ≤ L2NormReal (fun U => F_n n U - F U) μ * L2NormReal (G_n n) μ := by
    have hdiff : MemLp (fun U => F_n n U - F U) 2 μ := (hF_n n).sub hF
    have h_gram := wilson_rp_gram_bound β (fun U => F_n n U - F U) (G_n n)
                      hdiff (hG_n n)
    -- Match integrand on LHS: (F_n - F)(θU) = F_n(θU) - F(θU).
    have h_int_eq :
        ∫ U, star ((fun U => F_n n U - F U) (timeReflectionGaugeField U)) * G_n n U ∂μ
          = ∫ U, star ((F_n n (timeReflectionGaugeField U)) -
                        (F (timeReflectionGaugeField U))) * G_n n U ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards with U; rfl
    rw [← h_int_eq]
    exact h_gram
  have h_bd2 :
      ‖∫ U, star (F (timeReflectionGaugeField U)) * (G_n n U - G U) ∂μ‖
        ≤ NF * L2NormReal (fun U => G_n n U - G U) μ := by
    have hdiff : MemLp (fun U => G_n n U - G U) 2 μ := (hG_n n).sub hG
    have h_gram := wilson_rp_gram_bound β F (fun U => G_n n U - G U) hF hdiff
    -- h_gram has `(fun U => G_n n U - G U) U` instead of `G_n n U - G U`.
    have h_int_eq :
        ∫ U, star (F (timeReflectionGaugeField U)) *
            (fun U => G_n n U - G U) U ∂μ
          = ∫ U, star (F (timeReflectionGaugeField U)) * (G_n n U - G U) ∂μ :=
      rfl
    rw [← h_int_eq]
    exact h_gram
  -- Triangle: `‖A_n - A‖ ≤ ‖A_n - mix‖ + ‖mix - A‖`.
  have h_tri : ‖A_n - A‖
      ≤ ‖A_n - ∫ U, star (F (timeReflectionGaugeField U)) * G_n n U ∂μ‖
        + ‖(∫ U, star (F (timeReflectionGaugeField U)) * G_n n U ∂μ) - A‖ := by
    have : A_n - A = (A_n - ∫ U, star (F (timeReflectionGaugeField U)) * G_n n U ∂μ)
        + ((∫ U, star (F (timeReflectionGaugeField U)) * G_n n U ∂μ) - A) := by ring
    rw [this]
    exact norm_add_le _ _
  rw [h_An_sub_mix] at h_tri
  rw [h_mix_sub_A] at h_tri
  -- Now combine.
  have hn₁' := hN₁ n hn₁
  have hn₂' := hN₂ n hn₂
  have hn₃' := hN₃ n hn₃
  rw [Real.dist_eq, sub_zero] at hn₁' hn₂'
  -- Final bound.
  have h_abs_FF : L2NormReal (fun U => F U - F_n n U) μ
      = L2NormReal (fun U => F_n n U - F U) μ := by
    unfold L2NormReal
    congr 1
    refine integral_congr_ae ?_
    filter_upwards with U
    rw [show (F U - F_n n U) = -(F_n n U - F U) from by ring, norm_neg]
  rw [h_abs_FF] at hn₁'
  have h_An_sub_le :
      ‖∫ U, star ((F_n n (timeReflectionGaugeField U)) -
                   (F (timeReflectionGaugeField U))) * G_n n U ∂μ‖
        ≤ L2NormReal (fun U => F_n n U - F U) μ * (NG + 1) := by
    refine le_trans h_bd1 ?_
    refine mul_le_mul_of_nonneg_left hn₃' (L2NormReal_nonneg _ _)
  have h_An_sub_lt :
      ‖∫ U, star ((F_n n (timeReflectionGaugeField U)) -
                   (F (timeReflectionGaugeField U))) * G_n n U ∂μ‖ < δ := by
    refine lt_of_le_of_lt h_An_sub_le ?_
    exact lt_of_le_of_lt (le_abs_self _) hn₁'
  have h_abs_GG : L2NormReal (fun U => G U - G_n n U) μ
      = L2NormReal (fun U => G_n n U - G U) μ := by
    unfold L2NormReal
    congr 1
    refine integral_congr_ae ?_
    filter_upwards with U
    rw [show (G U - G_n n U) = -(G_n n U - G U) from by ring, norm_neg]
  rw [h_abs_GG] at hn₂'
  have h_mix_sub_lt :
      ‖∫ U, star (F (timeReflectionGaugeField U)) * (G_n n U - G U) ∂μ‖ < δ := by
    refine lt_of_le_of_lt h_bd2 ?_
    exact lt_of_le_of_lt (le_abs_self _) hn₂'
  -- `dist (A_n n) A = ‖A_n - A‖` in ℂ.
  have h_dist_eq : dist A_n A = ‖A_n - A‖ := dist_eq_norm _ _
  rw [h_dist_eq]
  linarith

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.wilsonL2GramEntryTendsto_holds
