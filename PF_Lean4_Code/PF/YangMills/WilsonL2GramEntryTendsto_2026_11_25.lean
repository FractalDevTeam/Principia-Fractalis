/-
# PF.YangMills.WilsonL2GramEntryTendsto_2026_11_25

**Step 5a of the YM L²-extension lane, discharged.**

`PF/YangMills/WilsonRPL2Extension_2026_11_12.lean` states
`wilson_reflection_positivity_of_L2` conditional on two named hypotheses and
calls this one "one bounded proof-engineering task":

* `WilsonL2GramEntryTendsto` — if `F_n → F` and `G_n → G` in `L²(μ_Gibbs)`,
  then the θ-crossed Gram entry `∫ star(F_n(θU)) · G_n U ∂μ_Gibbs` converges to
  `∫ star(F(θU)) · G U ∂μ_Gibbs`.

This file proves it. `wilson_reflection_positivity_of_L2` therefore drops from
two hypotheses to one, leaving only `WilsonL2DensityHypothesis` (step 3, the
mathlib-interaction task).

## Route

The ingredients were already in the tree; what was missing was the assembly.

* `wilson_rp_gram_bound` (2026-11-11) is exactly the bilinear estimate
  `‖∫ star(F(θU)) · G U‖ ≤ (∫‖F‖²)^(1/2) · (∫‖G‖²)^(1/2)`, i.e. with `l2R`
  below it reads `≤ l2R F * l2R G` definitionally. It needs no integrability:
  it goes through `norm_integral_le_integral_norm`, which is unconditional.
* The **split** does need integrability, since `integral_sub`/`integral_add` do.
  `MemLp.integrable_mul` supplies it from `MemLp _ 2` on both factors, with the
  θ-side lifted by `MemLp.comp_measurePreserving` against
  `wilsonGibbsMeasure_measurePreserving_timeReflection`.

The plan recorded in the step-5 file was an ε/2 argument. This proof avoids it:
`gram_entry_error_le` bounds the error for each index by

  `l2R (F - Fn) * (l2R G + l2R (G - Gn)) + l2R F * l2R (G - Gn)`

which tends to `0 * (l2R G + 0) + l2R F * 0 = 0` by continuity of multiplication
and addition alone. `squeeze_zero_norm` then closes it, and no `N` is ever named.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-11-25.
-/

import PF.YangMills.WilsonRPGramBound_2026_11_11
import PF.YangMills.WilsonRPL2Extension_2026_11_12

set_option autoImplicit false

namespace PF.YangMills

open MeasureTheory Filter
open scoped Topology ComplexOrder ENNReal

noncomputable section

variable {L : ℕ} [NeZero L]

/-! ## §1 — the real-valued L² norm that `wilson_rp_gram_bound` speaks in -/

/-- The right-hand side shape of `wilson_rp_gram_bound`: `(∫ ‖f‖² dμ)^(1/2)`,
with `‖·‖²` a natural-number power, exactly as that lemma states it. Kept a
plain `def` so the Gram bound's conclusion is *definitionally* a statement
about `l2R`, which is what lets the bounds below be `exact`, not `simpa`. -/
def l2R (β : ℝ) (f : GaugeField L → ℂ) : ℝ :=
  (∫ U, ‖f U‖ ^ 2 ∂(wilsonGibbsMeasure L β)) ^ ((1 : ℝ) / 2)

theorem l2R_nonneg (β : ℝ) (f : GaugeField L → ℂ) : 0 ≤ l2R β f :=
  Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _

/-- `l2R` is symmetric in a difference, because the pointwise norm is. -/
theorem l2R_sub_comm (β : ℝ) (f g : GaugeField L → ℂ) :
    l2R β (fun U => f U - g U) = l2R β (fun U => g U - f U) := by
  unfold l2R
  congr 1
  refine integral_congr_ae ?_
  filter_upwards with U
  rw [norm_sub_rev]

/-- `(eLpNorm f 2 μ).toReal = l2R β f` for `f ∈ L²`. The bridge the step-5
scoping note called the dominant cost of this step. -/
theorem toReal_eLpNorm_two_eq_l2R (β : ℝ) (f : GaugeField L → ℂ)
    (hf : MemLp f 2 (wilsonGibbsMeasure L β)) :
    (eLpNorm f 2 (wilsonGibbsMeasure L β)).toReal = l2R β f := by
  have hp1 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hp2 : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  have hnn : 0 ≤ ∫ U, ‖f U‖ ^ 2 ∂(wilsonGibbsMeasure L β) :=
    integral_nonneg fun _ => by positivity
  rw [hf.eLpNorm_eq_integral_rpow_norm hp1 hp2]
  have htr : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num
  rw [htr]
  have hint : (∫ U, ‖f U‖ ^ (2 : ℝ) ∂(wilsonGibbsMeasure L β))
      = ∫ U, ‖f U‖ ^ 2 ∂(wilsonGibbsMeasure L β) := by
    refine integral_congr_ae ?_
    filter_upwards with U
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hint, ENNReal.toReal_ofReal (Real.rpow_nonneg hnn _)]
  unfold l2R
  rw [one_div]

/-- The `eLpNorm`-valued convergence hypotheses, in real form. -/
theorem tendsto_l2R_of_tendsto_eLpNorm (β : ℝ) (f : GaugeField L → ℂ)
    (f_n : ℕ → GaugeField L → ℂ)
    (hmem : ∀ n, MemLp (fun U => f U - f_n n U) 2 (wilsonGibbsMeasure L β))
    (h : Tendsto (fun n => eLpNorm (fun U => f U - f_n n U) 2
          (wilsonGibbsMeasure L β)) atTop (𝓝 0)) :
    Tendsto (fun n => l2R β (fun U => f U - f_n n U)) atTop (𝓝 0) := by
  have hto : Tendsto (fun n => (eLpNorm (fun U => f U - f_n n U) 2
      (wilsonGibbsMeasure L β)).toReal) atTop (𝓝 0) := by
    have h0 : (0 : ℝ≥0∞) ≠ ∞ := by simp
    simpa using (ENNReal.tendsto_toReal h0).comp h
  refine hto.congr (fun n => ?_)
  exact toReal_eLpNorm_two_eq_l2R β _ (hmem n)

/-- `l2R` triangle inequality in the form the error bound needs. -/
theorem l2R_le_add_sub (β : ℝ) (G Gn : GaugeField L → ℂ)
    (hG : MemLp G 2 (wilsonGibbsMeasure L β))
    (hGn : MemLp Gn 2 (wilsonGibbsMeasure L β)) :
    l2R β Gn ≤ l2R β G + l2R β (fun U => G U - Gn U) := by
  have hdiff : MemLp (fun U => G U - Gn U) 2 (wilsonGibbsMeasure L β) := hG.sub hGn
  -- `eLpNorm_sub_le` speaks about `f - g` (Pi.sub); get it in that shape first,
  -- then transport, rather than rewriting `Gn` under its own hypotheses.
  have key : eLpNorm (G - fun U => G U - Gn U) 2 (wilsonGibbsMeasure L β)
      ≤ eLpNorm G 2 (wilsonGibbsMeasure L β)
        + eLpNorm (fun U => G U - Gn U) 2 (wilsonGibbsMeasure L β) :=
    eLpNorm_sub_le (p := 2) hG.aestronglyMeasurable
      hdiff.aestronglyMeasurable (by norm_num)
  have hshape : (G - fun U => G U - Gn U) = Gn := by
    funext U
    simp only [Pi.sub_apply]
    ring
  have hsum : eLpNorm Gn 2 (wilsonGibbsMeasure L β)
      ≤ eLpNorm G 2 (wilsonGibbsMeasure L β)
        + eLpNorm (fun U => G U - Gn U) 2 (wilsonGibbsMeasure L β) :=
    calc eLpNorm Gn 2 (wilsonGibbsMeasure L β)
        = eLpNorm (G - fun U => G U - Gn U) 2 (wilsonGibbsMeasure L β) := by
          rw [hshape]
      _ ≤ eLpNorm G 2 (wilsonGibbsMeasure L β)
            + eLpNorm (fun U => G U - Gn U) 2 (wilsonGibbsMeasure L β) := key
  have hfin : eLpNorm G 2 (wilsonGibbsMeasure L β)
      + eLpNorm (fun U => G U - Gn U) 2 (wilsonGibbsMeasure L β) ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨hG.eLpNorm_ne_top, hdiff.eLpNorm_ne_top⟩
  have hreal := (ENNReal.toReal_le_toReal hGn.eLpNorm_ne_top hfin).mpr hsum
  rw [ENNReal.toReal_add hG.eLpNorm_ne_top hdiff.eLpNorm_ne_top,
      toReal_eLpNorm_two_eq_l2R β _ hGn,
      toReal_eLpNorm_two_eq_l2R β _ hG,
      toReal_eLpNorm_two_eq_l2R β _ hdiff] at hreal
  exact hreal

/-! ## §2 — integrability of the θ-crossed product -/

/-- `U ↦ F (θ U)` is in `L²` whenever `F` is, by θ-invariance of `μ_Gibbs`. -/
theorem memLp_comp_timeReflection (β : ℝ) (F : GaugeField L → ℂ)
    (hF : MemLp F 2 (wilsonGibbsMeasure L β)) :
    MemLp (fun U => F (timeReflectionGaugeField U)) 2 (wilsonGibbsMeasure L β) :=
  hF.comp_measurePreserving
    (wilsonGibbsMeasure_measurePreserving_timeReflection β)

/-- The θ-crossed product of two `L²` functions is integrable. This is what the
Gram bound itself never needed and the split cannot do without. -/
theorem integrable_theta_cross (β : ℝ) (F G : GaugeField L → ℂ)
    (hF : MemLp F 2 (wilsonGibbsMeasure L β))
    (hG : MemLp G 2 (wilsonGibbsMeasure L β)) :
    Integrable (fun U => star (F (timeReflectionGaugeField U)) * G U)
      (wilsonGibbsMeasure L β) := by
  have hFθ := memLp_comp_timeReflection β F hF
  have hstar : MemLp (fun U => star (F (timeReflectionGaugeField U))) 2
      (wilsonGibbsMeasure L β) := hFθ.star
  exact hstar.integrable_mul hG

/-! ## §3 — the per-index error bound -/

/-- Pointwise algebraic identity behind the split. -/
theorem gram_integrand_split (F G Fn Gn : GaugeField L → ℂ) (U : GaugeField L) :
    star (Fn (timeReflectionGaugeField U)) * Gn U
        - star (F (timeReflectionGaugeField U)) * G U
      = star ((fun V => Fn V - F V) (timeReflectionGaugeField U)) * Gn U
        + star (F (timeReflectionGaugeField U)) * ((fun V => Gn V - G V) U) := by
  simp only [star_sub]
  ring

set_option maxHeartbeats 1000000 in
/-- **The error bound at one index.** Everything quantitative in step 5a. -/
theorem gram_entry_error_le (β : ℝ) (F G Fn Gn : GaugeField L → ℂ)
    (hF : MemLp F 2 (wilsonGibbsMeasure L β))
    (hG : MemLp G 2 (wilsonGibbsMeasure L β))
    (hFn : MemLp Fn 2 (wilsonGibbsMeasure L β))
    (hGn : MemLp Gn 2 (wilsonGibbsMeasure L β)) :
    ‖(∫ U, star (Fn (timeReflectionGaugeField U)) * Gn U
          ∂(wilsonGibbsMeasure L β))
        - ∫ U, star (F (timeReflectionGaugeField U)) * G U
          ∂(wilsonGibbsMeasure L β)‖
      ≤ l2R β (fun U => F U - Fn U)
          * (l2R β G + l2R β (fun U => G U - Gn U))
        + l2R β F * l2R β (fun U => G U - Gn U) := by
  have hIa := integrable_theta_cross β Fn Gn hFn hGn
  have hIb := integrable_theta_cross β F G hF hG
  have hI1 := integrable_theta_cross β (fun V => Fn V - F V) Gn (hFn.sub hF) hGn
  have hI2 := integrable_theta_cross β F (fun V => Gn V - G V) hF (hGn.sub hG)
  have hsplit :
      (∫ U, star (Fn (timeReflectionGaugeField U)) * Gn U
          ∂(wilsonGibbsMeasure L β))
        - ∫ U, star (F (timeReflectionGaugeField U)) * G U
          ∂(wilsonGibbsMeasure L β)
      = (∫ U, star ((fun V => Fn V - F V) (timeReflectionGaugeField U)) * Gn U
            ∂(wilsonGibbsMeasure L β))
        + ∫ U, star (F (timeReflectionGaugeField U))
              * ((fun V => Gn V - G V) U) ∂(wilsonGibbsMeasure L β) := by
    rw [← integral_sub hIa hIb, ← integral_add hI1 hI2]
    refine integral_congr_ae ?_
    filter_upwards with U
    exact gram_integrand_split F G Fn Gn U
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  -- each piece, by the Gram bound (definitionally a statement about `l2R`)
  have hb1 : ‖∫ U, star ((fun V => Fn V - F V) (timeReflectionGaugeField U))
        * Gn U ∂(wilsonGibbsMeasure L β)‖
      ≤ l2R β (fun V => Fn V - F V) * l2R β Gn :=
    wilson_rp_gram_bound β (fun V => Fn V - F V) Gn (hFn.sub hF) hGn
  have hb2 : ‖∫ U, star (F (timeReflectionGaugeField U))
        * ((fun V => Gn V - G V) U) ∂(wilsonGibbsMeasure L β)‖
      ≤ l2R β F * l2R β (fun V => Gn V - G V) :=
    wilson_rp_gram_bound β F (fun V => Gn V - G V) hF (hGn.sub hG)
  have htri := l2R_le_add_sub β G Gn hG hGn
  have hFsym : l2R β (fun V => Fn V - F V) = l2R β (fun U => F U - Fn U) :=
    l2R_sub_comm β Fn F
  have hGsym : l2R β (fun V => Gn V - G V) = l2R β (fun U => G U - Gn U) :=
    l2R_sub_comm β Gn G
  rw [hFsym] at hb1
  rw [hGsym] at hb2
  refine le_trans (add_le_add hb1 hb2) ?_
  exact add_le_add
    (mul_le_mul_of_nonneg_left htri (l2R_nonneg β _)) le_rfl

/-! ## §4 — step 5a -/

/-- **`WilsonL2GramEntryTendsto L β` holds.**

The θ-crossed Gram entry is jointly continuous along `L²`-convergent sequences.
With this, `wilson_reflection_positivity_of_L2` needs only
`WilsonL2DensityHypothesis`. -/
theorem wilsonL2GramEntryTendsto_holds (β : ℝ) :
    WilsonL2GramEntryTendsto L β := by
  intro F G F_n G_n hF hG hFn hGn hFtend hGtend
  have hdF : ∀ n, MemLp (fun U => F U - F_n n U) 2 (wilsonGibbsMeasure L β) :=
    fun n => hF.sub (hFn n)
  have hdG : ∀ n, MemLp (fun U => G U - G_n n U) 2 (wilsonGibbsMeasure L β) :=
    fun n => hG.sub (hGn n)
  have hFr : Tendsto (fun n => l2R β (fun U => F U - F_n n U)) atTop (𝓝 0) :=
    tendsto_l2R_of_tendsto_eLpNorm β F F_n hdF hFtend
  have hGr : Tendsto (fun n => l2R β (fun U => G U - G_n n U)) atTop (𝓝 0) :=
    tendsto_l2R_of_tendsto_eLpNorm β G G_n hdG hGtend
  rw [← tendsto_sub_nhds_zero_iff]
  have hg0 : Tendsto (fun n =>
      l2R β (fun U => F U - F_n n U)
          * (l2R β G + l2R β (fun U => G U - G_n n U))
        + l2R β F * l2R β (fun U => G U - G_n n U)) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => l2R β G) atTop (𝓝 (l2R β G)) :=
      tendsto_const_nhds
    have hcF : Tendsto (fun _ : ℕ => l2R β F) atTop (𝓝 (l2R β F)) :=
      tendsto_const_nhds
    have h1 := hFr.mul (hc.add hGr)
    have h2 := hcF.mul hGr
    have hsum := h1.add h2
    simpa using hsum
  refine squeeze_zero_norm (fun n => ?_) hg0
  exact gram_entry_error_le β F G (F_n n) (G_n n) hF hG (hFn n) (hGn n)

/-! ## §5 — the consequence: one hypothesis instead of two -/

/-- **Wilson reflection positivity on `L²` test functions, now needing only the
density hypothesis.** The Gram-convergence hypothesis of
`wilson_reflection_positivity_of_L2` is discharged by
`wilsonL2GramEntryTendsto_holds`.

NOT a Clay result: this is reflection positivity on a finite even periodic
lattice, one Osterwalder–Schrader axiom, for the `SU(2)` Wilson action. -/
theorem wilson_reflection_positivity_of_L2_of_density
    (hL : Even L) (β : ℝ)
    (h_density : WilsonL2DensityHypothesis L β)
    {K : ℕ} (F : Fin K → GaugeField L → ℂ)
    (hF_support : ∀ i : Fin K, supportedOnPlusZero (F i))
    (hF_mem : ∀ i : Fin K, MemLp (F i) 2 (wilsonGibbsMeasure L β)) :
    (Matrix.of (fun i j =>
      ∫ U, star (F i (timeReflectionGaugeField U)) * F j U
        ∂(wilsonGibbsMeasure L β))).PosSemidef :=
  wilson_reflection_positivity_of_L2 hL β h_density
    (wilsonL2GramEntryTendsto_holds β) F hF_support hF_mem

end

end PF.YangMills
