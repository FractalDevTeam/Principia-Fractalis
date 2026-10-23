/-
# Yang-Mills — Gibbs → Base integral with 3-way Boltzmann factored

**Rio's §P3 ACER directive, 2026-10-23.** The 3-way counterpart to
`wilsonGibbs_integral_bochner_factorize` (`f852724c`, binary split).

Direct consequence of composing `wilsonGibbs_integral_eq_base_integral`
with the 3-way factorization `wilsonBoltzmann_factorize_3way_real`
(`8426e74c`).

### Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-23.
-/
import PF.YangMills.WilsonBoltzmannFactorize3Way_2026_10_22
import PF.YangMills.WilsonFubiniFactorization_2026_10_20

set_option autoImplicit false

namespace PF.YangMills

open MeasureTheory

noncomputable section

variable {L : ℕ} [NeZero L]

/-- **★ 3-way Gibbs → Base ★**

For a `ℂ`-valued integrable `F`:

  `∫ F dμ_Gibbs = ∫ (exp(-β·S_+R) * exp(-β·S_0) * exp(-β·S_-R)) • F dμ_base`.

Compose `wilsonGibbs_integral_eq_base_integral` with the pointwise
3-way factorization. -/
theorem wilsonGibbs_integral_eq_base_integral_3way (β : ℝ) (F : GaugeField L → ℂ) :
    ∫ U, F U ∂(wilsonGibbsMeasure L β)
      = ∫ U, (Real.exp (-β * wilsonActionPlusR U)
              * Real.exp (-β * wilsonActionZero U)
              * Real.exp (-β * wilsonActionMinusR U)) • F U
        ∂(wilsonBaseMeasure L) := by
  rw [wilsonGibbs_integral_eq_base_integral β F]
  apply integral_congr_ae
  filter_upwards with U
  rw [wilsonBoltzmann_factorize_3way_real]

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.wilsonGibbs_integral_eq_base_integral_3way
