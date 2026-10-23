/-
# Yang-Mills — Regroup the Gibbs integrand into Fubini-ready form

**Rio's §P3 ACER directive, 2026-10-23.** A regrouping lemma: the
Gibbs integral of `star F_i(θU) · F_j(U)` equals the base integral of

  `[star F_i(θU) · exp(-β·S_-R(U)) · exp(-β·S_0(U))] · [F_j(U) · exp(-β·S_+R(U))]`

The first bracket depends on U's non-plus links (via `F_i` supportedOnPlusZero + `S_-R` + `S_0` gauge-dependence); the second on U's non-minus links. Base-measure Fubini then splits the integral across the Λ_- component.

### Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-23.
-/
import PF.YangMills.WilsonGibbs3WayFactorize_2026_10_23

set_option autoImplicit false

namespace PF.YangMills

open MeasureTheory

noncomputable section

variable {L : ℕ} [NeZero L]

/-- **Fubini-ready regrouping.** For `F_i, F_j : GaugeField L → ℂ`:

  `∫ star F_i(θU) · F_j(U) ∂μ_Gibbs
   = ∫ [star F_i(θU) · exp(-β·S_-R(U)) · exp(-β·S_0(U))]
       · [F_j(U) · exp(-β·S_+R(U))] ∂μ_base`.

Direct from `wilsonGibbs_integral_eq_base_integral_3way` + commutativity
of real-smul-complex. -/
theorem wilson_gibbs_integrand_regroup (β : ℝ) (F_i F_j : GaugeField L → ℂ) :
    ∫ U, star (F_i (timeReflectionGaugeField U)) * F_j U
      ∂(wilsonGibbsMeasure L β)
      = ∫ U, (star (F_i (timeReflectionGaugeField U))
              * (Real.exp (-β * wilsonActionMinusR U) : ℂ)
              * (Real.exp (-β * wilsonActionZero U) : ℂ))
            * (F_j U * (Real.exp (-β * wilsonActionPlusR U) : ℂ))
        ∂(wilsonBaseMeasure L) := by
  rw [wilsonGibbs_integral_eq_base_integral_3way β
       (fun U => star (F_i (timeReflectionGaugeField U)) * F_j U)]
  apply integral_congr_ae
  filter_upwards with U
  -- Goal: (exp_+R * exp_0 * exp_-R : ℝ) • (star F_i(θU) * F_j(U))
  --      = (star F_i(θU) * exp_-R * exp_0) * (F_j(U) * exp_+R)
  rw [Complex.real_smul]
  push_cast
  ring

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.wilson_gibbs_integrand_regroup
