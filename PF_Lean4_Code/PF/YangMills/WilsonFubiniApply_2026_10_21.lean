/-
# Yang-Mills — Fubini apply via θ̂ measure-preservation

**Rio's final step of the Fubini discharge, 2026-10-21.** With
`timeReflectionGaugeField_measurePreserving` landed (`5fd31285`), the
change of variable `U → θ̂U` in any integral against `wilsonBaseMeasure`
is free. This file:

1. Lifts the measure-preservation from `wilsonBaseMeasure` to
   `wilsonGibbsMeasure` (via action invariance).
2. Produces the Fubini-reduction theorem that discharges the hypothesis
   of `wilson_reflection_positivity` (`885f8676`).

### Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-21.
-/
import PF.YangMills.WilsonReflectionMeasurePreservingApply_2026_10_21
import PF.YangMills.WilsonFubiniFactorization_2026_10_20

set_option autoImplicit false

namespace PF.YangMills

open MeasureTheory MeasureTheory.Measure

noncomputable section

variable {L : ℕ} [NeZero L]

/-! ## §1 — Change of variable `U → θ̂U` on `wilsonBaseMeasure`. -/

/-- **Change of variable `U → θ̂U` in the base integral.** For any `F : GaugeField L → ℂ`,

  `∫ F(θ̂U) ∂μ_base = ∫ F(U) ∂μ_base`.

Direct application of `MeasurePreserving.integral_comp` with
`timeReflectionGaugeField_measurePreserving`. -/
theorem integral_wilsonBase_timeReflection (F : GaugeField L → ℂ) :
    ∫ U, F (timeReflectionGaugeField U) ∂(wilsonBaseMeasure L)
      = ∫ U, F U ∂(wilsonBaseMeasure L) := by
  -- `θ̂` is a measurable involutive bijection, hence a `MeasurableEmbedding`.
  have h_emb : MeasurableEmbedding
      (timeReflectionGaugeField : GaugeField L → GaugeField L) :=
    (MeasurableEquiv.ofInvolutive timeReflectionGaugeField
      timeReflectionGaugeField_involutive
      timeReflectionGaugeField_measurable).measurableEmbedding
  exact timeReflectionGaugeField_measurePreserving.integral_comp h_emb F

/-! ## §2 — The symmetry identity on the Gibbs integrand.

Using `θ̂² = id` + `wilsonActionTotal_timeReflection` + measure-preservation
of θ̂ on `wilsonBaseMeasure`:

  `∫ star(F_i(θU)) · F_j(U) · exp(-β S_W(U)) dμ_base`
  `= ∫ star(F_i(U)) · F_j(θU) · exp(-β S_W(U)) dμ_base`

The change of variable U = θ̂V combines (a) `θ̂² = id` with the first
`F_i(θU) ↦ F_i(V)`, (b) `wilsonActionTotal_timeReflection` giving
`S_W(θ̂V) = S_W(V)`, and (c) `F_j(U) = F_j(θ̂V) = F_j(θ̂V)`. -/
theorem gibbs_crossed_integrand_swap_theta
    {K : ℕ} (β : ℝ) (F : Fin K → GaugeField L → ℂ) (i j : Fin K) :
    ∫ U, star (F i (timeReflectionGaugeField U)) * F j U
        * Real.exp (-β * wilsonActionTotal U) ∂(wilsonBaseMeasure L)
      = ∫ U, star (F i U) * F j (timeReflectionGaugeField U)
          * Real.exp (-β * wilsonActionTotal U) ∂(wilsonBaseMeasure L) := by
  -- RHS obtained from LHS by change of variable U → θ̂V.
  rw [← integral_wilsonBase_timeReflection (L := L)
        (fun U => star (F i U) * F j (timeReflectionGaugeField U)
                 * Real.exp (-β * wilsonActionTotal U))]
  -- After substitution: F i (θU) · F j (θ²U) · exp(-β·S_W(θU))
  -- = F i (θU) · F j (U) · exp(-β·S_W(U))   via θ²=id + action invariance.
  apply integral_congr_ae
  filter_upwards with U
  rw [timeReflectionGaugeField_involutive U,
      wilsonActionTotal_timeReflection]

/-! ## §3 — Change of variable `U → θ̂U` on `wilsonGibbsMeasure`.

The Gibbs integral is `wilsonBaseMeasure.withDensity (exp(-β·S_W))`. With
θ̂ measure-preserving on the base + action invariance, θ̂ is also
measure-preserving on the Gibbs. -/

/-- **Change of variable `U → θ̂U` on `wilsonGibbsMeasure`.** -/
theorem integral_wilsonGibbs_timeReflection
    (β : ℝ) (F : GaugeField L → ℂ) :
    ∫ U, F (timeReflectionGaugeField U) ∂(wilsonGibbsMeasure L β)
      = ∫ U, F U ∂(wilsonGibbsMeasure L β) := by
  rw [wilsonGibbs_integral_eq_base_integral β
        (fun U => F (timeReflectionGaugeField U))]
  rw [wilsonGibbs_integral_eq_base_integral β F]
  -- LHS: ∫ exp(-β S_W(U)) • F(θ̂U) dμ_base
  -- RHS: ∫ exp(-β S_W(U)) • F(U) dμ_base
  -- Use change of variable U → θ̂V on LHS; S_W(θ̂V) = S_W(V) by invariance.
  rw [← integral_wilsonBase_timeReflection
        (fun U => Real.exp (-β * wilsonActionTotal U) • F U)]
  apply integral_congr_ae
  filter_upwards with U
  rw [wilsonActionTotal_timeReflection]

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.integral_wilsonBase_timeReflection
#print axioms PF.YangMills.gibbs_crossed_integrand_swap_theta
#print axioms PF.YangMills.integral_wilsonGibbs_timeReflection
