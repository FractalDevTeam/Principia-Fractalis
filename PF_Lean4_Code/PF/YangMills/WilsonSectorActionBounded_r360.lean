/-
# r360: the refined sector actions are continuous, measurable and bounded

★ 2026-10-28 r360 — the boundedness layer both remaining RP pieces need ★

## Why this file exists

`wilson_reflection_positivity` (`WilsonReflectionPositivity_2026_10_20.lean:112`)
carries exactly two hypotheses, `hΦ_integrable` and `hFubini`, and
`WilsonRPFubiniApplyR_2026_10_23.lean:52` already specialises it to the
concrete `Φ i := wilsonReducedPhiR β (F i)`. Both remaining pieces need the
same missing ingredient: the **refined sector** Boltzmann factors
`exp(-β · S_•R)` must be bounded.

`WilsonActionContinuity_2026_10_20.lean` supplies this for the *total* action
(`wilsonActionTotal_continuous` at `:118`, and the `BddAbove`-via-compact-range
argument inside `wilsonGibbsMeasure_isFiniteMeasure` at `:148`). It does **not**
supply it for the three refined sector actions `wilsonActionPlusR`,
`wilsonActionZero`, `wilsonActionMinusR`
(`WilsonSectorPlaquetteZero_2026_10_21.lean:101-113`), which are the ones the
refined Fubini route actually uses. This file closes that.

## Method

Each refined sector action is a `Finset.sum` of `wilsonActionDensity U p` over a
filtered plaquette set, and each density is continuous in `U`
(`wilsonActionDensity_continuous_U`). So `continuous_finset_sum` gives
continuity, `Continuous.measurable` gives measurability, and — because
`GaugeField L = LatticeLink L → SU2` is a finite product of compact spaces,
hence compact — `isCompact_range` plus `IsCompact.bddAbove` gives a uniform
bound on each Boltzmann factor. This is exactly the argument already used for
the total action, applied to the sectors.

## What this is NOT

This does not discharge `hΦ_integrable`. That additionally needs (a) a
boundedness hypothesis on `F`, which the headline does not currently carry —
`supportedOnPlusZero` is a support condition, not a bound — and (b)
measurability of the parametric integral `U ↦ wilsonReducedPhiR β F U`, which
is a separate problem about `Measure.pi`. Both are recorded here as the next
steps rather than claimed.

## Axiom budget

Zero project axioms; the three kernel axioms only.
-/

import PF.YangMills.WilsonActionContinuity_2026_10_20
import PF.YangMills.WilsonSectorPlaquetteZero_2026_10_21

set_option autoImplicit false

namespace PF.YangMills

open MeasureTheory

noncomputable section

variable {L : ℕ} [NeZero L]

/-! ## §1 — Continuity of the three refined sector actions

Each is a finite sum of continuous densities. -/

lemma wilsonActionPlusR_continuous :
    Continuous (fun U : GaugeField L => wilsonActionPlusR U) := by
  unfold wilsonActionPlusR
  exact continuous_finset_sum _ fun p _ => wilsonActionDensity_continuous_U p

lemma wilsonActionZero_continuous :
    Continuous (fun U : GaugeField L => wilsonActionZero U) := by
  unfold wilsonActionZero
  exact continuous_finset_sum _ fun p _ => wilsonActionDensity_continuous_U p

lemma wilsonActionMinusR_continuous :
    Continuous (fun U : GaugeField L => wilsonActionMinusR U) := by
  unfold wilsonActionMinusR
  exact continuous_finset_sum _ fun p _ => wilsonActionDensity_continuous_U p

/-! ## §2 — Measurability -/

theorem wilsonActionPlusR_measurable :
    Measurable (fun U : GaugeField L => wilsonActionPlusR U) :=
  wilsonActionPlusR_continuous.measurable

theorem wilsonActionZero_measurable :
    Measurable (fun U : GaugeField L => wilsonActionZero U) :=
  wilsonActionZero_continuous.measurable

theorem wilsonActionMinusR_measurable :
    Measurable (fun U : GaugeField L => wilsonActionMinusR U) :=
  wilsonActionMinusR_continuous.measurable

/-! ## §3 — The sector Boltzmann factors are continuous -/

lemma expWilsonActionPlusR_continuous (β : ℝ) :
    Continuous (fun U : GaugeField L => Real.exp (-β * wilsonActionPlusR U)) :=
  Real.continuous_exp.comp (continuous_const.mul wilsonActionPlusR_continuous)

lemma expWilsonActionZero_continuous (β : ℝ) :
    Continuous (fun U : GaugeField L => Real.exp (-β * wilsonActionZero U)) :=
  Real.continuous_exp.comp (continuous_const.mul wilsonActionZero_continuous)

lemma expWilsonActionMinusR_continuous (β : ℝ) :
    Continuous (fun U : GaugeField L => Real.exp (-β * wilsonActionMinusR U)) :=
  Real.continuous_exp.comp (continuous_const.mul wilsonActionMinusR_continuous)

/-! ## §4 — Uniform bounds on the sector Boltzmann factors

`GaugeField L = LatticeLink L → SU2` is a finite product of compact spaces, so
the continuous image is compact and therefore bounded above. This is the step
the refined Fubini and integrability arguments both consume. -/

theorem expWilsonActionPlusR_bddAbove (β : ℝ) :
    ∃ M : ℝ, ∀ U : GaugeField L, Real.exp (-β * wilsonActionPlusR U) ≤ M := by
  obtain ⟨M, hM⟩ :=
    (isCompact_range (expWilsonActionPlusR_continuous (L := L) β)).bddAbove
  exact ⟨M, fun U => hM ⟨U, rfl⟩⟩

theorem expWilsonActionZero_bddAbove (β : ℝ) :
    ∃ M : ℝ, ∀ U : GaugeField L, Real.exp (-β * wilsonActionZero U) ≤ M := by
  obtain ⟨M, hM⟩ :=
    (isCompact_range (expWilsonActionZero_continuous (L := L) β)).bddAbove
  exact ⟨M, fun U => hM ⟨U, rfl⟩⟩

theorem expWilsonActionMinusR_bddAbove (β : ℝ) :
    ∃ M : ℝ, ∀ U : GaugeField L, Real.exp (-β * wilsonActionMinusR U) ≤ M := by
  obtain ⟨M, hM⟩ :=
    (isCompact_range (expWilsonActionMinusR_continuous (L := L) β)).bddAbove
  exact ⟨M, fun U => hM ⟨U, rfl⟩⟩

/-! ## §5 — The bound is positive, and the factors are positive

Both facts are needed when the bound is used as a denominator or multiplied
into an inequality. -/

theorem expWilsonActionPlusR_pos (β : ℝ) (U : GaugeField L) :
    0 < Real.exp (-β * wilsonActionPlusR U) := Real.exp_pos _

theorem expWilsonActionPlusR_bddAbove_pos (β : ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ U : GaugeField L, Real.exp (-β * wilsonActionPlusR U) ≤ M := by
  obtain ⟨M, hM⟩ := expWilsonActionPlusR_bddAbove (L := L) β
  refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun U => ?_⟩
  exact le_trans (hM U) (le_max_left _ _)

/-! ## §6 — Non-vacuity

The bounds are statements about a nonempty space: there is at least one gauge
field, namely the identically-identity configuration. -/

-- `[NeZero L]` is in scope but unused here, which the unused-section-variable
-- linter flags and the pristine gate counts under criterion (d).
omit [NeZero L] in
theorem gaugeField_nonempty : Nonempty (GaugeField L) := ⟨fun _ => 1⟩

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.wilsonActionPlusR_continuous
#print axioms PF.YangMills.expWilsonActionPlusR_bddAbove
#print axioms PF.YangMills.expWilsonActionZero_bddAbove
#print axioms PF.YangMills.expWilsonActionMinusR_bddAbove
#print axioms PF.YangMills.expWilsonActionPlusR_bddAbove_pos
