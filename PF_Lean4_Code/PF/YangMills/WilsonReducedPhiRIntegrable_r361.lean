/-
# r361: the refined `Φ` is continuous, and `hΦ_integrable` is DISCHARGED

★ 2026-10-28 r361 — one of the two remaining RP hypotheses removed ★

## What this closes

`wilson_reflection_positivity` (`WilsonReflectionPositivity_2026_10_20.lean:112`)
carries exactly two hypotheses, `hΦ_integrable` and `hFubini`, and
`wilson_reflection_positivity_withReducedPhiR`
(`WilsonRPFubiniApplyR_2026_10_23.lean:52`) specialises it to
`Φ i := wilsonReducedPhiR β (F i)`.

r360's header named the two things `hΦ_integrable` still needed:

1. a boundedness hypothesis on `F` — `supportedOnPlusZero` is a support
   condition, not a bound; and
2. measurability of the parametric integral `U ↦ wilsonReducedPhiR β F U`,
   "a separate problem about `Measure.pi`".

Both are supplied here, and the hypothesis is discharged outright. The
replacement assumption on `F` is **continuity**, which is strictly what (1)
asked for: on the compact space `GaugeField L` a continuous function is
automatically bounded, so no separate bound has to be carried.

## Method

`wilsonReducedPhiR β F U` is a partial Bochner integral over the `Λ_+`
component, so (2) is exactly the hypothesis of
`MeasureTheory.continuous_of_dominated`, and r360 supplies its dominating
bound:

* the glued field is continuous in each variable separately (§1) — proved
  pointwise through `gaugeFieldGluePlus_apply_plus` / `_apply_pnot`, so no
  product-topology machinery is needed;
* `F` times the refined Boltzmann factor is continuous (§2), using
  r360's `wilsonActionPlusR_continuous`;
* that composite is bounded, because `GaugeField L` is compact
  (`gaugeField_compactSpace`) — this is r360's `isCompact_range` +
  `IsCompact.bddAbove` idiom (§3);
* so the dominating function is a *constant*, integrable because
  `Measure.pi` of Haar probability measures is finite (§4).

Continuity of `Φ` then gives integrability of `star (Φ i) * Φ j` against
`wilsonBaseMeasure`, a probability measure, by the same compactness bound (§5).

## What is NOT claimed

`hFubini` is untouched and remains the last hypothesis on the headline. This
file does not prove reflection positivity; it removes one of the two
assumptions under which the headline already proved it.

## Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-28.
-/
import PF.YangMills.WilsonReducedPhiR_2026_10_23
import PF.YangMills.WilsonSectorActionBounded_r360
import PF.YangMills.WilsonRPFubiniApplyR_2026_10_23

set_option autoImplicit false

namespace PF.YangMills

open MeasureTheory
-- `Matrix.PosSemidef` over `ℂ` needs the complex order; `open scoped` does not
-- cross imports, so the headline's own scoped open has to be repeated here.
open scoped ComplexOrder

noncomputable section

variable {L : ℕ} [NeZero L]

/-! ## §1 — The glued field is continuous in each variable separately

Both proofs go coordinate by coordinate: at a link `ℓ` the glued field reads
from `V` when `isPlusLink ℓ` and from `W` otherwise, and in each case the
coordinate map is either a projection or a constant. -/

/-- `restrictNonPlus` is continuous (companion to `restrictNonPlus_measurable`). -/
lemma restrictNonPlus_continuous :
    Continuous (restrictNonPlus (L := L)) := by
  unfold restrictNonPlus
  exact continuous_pi fun ℓ => continuous_apply ℓ.val

/-- With the non-`Λ_+` part fixed, the glued field is continuous in `V`. -/
lemma gluePlus_continuous_in_V (U : GaugeField L) :
    Continuous (fun V : Subtype (isPlusLink : LatticeLink L → Prop) → SU2 =>
      gaugeFieldGluePlus V (restrictNonPlus U)) := by
  refine continuous_pi fun ℓ => ?_
  by_cases h : isPlusLink ℓ
  · simp only [gaugeFieldGluePlus_apply_plus _ _ h]
    exact continuous_apply _
  · simp only [gaugeFieldGluePlus_apply_pnot _ _ h]
    exact continuous_const

/-- With the `Λ_+` part fixed, the glued field is continuous in `U`. -/
lemma gluePlus_continuous_in_U
    (V : Subtype (isPlusLink : LatticeLink L → Prop) → SU2) :
    Continuous (fun U : GaugeField L =>
      gaugeFieldGluePlus V (restrictNonPlus U)) := by
  refine continuous_pi fun ℓ => ?_
  by_cases h : isPlusLink ℓ
  · simp only [gaugeFieldGluePlus_apply_plus _ _ h]
    exact continuous_const
  · simp only [gaugeFieldGluePlus_apply_pnot _ _ h]
    simpa [restrictNonPlus] using continuous_apply ℓ

/-! ## §2 — `F` weighted by the refined-sector Boltzmann factor -/

/-- The integrand of `wilsonReducedPhiR`, as a function of the glued field
alone. By construction `wilsonReducedPhiR β F U = ∫ V, weightedPlusR β F (glue
V (restrictNonPlus U))`, definitionally. -/
def weightedPlusR (β : ℝ) (F : GaugeField L → ℂ) : GaugeField L → ℂ :=
  fun W => F W * (Real.exp (-β * wilsonActionPlusR W) : ℂ)

/-- `weightedPlusR` is continuous whenever `F` is — this is where r360's
`wilsonActionPlusR_continuous` enters. -/
lemma weightedPlusR_continuous (β : ℝ) (F : GaugeField L → ℂ)
    (hF : Continuous F) :
    Continuous (weightedPlusR β F) := by
  unfold weightedPlusR
  exact hF.mul (Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp (continuous_const.mul wilsonActionPlusR_continuous)))

/-- The definitional unfolding of `wilsonReducedPhiR` through `weightedPlusR`. -/
lemma wilsonReducedPhiR_eq_integral (β : ℝ) (F : GaugeField L → ℂ)
    (U : GaugeField L) :
    wilsonReducedPhiR β F U =
      ∫ V : Subtype (isPlusLink : LatticeLink L → Prop) → SU2,
        weightedPlusR β F (gaugeFieldGluePlus V (restrictNonPlus U))
        ∂(Measure.pi (fun _ : Subtype (isPlusLink : LatticeLink L → Prop) =>
            SU2_haar)) :=
  rfl

/-! ## §3 — Compactness gives a uniform bound

`GaugeField L` is compact (`gaugeField_compactSpace`), so a continuous
`ℂ`-valued function on it has bounded norm. This is r360's own idiom. -/

lemma exists_norm_bound (G : GaugeField L → ℂ) (hG : Continuous G) :
    ∃ C : ℝ, ∀ W : GaugeField L, ‖G W‖ ≤ C := by
  have hbdd : BddAbove (Set.range fun W : GaugeField L => ‖G W‖) :=
    (isCompact_range hG.norm).bddAbove
  obtain ⟨C, hC⟩ := hbdd
  exact ⟨C, fun W => hC ⟨W, rfl⟩⟩

/-! ## §4 — `Φ` is continuous: the `Measure.pi` parametric integral

This is the piece r360 named as missing. -/

/-- **★★★ r361: the refined `Φ` is continuous ★★★**

`wilsonReducedPhiR β F` is continuous whenever `F` is. The dominating
function is a constant, supplied by §3 and legitimate because
`Measure.pi` of probability measures is finite. -/
theorem wilsonReducedPhiR_continuous (β : ℝ) (F : GaugeField L → ℂ)
    (hF : Continuous F) :
    Continuous (wilsonReducedPhiR β F) := by
  obtain ⟨C, hC⟩ := exists_norm_bound (weightedPlusR β F)
    (weightedPlusR_continuous β F hF)
  -- `wilsonReducedPhiR` is definitionally this integral (`wilsonReducedPhiR_eq_integral`
  -- is `rfl`), but `simp` cannot rewrite under the binder, so change the goal by `show`.
  show Continuous fun U : GaugeField L =>
      ∫ V : Subtype (isPlusLink : LatticeLink L → Prop) → SU2,
        weightedPlusR β F (gaugeFieldGluePlus V (restrictNonPlus U))
        ∂(Measure.pi fun _ : Subtype (isPlusLink : LatticeLink L → Prop) =>
            SU2_haar)
  exact continuous_of_dominated (bound := fun _ => C)
    (fun U => ((weightedPlusR_continuous β F hF).comp
      (gluePlus_continuous_in_V U)).aestronglyMeasurable)
    (fun U => Filter.Eventually.of_forall fun V => hC _)
    (integrable_const C)
    (Filter.Eventually.of_forall fun V =>
      (weightedPlusR_continuous β F hF).comp (gluePlus_continuous_in_U V))

/-- `Φ` is measurable — immediate from continuity, and the second of the two
things r360 asked for. -/
theorem wilsonReducedPhiR_measurable (β : ℝ) (F : GaugeField L → ℂ)
    (hF : Continuous F) :
    Measurable (wilsonReducedPhiR β F) :=
  (wilsonReducedPhiR_continuous β F hF).measurable

/-! ## §5 — `hΦ_integrable`, discharged -/

/-- **★★★ r361: `hΦ_integrable` for the refined `Φ` ★★★**

The integrand of the RP headline's hypothesis is integrable against
`wilsonBaseMeasure`, for continuous test functions. -/
theorem wilsonReducedPhiR_integrable_star_mul (β : ℝ)
    (F G : GaugeField L → ℂ) (hF : Continuous F) (hG : Continuous G) :
    Integrable (fun U => star (wilsonReducedPhiR β F U) *
      wilsonReducedPhiR β G U) (wilsonBaseMeasure L) := by
  have hcont : Continuous (fun U : GaugeField L =>
      star (wilsonReducedPhiR β F U) * wilsonReducedPhiR β G U) :=
    (continuous_star.comp (wilsonReducedPhiR_continuous β F hF)).mul
      (wilsonReducedPhiR_continuous β G hG)
  -- On a compact space every function has compact support, so continuity alone
  -- suffices against the finite `wilsonBaseMeasure`.
  exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-! ## §6 — The headline with `hΦ_integrable` removed

Only `hFubini` remains. -/

/-- **★★★ r361: Wilson RP for continuous test functions, `hΦ_integrable`
discharged ★★★**

Compare `wilson_reflection_positivity_withReducedPhiR`, which assumes
`hΦ_integrable`. Here it is *proved* from continuity of the `F i`. -/
theorem wilson_reflection_positivity_withReducedPhiR_of_continuous
    {K : ℕ} (β : ℝ) (F : Fin K → GaugeField L → ℂ)
    (hF_support : ∀ i : Fin K, supportedOnPlusZero (F i))
    (hF_cont : ∀ i : Fin K, Continuous (F i))
    (hFubini : ∀ i j : Fin K,
      ∫ U, star (F i (timeReflectionGaugeField U)) * F j U
        ∂(wilsonGibbsMeasure L β)
      = ∫ U, star (wilsonReducedPhiR β (F i) U) * wilsonReducedPhiR β (F j) U
        ∂(wilsonBaseMeasure L)) :
    (Matrix.of (fun i j : Fin K =>
      ∫ U, star (F i (timeReflectionGaugeField U)) * F j U
        ∂(wilsonGibbsMeasure L β))).PosSemidef :=
  wilson_reflection_positivity_withReducedPhiR β F hF_support
    (fun i j => wilsonReducedPhiR_integrable_star_mul β (F i) (F j)
      (hF_cont i) (hF_cont j))
    hFubini

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.restrictNonPlus_continuous
#print axioms PF.YangMills.gluePlus_continuous_in_V
#print axioms PF.YangMills.gluePlus_continuous_in_U
#print axioms PF.YangMills.weightedPlusR_continuous
#print axioms PF.YangMills.exists_norm_bound
#print axioms PF.YangMills.wilsonReducedPhiR_continuous
#print axioms PF.YangMills.wilsonReducedPhiR_measurable
#print axioms PF.YangMills.wilsonReducedPhiR_integrable_star_mul
#print axioms PF.YangMills.wilson_reflection_positivity_withReducedPhiR_of_continuous
