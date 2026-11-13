/-
# PF.YangMills.WilsonBaseFubiniCollapse_2026_11_12

**Step 3c.4c ingredient**: when an integrand depends only on the
non-minus-link part of a gauge field, its integral against the base
measure equals the integral of the collapsed function against the
non-minus Pi Haar measure.

This is the "Fubini-collapse" identity used in the base-measure
L²-contraction of `avgMinus`: because `avgMinus F U` depends on `U`
only through `projectNonMinus U`, the outer integral over `U ∂μ_base`
collapses to an integral over the non-minus factor only.

Delivers:

* `nonMinusHaarMeasure` — `Measure.pi (fun _ : NonMinusLinks L => SU2_haar)`.
* `nonMinusHaarMeasure_isProbabilityMeasure` — `IsProbabilityMeasure`.
* `wilsonBaseMeasure_lintegral_collapse_projectNonMinus` — for any
  measurable `h : NonMinusGauge L → ℝ≥0∞`,

      `∫⁻ U, h (projectNonMinus U) ∂wilsonBaseMeasure L
          = ∫⁻ W, h W ∂nonMinusHaarMeasure L`.

Proof chain:
* Use `wilsonBaseMeasure_split_minus : MeasurePreserving (piEquivPiSubtypeProd ..)`.
* Compose with `MeasurePreserving.lintegral_map_equiv`.
* The post-split integrand `(U_m, U_n) ↦ h(U_n)` collapses via
  `lintegral_prod_const` / `lintegral_const_mul` since `μ_minus(univ) = 1`.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-12.
-/

import PF.YangMills.WilsonSectorMeasureSplit_2026_10_20
import PF.YangMills.WilsonMinusLinkAveraging_2026_11_12

namespace PF.YangMills

open MeasureTheory ENNReal

variable {L : ℕ} [NeZero L]

/-- The Haar product measure on `NonMinusGauge L` — Haar on each
non-minus link, independent across links.  -/
noncomputable def nonMinusHaarMeasure (L : ℕ) : Measure (NonMinusGauge L) :=
  Measure.pi (fun _ : NonMinusLinks L => SU2_haar)

/-- `nonMinusHaarMeasure L` is a probability measure. -/
instance nonMinusHaarMeasure_isProbabilityMeasure (L : ℕ) :
    IsProbabilityMeasure (nonMinusHaarMeasure L) :=
  inferInstanceAs (IsProbabilityMeasure
    (Measure.pi (fun _ : NonMinusLinks L => SU2_haar)))

/-- **Collapse identity**: for any measurable `h : NonMinusGauge L → ℝ≥0∞`
depending only on the non-minus part, the integral against the base
measure equals the integral against the non-minus Haar measure.

  `∫⁻ U, h (projectNonMinus U) ∂wilsonBaseMeasure L
      = ∫⁻ W, h W ∂nonMinusHaarMeasure L`.

Proof: via the sector split `wilsonBaseMeasure_split_minus`,
transport to the product measure and collapse the inner `minusHaarMeasure`
integral since `h` is constant in `V`. -/
theorem wilsonBaseMeasure_lintegral_collapse_projectNonMinus
    (h : NonMinusGauge L → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ U, h (projectNonMinus U) ∂(wilsonBaseMeasure L)
      = ∫⁻ W, h W ∂(nonMinusHaarMeasure L) := by
  -- Use the measure-preserving sector split.
  have hMP := wilsonBaseMeasure_split_minus (L := L)
  -- Transport the LHS integral via `lintegral_map_equiv`.
  -- `e : GaugeField L ≃ᵐ MinusGauge-ish × NonMinusGauge-ish`.
  set e := MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : LatticeLink L => SU2) (isMinusLink : LatticeLink L → Prop)
  -- We know `MeasurePreserving e (wilsonBaseMeasure L) (minusHaar × nonMinusHaar)`.
  -- `lintegral_map_equiv` gives:
  --   ∫⁻ U, (f ∘ e.symm ∘ e) U ∂μ_base = ∫⁻ p, (f ∘ e.symm) p ∂(e_*μ_base) = ∫⁻ p, f(e.symm p) ∂(prod)
  -- Apply with `f (V, W) := h W`.
  have h_meas_comp : Measurable (fun p : (MinusLinks L → SU2) × (NonMinusLinks L → SU2) =>
      h p.2) := hh.comp measurable_snd
  rw [show (fun U => h (projectNonMinus U))
        = (fun U => (fun p : (MinusLinks L → SU2) × (NonMinusLinks L → SU2) =>
                        h p.2) (e U)) from rfl]
  -- Now use `MeasurePreserving.lintegral_comp` for measure-preserving maps.
  rw [hMP.lintegral_comp h_meas_comp]
  -- Apply Tonelli on the specific product type.
  haveI : IsProbabilityMeasure
    (Measure.pi (fun _ : Subtype (isMinusLink : LatticeLink L → Prop) =>
      SU2_haar)) := by infer_instance
  -- Rewrite as iterated integral via Tonelli.  Because `h b.2` depends only on
  -- `b.2`, the outer integral over `b.1` is trivial on the probability measure.
  calc ∫⁻ b : (Subtype (isMinusLink : LatticeLink L → Prop) → SU2) ×
              ({ i // ¬ isMinusLink (L := L) i } → SU2),
        h b.2
          ∂((Measure.pi (fun _ : Subtype (isMinusLink : LatticeLink L → Prop) =>
              SU2_haar)).prod
            (Measure.pi (fun _ : Subtype
                (fun ℓ : LatticeLink L => ¬ isMinusLink ℓ) => SU2_haar)))
      = ∫⁻ _V, ∫⁻ W, h W
          ∂(Measure.pi (fun _ : Subtype
              (fun ℓ : LatticeLink L => ¬ isMinusLink ℓ) => SU2_haar))
          ∂(Measure.pi (fun _ : Subtype (isMinusLink : LatticeLink L → Prop) =>
              SU2_haar)) := by
          exact MeasureTheory.lintegral_prod _ h_meas_comp.aemeasurable
    _ = ∫⁻ W, h W
          ∂(Measure.pi (fun _ : Subtype
              (fun ℓ : LatticeLink L => ¬ isMinusLink ℓ) => SU2_haar)) := by
          rw [lintegral_const]; simp [measure_univ]
    _ = ∫⁻ W, h W ∂(nonMinusHaarMeasure L) := rfl

set_option linter.unusedSectionVars false in
/-- **Identification `gluePlusMinus = piEquivPiSubtypeProd.symm` on sectors.**
For any `W : NonMinusGauge L` and `V : MinusGauge L`,

  `gluePlusMinus W V = (piEquivPiSubtypeProd _ isMinusLink).symm (V, W)`

modulo the `isMinusLink ↔ linkSector = .minus` subtype identification.
This is the structural fact that makes the sector-split Fubini apply
to the reassembly of `avgMinus` integrals. -/
theorem gluePlusMinus_eq_piEquivSymm (W : NonMinusGauge L) (V : MinusGauge L) :
    (gluePlusMinus W V : GaugeField L)
      = (MeasurableEquiv.piEquivPiSubtypeProd
          (fun _ : LatticeLink L => SU2)
          (isMinusLink : LatticeLink L → Prop)).symm (V, W) := by
  funext ℓ
  unfold gluePlusMinus
  simp only [MeasurableEquiv.piEquivPiSubtypeProd_symm_apply]
  by_cases h : isMinusLink ℓ
  · have hne : ¬ (linkSector ℓ ≠ LinkSector.minus) := by
      unfold isMinusLink at h; exact fun hne => hne h
    simp [dif_neg hne, h]
  · have hne : linkSector ℓ ≠ LinkSector.minus := by
      unfold isMinusLink at h; exact h
    simp [dif_pos hne, h]

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.nonMinusHaarMeasure_isProbabilityMeasure
#print axioms PF.YangMills.wilsonBaseMeasure_lintegral_collapse_projectNonMinus
#print axioms PF.YangMills.gluePlusMinus_eq_piEquivSymm
