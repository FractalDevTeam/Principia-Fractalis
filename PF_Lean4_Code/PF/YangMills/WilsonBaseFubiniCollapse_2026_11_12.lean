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

/-- **Fubini reassemble** — the "assembly" direction.  For any
measurable `f : GaugeField L → ℝ≥0∞`,

  `∫⁻ W, ∫⁻ V, f (gluePlusMinus W V) ∂minusHaarMeasure ∂nonMinusHaarMeasure
      = ∫⁻ U, f U ∂wilsonBaseMeasure L`.

Proof: via the sector-split MeasurePreserving `wilsonBaseMeasure_split_minus`
and `lintegral_prod_swap`.  Pattern mirrors mathlib's `lintegral_prod_symm`. -/
theorem wilsonBaseMeasure_lintegral_reassemble_glue
    (f : GaugeField L → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ W, ∫⁻ V, f (gluePlusMinus W V) ∂(minusHaarMeasure L)
        ∂(nonMinusHaarMeasure L)
      = ∫⁻ U, f U ∂(wilsonBaseMeasure L) := by
  have hMP := wilsonBaseMeasure_split_minus (L := L)
  set e := MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : LatticeLink L => SU2) (isMinusLink : LatticeLink L → Prop) with he_def
  -- Measurability of `f ∘ e.symm`.
  have h_fe_meas :
      Measurable (fun p : (MinusLinks L → SU2) × (NonMinusLinks L → SU2) =>
                    f (e.symm p)) :=
    hf.comp e.symm.measurable
  -- Step 1: Transport RHS via hMP to the product space.
  --   ∫⁻ U, f U ∂μ_base = ∫⁻ p, f (e.symm p) ∂(μ_minus × μ_nonMinus).
  have hRHS :
      ∫⁻ U, f U ∂(wilsonBaseMeasure L)
        = ∫⁻ p : (MinusLinks L → SU2) × (NonMinusLinks L → SU2),
            f (e.symm p)
              ∂((minusHaarMeasure L).prod (nonMinusHaarMeasure L)) := by
    have := hMP.lintegral_comp h_fe_meas
    -- `this : ∫⁻ a, (fun p => f (e.symm p)) (e a) ∂μ_base = ∫⁻ p, f (e.symm p) ∂(prod)`.
    -- LHS simplifies to `∫⁻ a, f a ∂μ_base`.
    simpa [MeasurableEquiv.symm_apply_apply] using this
  -- Step 2: Apply `lintegral_prod_swap` to flip the product order.
  --   ∫⁻ q, (f ∘ e.symm) q.swap ∂(nonMinus × minus) = ∫⁻ p, (f ∘ e.symm) p ∂(minus × nonMinus).
  have h_swap :
      ∫⁻ p : (MinusLinks L → SU2) × (NonMinusLinks L → SU2),
            f (e.symm p)
              ∂((minusHaarMeasure L).prod (nonMinusHaarMeasure L))
        = ∫⁻ q : (NonMinusLinks L → SU2) × (MinusLinks L → SU2),
            f (e.symm q.swap)
              ∂((nonMinusHaarMeasure L).prod (minusHaarMeasure L)) := by
    exact (MeasureTheory.lintegral_prod_swap (μ := minusHaarMeasure L)
            (ν := nonMinusHaarMeasure L) (fun p => f (e.symm p))).symm
  -- Step 3: Rewrite the LHS of the goal using `lintegral_prod` (Tonelli), reverse direction.
  have h_LHS_prod :
      ∫⁻ W, ∫⁻ V, f (gluePlusMinus W V) ∂(minusHaarMeasure L)
          ∂(nonMinusHaarMeasure L)
        = ∫⁻ q : (NonMinusLinks L → SU2) × (MinusLinks L → SU2),
            f (gluePlusMinus q.1 q.2)
              ∂((nonMinusHaarMeasure L).prod (minusHaarMeasure L)) := by
    have h_glue_meas :
        Measurable (fun q : (NonMinusLinks L → SU2) × (MinusLinks L → SU2) =>
                      f (gluePlusMinus q.1 q.2)) := by
      refine hf.comp ?_
      refine gluePlusMinus_continuous.measurable.comp ?_
      exact Measurable.prodMk measurable_fst measurable_snd
    exact (MeasureTheory.lintegral_prod _ h_glue_meas.aemeasurable).symm
  -- Step 4: Identify `f (gluePlusMinus q.1 q.2)` with `f (e.symm q.swap)`.
  -- `gluePlusMinus q.1 q.2 = e.symm (q.2, q.1) = e.symm q.swap`.
  have h_glue_eq_eswap :
      ∀ q : (NonMinusLinks L → SU2) × (MinusLinks L → SU2),
        f (gluePlusMinus q.1 q.2) = f (e.symm q.swap) := by
    intro q
    rw [gluePlusMinus_eq_piEquivSymm]
    rfl
  -- Combine: LHS = ∫⁻ q, f(glue q.1 q.2) d(ν_nm × μ_m) = ∫⁻ q, f(e.symm q.swap) d(ν_nm × μ_m)
  --        = ∫⁻ p, f(e.symm p) d(μ_m × ν_nm)                              [h_swap.symm]
  --        = ∫⁻ U, f U dμ_base                                             [hRHS.symm]
  rw [h_LHS_prod]
  rw [show (fun q : (NonMinusLinks L → SU2) × (MinusLinks L → SU2) =>
              f (gluePlusMinus q.1 q.2))
        = (fun q => f (e.symm q.swap)) from funext h_glue_eq_eswap]
  rw [← h_swap, ← hRHS]

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.nonMinusHaarMeasure_isProbabilityMeasure
#print axioms PF.YangMills.wilsonBaseMeasure_lintegral_collapse_projectNonMinus
#print axioms PF.YangMills.gluePlusMinus_eq_piEquivSymm
#print axioms PF.YangMills.wilsonBaseMeasure_lintegral_reassemble_glue
