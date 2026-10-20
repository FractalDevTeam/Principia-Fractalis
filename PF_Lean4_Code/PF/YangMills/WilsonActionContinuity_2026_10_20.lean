/-
# Yang-Mills — Wilson action continuity + measurability (Legion step 1)

**Rio's Step 1, 2026-10-20.** The prerequisites for Fubini (step 6).
Everything from Phase B onward uses `wilsonActionTotal` either inside
`exp(−β · ·)` under an integral, or as a measurable function on the
compact gauge-field space.

### What this file provides

* `GaugeField.compactSpace` — the gauge-field space is compact (finite
  product of compact SU(2) factors).
* `plaquetteHolonomy_continuous_U` — for each fixed plaquette `p`, the
  map `U ↦ plaquetteHolonomy U p` is continuous.
* `wilsonActionDensity_continuous_U` — for each fixed `p`, the map
  `U ↦ wilsonActionDensity U p` is continuous.
* `wilsonActionTotal_continuous` — the total Wilson action is continuous
  on `GaugeField L`.
* `wilsonActionTotal_measurable` — hence measurable (Borel σ-algebra).
* `expWilsonDensity_measurable` — `U ↦ ENNReal.ofReal (exp(−β · S_W(U)))`
  is measurable, which is what `withDensity` consumes.
* `wilsonGibbsMeasure_isFiniteMeasure` — the Gibbs measure is finite
  (compact + continuous density + probability base).

### Why

Fubini on `∫_{Λ₊ ⊕ Λ₀ ⊕ Λ₋} exp(−β·S_W) dU` factorizes only when the
density is integrable; integrability on a finite measure requires
measurability and boundedness. Both follow from continuity on compact.

### Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-20.
-/
import PF.YangMills.WilsonSectorGaugeDependence_2026_10_20
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.Analysis.Matrix

set_option autoImplicit false

namespace PF.YangMills

open MeasureTheory Topology

noncomputable section

attribute [local instance] Matrix.seminormedAddCommGroup
attribute [local instance] Matrix.normedAddCommGroup
attribute [local instance] Matrix.normedSpace

/-- The ambient `Matrix (Fin 2) (Fin 2) ℂ` is second-countable (finite-dim normed
space over ℂ, hence ProperSpace, hence SecondCountable). Needed to lift
`SecondCountableTopology` to `SU2` via `Subtype.secondCountableTopology`. -/
instance matrix_fin2_C_secondCountableTopology :
    SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) := by
  haveI : ProperSpace (Matrix (Fin 2) (Fin 2) ℂ) :=
    FiniteDimensional.proper (𝕜 := ℂ) (Matrix (Fin 2) (Fin 2) ℂ)
  exact secondCountable_of_proper

/-- `SU2` is second-countable (Subtype of a second-countable ambient space). -/
instance SU2_secondCountableTopology : SecondCountableTopology SU2 := by
  show SecondCountableTopology
    (Matrix.specialUnitaryGroup (Fin 2) ℂ : Submonoid (Matrix (Fin 2) (Fin 2) ℂ))
  infer_instance

variable {L : ℕ} [NeZero L]

/-! ## §1 — Compactness of the gauge-field space. -/

/-- `GaugeField L` is compact (finite product of compact SU(2)). -/
instance gaugeField_compactSpace : CompactSpace (GaugeField L) :=
  Pi.compactSpace

/-! ## §2 — Continuity of the plaquette holonomy. -/

/-- The link-projection `U ↦ U(ℓ)` is continuous on `GaugeField L`
(product-topology projection). -/
lemma continuous_link_eval (ℓ : LatticeLink L) :
    Continuous (fun U : GaugeField L => U ℓ) :=
  continuous_apply ℓ

/-- Plaquette holonomy, viewed as a function of `U` for fixed `p`,
is continuous. -/
lemma plaquetteHolonomy_continuous_U (p : Plaquette L) :
    Continuous (fun U : GaugeField L => plaquetteHolonomy U p) := by
  unfold plaquetteHolonomy
  exact (((continuous_link_eval (p.1, p.2.1)).mul
            (continuous_link_eval (shiftSite p.1 p.2.1, p.2.2))).mul
         (continuous_link_eval (shiftSite p.1 p.2.2, p.2.1)).inv).mul
        (continuous_link_eval (p.1, p.2.2)).inv

/-! ## §3 — Continuity of the Wilson action density. -/

/-- The subtype-value map `SU2 → Matrix (Fin 2) (Fin 2) ℂ` is continuous
(subtype coercion). -/
lemma continuous_SU2_val : Continuous (fun X : SU2 => (X : Matrix (Fin 2) (Fin 2) ℂ)) :=
  continuous_subtype_val

/-- Wilson action density, for fixed `p`, is continuous in `U`. -/
lemma wilsonActionDensity_continuous_U (p : Plaquette L) :
    Continuous (fun U : GaugeField L => wilsonActionDensity U p) := by
  unfold wilsonActionDensity
  refine Continuous.sub continuous_const ?_
  refine Continuous.mul continuous_const ?_
  refine Complex.continuous_re.comp ?_
  refine Continuous.matrix_trace ?_
  exact continuous_SU2_val.comp (plaquetteHolonomy_continuous_U p)

/-! ## §4 — Continuity of the total Wilson action. -/

/-- **`wilsonActionTotal` is continuous.** -/
theorem wilsonActionTotal_continuous :
    Continuous (wilsonActionTotal : GaugeField L → ℝ) := by
  unfold wilsonActionTotal
  exact continuous_finset_sum _ (fun p _ => wilsonActionDensity_continuous_U p)

/-! ## §5 — Measurability. -/

/-- `wilsonActionTotal` is measurable (continuous on a Borel space). -/
theorem wilsonActionTotal_measurable :
    Measurable (wilsonActionTotal : GaugeField L → ℝ) :=
  wilsonActionTotal_continuous.measurable

/-- The exponential Boltzmann density, as an `ℝ`-valued function. -/
lemma expWilsonDensityReal_continuous (β : ℝ) :
    Continuous (fun U : GaugeField L => Real.exp (-β * wilsonActionTotal U)) := by
  exact Real.continuous_exp.comp (continuous_const.mul wilsonActionTotal_continuous)

/-- **The exp-density is measurable** as an `ℝ≥0∞`-valued function
(what `Measure.withDensity` consumes). -/
theorem expWilsonDensity_measurable (β : ℝ) :
    Measurable (fun U : GaugeField L =>
      ENNReal.ofReal (Real.exp (-β * wilsonActionTotal U))) :=
  ENNReal.measurable_ofReal.comp (expWilsonDensityReal_continuous β).measurable

/-! ## §6 — Finiteness of the Gibbs measure. -/

/-- The exp-density is bounded above by `M` where `M` is any upper bound on
`exp(−β · wilsonActionTotal U)` over the compact gauge space. Combined with
the base measure being a probability measure, the resulting Gibbs measure
is finite. -/
theorem wilsonGibbsMeasure_isFiniteMeasure (β : ℝ) :
    IsFiniteMeasure (wilsonGibbsMeasure L β) := by
  unfold wilsonGibbsMeasure
  -- Compact + continuous ⇒ bounded above
  have h_range_compact : IsCompact
      (Set.range (fun U : GaugeField L => Real.exp (-β * wilsonActionTotal U))) :=
    isCompact_range (expWilsonDensityReal_continuous β)
  have h_bdd : BddAbove
      (Set.range (fun U : GaugeField L => Real.exp (-β * wilsonActionTotal U))) :=
    h_range_compact.bddAbove
  obtain ⟨M, hM⟩ := h_bdd
  refine ⟨?_⟩
  rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ]
  have h_bound :
      ∫⁻ U in Set.univ,
          ENNReal.ofReal (Real.exp (-β * wilsonActionTotal U))
            ∂(wilsonBaseMeasure L)
        ≤ ENNReal.ofReal M * (wilsonBaseMeasure L) Set.univ := by
    calc ∫⁻ U in Set.univ,
            ENNReal.ofReal (Real.exp (-β * wilsonActionTotal U))
              ∂(wilsonBaseMeasure L)
        ≤ ∫⁻ _ in Set.univ, ENNReal.ofReal M ∂(wilsonBaseMeasure L) := by
          apply MeasureTheory.setLIntegral_mono measurable_const
          intro U _
          exact ENNReal.ofReal_le_ofReal (hM ⟨U, rfl⟩)
      _ = ENNReal.ofReal M * (wilsonBaseMeasure L) Set.univ := by
          rw [setLIntegral_const]
  calc ∫⁻ U in Set.univ,
          ENNReal.ofReal (Real.exp (-β * wilsonActionTotal U))
            ∂(wilsonBaseMeasure L)
      ≤ ENNReal.ofReal M * (wilsonBaseMeasure L) Set.univ := h_bound
    _ < ⊤ := by
        rw [measure_univ]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by norm_num)

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.gaugeField_compactSpace
#print axioms PF.YangMills.continuous_link_eval
#print axioms PF.YangMills.plaquetteHolonomy_continuous_U
#print axioms PF.YangMills.continuous_SU2_val
#print axioms PF.YangMills.wilsonActionDensity_continuous_U
#print axioms PF.YangMills.wilsonActionTotal_continuous
#print axioms PF.YangMills.wilsonActionTotal_measurable
#print axioms PF.YangMills.expWilsonDensityReal_continuous
#print axioms PF.YangMills.expWilsonDensity_measurable
#print axioms PF.YangMills.wilsonGibbsMeasure_isFiniteMeasure
