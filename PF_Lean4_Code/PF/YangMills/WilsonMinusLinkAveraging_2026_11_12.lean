/-
# PF.YangMills.WilsonMinusLinkAveraging_2026_11_12

**Route B for YM L² extension step 3c.4** — the minus-link averaging
operator.

Delivers:

* `MinusLinks L` — the subtype of minus-sector lattice links.
* `MinusGauge L := MinusLinks L → SU2`.
* `gluePlusMinus : NonMinusGauge L → MinusGauge L → GaugeField L` —
  the glue map joining a non-minus restriction with a minus
  assignment.
* `avgMinus G U := ∫ V, G (gluePlusMinus (projectNonMinus U) V) dμ_minus(V)`
  — the minus-link averaging operator.
* Core properties:
  - `avgMinus` is `supportedOnPlusZero` output always.
  - `avgMinus F = F` when `F` is `supportedOnPlusZero`.

Not yet delivered: `avgMinus` continuity and `L²` boundedness (step 3c.4
proper). Those require parametric integral continuity on compact
spaces + a Fubini-based L²-boundedness argument.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-12.
-/

import PF.YangMills.WilsonNonMinusProjection_2026_11_12
import PF.YangMills.WilsonGibbsMeasurePreserving_2026_11_11
import Mathlib.Topology.ContinuousMap.Bounded.Basic

namespace PF.YangMills

open MeasureTheory

variable {L : ℕ} [NeZero L]

/-- The subtype of lattice links in the `minus` sector. -/
abbrev MinusLinks (L : ℕ) : Type :=
  {ℓ : LatticeLink L // linkSector ℓ = LinkSector.minus}

/-- Minus-sector gauge configurations: assignments on `MinusLinks L`. -/
abbrev MinusGauge (L : ℕ) : Type := MinusLinks L → SU2

/-- The Haar product measure on `MinusGauge L` — Haar on each
minus-link, independent across links.  The averaging operator below
integrates against this measure. -/
noncomputable def minusHaarMeasure (L : ℕ) : Measure (MinusGauge L) :=
  Measure.pi (fun _ : MinusLinks L => SU2_haar)

/-- The minus Haar measure is a probability measure. -/
instance minusHaarMeasure_isProbabilityMeasure (L : ℕ) :
    IsProbabilityMeasure (minusHaarMeasure L) :=
  inferInstanceAs (IsProbabilityMeasure
    (Measure.pi (fun _ : MinusLinks L => SU2_haar)))

/-- **Glue** a non-minus assignment and a minus assignment into a full
gauge-field configuration. -/
def gluePlusMinus (U' : NonMinusGauge L) (V' : MinusGauge L) : GaugeField L :=
  fun ℓ => if h : linkSector ℓ ≠ LinkSector.minus
            then U' ⟨ℓ, h⟩
            else V' ⟨ℓ, not_not.mp (by exact fun hne => h hne)⟩

/-- Projecting a glued configuration recovers the non-minus side. -/
theorem projectNonMinus_gluePlusMinus (U' : NonMinusGauge L) (V' : MinusGauge L) :
    projectNonMinus (gluePlusMinus U' V') = U' := by
  funext ℓ
  show gluePlusMinus U' V' ℓ.1 = U' ℓ
  simp only [gluePlusMinus]
  rw [dif_pos ℓ.2]

/-- The minus-link averaging operator.  For `G : GaugeField L → ℂ`,

    `(avgMinus G)(U) := ∫ V, G (gluePlusMinus (projectNonMinus U) V) dμ_minus(V)`.

The resulting function depends only on `projectNonMinus U` (it is
`supportedOnPlusZero` by construction).  If `G` is continuous, so is
`avgMinus G` (via parametric-integral continuity). -/
noncomputable def avgMinus (G : GaugeField L → ℂ) (U : GaugeField L) : ℂ :=
  ∫ V, G (gluePlusMinus (projectNonMinus U) V) ∂(minusHaarMeasure L)

/-- **`avgMinus G` is always `supportedOnPlusZero`.**  The output
depends only on `projectNonMinus U`, hence agrees for any two inputs
that agree on all non-minus links. -/
theorem avgMinus_supportedOnPlusZero (G : GaugeField L → ℂ) :
    supportedOnPlusZero (avgMinus G) := by
  intro U₁ U₂ hU
  unfold avgMinus
  congr 1
  funext V
  congr 2
  funext ℓ
  exact hU ℓ.1 ℓ.2

/-- **`avgMinus F = F` when `F` is `supportedOnPlusZero`.**  If `F`
only depends on non-minus links, then `F(gluePlusMinus (projectNonMinus
U) V)` equals `F U` regardless of `V` (since the glue agrees with `U`
on all non-minus links), and integrating a constant over a probability
measure returns the constant. -/
theorem avgMinus_eq_of_supportedOnPlusZero
    (F : GaugeField L → ℂ) (hF : supportedOnPlusZero F) (U : GaugeField L) :
    avgMinus F U = F U := by
  unfold avgMinus
  have h_const : ∀ V : MinusGauge L,
      F (gluePlusMinus (projectNonMinus U) V) = F U := by
    intro V
    apply hF
    intro ℓ hℓ
    show gluePlusMinus (projectNonMinus U) V ℓ = U ℓ
    simp only [gluePlusMinus]
    rw [dif_pos hℓ]
    rfl
  simp_rw [h_const]
  simp

/-! ## §Continuity of `avgMinus` under bounded continuous input

For bounded continuous `G : BoundedContinuousFunction (GaugeField L) ℂ`, the averaged
`avgMinus G` is continuous.  Proof: mathlib's `continuous_of_dominated`
on the parametric integral, with domination by the global bound on
`G`. -/

/-- `gluePlusMinus` is continuous in both arguments (coordinate
projection on a finite product). -/
theorem gluePlusMinus_continuous :
    Continuous (fun p : NonMinusGauge L × MinusGauge L =>
      gluePlusMinus p.1 p.2) := by
  refine continuous_pi fun ℓ => ?_
  by_cases h : linkSector ℓ ≠ LinkSector.minus
  · -- The link is non-minus: the glue entry is p.1 ⟨ℓ, h⟩.
    simp only [gluePlusMinus]
    have : (fun p : NonMinusGauge L × MinusGauge L =>
        if h' : linkSector ℓ ≠ LinkSector.minus
          then p.1 ⟨ℓ, h'⟩
          else p.2 ⟨ℓ, not_not.mp (fun hne => h' hne)⟩)
          = fun p => p.1 ⟨ℓ, h⟩ := by
      funext p
      rw [dif_pos h]
    rw [this]
    exact (continuous_apply _).comp continuous_fst
  · -- The link is minus: the glue entry is p.2 ⟨ℓ, _⟩.
    simp only [gluePlusMinus]
    have hh : linkSector ℓ = LinkSector.minus := not_not.mp h
    have : (fun p : NonMinusGauge L × MinusGauge L =>
        if h' : linkSector ℓ ≠ LinkSector.minus
          then p.1 ⟨ℓ, h'⟩
          else p.2 ⟨ℓ, not_not.mp (fun hne => h' hne)⟩)
          = fun p => p.2 ⟨ℓ, hh⟩ := by
      funext p
      rw [dif_neg h]
    rw [this]
    exact (continuous_apply _).comp continuous_snd

/-- **`avgMinus (G : BoundedContinuousFunction (GaugeField L) ℂ)` is continuous.**  Direct from
mathlib's `continuous_of_dominated` applied to the parametric integral,
with domination by the uniform bound on bounded-continuous `G`. -/
theorem avgMinus_continuous (G : BoundedContinuousFunction (GaugeField L) ℂ) :
    Continuous (avgMinus (G : GaugeField L → ℂ)) := by
  unfold avgMinus
  refine continuous_of_dominated (bound := fun _ : MinusGauge L => ‖G‖) ?_ ?_ ?_ ?_
  -- hF_meas: for each U, the integrand in V is measurable (in fact continuous).
  · intro U
    refine Continuous.aestronglyMeasurable ?_
    have h₁ : Continuous (fun V : MinusGauge L => (projectNonMinus U, V)) :=
      continuous_const.prodMk continuous_id
    have h₂ : Continuous (fun V : MinusGauge L =>
        gluePlusMinus (projectNonMinus U) V) :=
      gluePlusMinus_continuous.comp h₁
    exact G.continuous.comp h₂
  -- h_bound: uniform bound by ‖G‖ (bounded continuous).
  · intro U
    filter_upwards with V
    exact G.norm_coe_le_norm _
  -- bound_integrable: constant is integrable on finite measure.
  · exact integrable_const _
  -- h_cont: for each V, U ↦ G(glue (projNonMinus U) V) is continuous.
  · filter_upwards with V
    have h₁ : Continuous (fun U : GaugeField L => (projectNonMinus U, V)) :=
      projectNonMinus_continuous.prodMk continuous_const
    have h₂ : Continuous (fun U : GaugeField L =>
        gluePlusMinus (projectNonMinus U) V) :=
      gluePlusMinus_continuous.comp h₁
    exact G.continuous.comp h₂

/-! ## §L²-boundedness of `avgMinus` — the step-3c.4c hypothesis

Target: `‖avgMinus G‖_{L²(μ_Gibbs)} ≤ C · ‖G‖_{L²(μ_Gibbs)}` for some
finite `C` and all bounded-continuous `G`, with `C = e^{β·(S_max − S_min)}`.

Full proof outline:
1. **Jensen**: `|avgMinus G U|² ≤ ∫ |G(glue (proj U) V)|² dμ_minus(V)`
   (since μ_minus is a probability measure, Cauchy-Schwarz gives this).
2. **Integrate**: `‖avgMinus G‖²_{L²(μ_Gibbs)} ≤ ∫∫ |G(glue (proj U) V)|²
   dμ_minus dμ_Gibbs`.
3. **Product-measure factorization**: `wilsonBaseMeasure = Haar_nm ⊗ μ_minus`
   (via the LatticeLink partition → non-minus ⊕ minus; mathlib's
   `Measure.pi` factoring on finite disjoint unions).
4. **Fubini + `μ_Gibbs = exp(-βS)·μ_base`**: both sides unfold to
   integrals over `(U_nm, V, V')` with weight `exp(-βS)` applied once
   to `glue U_nm V'` on the avg-side vs `glue U_nm V` on the direct side.
5. **Pointwise bound**: the integrand ratio is
   `W(U_nm)·exp(βS(glue U_nm V))` where `W(U_nm) := ∫ exp(-βS(glue U_nm V'))
   dμ_minus(V')`.  Using `S_min ≤ S ≤ S_max` (continuous on compact)
   this is bounded by `C := e^{β(S_max − S_min)}`.

Each step is doable in mathlib but the product-measure factorization
(step 3) is the main structural work. Estimated 100-150 lines total.

Below, we state this as a named hypothesis `WilsonAvgMinusL2Bound` and
derive the density composition conditional on it. Discharging the
hypothesis is a dedicated-session task. -/

/-- **The L²-boundedness of `avgMinus` on bounded continuous input**,
stated as a named hypothesis (see outline above for the proof plan). -/
def WilsonAvgMinusL2Bound (L : ℕ) [NeZero L] (β : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ G : BoundedContinuousFunction (GaugeField L) ℂ,
      eLpNorm (avgMinus (G : GaugeField L → ℂ)) 2 (wilsonGibbsMeasure L β)
        ≤ ENNReal.ofReal C *
          eLpNorm (G : GaugeField L → ℂ) 2 (wilsonGibbsMeasure L β)

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.minusHaarMeasure_isProbabilityMeasure
#print axioms PF.YangMills.projectNonMinus_gluePlusMinus
#print axioms PF.YangMills.avgMinus_supportedOnPlusZero
#print axioms PF.YangMills.avgMinus_eq_of_supportedOnPlusZero
#print axioms PF.YangMills.gluePlusMinus_continuous
#print axioms PF.YangMills.avgMinus_continuous
#print axioms PF.YangMills.WilsonAvgMinusL2Bound
