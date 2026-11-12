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

**UPDATE 2026-11-12**: on a thorough search of the YM tree, the key
infrastructure for this proof IS ALREADY PRESENT:

* **`wilsonBaseMeasure_split_minus`** (`WilsonSectorMeasureSplit_2026_10_20`)
  — the measure-preserving sector split via
  `measurePreserving_piEquivPiSubtypeProd` of `wilsonBaseMeasure` as
  `Haar_minus ⊗ Haar_nonMinus`.
* **`wilsonBaseMeasure_integral_split`** (same file) — Bochner Fubini
  on the split.
* **`wilsonBase_measurePreserving_split`** (`WilsonBaseMeasureSplit_r362`)
  — same for arbitrary decidable predicate.
* **`expWilsonActionPlusR_bddAbove_pos`** (`WilsonSectorActionBounded_r360`)
  — bounded-above-by-positive for exp(-β·wilsonActionPlusR). Similar
  lemmas for `_Zero` and `_MinusR`.

Missing from the tree:
* A strict LOWER bound `exp(-β·wilsonActionTotal) ≥ m > 0` (follows from
  continuity + compactness + positivity — mathlib has
  `IsCompact.exists_forall_le` for continuous functions on compact).
* The composition into the final `avgMinus` L²-bound — the main work.

Updated effort estimate: **~80-120 Lean lines** using the existing
infrastructure (vs. the ~150+ lines of from-scratch work previously
estimated).

Full proof outline (concrete chain):

**Setup.** `wilsonActionTotal` is continuous (`wilsonActionTotal_continuous`)
on the compact `GaugeField L`. Hence `isCompact_univ.bddAbove_image /
bddBelow_image` give `S_min ≤ wilsonActionTotal U ≤ S_max`. For β ≥ 0,
`m := exp(-β·S_max) ≤ exp(-β·wilsonActionTotal U) ≤ exp(-β·S_min) =: M`
with `m > 0`.

**Step 1: Jensen on μ_minus** (probability measure):

   `|avgMinus K U|² = |∫ K(glue (proj U) V') dμ_minus(V')|²
                   ≤ ∫ |K(glue (proj U) V')|² dμ_minus(V')`

(via `norm_integral_le_integral_norm` and Cauchy-Schwarz for probability measure).

**Step 2: Fubini-unfold `‖K‖²_{L²(μ_Gibbs)}` via existing infrastructure**.
Both `∫|avgMinus K|² dμ_Gibbs` and `∫|K|² dμ_Gibbs` unfold through:

   `μ_Gibbs = μ_base.withDensity (exp(-β·S))`
   `μ_base = Haar_minus ⊗ Haar_nonMinus` via `wilsonBaseMeasure_split_minus`.

So:
- `∫|K|² dμ_Gibbs = (1/Z) ∫∫ |K(glue W V)|² exp(-β·S(glue W V))
                     dμ_minus(V) dμ_nonMinus(W)`.
- `∫|avgMinus K|² dμ_Gibbs ≤ (1/Z) ∫∫ |K(glue W V')|² exp(-β·S(glue W V))
                              dμ_minus(V) dμ_minus(V') dμ_nonMinus(W)` (via Step 1).

**Step 3: Pointwise ratio bound.** The integrand of the Fubini-unfolded
`avgMinus K`²-integral has `|K(glue W V')|² · exp(-β·S(glue W V))` while
the direct `K`²-integral has `|K(glue W V)|² · exp(-β·S(glue W V))`.
Both integrals share the factor `exp(-β·S(glue W V))`; only the
argument of `|K|²` differs (V' vs V).  Separately:

   `∫ exp(-β·S(glue W V)) dμ_minus(V) ∈ [m, M]` (bound by extremes).

So we get `‖avgMinus K‖² ≤ (M/m) · ‖K‖²`, giving `C = √(M/m)`.

**Mathlib lemmas cited**:
* `IsCompact.bddAbove_image` + `IsCompact.bddBelow_image` (from `IsCompact.image`).
* `Real.exp_pos`, `Real.exp_le_exp` (monotonicity).
* `wilsonActionTotal_continuous` (already in tree).
* `norm_integral_le_integral_norm` + probability measure Cauchy-Schwarz.
* `integral_withDensity_eq_integral_smul` (integral vs withDensity).
* `wilsonBaseMeasure_integral_split` (EXISTS 2026-10-20) — Fubini via sector split.
* `integral_prod` (Fubini on product).
* `lintegral_mono` / `integral_mono_of_nonneg` (bound chain).

Below, we state this as a named hypothesis `WilsonAvgMinusL2Bound` and
derive the density composition conditional on it. Discharging the
hypothesis is bounded dedicated-session work on top of existing
infrastructure. -/

/-- **The L²-boundedness of `avgMinus` on bounded continuous input**,
stated as a named hypothesis (see outline above for the proof plan).

The hypothesis uses the stronger form `‖avgMinus (G - H)‖ ≤ C ·
‖G - H‖` for `G, H` bounded continuous — which, by linearity of the
Bochner integral in the integrand, is equivalent to `‖avgMinus G‖ ≤
C · ‖G‖` for individual bounded-continuous `G`. The pair form is used
directly in the density composition below. -/
def WilsonAvgMinusL2Bound (L : ℕ) [NeZero L] (β : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ G H : BoundedContinuousFunction (GaugeField L) ℂ,
      eLpNorm (fun U => avgMinus (G : GaugeField L → ℂ) U -
                        avgMinus (H : GaugeField L → ℂ) U) 2
        (wilsonGibbsMeasure L β)
        ≤ ENNReal.ofReal C *
          eLpNorm (fun U => (G : GaugeField L → ℂ) U -
                             (H : GaugeField L → ℂ) U) 2
            (wilsonGibbsMeasure L β)

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.minusHaarMeasure_isProbabilityMeasure
#print axioms PF.YangMills.projectNonMinus_gluePlusMinus
#print axioms PF.YangMills.avgMinus_supportedOnPlusZero
#print axioms PF.YangMills.avgMinus_eq_of_supportedOnPlusZero
#print axioms PF.YangMills.gluePlusMinus_continuous
#print axioms PF.YangMills.avgMinus_continuous
#print axioms PF.YangMills.WilsonAvgMinusL2Bound
