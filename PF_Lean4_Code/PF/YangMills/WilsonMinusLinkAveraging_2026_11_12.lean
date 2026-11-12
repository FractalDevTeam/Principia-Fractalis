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

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.minusHaarMeasure_isProbabilityMeasure
#print axioms PF.YangMills.projectNonMinus_gluePlusMinus
#print axioms PF.YangMills.avgMinus_supportedOnPlusZero
#print axioms PF.YangMills.avgMinus_eq_of_supportedOnPlusZero
