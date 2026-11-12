/-
# PF.YangMills.WilsonNonMinusProjection_2026_11_12

**Step 3 foundations** for the YM L²-extension plan — the
non-minus-link projection apparatus.

`LatticeLink L` partitions into `minusLinks` (where
`linkSector ℓ = .minus`) and `nonMinusLinks` (the complement).  A
`GaugeField L` restricted to `nonMinusLinks` sits in a smaller product
space `NonMinusGauge L`.

This file defines:

* `NonMinusLinks L`     — the subtype of non-minus links.
* `NonMinusGauge L`     — functions `NonMinusLinks L → SU2`.
* `projectNonMinus`     — the restriction map `GaugeField L → NonMinusGauge L`.

and proves:

* `projectNonMinus_continuous` — the projection is continuous
  (coordinate projection on a finite product).
* `projectNonMinus_measurable` — the projection is measurable.
* `supportedOnPlusZero_iff_factors` — the key characterisation:
  `F` is `supportedOnPlusZero` ↔ `F` factors through `projectNonMinus`.

The `supportedOnPlusZero_iff_factors` characterisation is the structural
core of step 3: once a function is known to factor through the
projection, the density of continuous-in-L² argument pushes back
through the projection and preserves the factoring (hence preserves
`supportedOnPlusZero`).

Not yet delivered: the measure pushforward identity and composition
with mathlib's `MemLp.exists_boundedContinuous_eLpNorm_sub_le`. Those
are the ~40 remaining lines in step 3.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-12.
-/

import PF.YangMills.WilsonReflectionPositivity_2026_10_20
import PF.YangMills.WilsonSectorDecomposition_2026_10_19

namespace PF.YangMills

open MeasureTheory

variable {L : ℕ}

/-- The subtype of lattice links that are NOT in the `minus` sector. -/
abbrev NonMinusLinks (L : ℕ) : Type :=
  {ℓ : LatticeLink L // linkSector ℓ ≠ LinkSector.minus}

/-- The restricted gauge-field space, indexed by non-minus links only. -/
abbrev NonMinusGauge (L : ℕ) : Type := NonMinusLinks L → SU2

/-- The natural projection: a `GaugeField L` restricted to non-minus
links gives a `NonMinusGauge L`. -/
def projectNonMinus (U : GaugeField L) : NonMinusGauge L :=
  fun ℓ => U ℓ.1

/-- **Projection is continuous.**  Each coordinate `(projectNonMinus U) ℓ
= U ℓ.1` is continuous in `U` (coordinate projection on a finite
product), and a function into a finite product is continuous iff each
coordinate is. -/
theorem projectNonMinus_continuous :
    Continuous (projectNonMinus : GaugeField L → NonMinusGauge L) :=
  continuous_pi fun ℓ => continuous_apply ℓ.1

/-- **Projection is measurable** — follows from continuity + Borel
measurable space on the product. -/
theorem projectNonMinus_measurable :
    Measurable (projectNonMinus : GaugeField L → NonMinusGauge L) :=
  projectNonMinus_continuous.measurable

/-- **The structural characterisation.** A function `F : GaugeField L
→ ℂ` is `supportedOnPlusZero` iff it factors through `projectNonMinus`.

Forward direction: `supportedOnPlusZero F → ∃ F', F = F' ∘ projectNonMinus`.
Reverse: any `F' ∘ projectNonMinus` is automatically `supportedOnPlusZero`. -/
theorem supportedOnPlusZero_iff_factors (F : GaugeField L → ℂ) :
    supportedOnPlusZero F ↔
      ∃ F' : NonMinusGauge L → ℂ, F = F' ∘ projectNonMinus := by
  constructor
  · intro hF
    -- Define F' U' := F applied to any U with `projectNonMinus U = U'`.
    -- Concretely: extend U' by setting minus-links to a fixed value (identity).
    refine ⟨fun U' => F (fun ℓ => if h : linkSector ℓ ≠ LinkSector.minus
                                   then U' ⟨ℓ, h⟩
                                   else 1), ?_⟩
    funext U
    apply hF
    intro ℓ hℓ
    show U ℓ = _
    rw [dif_pos hℓ]
    rfl
  · rintro ⟨F', hF'⟩
    intro U₁ U₂ hU
    subst hF'
    simp only [Function.comp_apply]
    congr 1
    funext ℓ
    exact hU ℓ.1 ℓ.2

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.projectNonMinus_continuous
#print axioms PF.YangMills.projectNonMinus_measurable
#print axioms PF.YangMills.supportedOnPlusZero_iff_factors
