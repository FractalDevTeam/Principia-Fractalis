/-
# Yang-Mills — Haar measure on `specialUnitaryGroup (Fin 2) ℂ` (step 1 of Rio's YM plan)

**Rio's YM step 1, 2026-10-17** (codex `f85c078b`): with CompactSpace +
IsTopologicalGroup landed (`SpecialUnitaryGroupTopology_2026_10_17.lean`,
commit `3adddcf1`), mathlib's `MeasureTheory.Measure.haarMeasure` applies.
We instantiate it on SU(2), obtaining a left-invariant probability measure.

### What this file provides

* `SU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ` — abbreviation.
* `MeasurableSpace SU2` + `BorelSpace SU2` — the Borel σ-algebra of the
  subspace topology.
* `Nonempty SU2` — the identity matrix.
* `SU2_univ_positiveCompacts : PositiveCompacts SU2` — the whole group,
  via `⊤` (CompactSpace + Nonempty).
* `SU2_haar : Measure SU2` — the Haar measure, scaled to be a probability
  measure (`SU2_haar univ = 1`).
* `IsMulLeftInvariant SU2_haar` — mathlib automatically.
* `IsProbabilityMeasure SU2_haar` — from `haarMeasure_self`.

### What this file does NOT prove

* Uniqueness of Haar on a compact group (mathlib's `haarMeasure_unique`
  gives this up to a scalar; probability-normalized Haar is unique).
* Bi-invariance (follows on compact groups from unimodularity; not needed
  for Wilson measure).
* Translation to the Wilson lattice measure (step 2, next file).

Three-axiom bar: every declaration kernel-clean
`[propext, Classical.choice, Quot.sound]`. No sorry.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-17.
-/
import PF.YangMills.SpecialUnitaryGroupTopology_2026_10_17
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

set_option autoImplicit false

namespace PF.YangMills

open Matrix MeasureTheory TopologicalSpace

noncomputable section

/-- Abbreviation for `Matrix.specialUnitaryGroup (Fin 2) ℂ`. -/
abbrev SU2 : Type := Matrix.specialUnitaryGroup (Fin 2) ℂ

/-! ## §1 — Measurable-space structure on SU(2). -/

/-- SU(2) carries the Borel σ-algebra of the subtype topology (inherited from
`Matrix (Fin 2) (Fin 2) ℂ`). -/
instance SU2_measurableSpace : MeasurableSpace SU2 := borel SU2

/-- The chosen measurable structure IS the Borel σ-algebra — tautological by
construction. -/
instance SU2_borelSpace : BorelSpace SU2 := ⟨rfl⟩

/-- SU(2) is nonempty — the identity matrix is special-unitary. -/
instance SU2_nonempty : Nonempty SU2 := ⟨1⟩

/-! ## §2 — The whole group as a positive-compact. -/

/-- The whole group `SU2` as an element of `PositiveCompacts SU2`. Uses
`Top` instance on `PositiveCompacts` for CompactSpace + Nonempty spaces. -/
def SU2_univ_positiveCompacts : PositiveCompacts SU2 := ⊤

@[simp]
theorem coe_SU2_univ_positiveCompacts :
    (SU2_univ_positiveCompacts : Set SU2) = Set.univ := rfl

/-! ## §3 — The Haar measure. -/

/-- **★ Haar measure on SU(2) ★** — left-invariant, probability-normalized
(`SU2_haar univ = 1`). The first measure on SU(2) in the repo; built from
mathlib's `haarMeasure` applied to `SU2_univ_positiveCompacts`. -/
def SU2_haar : Measure SU2 :=
  Measure.haarMeasure SU2_univ_positiveCompacts

/-- **Left invariance** of `SU2_haar`. Inherited from mathlib's
`isMulLeftInvariant_haarMeasure`. -/
instance SU2_haar_isMulLeftInvariant : SU2_haar.IsMulLeftInvariant :=
  Measure.isMulLeftInvariant_haarMeasure _

/-- **`SU2_haar` is a probability measure**: `SU2_haar univ = 1`. Follows from
`haarMeasure_self` with the scaling-set being the whole group. -/
instance SU2_haar_isProbabilityMeasure : IsProbabilityMeasure SU2_haar where
  measure_univ := by
    show Measure.haarMeasure SU2_univ_positiveCompacts Set.univ = 1
    rw [← coe_SU2_univ_positiveCompacts]
    exact Measure.haarMeasure_self

/-- `SU2_haar` is a Haar measure (compatible with the `IsHaarMeasure` typeclass
— i.e., left-invariant, finite on compacts, positive on open sets). Inherited
from `isHaarMeasure_haarMeasure`. -/
instance SU2_haar_isHaarMeasure : SU2_haar.IsHaarMeasure :=
  Measure.isHaarMeasure_haarMeasure _

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.SU2_measurableSpace
#print axioms PF.YangMills.SU2_borelSpace
#print axioms PF.YangMills.SU2_nonempty
#print axioms PF.YangMills.SU2_univ_positiveCompacts
#print axioms PF.YangMills.SU2_haar
#print axioms PF.YangMills.SU2_haar_isMulLeftInvariant
#print axioms PF.YangMills.SU2_haar_isProbabilityMeasure
#print axioms PF.YangMills.SU2_haar_isHaarMeasure
