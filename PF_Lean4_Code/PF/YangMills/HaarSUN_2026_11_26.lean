/-
Copyright (c) 2026 Pablo Cohen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Cohen + Claude Opus 5 (1M context)
-/
import PF.YangMills.UnitaryGroupTopologyGeneral_mathlib
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Haar measure on SU(N), for every finite index type — and SU(3) named

`PF/YangMills/HaarSU2_2026_10_17.lean` and
`PF/YangMills/SU2HaarUnimodular_2026_10_21.lean` build the measure-theoretic
foundation the Wilson lattice construction stands on: a Borel structure, a Haar
probability measure, left invariance, right invariance (unimodularity) and
inv-invariance — all stated for `SU(2)`.

**Not one of those proofs uses the dimension.** They use
`map_right_mul_eq_modularCharacterFun_smul`, `measurable_mul_const`,
`isMulLeftInvariant_eq_smul_of_innerRegular` and `haarScalarFactor`, each
generic, plus `CompactSpace` and `Nonempty` — and
`PF/YangMills/UnitaryGroupTopologyGeneral_mathlib.lean` already supplies
`CompactSpace (Matrix.specialUnitaryGroup n ℂ)` for an arbitrary finite index
type. So the layer generalises verbatim, and this file does that.

## Why it matters, stated precisely

`PF/Referee/YMSubstrateScopeAccountability.lean` books the SU(2) restriction as
a scope limit, and the Clay Yang–Mills statement quantifies over an arbitrary
compact simple gauge group — with `SU(3)`, the gauge group of quantum
chromodynamics, as the physical case. After this file that restriction is **no
longer a group-theory limitation**: every measure-theoretic prerequisite the
lattice construction consumes holds at every `N` at once, and `SU3` is named.

## A note on the universe, because it is what broke the first draft

`Matrix.specialUnitaryGroup n ℂ` is a `Submonoid (Matrix n n ℂ)`, so for
`n : Type u` its coercion to a type lives in `Type u`, not `Type 0`. The
existing `SU2` abbreviation can be ascribed `Type` only because `Fin 2 : Type 0`.
Writing `SUN (n : Type*) : Type` therefore fails with a sort mismatch, and every
downstream instance failure follows from that one ascription rather than from
any missing typeclass. Hence the explicit `universe u` and `↥` below.

## Scope — read this before anything else here

This is the **group-and-measure layer only**. It does NOT port the lattice
construction, the Wilson action, or reflection positivity to SU(3). Those rest
on `GaugeField L := LatticeLink L → SU2`, whose base type is fixed, and on the
action density `1 - (1/2)·Re tr` whose `1/2` is `1/N` — annotated as such at
`WilsonMeasure_2026_10_17.lean:100`. Parametrising that layer is separate and
larger work.

**Nothing here claims any part of the Clay Yang–Mills problem**, and nothing
here is a statement about confinement, the mass gap, or asymptotic freedom.

SPDX-License-Identifier: Apache-2.0
-/

set_option autoImplicit false

universe u

namespace PF.YangMills

open Matrix MeasureTheory MeasureTheory.Measure TopologicalSpace

noncomputable section

/-- `SU(N)` for an arbitrary finite index type. At `n = Fin 2` this is the same
type as the existing `SU2` abbreviation; at `n = Fin 3` it is the QCD gauge
group. -/
abbrev SUN (n : Type u) [DecidableEq n] [Fintype n] : Type u :=
  ↥(Matrix.specialUnitaryGroup n ℂ)

variable {n : Type u} [DecidableEq n] [Fintype n]

/-! ## §1 — Measurable structure, for every `n` -/

/-- `SU(N)` carries the Borel σ-algebra of its subtype topology. -/
instance SUN_measurableSpace : MeasurableSpace (SUN n) := borel (SUN n)

/-- The chosen structure IS the Borel σ-algebra, by construction. -/
instance SUN_borelSpace : BorelSpace (SUN n) := ⟨rfl⟩

/-- `SU(N)` is nonempty: the identity matrix is special unitary. -/
instance SUN_nonempty : Nonempty (SUN n) := ⟨1⟩

/-! ## §2 — The whole group as a positive compact

`CompactSpace (SUN n)` comes from `instCompactSpaceSpecialUnitaryGroup`, which
is already generic in the index type. -/

/-- The whole of `SU(N)` as a `PositiveCompacts`. -/
def SUN_univ_positiveCompacts (n : Type u) [DecidableEq n] [Fintype n] :
    PositiveCompacts (SUN n) := ⊤

@[simp] theorem coe_SUN_univ_positiveCompacts (n : Type u) [DecidableEq n]
    [Fintype n] :
    ((SUN_univ_positiveCompacts n) : Set (SUN n)) = Set.univ := rfl

/-! ## §3 — Haar measure, for every `n` -/

/-- **Haar measure on `SU(N)`**, probability-normalised. -/
def SUN_haar (n : Type u) [DecidableEq n] [Fintype n] : Measure (SUN n) :=
  Measure.haarMeasure (SUN_univ_positiveCompacts n)

instance SUN_haar_isMulLeftInvariant : (SUN_haar n).IsMulLeftInvariant :=
  Measure.isMulLeftInvariant_haarMeasure _

instance SUN_haar_isProbabilityMeasure : IsProbabilityMeasure (SUN_haar n) where
  measure_univ := by
    show Measure.haarMeasure (SUN_univ_positiveCompacts n) Set.univ = 1
    rw [← coe_SUN_univ_positiveCompacts n]
    exact Measure.haarMeasure_self

instance SUN_haar_isHaarMeasure : (SUN_haar n).IsHaarMeasure :=
  Measure.isHaarMeasure_haarMeasure _

/-! ## §4 — Unimodularity, for every `n`

Transcribed from the SU(2) proofs, which never used the dimension. -/

/-- **The modular character of `SU(N)` is trivial.** Apply
`map_right_mul_eq_modularCharacterFun_smul` to `Set.univ` and use that
`SUN_haar` is a probability measure. -/
theorem SUN_modularCharacterFun_eq_one (g : SUN n) :
    modularCharacterFun g = (1 : NNReal) := by
  have h := map_right_mul_eq_modularCharacterFun_smul (SUN_haar n) g
  have h_univ : (map (· * g) (SUN_haar n)) Set.univ
      = (modularCharacterFun g • (SUN_haar n)) Set.univ := by rw [h]
  have h_measurable : Measurable (fun x : SUN n => x * g) :=
    measurable_mul_const g
  rw [Measure.map_apply h_measurable MeasurableSet.univ, Set.preimage_univ,
    measure_univ] at h_univ
  rw [Measure.coe_nnreal_smul_apply, measure_univ, mul_one] at h_univ
  exact_mod_cast h_univ.symm

/-- **`SUN_haar` is right-invariant.** Trivial modular character. -/
instance SUN_haar_isMulRightInvariant : IsMulRightInvariant (SUN_haar n) := by
  constructor
  intro g
  have h := map_right_mul_eq_modularCharacterFun_smul (SUN_haar n) g
  rw [SUN_modularCharacterFun_eq_one] at h
  rw [h]
  simp

instance SUN_haar_inv_isMulLeftInvariant :
    IsMulLeftInvariant (SUN_haar n).inv :=
  inferInstance

instance SUN_haar_inv_isProbabilityMeasure :
    IsProbabilityMeasure (SUN_haar n).inv := by
  constructor
  rw [inv_apply, Set.inv_univ, measure_univ]

/-- **`SU(N)` Haar is inv-invariant.** Both `(SUN_haar n).inv` and `SUN_haar n`
are left-Haar probability measures, inner regular on a compact space, so they
agree up to a scalar; probability normalisation pins the scalar at `1`. -/
instance SUN_haar_isInvInvariant : IsInvInvariant (SUN_haar n) := by
  constructor
  have h_uniq : (SUN_haar n).inv
      = haarScalarFactor (SUN_haar n).inv (SUN_haar n) • (SUN_haar n) :=
    isMulLeftInvariant_eq_smul_of_innerRegular _ _
  set c := haarScalarFactor (SUN_haar n).inv (SUN_haar n) with hc
  have h_univ : (SUN_haar n).inv Set.univ = (c • (SUN_haar n)) Set.univ := by
    rw [h_uniq]
  rw [Measure.coe_nnreal_smul_apply, measure_univ, measure_univ, mul_one]
    at h_univ
  have h_c : c = (1 : NNReal) := by
    have hcast : (c : ENNReal) = 1 := h_univ.symm
    exact_mod_cast hcast
  rw [h_uniq, h_c]
  simp

/-! ## §5 — SU(3), the QCD gauge group -/

/-- **`SU(3)`** — the gauge group of quantum chromodynamics, as an instance of
the construction above. -/
abbrev SU3 : Type := SUN (Fin 3)

/-- Haar probability measure on `SU(3)`. An `abbrev`, not a `def`, so that
instance resolution sees through it to `SUN_haar (Fin 3)` and the §1–§4
instances apply without restating any of them. -/
abbrev SU3_haar : Measure SU3 := SUN_haar (Fin 3)

/-- Every measure-theoretic fact of §1–§4 holds of `SU(3)` by instantiation,
with no separate proof. Bundled so the instantiation is kernel-checked rather
than asserted. -/
theorem su3_haar_facts :
    IsProbabilityMeasure SU3_haar
      ∧ SU3_haar.IsMulLeftInvariant
      ∧ IsMulRightInvariant SU3_haar
      ∧ IsInvInvariant SU3_haar
      ∧ SU3_haar.IsHaarMeasure :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

theorem su3_compactSpace : CompactSpace SU3 := inferInstance

/-- The three colours are a real feature of the carrier: `SU(3)` is matrices on
`Fin 3`, whose index type has exactly three elements. Recorded so the `3` is
tied to the carrier rather than asserted. -/
theorem card_su3_index : Fintype.card (Fin 3) = 3 := by simp

/-- **The scope limit was never group theory.** The measure-theoretic
prerequisites the Wilson construction consumes — a Haar probability measure that
is left-invariant, right-invariant and inv-invariant — hold at two independent
finite index types simultaneously, hence at `Fin 2` and `Fin 3` together. -/
theorem sun_haar_layer_is_dimension_free
    (m k : Type u) [DecidableEq m] [Fintype m] [DecidableEq k] [Fintype k] :
    IsProbabilityMeasure (SUN_haar m)
      ∧ IsInvInvariant (SUN_haar m)
      ∧ IsProbabilityMeasure (SUN_haar k)
      ∧ IsInvInvariant (SUN_haar k) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

end

end PF.YangMills
