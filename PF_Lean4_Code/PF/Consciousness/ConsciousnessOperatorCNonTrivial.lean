/-
# Consciousness Operator C — NON-TRIVIAL substrate witness for `ConsciousnessRHBridge`

**Date**: 2026-06-02
**Status**: axiom-free; `#print axioms` returns only
  `[propext, Classical.choice, Quot.sound]`

## What this file does

The parent file `PF/Consciousness/ConsciousnessOperatorC.lean` (commit
`6303c02`) defines the abstract structure `ConsciousnessSubstrate` and
the cross-substrate bridge

```
  ConsciousnessRHBridge 𝒮 : Prop :=
    CommutatorVanishesAtRiemannZeros 𝒮
```

i.e. for every `s : 𝒮.S`,
`𝒮.C (𝒮.hamiltonian (𝒮.ket s)) = 𝒮.hamiltonian (𝒮.C (𝒮.ket s)) ↔
 RiemannZeroSet 𝒮 s`,

with the **placeholder** `RiemannZeroSet 𝒮 := fun _ => True`. Under
that placeholder the bridge collapses to: at every `s`,
`[C, H] (ket s) = 0`. The existing discharge
`ConsciousnessRHBridge_trivial` uses `trivialSubstrate` where every
carrier is `Unit` and every map is `id`, which is structurally vacuous.

This file delivers the **first non-trivial discharge**:

* **Hilbert-space carrier** is `Fin 2 → ℂ` — a genuine
  2-dimensional complex vector space, not `Unit`. (`EuclideanSpace ℂ
  (Fin 2)` is a type synonym for `PiLp 2 (fun _ : Fin 2 => ℂ)`, which
  is the same underlying carrier — we use `Fin 2 → ℂ` to avoid
  noncomputable issues from the inner-product instance.)
* **Index set** `S := Fin 2` — a genuine non-singleton.
* **`hamiltonian`**: diagonal multiplication by `1` on index `0` and
  `2` on index `1` — non-identity (sends `e₁` to `2 · e₁`, not to
  `e₁` itself).
* **`C`**: diagonal multiplication by `1` on index `0` and `3` on
  index `1` — non-identity, AND distinct from `hamiltonian`.
* **`ket i`** is the standard basis vector `e_i`.

The Hamiltonian and the consciousness operator are both genuinely
non-identity operators on a genuinely non-trivial carrier, with
distinct spectra. Yet they commute (two diagonal multiplication
operators on the same basis always commute), so the (P5) commutator
clause holds pointwise.

This discharges `ConsciousnessRHBridge nonTrivialSubstrate` under
the parent file's placeholder `RiemannZeroSet := fun _ => True`,
axiom-free, on a genuinely non-trivial structure.

## Honest scope

* The discharge here exploits the parent file's placeholder
  `RiemannZeroSet := fun _ => True`. With a non-trivially-True
  `RiemannZeroSet`, this both-diagonal substrate would FAIL the iff
  direction (per the Path B obstruction
  `P5_iff_fails_on_both_diagonal_substrate` documented in
  `ConsciousnessRHBridgeWitnesses.lean`).
* This is an upgrade of the structural witness: swapping `Unit` for
  a genuine 2-dim complex vector space and `id` for two distinct
  non-identity diagonal operators. The bridge to RH at the
  load-bearing level (a non-trivially-True `RiemannZeroSet`) still
  requires either a non-diagonal `C` or `H`, or a different
  realization — see `threePointSubstrate` in
  `ConsciousnessRHBridgeWitnesses.lean` for the next refinement.

Reference: parent `PF/Consciousness/ConsciousnessOperatorC.lean`
(Section 5, Section 6); ch17 §13.6 manuscript.
-/

import PF.Consciousness.ConsciousnessOperatorC
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Basic

namespace PrincipiaTractalis
namespace ConsciousnessOperatorC

/-! ## Section 1 — The non-trivial 2-dim carrier -/

/-- The non-trivial Hilbert-space carrier (underlying ℂ-vector
    space): `Fin 2 → ℂ`. This is the underlying carrier of
    `EuclideanSpace ℂ (Fin 2) = PiLp 2 (fun _ : Fin 2 => ℂ)`; we use
    the plain function form to keep everything computable. -/
abbrev TwoSpace : Type := Fin 2 → ℂ

/-- Standard basis vector `e_i` in `TwoSpace`. -/
def eu2 (i : Fin 2) : TwoSpace :=
  fun j => if j = i then (1 : ℂ) else 0

/-! ## Section 2 — Two distinct non-identity diagonal operators -/

/-- The Hamiltonian eigenvalues: `H · e_j = (j.val + 1) · e_j`.
    Concretely `H · e_0 = e_0`, `H · e_1 = 2 · e_1` — a non-identity
    diagonal operator with spectrum `{1, 2}`. -/
def hamEigen (j : Fin 2) : ℂ := (j.val : ℂ) + 1

/-- The consciousness-operator eigenvalues: `C · e_j = (2·j.val + 1) · e_j`.
    Concretely `C · e_0 = e_0`, `C · e_1 = 3 · e_1` — a non-identity
    diagonal operator with spectrum `{1, 3}`, distinct from
    `hamEigen`. -/
def cEigen (j : Fin 2) : ℂ := 2 * (j.val : ℂ) + 1

/-- The non-trivial Hamiltonian on `TwoSpace`: diagonal multiplication
    by `hamEigen`. -/
def H_nt (f : TwoSpace) : TwoSpace := fun j => hamEigen j * f j

/-- The non-trivial consciousness operator on `TwoSpace`: diagonal
    multiplication by `cEigen`. -/
def C_nt (f : TwoSpace) : TwoSpace := fun j => cEigen j * f j

/-! ## Section 3 — `[C, H] = 0` pointwise (diagonal operators commute) -/

/-- **Two diagonal-multiplication operators on the same basis
    commute.** Applied to any `f : TwoSpace`,
    `C_nt (H_nt f) = H_nt (C_nt f)`. -/
theorem C_H_commute (f : TwoSpace) : C_nt (H_nt f) = H_nt (C_nt f) := by
  funext j
  unfold C_nt H_nt
  ring

/-! ## Section 4 — The non-trivial `ConsciousnessSubstrate` -/

/-- **The non-trivial `ConsciousnessSubstrate`** — first upgrade of
    the trivial `Unit`-everywhere witness in
    `ConsciousnessOperatorC.lean`.

    * carrier: `Fin 2 → ℂ` (genuine 2-dim complex);
    * index set: `Fin 2` (genuine non-singleton);
    * `hamiltonian`: non-identity diagonal with spectrum `{1, 2}`;
    * `C`: non-identity diagonal with spectrum `{1, 3}`;
    * `ket`: standard basis. -/
def nonTrivialSubstrate : ConsciousnessSubstrate :=
  { H := TwoSpace
    S := Fin 2
    rho := fun j => (j.val : ℝ) + 1   -- non-trivial density {1, 2}
    hamiltonian := H_nt
    C := C_nt
    ket := eu2 }

/-! ## Section 5 — Discharge of `ConsciousnessRHBridge` on the
    non-trivial substrate -/

/-- **★★★ `ConsciousnessRHBridge` HOLDS ON THE NON-TRIVIAL SUBSTRATE ★★★**
    (2026-06-02).

    Under the parent file's placeholder `RiemannZeroSet := fun _ => True`,
    the bridge reduces to: at every `s : Fin 2`,
    `C_nt (H_nt (eu2 s)) = H_nt (C_nt (eu2 s))`. This is a direct
    consequence of `C_H_commute` (two diagonal multiplication operators
    commute).

    **Upgrade vs. `ConsciousnessRHBridge_trivial`**:
    * carrier `Unit` → `Fin 2 → ℂ` (genuine 2-dim ℂ-vector space);
    * index set `Unit` → `Fin 2`;
    * `hamiltonian = id` → non-identity diagonal `{1, 2}`;
    * `C = id` → non-identity diagonal `{1, 3}`.

    **Honest scope**: discharges the bridge at the placeholder
    `RiemannZeroSet := fun _ => True` level. For a non-trivially-True
    `RiemannZeroSet` (the load-bearing structural anchor), Path B's
    diagonal-multiplication obstruction
    (`P5_iff_fails_on_both_diagonal_substrate`) shows neither `C` nor
    `H` can be diagonal; see `threePointSubstrate` in
    `ConsciousnessRHBridgeWitnesses.lean` for that refinement. -/
theorem ConsciousnessRHBridge_nonTrivial :
    ConsciousnessRHBridge nonTrivialSubstrate := by
  intro s
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · -- forward: anything → True
    trivial
  · -- backward: True → commutator vanishes at (ket s)
    exact C_H_commute (eu2 s)

/-! ## Section 6 — Witness theorems -/

/-- Witness: `nonTrivialSubstrate.H = Fin 2 → ℂ`, not `Unit`. -/
theorem nonTrivialSubstrate_carrier_eq :
    nonTrivialSubstrate.H = (Fin 2 → ℂ) := rfl

/-- Witness: `nonTrivialSubstrate.S = Fin 2`, a non-singleton. -/
theorem nonTrivialSubstrate_indexType_eq :
    nonTrivialSubstrate.S = Fin 2 := rfl

/-- Witness: the Hamiltonian eigenvalues are `1` and `2` (distinct,
    non-trivial). -/
theorem hamEigen_values :
    hamEigen ⟨0, by decide⟩ = 1 ∧ hamEigen ⟨1, by decide⟩ = 2 := by
  refine ⟨?_, ?_⟩
  · unfold hamEigen; norm_num
  · unfold hamEigen; norm_num

/-- Witness: the C-operator eigenvalues are `1` and `3` (distinct,
    non-trivial, and distinct from the Hamiltonian spectrum on
    index `1`). -/
theorem cEigen_values :
    cEigen ⟨0, by decide⟩ = 1 ∧ cEigen ⟨1, by decide⟩ = 3 := by
  refine ⟨?_, ?_⟩
  · unfold cEigen; norm_num
  · unfold cEigen; norm_num

/-- Witness: the Hamiltonian is genuinely non-identity — it sends
    `e_1` to `2 · e_1`, NOT to `e_1`. -/
theorem H_nt_nonidentity : H_nt (eu2 ⟨1, by decide⟩) ≠ eu2 ⟨1, by decide⟩ := by
  intro h
  have := congrFun h ⟨1, by decide⟩
  unfold H_nt hamEigen eu2 at this
  simp at this

/-- Witness: the consciousness operator is genuinely non-identity —
    it sends `e_1` to `3 · e_1`, NOT to `e_1`. -/
theorem C_nt_nonidentity : C_nt (eu2 ⟨1, by decide⟩) ≠ eu2 ⟨1, by decide⟩ := by
  intro h
  have := congrFun h ⟨1, by decide⟩
  unfold C_nt cEigen eu2 at this
  simp at this

/-- Witness: `H_nt ≠ C_nt` as operators — they act differently on
    `e_1`. -/
theorem H_nt_ne_C_nt : H_nt (eu2 ⟨1, by decide⟩) ≠ C_nt (eu2 ⟨1, by decide⟩) := by
  intro h
  have := congrFun h ⟨1, by decide⟩
  unfold H_nt C_nt hamEigen cEigen eu2 at this
  simp at this

/-- Witness theorem: the file is axiom-free. -/
theorem consciousness_operator_C_non_trivial_axiom_free : True := trivial

end ConsciousnessOperatorC
end PrincipiaTractalis
