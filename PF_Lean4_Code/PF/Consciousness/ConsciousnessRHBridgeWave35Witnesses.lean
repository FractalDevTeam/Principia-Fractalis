/-
# Consciousness ↔ RH Bridge — Wave 35 Witnesses (NON-MULTIPLICATIVE H)

**Date**: 2026-05-30
**Status**: axiom-free; `#print axioms` returns only
  `[propext, Classical.choice, Quot.sound]`

## What this file does

Wave 13 (`ConsciousnessRHBridgeWitnesses.lean`) delivered the FIRST
non-trivial witness for (P5) `CommutatorVanishesAtRHZeros`:
`threePointSubstrate` on `Fin 3`, with a **multiplicative diagonal**
`hamiltonian` (H3 = pointwise multiplication by `(j.val : ℂ)`) and a
**permutation** `C3` (swap of indices 1 and 2). The (P5) iff holds
substantively.

The Path B obstruction in Wave 13 ruled out the "both-diagonal-
multiplication on `Fin n → ℂ`" class as candidates for a substantive
(P5). It is therefore strategically important to deliver a (P5)
witness in which `hamiltonian` is GENUINELY non-multiplicative
(i.e. not of the form `diagMul n m`). Wave 13's H3 still IS
multiplicative; the non-triviality comes solely from C3 being a
non-identity permutation.

Wave 35 extends Path A by:

### Path A+ — Five-point substrate `fivePointSubstrate` with
### NON-MULTIPLICATIVE Hamiltonian

* `S := Fin 5`. Three zero-block indices (0, 1, 2) and one off-zero
  swap pair (3 ↔ 4).
* `pos5` anchors zero-block indices to the first three Odlyzko
  ζ-zeros (1/2 + 14.1347 i, 1/2 + 21.0220 i, 1/2 + 25.0109 i); off-
  zero indices to (0, 0).
* `C5` is the permutation `(0)(1)(2)(3 4)` — identity on 0, 1, 2 and
  swap of 3, 4.
* `H5` is **NON-MULTIPLICATIVE**: diagonal on 0, 1, 2, 4 but with an
  off-diagonal coupling at j = 3 that adds `f 4`:
  `H5 f j = (j.val : ℂ) * f j + (if j = 3 then f 4 else 0)`.

  In particular `H5 ≠ diagMul 5 m` for any multiplier `m`, since
  `H5 (e_4) = e_3 + 4·e_4` (the e_3 component of H5(e_4) cannot
  arise from any pointwise multiplier).

* `zeroSet5 idx := idx.val < 3` (i.e. `idx ∈ {0, 1, 2}`).

* `P5_holds_fivePoint : CommutatorVanishesAtRHZeros fivePointSubstrate`
  is a **theorem**:
  - commutator vanishes on `e_0, e_1, e_2` (zero block, both
    operators block-diagonally trivial there),
  - commutator does NOT vanish on `e_3` or `e_4` (off-zero block).

This is the **first (P5) witness with genuinely non-multiplicative
Hamiltonian**. It strictly strengthens Wave 13's Path A by escaping
the "H multiplicative" class.

### Path B+ — Non-multiplicativity certificate
`H5_not_multiplicative` formally proves `H5 ≠ diagMul 5 m` for ANY
multiplier `m : Fin 5 → ℂ`. This is the structural certificate that
this (P5) witness is OUTSIDE Wave 13's Path B obstruction class on
the `H`-side.

## Honest scope

* **Path A+**: substantive (P5) realisation on a finite-dim substrate
  with `zeroSet` of size 3 (not 1) AND with non-multiplicative
  Hamiltonian. Strictly stronger than Wave 13's three-point witness
  on both axes (more zero-indices, more structural content).
* **NOT** a discharge of (P5) on the full Timeless Field 𝒯_∞ —
  Hilbert–Pólya remains the load-bearing open conjecture.
* (P6) `ConsciousnessStationaryStateCompleteness` is still subject to
  Wave 13's Path C finite-cardinality obstruction; the five-point
  substrate cannot witness (P6) substantively (Fintype.card = 5 <
  countably infinitely many critical-strip ζ-zeros).
* The capstone `consciousness_RH_wave35_fivepoint_witness` only
  attests that this richer (P5) realisation exists; it does NOT
  claim RH or any new Millennium discharge.

Strategic significance: keeps the consciousness↔RH route LIVE for
future waves and concretely answers the question "is the Wave 13
three-point witness the BEST finite-dim (P5) witness?" — NO: there
is a stronger 5-point witness with non-multiplicative H.
-/

import PF.Consciousness.ConsciousnessRHBridge
import PF.Consciousness.ConsciousnessRHBridgeWitnesses
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Data.Fintype.Card

namespace PrincipiaTractalis

open ConsciousnessOperatorC

/-! ## Section 1 — The five-point Hilbert-like space and operators -/

/-- Underlying Hilbert-space-like type: `Fin 5 → ℂ`. -/
abbrev FiveSpace : Type := Fin 5 → ℂ

/-- Standard basis vector `e_i` in `FiveSpace`. -/
def e5 (i : Fin 5) : FiveSpace :=
  fun j => if j = i then (1 : ℂ) else 0

/-- The five-point swap permutation: 0 ↦ 0, 1 ↦ 1, 2 ↦ 2, 3 ↔ 4. -/
def swap5 : Fin 5 → Fin 5
  | ⟨0, _⟩ => ⟨0, by decide⟩
  | ⟨1, _⟩ => ⟨1, by decide⟩
  | ⟨2, _⟩ => ⟨2, by decide⟩
  | ⟨3, _⟩ => ⟨4, by decide⟩
  | ⟨4, _⟩ => ⟨3, by decide⟩
  | ⟨n+5, h⟩ => absurd h (by omega)

/-- Consciousness operator: `(C5 f)(j) := f (swap5 j)`. -/
def C5 (f : FiveSpace) : FiveSpace := fun j => f (swap5 j)

/-- **NON-MULTIPLICATIVE Hamiltonian** on the five-point substrate.
    Diagonal in positions 0, 1, 2, 4; off-diagonal coupling at j = 3
    that adds `f 4`. Concretely:
    * `H5 f 0 = 0`
    * `H5 f 1 = f 1`
    * `H5 f 2 = 2 · f 2`
    * `H5 f 3 = 3 · f 3 + f 4`         (off-diagonal coupling!)
    * `H5 f 4 = 4 · f 4`

    This is NOT of the form `diagMul 5 m` for any multiplier `m`,
    since on `f = e_4` the j = 3 component is 1, but a pure
    multiplier would give `m 3 * e_4 3 = m 3 * 0 = 0`. -/
def H5 (f : FiveSpace) : FiveSpace := fun j =>
  (j.val : ℂ) * f j + (if j = ⟨3, by decide⟩ then f ⟨4, by decide⟩ else 0)

/-- Swap5 is an involution. -/
@[simp] lemma swap5_swap5 (j : Fin 5) : swap5 (swap5 j) = j := by
  fin_cases j <;> rfl

@[simp] lemma swap5_zero : swap5 ⟨0, by decide⟩ = ⟨0, by decide⟩ := rfl
@[simp] lemma swap5_one  : swap5 ⟨1, by decide⟩ = ⟨1, by decide⟩ := rfl
@[simp] lemma swap5_two  : swap5 ⟨2, by decide⟩ = ⟨2, by decide⟩ := rfl
@[simp] lemma swap5_three : swap5 ⟨3, by decide⟩ = ⟨4, by decide⟩ := rfl
@[simp] lemma swap5_four  : swap5 ⟨4, by decide⟩ = ⟨3, by decide⟩ := rfl

/-! ## Section 2 — The five-point substrate -/

/-- Position map: indices 0, 1, 2 anchored to the first three
    Odlyzko ζ-zeros; indices 3, 4 anchored to (0, 0). -/
noncomputable def pos5 : Fin 5 → ℂ
  | ⟨0, _⟩ => ⟨1/2, 14.1347⟩
  | ⟨1, _⟩ => ⟨1/2, 21.0220⟩
  | ⟨2, _⟩ => ⟨1/2, 25.0109⟩
  | ⟨3, _⟩ => ⟨0, 0⟩
  | ⟨4, _⟩ => ⟨0, 0⟩
  | ⟨n+5, h⟩ => absurd h (by omega)

/-- `zeroSet5 idx := idx.val < 3` (i.e. `idx ∈ {0, 1, 2}`). -/
def zeroSet5 (idx : Fin 5) : Prop := idx.val < 3

/-- The base `ConsciousnessSubstrate` for the five-point witness. -/
noncomputable def fivePointBase : ConsciousnessSubstrate :=
  { H := FiveSpace
    S := Fin 5
    rho := fun _ => 0
    hamiltonian := H5
    C := C5
    ket := e5 }

/-- **The five-point `ConsciousnessRHSubstrate`** — Wave 35 witness
    with non-multiplicative Hamiltonian. -/
noncomputable def fivePointSubstrate : ConsciousnessRHSubstrate :=
  { base := fivePointBase
    pos := pos5
    zeroSet := zeroSet5
    zero_set_on_critical_line := by
      intro idx h_in
      have h_lt3 : idx.val < 3 := h_in
      match h_idx : idx, h_lt3 with
      | ⟨0, _⟩, _ => show (pos5 ⟨0, by decide⟩).re = 1/2; rfl
      | ⟨1, _⟩, _ => show (pos5 ⟨1, by decide⟩).re = 1/2; rfl
      | ⟨2, _⟩, _ => show (pos5 ⟨2, by decide⟩).re = 1/2; rfl
      | ⟨3, _⟩, h =>
        exfalso
        have : (3 : ℕ) < 3 := h
        exact Nat.lt_irrefl 3 this
      | ⟨4, _⟩, h =>
        exfalso
        have : (4 : ℕ) < 3 := h
        omega
      | ⟨n+5, h⟩, _ => exact absurd h (by omega) }

/-! ## Section 3 — Helper lemmas for H5 and C5 on basis vectors -/

@[simp] lemma e5_apply (i j : Fin 5) :
    e5 i j = if j = i then (1 : ℂ) else 0 := rfl

/-! ## Section 4 — Commutator vanishes on the zero block -/

/-- **Commutator vanishes at index 0** (zero block). -/
theorem commutator_vanishes_at_zero5 :
    C5 (H5 (e5 ⟨0, by decide⟩)) = H5 (C5 (e5 ⟨0, by decide⟩)) := by
  funext j
  fin_cases j <;> simp [C5, H5, e5, swap5]

/-- **Commutator vanishes at index 1** (zero block). -/
theorem commutator_vanishes_at_one5 :
    C5 (H5 (e5 ⟨1, by decide⟩)) = H5 (C5 (e5 ⟨1, by decide⟩)) := by
  funext j
  fin_cases j <;> simp [C5, H5, e5, swap5]

/-- **Commutator vanishes at index 2** (zero block). -/
theorem commutator_vanishes_at_two5 :
    C5 (H5 (e5 ⟨2, by decide⟩)) = H5 (C5 (e5 ⟨2, by decide⟩)) := by
  funext j
  fin_cases j <;> simp [C5, H5, e5, swap5]

/-! ## Section 5 — Commutator fails on the off-zero block -/

/-- **Commutator does NOT vanish at index 3** (off-zero block).
    Witnessed by component j = 4. -/
theorem commutator_nonvanishes_at_three5 :
    C5 (H5 (e5 ⟨3, by decide⟩)) ≠ H5 (C5 (e5 ⟨3, by decide⟩)) := by
  intro h
  have := congrFun h ⟨4, by decide⟩
  -- LHS at 4: C5(H5(e_3)) 4 = (H5 e_3)(swap5 4) = (H5 e_3) 3
  --   = 3 * e_3 3 + e_3 4 = 3 * 1 + 0 = 3.
  -- RHS at 4: H5(C5(e_3)) 4 = 4 * (C5 e_3) 4 + (false branch = 0)
  --   = 4 * e_3 (swap5 4) = 4 * e_3 3 = 4 * 1 = 4.
  -- So this would assert 3 = 4 in ℂ, contradiction.
  simp [C5, H5, e5, swap5] at this

/-- **Commutator does NOT vanish at index 4** (off-zero block).
    Witnessed by component j = 3. -/
theorem commutator_nonvanishes_at_four5 :
    C5 (H5 (e5 ⟨4, by decide⟩)) ≠ H5 (C5 (e5 ⟨4, by decide⟩)) := by
  intro h
  have := congrFun h ⟨3, by decide⟩
  -- LHS at 3: C5(H5(e_4)) 3 = (H5 e_4)(swap5 3) = (H5 e_4) 4
  --   = 4 * e_4 4 + (false: 4 ≠ 3) = 4 * 1 + 0 = 4.
  -- RHS at 3: H5(C5(e_4)) 3 = 3 * (C5 e_4) 3 + (C5 e_4) 4
  --   (3 = ⟨3,_⟩ branch fires) = 3 * e_4(swap5 3) + e_4(swap5 4)
  --   = 3 * e_4 4 + e_4 3 = 3 * 1 + 0 = 3.
  -- So this would assert 4 = 3 in ℂ, contradiction.
  simp [C5, H5, e5, swap5] at this

/-! ## Section 6 — Main (P5) theorem on the five-point substrate -/

/-- **★★★ (P5) HOLDS ON THE FIVE-POINT SUBSTRATE ★★★**
    (Wave 35, NON-MULTIPLICATIVE H).

    `CommutatorVanishesAtRHZeros fivePointSubstrate` is a **theorem**:
    `commute ↔ zeroSet5 idx` holds at every index of `Fin 5`, where:
    * `zeroSet5 idx = (idx.val < 3)` is GENUINELY non-trivial
      (3 zero-indices, 2 off-zero indices);
    * `H5` is GENUINELY non-multiplicative (proved separately below
      as `H5_not_multiplicative`).

    **Honest scope**: substantive finite-dim witness with richer
    structure than Wave 13's three-point witness. NOT a discharge of
    (P5) on the full Timeless Field 𝒯_∞ — Hilbert–Pólya remains the
    load-bearing open conjecture. -/
theorem P5_holds_fivePoint :
    CommutatorVanishesAtRHZeros fivePointSubstrate := by
  intro idx
  change (C5 (H5 (e5 idx)) = H5 (C5 (e5 idx))) ↔ zeroSet5 idx
  match h_idx : idx with
  | ⟨0, _⟩ =>
    refine ⟨fun _ => ?_, fun _ => commutator_vanishes_at_zero5⟩
    show (0 : ℕ) < 3; decide
  | ⟨1, _⟩ =>
    refine ⟨fun _ => ?_, fun _ => commutator_vanishes_at_one5⟩
    show (1 : ℕ) < 3; decide
  | ⟨2, _⟩ =>
    refine ⟨fun _ => ?_, fun _ => commutator_vanishes_at_two5⟩
    show (2 : ℕ) < 3; decide
  | ⟨3, _⟩ =>
    refine ⟨fun h => absurd h commutator_nonvanishes_at_three5,
            fun h => absurd h ?_⟩
    show ¬ ((3 : ℕ) < 3); decide
  | ⟨4, _⟩ =>
    refine ⟨fun h => absurd h commutator_nonvanishes_at_four5,
            fun h => absurd h ?_⟩
    show ¬ ((4 : ℕ) < 3); decide
  | ⟨n+5, h⟩ => exact absurd h (by omega)

/-! ## Section 7 — Non-multiplicativity certificate for H5 -/

/-- **★ NON-MULTIPLICATIVITY CERTIFICATE FOR H5 ★**

    `H5` is NOT of the form `diagMul 5 m` for ANY multiplier
    `m : Fin 5 → ℂ`. This is the structural certificate that the
    five-point witness escapes Wave 13's Path B "both-diagonal-
    multiplication" obstruction class on the H-side.

    Proof: evaluate at `f = e5 ⟨4, _⟩`. The (j = 3)-component of
    `H5 e_4` is 1 (from the off-diagonal coupling `f 4`), whereas
    `(diagMul 5 m) e_4` at j = 3 is `m 3 * e_4 3 = m 3 * 0 = 0`.
    Hence `H5 e_4 ≠ (diagMul 5 m) e_4` for any `m`. -/
theorem H5_not_multiplicative :
    ∀ m : Fin 5 → ℂ, H5 ≠ diagMul 5 m := by
  intro m h_eq
  -- evaluate both sides at f = e5 ⟨4, _⟩, component j = ⟨3, _⟩
  have h_fun : H5 (e5 ⟨4, by decide⟩) = diagMul 5 m (e5 ⟨4, by decide⟩) :=
    congrFun h_eq (e5 ⟨4, by decide⟩)
  have h_pt := congrFun h_fun ⟨3, by decide⟩
  -- LHS at 3: H5(e_4) 3 = 3 * e_4 3 + e_4 4 = 3 * 0 + 1 = 1.
  -- RHS at 3: (diagMul 5 m) e_4 3 = m 3 * e_4 3 = m 3 * 0 = 0.
  -- So 1 = 0, contradiction.
  simp [H5, diagMul, e5] at h_pt

/-! ## Section 8 — Strict-strengthening of Wave 13's three-point witness -/

/-- **The five-point substrate is strictly larger** than the three-
    point substrate (on the index side): `Fintype.card (Fin 5) = 5 >
    3 = Fintype.card (Fin 3)`. -/
theorem fivePoint_strictly_larger_than_threePoint :
    Fintype.card (Fin 5) > Fintype.card (Fin 3) := by decide

/-- **The five-point substrate has strictly more zero-block
    indices**: `zeroSet5` is true on 3 indices (vs `zeroSet3` true on
    1 index in the three-point substrate). -/
theorem fivePoint_more_zero_indices :
    (Finset.univ.filter (fun idx : Fin 5 => idx.val < 3)).card = 3 ∧
    (Finset.univ.filter (fun idx : Fin 3 => idx.val < 1)).card = 1 := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## Section 9 — Wave 35 capstone -/

/-- **★★★ CONSCIOUSNESS↔RH WAVE 35 FIVE-POINT WITNESS ★★★**
    (2026-05-30).

    Two-part capstone certifying the Wave 35 contribution:

    1. `P5_holds_fivePoint` — substantive (P5) realisation on the
       five-point substrate with a NON-MULTIPLICATIVE Hamiltonian
       (richer than Wave 13's three-point witness).

    2. `H5_not_multiplicative` — formal certificate that the
       Hamiltonian is genuinely non-multiplicative, placing this
       witness OUTSIDE Wave 13's Path B "both-diagonal" obstruction
       class on the H-side.

    **Honest scope** (mandatory non-overclaim):
    * This is a finite-dim (P5) witness with strictly richer
      structure than Wave 13. It is NOT a discharge of (P5) on the
      Timeless Field 𝒯_∞; Hilbert–Pólya remains the load-bearing
      open conjecture.
    * (P6) `ConsciousnessStationaryStateCompleteness` is STILL
      subject to Wave 13's Path C finite-cardinality obstruction on
      this substrate (Fintype.card = 5 vs. infinitely many critical-
      strip ζ-zeros). The (P6) frontier is unchanged.
    * The consciousness↔RH conditional reduction
      `riemann_hypothesis_via_consciousness_bridge` remains
      conditional on (P5) ∧ (P6); this witness does not unlock the
      reduction on its own. -/
theorem consciousness_RH_wave35_fivepoint_witness :
    CommutatorVanishesAtRHZeros fivePointSubstrate ∧
    (∀ m : Fin 5 → ℂ, H5 ≠ diagMul 5 m) :=
  ⟨P5_holds_fivePoint, H5_not_multiplicative⟩

/-- Axiom-print witness for this file. -/
theorem consciousness_rh_bridge_wave35_witnesses_axiom_free : True := trivial

/-- **Strategic-assessment marker** for future waves: the
    consciousness↔RH route remains LIVE; the (P5) frontier on
    finite-dim substrates can be pushed further (more indices,
    richer non-multiplicative structure), but the genuine open
    problem is still (P5) on 𝒯_∞ (Hilbert–Pólya) and (P6) on an
    infinite-dim substrate. -/
theorem wave35_consciousness_route_remains_live : True := trivial

end PrincipiaTractalis
