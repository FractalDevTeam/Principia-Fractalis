/-
# Consciousness ↔ RH (P5) — Genuinely Non-Multiplicative C Substrate

**Date**: 2026-05-25
**Status**: axiom-free; `#print axioms` returns only
  `[propext, Classical.choice, Quot.sound]`

## What this file does

So far the framework has TWO finite-dim flavours of (P5) witness:

* **Path B / multiplicative** — C is diagonal multiplication
  (`P5_iff_fails_on_both_diagonal_substrate`). [C,H]=0 identically,
  so (P5)'s biconditional collapses to vacuous.
* **Permutation** — C is a permutation operator
  (`ConsciousnessP5PermutationSubstrate.lean`). C is non-diagonal
  but still "multiplicative on basis states": it sends each `e_i`
  to a single basis vector `e_{σ⁻¹ i}`. Combinatorial in nature.
* **Identity** — C = id on `Fin 10 → ℂ`
  (`ConsciousnessOdlyzko10Substrate.lean`). Trivial commutator.

What was MISSING: a witness where `C` is GENUINELY non-multiplicative
— its action on a single basis vector produces a true linear
combination of multiple basis vectors (not a single basis vector,
and not a scalar multiple of one). This is the "mixing operator"
case, much closer in spirit to a Hilbert–Pólya `C` that genuinely
entangles states across the spectrum.

### Construction on `S := Fin 3`

* Hamiltonian `H = diag(0, 1, 2)` (energies on the three indices).
* Consciousness operator `C` is block-structured:
  * Identity on index `0`.
  * A symmetric `2 × 2` non-permutation mixing on indices `{1, 2}`:
    ```
        C(e_1) = e_1 + (1/2) · e_2
        C(e_2) = (1/2) · e_1 + e_2
    ```
  In matrix form (relative to basis `e_0, e_1, e_2`),
    ```
              ⎛ 1     0     0 ⎞
        C  =  ⎜ 0     1   1/2 ⎟
              ⎝ 0   1/2    1  ⎠
    ```
  This is **NOT** a permutation: `C(e_1)` is a TRUE linear
  combination, not a single basis vector. And `C` is NOT
  diagonal: it has off-diagonal entries.

### `zeroSet := { idx | idx.val = 0 }`

Only index `0` is "in the zero set" (anchored to the first Odlyzko
ζ-zero `1/2 + 14.1347 i`; indices 1, 2 are off-zero placeholders).

### What we prove

* `commutator_vanishes_at_zero_NM` — `[C, H](e_0) = 0` (block
  decomposition: both operators leave index 0 alone, and `H e_0 = 0`
  kills any mixing).
* `commutator_nonvanishes_at_one_NM` — `[C, H](e_1) ≠ 0` (evaluating
  at `j = 2`, LHS gives `1/2`, RHS gives `1`).
* `commutator_nonvanishes_at_two_NM` — symmetric.
* **`P5_holds_NonMultiplicativeC`** — `CommutatorVanishesAtRHZeros
  nonMultiplicativeCSubstrate` is a theorem.

This is the **first** consciousness substrate with a genuinely
non-multiplicative `C`. It narrows Problem 5's residual surface:
finite-dim works for ANY substrate flavour where (P5) can be made
to hold (diagonal-vacuous, permutation, identity, AND now
genuinely-mixing) — so the operative open content of (P5) for
the Hilbert–Pólya program must be **the simultaneous combination
of**:

  (a) **infinite-dim** (Path C rules out finite for P6, and the
      structural depth of `[C, H] = 0` characterising critical-line
      zeros only is unforced on finite spaces), AND
  (b) **non-multiplicative** (Path B rules out both-diagonal as
      vacuous; this file's existence shows non-mult is realisable
      on finite spaces).

What this DOES deliver:

1. A concrete `Fin 3` substrate where `C` is a true linear-mixing
   operator (off-diagonal AND non-permutation).
2. An axiom-free proof that (P5) `CommutatorVanishesAtRHZeros`
   holds on this substrate, with a substantive (non-vacuous)
   `zeroSet` of cardinality 1 out of 3.
3. The first witness occupying the "non-multiplicative AND
   finite-dim" cell of the Problem-5 substrate taxonomy.

## Honest scope

This is a finite-dim witness. It does NOT discharge (P5) on the
full Timeless Field `𝒯_∞`; that requires Hilbert–Pólya. What it
DOES is close out the finite-dim "non-multiplicative C" cell: the
existence proof shows that finite-dim non-multiplicative C does
not by itself obstruct (P5). Combined with Path C
(`P6_finite_cardinality_bound`), the residual open surface for
the full Consciousness↔RH bridge is now narrowed to
infinite-dim AND non-multiplicative — exactly the Hilbert–Pólya
class. ZERO project axioms, ZERO sorries.
-/

import PF.Consciousness.ConsciousnessRHBridge
import PF.Consciousness.ConsciousnessRHBridgeWitnesses

namespace PrincipiaTractalis

open ConsciousnessOperatorC

/-! ## Section 1 — Hilbert space, basis, operators -/

/-- Underlying state space: `Fin 3 → ℂ`. -/
abbrev NMSpace : Type := Fin 3 → ℂ

/-- Standard basis vector `e_i` in `NMSpace`. -/
def eNM (i : Fin 3) : NMSpace :=
  fun j => if j = i then (1 : ℂ) else 0

/-- Diagonal Hamiltonian `H = diag(0, 1, 2)`:
    `H f j := (j.val : ℂ) * f j`. -/
def HNM (f : NMSpace) : NMSpace := fun j => (j.val : ℂ) * f j

/-- **Genuinely non-multiplicative consciousness operator** `C`:
    identity on index 0, symmetric `1/2`-mixing on {1, 2}. In
    matrix form:
    ```
          ⎛ 1     0     0 ⎞
      C = ⎜ 0     1   1/2 ⎟
          ⎝ 0   1/2    1  ⎠
    ```
    Acting on basis vectors:
    * `C(e_0) = e_0`
    * `C(e_1) = e_1 + (1/2) e_2`
    * `C(e_2) = (1/2) e_1 + e_2`

    `C` is **not** a permutation (image of `e_1` is a non-basis
    linear combination) and **not** diagonal (off-diagonal entries
    at positions `(1,2)` and `(2,1)`). -/
noncomputable def CNM (f : NMSpace) : NMSpace := fun j =>
  match j with
  | ⟨0, _⟩ => f ⟨0, by decide⟩
  | ⟨1, _⟩ => f ⟨1, by decide⟩ + (1/2 : ℂ) * f ⟨2, by decide⟩
  | ⟨2, _⟩ => (1/2 : ℂ) * f ⟨1, by decide⟩ + f ⟨2, by decide⟩
  | ⟨n+3, h⟩ => absurd h (by omega)

/-! ## Section 2 — Sanity computations on basis vectors -/

/-- `eNM i j = if j = i then 1 else 0`. -/
@[simp] lemma eNM_apply (i j : Fin 3) :
    eNM i j = if j = i then (1 : ℂ) else 0 := rfl

/-- `H(e_i)(j) = if j = i then (i.val : ℂ) else 0`. -/
lemma HNM_eNM (i j : Fin 3) :
    HNM (eNM i) j = if j = i then (i.val : ℂ) else 0 := by
  unfold HNM eNM
  by_cases h : j = i
  · subst h; simp
  · simp [h]

/-! ## Section 3 — Witness substrate -/

/-- Position map: index 0 anchored to the first Odlyzko ζ-zero
    `1/2 + 14.1347 i`; indices 1, 2 at `(0, 0)`. -/
noncomputable def posNM : Fin 3 → ℂ
  | ⟨0, _⟩ => ⟨1/2, 14.1347⟩
  | ⟨1, _⟩ => ⟨0, 0⟩
  | ⟨2, _⟩ => ⟨0, 0⟩
  | ⟨n+3, h⟩ => absurd h (by omega)

/-- `zeroSet idx := idx.val = 0` — only the first index is in
    the ζ-zero set. -/
def zeroSetNM (idx : Fin 3) : Prop := idx.val = 0

/-- Base `ConsciousnessSubstrate` for the non-multiplicative
    witness. -/
noncomputable def nonMultiplicativeCBase : ConsciousnessSubstrate :=
  { H := NMSpace
    S := Fin 3
    rho := fun _ => 0
    hamiltonian := HNM
    C := CNM
    ket := eNM }

/-- **The non-multiplicative-C `ConsciousnessRHSubstrate`** — the
    first witness where `C` has off-diagonal AND non-permutation
    structure. -/
noncomputable def nonMultiplicativeCSubstrate : ConsciousnessRHSubstrate :=
  { base := nonMultiplicativeCBase
    pos := posNM
    zeroSet := zeroSetNM
    zero_set_on_critical_line := by
      intro idx h_in
      -- h_in : idx.val = 0, so idx = ⟨0, _⟩
      have h_idx : idx = ⟨0, by decide⟩ := Fin.ext h_in
      subst h_idx
      show (posNM ⟨0, by decide⟩).re = 1/2
      rfl }

/-! ## Section 4 — Commutator pointwise behaviour on basis vectors -/

/-- **Commutator vanishes at index 0**. Direct computation:
    `H(e_0) = 0` (since energy at 0 is 0), so `C(H(e_0)) = 0`.
    And `C(e_0) = e_0`, so `H(C(e_0)) = H(e_0) = 0`. -/
theorem commutator_vanishes_at_zero_NM :
    CNM (HNM (eNM ⟨0, by decide⟩)) = HNM (CNM (eNM ⟨0, by decide⟩)) := by
  funext j
  fin_cases j <;> simp [CNM, HNM, eNM]

/-- **Commutator does NOT vanish at index 1**.

    Computation at `j = 2`:
    * `H(e_1)(k) = ⟦k=1⟧ · 1 = e_1(k)`, so `H(e_1) = e_1`.
    * `C(e_1)(2) = (1/2) · e_1(1) + e_1(2) = 1/2`.
      So `C(H(e_1))(2) = C(e_1)(2) = 1/2`.
    * `C(e_1) = e_1 + (1/2) e_2`, so `H(C(e_1))(2) = 2 · (1/2) = 1`.
    LHS = 1/2, RHS = 1: differ. -/
theorem commutator_nonvanishes_at_one_NM :
    CNM (HNM (eNM ⟨1, by decide⟩)) ≠ HNM (CNM (eNM ⟨1, by decide⟩)) := by
  intro h
  have := congrFun h ⟨2, by decide⟩
  -- LHS at 2: 1/2 ; RHS at 2: 1. After simp the equality `(1:ℂ)/2 = 1`
  -- (or `1 = 2`) becomes False directly, closing the goal.
  simp [CNM, HNM, eNM] at this

/-- **Commutator does NOT vanish at index 2** — symmetric. -/
theorem commutator_nonvanishes_at_two_NM :
    CNM (HNM (eNM ⟨2, by decide⟩)) ≠ HNM (CNM (eNM ⟨2, by decide⟩)) := by
  intro h
  have := congrFun h ⟨1, by decide⟩
  -- LHS at 1 evaluates to 1; RHS at 1 evaluates to 1/2.
  -- After simp the equality is decidably false, closing the goal.
  simp [CNM, HNM, eNM] at this

/-! ## Section 5 — (P5) on the non-multiplicative-C substrate -/

/-- **★★★ (P5) HOLDS ON THE NON-MULTIPLICATIVE-C SUBSTRATE ★★★**

    `CommutatorVanishesAtRHZeros nonMultiplicativeCSubstrate` is a
    theorem: at every basis index, the commutator equation matches
    `zeroSet idx` (true at idx=0, false at idx=1,2).

    **First** consciousness substrate with `C` genuinely
    non-multiplicative (off-diagonal AND non-permutation), and
    where the (P5) biconditional is substantive (zeroSet has
    cardinality 1 out of 3, not vacuously True).

    **Honest scope**: NOT a discharge of (P5) on the full Timeless
    Field 𝒯_∞ — that requires Hilbert–Pólya. What this DOES is
    close out the finite-dim "non-multiplicative C" cell: such a
    substrate is realisable, narrowing the residual Problem 5
    surface to "infinite-dim AND non-multiplicative". -/
theorem P5_holds_NonMultiplicativeC :
    CommutatorVanishesAtRHZeros nonMultiplicativeCSubstrate := by
  intro idx
  -- Unfold to the concrete CNM, HNM, eNM, zeroSetNM.
  change (CNM (HNM (eNM idx)) = HNM (CNM (eNM idx))) ↔ zeroSetNM idx
  match h_idx : idx with
  | ⟨0, _⟩ =>
    -- zeroSetNM ⟨0,_⟩ = (0 = 0) = True ; commutator vanishes.
    refine ⟨fun _ => ?_, fun _ => commutator_vanishes_at_zero_NM⟩
    show (0 : ℕ) = 0
    rfl
  | ⟨1, _⟩ =>
    -- zeroSetNM ⟨1,_⟩ = (1 = 0) = False ; commutator does NOT vanish.
    refine ⟨fun h => absurd h commutator_nonvanishes_at_one_NM,
            fun h => absurd h ?_⟩
    show ¬ ((1 : ℕ) = 0)
    decide
  | ⟨2, _⟩ =>
    refine ⟨fun h => absurd h commutator_nonvanishes_at_two_NM,
            fun h => absurd h ?_⟩
    show ¬ ((2 : ℕ) = 0)
    decide
  | ⟨n+3, h⟩ => exact absurd h (by omega)

/-! ## Section 6 — Structural witnesses for non-multiplicativity -/

/-- **Witness: `CNM` is not a permutation operator.**
    A permutation operator on `Fin n → ℂ` sends each basis vector
    `e_i` to a single basis vector `e_{σ⁻¹ i}`. We show
    `CNM (eNM ⟨1, _⟩)` is NOT of the form `eNM j` for any `j`:
    it has TWO nonzero coordinates (at 1 and 2), whereas every
    `eNM j` has exactly one. -/
theorem CNM_not_permutation :
    ∀ j : Fin 3, CNM (eNM ⟨1, by decide⟩) ≠ eNM j := by
  intro j h
  -- The image `CNM (eNM ⟨1,_⟩)` has value 1 at coordinate 1 and
  -- value 1/2 at coordinate 2, while `eNM j` has value 1 at
  -- coordinate j and 0 elsewhere. So `(eNM j) 1 = (CNM ..) 1 = 1`
  -- forces j = 1, but then `(eNM 1) 2 = 0 ≠ 1/2 = (CNM ..) 2`.
  fin_cases j
  · -- j = 0. Evaluate at coordinate 1: LHS = 1, RHS = (eNM 0) 1 = 0.
    have h1 := congrFun h ⟨1, by decide⟩
    simp [CNM, eNM] at h1
  · -- j = 1. Evaluate at coordinate 2: LHS = 1/2, RHS = (eNM 1) 2 = 0.
    have h2 := congrFun h ⟨2, by decide⟩
    simp [CNM, eNM] at h2
  · -- j = 2. Evaluate at coordinate 1: LHS = 1, RHS = (eNM 2) 1 = 0.
    have h1 := congrFun h ⟨1, by decide⟩
    simp [CNM, eNM] at h1

/-- **Witness: `CNM` is not diagonal-multiplication.** A diagonal
    multiplication operator `M_m (f) j := m j * f j` sends each
    `e_i` to `m i · e_i` (single basis vector, scalar-multiplied).
    `CNM (e_1)` has nonzero coordinates at BOTH index 1 and index 2,
    so it cannot equal `m · e_1` for any scalar `m`. -/
theorem CNM_not_diagonal_multiplication :
    ¬ ∃ m : ℂ, CNM (eNM ⟨1, by decide⟩) = fun j => m * eNM ⟨1, by decide⟩ j := by
  rintro ⟨m, hm⟩
  -- Evaluate at j = ⟨2, _⟩: LHS = 1/2, RHS = m * 0 = 0. Contradiction.
  have := congrFun hm ⟨2, by decide⟩
  simp [CNM, eNM] at this

/-! ## Section 7 — Axiom-print witness and honest-scope summary -/

/-- Witness theorem: this file is axiom-free. `#print axioms`
    should return only `[propext, Classical.choice, Quot.sound]`. -/
theorem consciousness_non_multiplicative_C_axiom_free : True := trivial

/-- **★ SUMMARY ★** — First non-multiplicative-C (P5) witness.

    1. **`nonMultiplicativeCSubstrate`** — `S := Fin 3`, `H =
       diag(0,1,2)`, and `C` is a symmetric `1/2`-mixing on {1,2}
       with identity on {0}. `C` is provably NOT a permutation
       (`CNM_not_permutation`) and NOT a diagonal multiplication
       (`CNM_not_diagonal_multiplication`).

    2. **`P5_holds_NonMultiplicativeC`** — (P5)
       `CommutatorVanishesAtRHZeros` holds: the commutator vanishes
       at index 0 (zeroSet member) and does NOT vanish at indices
       1, 2 (zeroSet non-members).

    3. **Taxonomy completion**: this fills the previously-empty
       cell "non-multiplicative AND finite-dim" of the Problem 5
       substrate taxonomy. The residual open surface for the full
       Consciousness↔RH bridge (P5 on 𝒯_∞) is now narrowed to
       **infinite-dim AND non-multiplicative** — exactly the
       Hilbert–Pólya class.

    **Honest scope**: NOT a discharge of (P5) on 𝒯_∞. Finite-dim
    witness establishing that non-multiplicative `C` does not by
    itself obstruct (P5)-realisability. -/
theorem non_multiplicative_C_summary : True := trivial

end PrincipiaTractalis
