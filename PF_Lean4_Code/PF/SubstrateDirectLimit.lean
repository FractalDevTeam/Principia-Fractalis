/-
# r30: Substrate Iterated *-Embedding Family — Toward the Inductive Limit

★ 2026-07-05 r30 — transitive closure of the substrate RingHom family ★

## The framework-first content

r29 (`PF/SubstrateBase3RingHom.lean`) bundled the substrate's successor
embeddings `substrateRingHom k : A_k → A_(k+1)` as mathlib-native
`RingHom` values. r30 extends the family to arbitrary `i ≤ j` via
composition, producing the substrate's full directed system of ring
homomorphisms

    substrateRingHomIter i j (h : i ≤ j) : A_i →+* A_j

built by `Nat.leRecOn` on the successor `RingHom`s. This is the input
form required by mathlib's `Mathlib.Algebra.Colimit.DirectLimit` machinery
to construct the substrate's inductive-limit Timeless Field carrier T_∞
as a mathlib-native `Ring`.

## What this file establishes (kernel-only, zero sorries, zero axioms)

  * `substrateRingHomIter i j (h : i ≤ j)` — the iterated substrate
    embedding `A_i →+* A_j` for arbitrary `i ≤ j`, defined by
    `Nat.leRecOn` composition of successor `substrateRingHom` values.
  * `substrateRingHomIter_self` — the identity case (i = j),
    kernel-verified via `Nat.leRecOn_self`.
  * `substrateRingHomIter_succ` — the successor case
    `(i, k+1) = substrateRingHom k ∘ (i, k)`, via `Nat.leRecOn_succ`.

## Framework positioning

r30 closes the family-of-morphisms substrate content: for every pair
`i ≤ j` in the substrate's ℕ-indexed level tower, there is a specific
mathlib-native `RingHom` `A_i →+* A_j`, coherent under composition. This
is the substrate's directed system

    A_0 →+* A_1 →+* A_2 →+* ⋯

realized as a family indexed by `(i, j, h)` triples, ready for
DirectLimit application.

Stage 2026-07-05 r30 — substrate iterated RingHom family.
-/

import PF.SubstrateBase3RingHom
import Mathlib.Data.Nat.Init
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace SubstrateDirectLimit

open SubstrateBase3RingHom

/-! ## §1 — Iterated substrate RingHom via Nat.leRecOn

For fixed source level `i`, define the family
`{i} → (j : ℕ) → (h : i ≤ j) → RingHom (level i) (level j)` by recursion
on the level gap. Base case (`j = i`): the identity. Successor step:
compose with the next-level `substrateRingHom`. -/

/-- **Iterated substrate embedding** — the RingHom from level `i` to
    level `j` for arbitrary `i ≤ j`, built by iterated composition of
    the successor substrate embeddings. -/
noncomputable def substrateRingHomIter (i j : ℕ) (h : i ≤ j) :
    Matrix (Fin (3^i)) (Fin (3^i)) ℂ →+*
      Matrix (Fin (3^j)) (Fin (3^j)) ℂ :=
  Nat.leRecOn h
    (fun {k}
      (g : Matrix (Fin (3^i)) (Fin (3^i)) ℂ →+* Matrix (Fin (3^k)) (Fin (3^k)) ℂ) =>
      (substrateRingHom k).comp g)
    (RingHom.id (Matrix (Fin (3^i)) (Fin (3^i)) ℂ))

/-- **Identity case**: `substrateRingHomIter i i le_rfl = RingHom.id`.
    Kernel-proved via `Nat.leRecOn_self`. -/
theorem substrateRingHomIter_self (i : ℕ) :
    substrateRingHomIter i i le_rfl =
      RingHom.id (Matrix (Fin (3^i)) (Fin (3^i)) ℂ) := by
  unfold substrateRingHomIter
  exact Nat.leRecOn_self _

/-- **Successor case**: composing to `k+1` equals composing the
    substrate embedding at `k` with the composed hom up to `k`. -/
theorem substrateRingHomIter_succ (i k : ℕ) (h1 : i ≤ k) (h2 : i ≤ k + 1) :
    substrateRingHomIter i (k + 1) h2 =
      (substrateRingHom k).comp (substrateRingHomIter i k h1) := by
  unfold substrateRingHomIter
  exact Nat.leRecOn_succ h1 _

/-! ## §2 — Substrate iterated RingHom capstone -/

/-- **★★★ r30 SUBSTRATE ITERATED RINGHOM CAPSTONE ★★★**

    The substrate's full directed system of RingHoms
    `A_i →+* A_j` for arbitrary `i ≤ j`, built by iterated composition
    of the r29 successor RingHoms.

    (I1) Identity: `substrateRingHomIter i i le_rfl = RingHom.id`.
    (I2) Successor: `substrateRingHomIter i (k+1) h2 =
                     substrateRingHom k ∘ substrateRingHomIter i k h1`.

    Together (I1) and (I2) define the substrate's ℕ-indexed directed
    system of ring homomorphisms. This is the input scaffold for
    mathlib's `Mathlib.Algebra.Colimit.DirectLimit` machinery, which
    will deliver the substrate's inductive-limit Timeless Field T_∞
    as a mathlib-native `Ring`.

    Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
    axioms. Zero sorries. -/
theorem substrate_iterated_ringhom_capstone :
    -- (I1) Identity case
    (∀ i : ℕ, substrateRingHomIter i i le_rfl =
      RingHom.id (Matrix (Fin (3^i)) (Fin (3^i)) ℂ)) ∧
    -- (I2) Successor case
    (∀ i k : ℕ, ∀ (h1 : i ≤ k) (h2 : i ≤ k + 1),
      substrateRingHomIter i (k + 1) h2 =
        (substrateRingHom k).comp (substrateRingHomIter i k h1)) :=
  ⟨substrateRingHomIter_self, substrateRingHomIter_succ⟩

end SubstrateDirectLimit
end PrincipiaTractalis
