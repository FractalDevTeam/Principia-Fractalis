/-
# r29: Substrate Base-3 Embeddings Bundled as RingHom — Toward the Direct Limit

★ 2026-07-05 r29 — bundling the substrate directed system for mathlib DirectLimit ★

## The framework-first content

r28 (`PF/SubstrateBase3Embed.lean`) established the substrate's inter-level
embeddings `substrateEmbedMatrix k : A_k → A_(k+1)` as real *-algebra maps
with six kernel-proved preservation properties (0, +, •, ×, 1, *).

r29 bundles those preservation properties into a genuine mathlib-native
`RingHom` — the standard bundled homomorphism type in mathlib for
non-commutative rings. This is the necessary bundling step for applying
mathlib's `Mathlib.Algebra.Colimit.DirectLimit` machinery to the
substrate directed system, delivering the substrate's inductive-limit
Timeless Field T_∞ as a mathlib-native `Ring`.

## What this file establishes (kernel-only, zero sorries, zero axioms)

  * `substrateRingHom k : SubstrateLevel k →+* SubstrateLevel (k+1)` —
    the substrate's inter-level *-embedding bundled as a `RingHom`,
    constructed directly from the r28 preservation properties.
  * Kernel-verified: `substrateRingHom_apply` unfolds to
    `substrateEmbedMatrix`, connecting the bundled form to the r28
    function definition.
  * Kernel-verified: the RingHom bundle preserves all four ring
    operations (zero, add, one, mul) by construction from r28.

## Framework positioning

r29 turns r28's function-level *-algebra homomorphisms into mathlib-
native `RingHom` bundles, providing the input type mathlib's
`DirectedSystem` and `DirectLimit` require. The substrate's Timeless
Field T_∞ as a mathlib-native `Ring` via inductive limit is the next
substrate step; r29 provides the bundled homomorphism scaffolding it
requires.

Stage 2026-07-05 r29 — substrate embeddings bundled as mathlib RingHom.
-/

import PF.SubstrateBase3Embed
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace SubstrateBase3RingHom

open SubstrateBase3Embed

/-! ## §1 — Substrate embedding bundled as RingHom

The `RingHom` type in mathlib bundles four operation-preservation
properties: `map_zero'`, `map_add'`, `map_one'`, `map_mul'`, along
with the underlying function `toFun`. We construct the substrate's
`RingHom k : SubstrateLevel k →+* SubstrateLevel (k+1)` from r28's
kernel-proved preservation properties, working at the underlying
`Matrix` level. -/

/-- **Substrate embedding as a `RingHom`** — the r28 embedding
    `substrateEmbedMatrix k` bundled with its four ring-hom properties.
    Source and target are the underlying `Matrix` types of the substrate
    level C*-algebras. -/
noncomputable def substrateRingHom (k : ℕ) :
    Matrix (Fin (3^k)) (Fin (3^k)) ℂ →+* Matrix (Fin (3^(k+1))) (Fin (3^(k+1))) ℂ where
  toFun := substrateEmbedMatrix k
  map_zero' := substrateEmbedMatrix_zero k
  map_add' := substrateEmbedMatrix_add k
  map_one' := substrateEmbedMatrix_one k
  map_mul' := substrateEmbedMatrix_mul k

/-! ## §2 — RingHom preservation lemmas (kernel-checked corollaries) -/

/-- The bundled substrate `RingHom` applied to A equals the r28
    embedding of A. Definitional. -/
@[simp]
theorem substrateRingHom_apply (k : ℕ) (A : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    substrateRingHom k A = substrateEmbedMatrix k A := rfl

/-- The bundled `RingHom` sends 0 to 0. -/
theorem substrateRingHom_zero (k : ℕ) :
    substrateRingHom k 0 = 0 := (substrateRingHom k).map_zero

/-- The bundled `RingHom` sends 1 to 1. -/
theorem substrateRingHom_one (k : ℕ) :
    substrateRingHom k 1 = 1 := (substrateRingHom k).map_one

/-- The bundled `RingHom` respects addition. -/
theorem substrateRingHom_add (k : ℕ) (A B : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    substrateRingHom k (A + B) = substrateRingHom k A + substrateRingHom k B :=
  (substrateRingHom k).map_add A B

/-- The bundled `RingHom` respects multiplication. -/
theorem substrateRingHom_mul (k : ℕ) (A B : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    substrateRingHom k (A * B) = substrateRingHom k A * substrateRingHom k B :=
  (substrateRingHom k).map_mul A B

/-! ## §3 — Substrate directed system: substrate embeddings capstone -/

/-- **★★★ r29 SUBSTRATE RINGHOM CAPSTONE ★★★**

    The substrate's inter-level embedding `ι_k : A_k → A_(k+1)` is a
    genuine mathlib-native `RingHom` between the level-k and level-(k+1)
    matrix rings. Four ring-hom preservation properties bundled from
    r28's kernel-proved substrate embedding lemmas:

    (R1) `substrateRingHom k 0 = 0`
    (R2) `substrateRingHom k (A + B) = ι(A) + ι(B)`
    (R3) `substrateRingHom k 1 = 1`
    (R4) `substrateRingHom k (A * B) = ι(A) * ι(B)`

    Together with `substrateRingHom_apply`, this establishes the
    substrate embedding at r28's underlying `Matrix` level as a
    genuine mathlib-native `RingHom`, providing the input bundling
    that mathlib's `DirectedSystem` and `DirectLimit` machinery
    require for the substrate's inductive-limit construction.

    Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
    axioms. Zero sorries. -/
theorem substrate_ringhom_capstone (k : ℕ) :
    (substrateRingHom k 0 = 0) ∧
    (substrateRingHom k 1 = 1) ∧
    (∀ A B : Matrix (Fin (3^k)) (Fin (3^k)) ℂ,
      substrateRingHom k (A + B) = substrateRingHom k A + substrateRingHom k B) ∧
    (∀ A B : Matrix (Fin (3^k)) (Fin (3^k)) ℂ,
      substrateRingHom k (A * B) = substrateRingHom k A * substrateRingHom k B) ∧
    (∀ A : Matrix (Fin (3^k)) (Fin (3^k)) ℂ,
      substrateRingHom k A = substrateEmbedMatrix k A) :=
  ⟨substrateRingHom_zero k,
   substrateRingHom_one k,
   substrateRingHom_add k,
   substrateRingHom_mul k,
   substrateRingHom_apply k⟩

end SubstrateBase3RingHom
end PrincipiaTractalis
