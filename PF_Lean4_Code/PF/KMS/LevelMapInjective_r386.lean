/-
# r386: `LevelMapInjective` discharged — the substrate dynamics is non-identity

★ 2026-10-29 r386 — r372's named gap closed, and the conditional made
unconditional ★

## The gap, and why it stayed open

r372 descended the level-wise modular automorphisms to a ring automorphism `Σ`
of `T_∞`, and could not show `Σ ≠ id` **as a map**. It needed injectivity of the
level map `ι_k : M_{3^k} → T_∞`, declared the requirement as a predicate
`LevelMapInjective`, and proved the implication
`LevelMapInjective → substrateModularAutProduct ≠ id`. Its header recorded why
the predicate was left open:

> **Measured at this pin:** mathlib's `Algebra/Colimit/DirectLimit.lean` contains
> **zero** occurrences of the word "injective" — there is no `of_injective` to
> apply.

**That measurement is exactly right, and the conclusion drawn from it was
wrong.** Re-measured at this pin: `Algebra/Colimit/DirectLimit.lean` does exist
and does contain **0** occurrences of "injective". The file was real and the
count was correct.

It is one file of five in that directory, and the siblings hold 23 occurrences
between them:

| file | occurrences of "injective" |
|---|---|
| `DirectLimit.lean` — the one searched | **0** |
| `Ring.lean` | 12 |
| `Module.lean` | 10 |
| `Finiteness.lean` | 1 |
| `TensorProduct.lean` | 0 |

So the failure was **scope, not naming and not execution** — the same family as
this project's standing note that a guard's scope must be audited and not just
its existence. The usable tool is `Ring.DirectLimit.of.zero_exact`, in
`Ring.lean`; a grep of the *directory* would have hit that file's twelve.

And for the *root* `DirectLimit` that `T_∞` is actually built on, even that is
unnecessary: the setoid relation is right there, and `Quotient.eq` unfolds it in
one step. That is the route taken below.

So the gap was never a gap in mathlib. It was a gap in the sweep's radius. This
file closes it from the definitions, needing nothing from mathlib's colimit API
beyond `Quotient.eq`.

## The proof, which is short

Two steps.

1. **The connecting maps are injective.** `substrateEmbedMatrix k A` is
   `reindex (levelStepEquiv k) (levelStepEquiv k) (A ⊗ₖ 1₃)`. `reindex` is an
   `Equiv`, so it is injective; and `A ↦ A ⊗ₖ 1₃` is injective because `A` is
   readable off the `(·,0),(·,0)` entries: `(A ⊗ₖ 1₃) (i,0) (j,0) = A i j · 1`.
   Iterating over the level gap by `Nat.le_induction` gives injectivity of
   `substrateRingHomIter i j`.

2. **Injective connecting maps give an injective level map.** `T_∞` is
   `Quotient (DirectLimit.setoid ·)`, whose relation is
   `∃ i (hx : x.1 ≤ i) (hy : y.1 ≤ i), f _ _ hx x.2 = f _ _ hy y.2`. From
   `ι_k x = ι_k y`, `Quotient.eq` produces a common level `j` with
   `f k j hx x = f k j hy y`; the two proofs of `k ≤ j` are proofs of the same
   `Prop`, so the maps coincide, and step 1 finishes.

## What this unlocks

`substrateModularAutProduct_ne_id_of_levelMapInjective` (r372) becomes
unconditional. So for a product-type weight family with a non-scalar factor, the
descended modular automorphism of `T_∞` is **provably not the identity map** —
not merely non-trivial in its action on a state. Combined with r379's KMS
identity and r378's non-tracial `Ω`, the dynamics on `T_∞` is now non-trivial in
both senses: it moves an element of the algebra, and it is visible to the state.

## What is NOT claimed

Unchanged from r372 and r379: nothing about `Out(T_∞)` (non-identity is not
non-inner); nothing about the `C*` completion or continuity; `Ω` is still not
shown to be a state in the full `C*` sense (positivity is level-wise). And
nothing here computes a spectral datum or touches the physical dictionary — the
gap `THE MAP` §5(A) actually cares about is untouched, as r379 said.

r113 remains untouched: it is a theorem about *tracial* states.

## Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-29.
-/
import PF.KMS.ProductTypeDescent_r372

set_option autoImplicit false

namespace PF.KMS

open Matrix
open scoped Kronecker
open PrincipiaTractalis.SubstrateBase3Embed
open PrincipiaTractalis.SubstrateBase3RingHom
open PrincipiaTractalis.SubstrateDirectLimit

/-! ## §1 — `A ↦ A ⊗ₖ 1` is injective

`A` is readable off the `(·,0),(·,0)` entries of the Kronecker product. -/

lemma kronecker_one_right_injective {n : ℕ} :
    Function.Injective
      (fun A : Matrix (Fin n) (Fin n) ℂ =>
        A ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ)) := by
  intro A B h
  ext i j
  have hij := congrFun (congrFun h (i, 0)) (j, 0)
  simpa using hij

/-! ## §2 — The connecting maps are injective -/

lemma substrateEmbedMatrix_injective (k : ℕ) :
    Function.Injective (substrateEmbedMatrix k) := fun _ _ h =>
  kronecker_one_right_injective
    ((Matrix.reindex (levelStepEquiv k) (levelStepEquiv k)).injective h)

lemma substrateRingHom_injective (k : ℕ) :
    Function.Injective (substrateRingHom k) :=
  substrateEmbedMatrix_injective k

/-- **The iterated connecting map is injective**, for every level gap. -/
theorem substrateRingHomIter_injective (i j : ℕ) (h : i ≤ j) :
    Function.Injective (substrateRingHomIter i j h) := by
  induction j, h using Nat.le_induction with
  | base =>
      have hself : substrateRingHomIter i i (Nat.le_refl i)
          = RingHom.id (Matrix (Fin (3^i)) (Fin (3^i)) ℂ) :=
        substrateRingHomIter_self i
      rw [hself]
      exact fun _ _ hxy => hxy
  | succ k hik ih =>
      rw [substrateRingHomIter_succ i k hik (Nat.le_succ_of_le hik),
        RingHom.coe_comp]
      exact (substrateRingHom_injective k).comp ih

/-! ## §3 — The level map into `T_∞` is injective -/

/-- **★★★ r386: `LevelMapInjective` — r372's named gap, discharged ★★★**

From the setoid relation directly. No mathlib colimit API beyond `Quotient.eq`. -/
theorem levelMapInjective : LevelMapInjective := by
  intro k x y hxy
  unfold substrateLevelToTimelessField at hxy
  obtain ⟨j, hx, hy, heq⟩ := Quotient.eq.mp hxy
  exact substrateRingHomIter_injective k j hx heq

/-! ## §4 — The conditional, made unconditional -/

/-- **★ r386: the substrate dynamics moves an element of `T_∞` ★**

r372's implication with its hypothesis supplied. -/
theorem substrateModularAutProduct_moves
    (X : ∀ k : ℕ, Matrix (Fin (3^k)) (Fin (3^k)) ℂ)
    (x : ∀ _ : ℕ, Matrix (Fin 3) (Fin 3) ℂ)
    (hX : ProductTypeFamily X x) (hXdet : ∀ k, IsUnit (X k).det)
    (hxdet : ∀ k, IsUnit (x k).det)
    (a : Matrix (Fin (3^1)) (Fin (3^1)) ℂ) (ha : modularAut (X 1) a ≠ a) :
    substrateModularAutProduct X x hX hXdet hxdet
        (substrateLevelToTimelessField 1 a)
      ≠ substrateLevelToTimelessField 1 a :=
  substrateModularAutProduct_ne_id_of_levelMapInjective
    X x hX hXdet hxdet levelMapInjective a ha

/-- **★ r386: and so it is not the identity ring homomorphism ★** -/
theorem substrateModularAutProduct_ne_id
    (X : ∀ k : ℕ, Matrix (Fin (3^k)) (Fin (3^k)) ℂ)
    (x : ∀ _ : ℕ, Matrix (Fin 3) (Fin 3) ℂ)
    (hX : ProductTypeFamily X x) (hXdet : ∀ k, IsUnit (X k).det)
    (hxdet : ∀ k, IsUnit (x k).det)
    (a : Matrix (Fin (3^1)) (Fin (3^1)) ℂ) (ha : modularAut (X 1) a ≠ a) :
    substrateModularAutProduct X x hX hXdet hxdet
      ≠ RingHom.id TimelessFieldRing := by
  intro hid
  exact substrateModularAutProduct_moves X x hX hXdet hxdet a ha (by rw [hid]; rfl)

end PF.KMS

/-! ## §Axiom check -/
#print axioms PF.KMS.kronecker_one_right_injective
#print axioms PF.KMS.substrateEmbedMatrix_injective
#print axioms PF.KMS.substrateRingHom_injective
#print axioms PF.KMS.substrateRingHomIter_injective
#print axioms PF.KMS.levelMapInjective
#print axioms PF.KMS.substrateModularAutProduct_moves
#print axioms PF.KMS.substrateModularAutProduct_ne_id
