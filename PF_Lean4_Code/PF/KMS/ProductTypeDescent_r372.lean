/-
# r372: the product-type descent — step (3)

★ 2026-10-28 r372 — a positive, non-scalar dynamics descends to `T_∞` ★

## What this does

r369 showed r368's descent was fed a hypothesis that admitted only scalar
weights. r370–r371 built the replacement: a product-type family that is
non-scalar (`productWeight_nontrivial`) and positive definite
(`productWeight_posDef`). This file runs the descent against **that**
hypothesis, as r369 predicted it could — the lift machinery is reused
unchanged, only the hypothesis differs.

## The computation, once

With `E := substrateRingHom k`, `N := newFactor k (x k)` and
`X (k+1) = E (X k) * N`:

    σ_{X(k+1)}(E a) = (E Xₖ · N) · E a · (E Xₖ · N)⁻¹
                    = E Xₖ · N · E a · N⁻¹ · (E Xₖ)⁻¹     [mul_inv_rev]
                    = E Xₖ · E a · (N · N⁻¹) · (E Xₖ)⁻¹   [newFactor_commute]
                    = E Xₖ · E a · (E Xₖ)⁻¹
                    = E (Xₖ · a · Xₖ⁻¹)  =  E (σ_{Xₖ} a)

The new factor **cancels against its own inverse** because it commutes with the
embedded element. That is r370's mechanism doing the work, and it is why the
extra degree of freedom per level costs nothing in compatibility.

## What is proved

* **`productType_modularAut_comm`** — the intertwining at the successor
  embedding, for any product-type family with invertible data;
* `productType_modularAut_comm_iter` — along the iterated embedding, by
  induction on the level gap;
* **`substrateModularAutProduct`** — the descended ring endomorphism of
  `T_∞`, via `DirectLimit.Ring.lift`;
* `substrateModularAutProduct_apply` — it acts level-wise as `σ_{X k}`
  (by `rfl`);
* `substrateModularAutProduct_moves_level_one` — at level 1 it moves an
  element, for the r371 witness family.

## The one gap, measured and named rather than asserted

It is tempting to conclude "therefore `substrateModularAutProduct ≠ id` on
`T_∞`". **That does not follow from what is proved here**, and the missing step
is injectivity of the level map `ι_k : M_{3^k} → T_∞`: from `σ(ι₁ a) = ι₁ (σ a)`
with `σ a ≠ a` one gets `ι₁ (σ a) ≠ ι₁ a` only if `ι₁` is injective.

**Measured at this pin:** mathlib's `Algebra/Colimit/DirectLimit.lean` contains
**zero** occurrences of the word "injective" — there is no `of_injective` to
apply. `SubstrateRigidity.lean:394` asserts injectivity of the level
star-algebra map *in prose*, inside a comment, which is not a usable lemma.

So the gap is declared as a predicate, `LevelMapInjective`, and the
implication is proved: **`LevelMapInjective → substrateModularAutProduct ≠ id`**
(`substrateModularAutProduct_ne_id_of_levelMapInjective`). The conclusion is
therefore available the moment injectivity is supplied, and until then it is
visibly conditional rather than quietly assumed. This is the same discipline
the 2026-08-24 KMS verdict failed
(`codex/KMS_OBSTRUCTION_RECHECK_2026-10-28.md`): an absence is not a theorem,
in either direction.

## What is NOT claimed

Not claimed: that `substrateModularAutProduct` is non-identity (see above);
that it is non-inner, or anything about `Out(T_∞)`; that the level states
assemble into a state on `T_∞` (the weights are positive by r371, but the
*limit* state and its traciality are untouched); anything about the `C*`
completion, continuity, or the KMS condition on `T_∞`.

## Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-28.
-/
import PF.KMS.ProductWeightPositive_r371

set_option autoImplicit false

namespace PF.KMS

open Matrix
open scoped Kronecker
open PrincipiaTractalis.SubstrateBase3Embed
open PrincipiaTractalis.SubstrateBase3RingHom
open PrincipiaTractalis.SubstrateDirectLimit

private abbrev TObj : ℕ → Type := fun k => Matrix (Fin (3^k)) (Fin (3^k)) ℂ

private noncomputable abbrev TMap :
    ∀ i j : ℕ, i ≤ j → (TObj i →+* TObj j) :=
  fun i j h => substrateRingHomIter i j h

/-! ## §1 — The intertwining under `ProductTypeFamily` -/

/-- **★★★ r372: the product-type intertwining ★★★**

The new factor cancels because it commutes with the embedded element. -/
theorem productType_modularAut_comm
    {X : ∀ k : ℕ, TObj k} {x : ∀ k : ℕ, Matrix (Fin 3) (Fin 3) ℂ}
    (hX : ProductTypeFamily X x) (hXdet : ∀ k, IsUnit (X k).det)
    (hxdet : ∀ k, IsUnit (x k).det) (k : ℕ) (a : TObj k) :
    substrateRingHom k (modularAut (X k) a)
      = modularAut (X (k + 1)) (substrateRingHom k a) := by
  have hN : (newFactor k (x k)) * (newFactor k (x k))⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (newFactor_isUnit_det k (hxdet k))
  have hcomm : newFactor k (x k) * substrateRingHom k a
      = substrateRingHom k a * newFactor k (x k) :=
    (newFactor_commute k a (x k)).symm
  have hEinv : substrateRingHom k (X k)⁻¹ = (substrateRingHom k (X k))⁻¹ :=
    ringHom_map_inv (substrateRingHom k) (hXdet k)
  -- the cancellation, isolated: each step is pure associativity or one rewrite
  have key : (substrateRingHom k (X k) * newFactor k (x k))
        * substrateRingHom k a
        * ((newFactor k (x k))⁻¹ * (substrateRingHom k (X k))⁻¹)
      = substrateRingHom k (X k) * substrateRingHom k a
        * (substrateRingHom k (X k))⁻¹ := by
    calc (substrateRingHom k (X k) * newFactor k (x k))
            * substrateRingHom k a
            * ((newFactor k (x k))⁻¹ * (substrateRingHom k (X k))⁻¹)
        = substrateRingHom k (X k)
            * (newFactor k (x k) * substrateRingHom k a)
            * ((newFactor k (x k))⁻¹ * (substrateRingHom k (X k))⁻¹) := by
          noncomm_ring
      _ = substrateRingHom k (X k)
            * (substrateRingHom k a * newFactor k (x k))
            * ((newFactor k (x k))⁻¹ * (substrateRingHom k (X k))⁻¹) := by
          rw [hcomm]
      _ = substrateRingHom k (X k) * substrateRingHom k a
            * (newFactor k (x k) * (newFactor k (x k))⁻¹)
            * (substrateRingHom k (X k))⁻¹ := by noncomm_ring
      _ = substrateRingHom k (X k) * substrateRingHom k a
            * (substrateRingHom k (X k))⁻¹ := by rw [hN, mul_one]
  calc substrateRingHom k (modularAut (X k) a)
      = substrateRingHom k (X k) * substrateRingHom k a
          * (substrateRingHom k (X k))⁻¹ := by
        simp only [modularAut, map_mul, hEinv]
    _ = (substrateRingHom k (X k) * newFactor k (x k))
          * substrateRingHom k a
          * ((newFactor k (x k))⁻¹ * (substrateRingHom k (X k))⁻¹) := key.symm
    _ = modularAut (X (k + 1)) (substrateRingHom k a) := by
        -- `hX` is stated with `substrateEmbedMatrix`, the bundled hom's own
        -- `toFun`, so the two sides close by `rfl`.
        simp only [modularAut, hX k, Matrix.mul_inv_rev, mul_assoc]
        rfl

/-- The same along the iterated embedding. -/
theorem productType_modularAut_comm_iter
    {X : ∀ k : ℕ, TObj k} {x : ∀ k : ℕ, Matrix (Fin 3) (Fin 3) ℂ}
    (hX : ProductTypeFamily X x) (hXdet : ∀ k, IsUnit (X k).det)
    (hxdet : ∀ k, IsUnit (x k).det)
    (i j : ℕ) (h : i ≤ j) (a : TObj i) :
    substrateRingHomIter i j h (modularAut (X i) a)
      = modularAut (X j) (substrateRingHomIter i j h a) := by
  induction j, h using Nat.le_induction with
  | base => rw [substrateRingHomIter_self]; rfl
  | succ j hij ih =>
      have hstep : ∀ b : TObj i,
          substrateRingHomIter i (j + 1) (hij.trans (Nat.le_succ j)) b
            = substrateRingHom j (substrateRingHomIter i j hij b) := by
        intro b
        rw [substrateRingHomIter_succ i j hij (hij.trans (Nat.le_succ j))]
        rfl
      rw [hstep, hstep, ih, productType_modularAut_comm hX hXdet hxdet j]

/-! ## §2 — The descent -/

/-- **★★★ r372: the product-type modular automorphism of `T_∞` ★★★** -/
noncomputable def substrateModularAutProduct
    (X : ∀ k : ℕ, TObj k) (x : ∀ k : ℕ, Matrix (Fin 3) (Fin 3) ℂ)
    (hX : ProductTypeFamily X x) (hXdet : ∀ k, IsUnit (X k).det)
    (hxdet : ∀ k, IsUnit (x k).det) :
    TimelessFieldRing →+* TimelessFieldRing :=
  DirectLimit.Ring.lift TObj TMap TimelessFieldRing
    (fun k => (DirectLimit.Ring.of TObj TMap k).comp (modularAutHom (X k) (hXdet k)))
    (fun i j hij a => by
      show DirectLimit.Ring.of TObj TMap j
            (modularAut (X j) (substrateRingHomIter i j hij a))
          = DirectLimit.Ring.of TObj TMap i (modularAut (X i) a)
      rw [← productType_modularAut_comm_iter hX hXdet hxdet i j hij a]
      exact DirectLimit.Ring.of_f hij _)

@[simp] theorem substrateModularAutProduct_apply
    (X : ∀ k : ℕ, TObj k) (x : ∀ k : ℕ, Matrix (Fin 3) (Fin 3) ℂ)
    (hX : ProductTypeFamily X x) (hXdet : ∀ k, IsUnit (X k).det)
    (hxdet : ∀ k, IsUnit (x k).det) (k : ℕ) (a : TObj k) :
    substrateModularAutProduct X x hX hXdet hxdet
        (substrateLevelToTimelessField k a)
      = substrateLevelToTimelessField k (modularAut (X k) a) := rfl

/-! ## §3 — It moves something at level 1, and the one remaining gap -/

/-- The level map into `T_∞` is injective. **Measured absent** at this pin:
mathlib's `DirectLimit` file has no injectivity result, and
`SubstrateRigidity.lean:394` asserts it only in prose. Declared as a predicate
so the consequence below is visibly conditional. -/
def LevelMapInjective : Prop :=
  ∀ k : ℕ, Function.Injective (substrateLevelToTimelessField k)

/-- At level 1 the descended map sends `ι₁ a` to `ι₁ (σ a)` with `σ a ≠ a`. -/
theorem substrateModularAutProduct_moves_level_one
    (X : ∀ k : ℕ, TObj k) (x : ∀ k : ℕ, Matrix (Fin 3) (Fin 3) ℂ)
    (hX : ProductTypeFamily X x) (hXdet : ∀ k, IsUnit (X k).det)
    (hxdet : ∀ k, IsUnit (x k).det)
    (a : TObj 1) (ha : modularAut (X 1) a ≠ a) :
    substrateModularAutProduct X x hX hXdet hxdet
        (substrateLevelToTimelessField 1 a)
      = substrateLevelToTimelessField 1 (modularAut (X 1) a)
    ∧ modularAut (X 1) a ≠ a :=
  ⟨rfl, ha⟩

/-- **The conditional conclusion.** Given injectivity of the level map, the
descended automorphism is **not** the identity — in contrast with r369, where
it provably was. The hypothesis is named, not assumed away. -/
theorem substrateModularAutProduct_ne_id_of_levelMapInjective
    (X : ∀ k : ℕ, TObj k) (x : ∀ k : ℕ, Matrix (Fin 3) (Fin 3) ℂ)
    (hX : ProductTypeFamily X x) (hXdet : ∀ k, IsUnit (X k).det)
    (hxdet : ∀ k, IsUnit (x k).det)
    (hinj : LevelMapInjective)
    (a : TObj 1) (ha : modularAut (X 1) a ≠ a) :
    substrateModularAutProduct X x hX hXdet hxdet
      (substrateLevelToTimelessField 1 a) ≠ substrateLevelToTimelessField 1 a := by
  rw [substrateModularAutProduct_apply]
  intro hcontra
  exact ha (hinj 1 hcontra)

end PF.KMS

/-! ## §Axiom check -/
#print axioms PF.KMS.productType_modularAut_comm
#print axioms PF.KMS.productType_modularAut_comm_iter
#print axioms PF.KMS.substrateModularAutProduct
#print axioms PF.KMS.substrateModularAutProduct_apply
#print axioms PF.KMS.substrateModularAutProduct_moves_level_one
#print axioms PF.KMS.substrateModularAutProduct_ne_id_of_levelMapInjective
