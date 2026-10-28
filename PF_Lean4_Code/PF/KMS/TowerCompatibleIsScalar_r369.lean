/-
# r369: `TowerCompatible` is VACUOUS — and the condition that replaces it

★ 2026-10-28 r369 — a vacuity finding against my own r367/r368 ★

## The finding

r367 defined

    TowerCompatible X  :=  ∀ k, substrateRingHom k (X k) = X (k+1)

and r368 descended the modular automorphisms of such a family to an
automorphism of `T_∞`. Both files are **correct**. But the hypothesis is far
stronger than it looks, and this file proves what it actually permits:

> **`TowerCompatible X` forces every `X k` to be a scalar multiple of the
> identity.** Hence `ω_{X k}` is the normalized trace, `σ_{X k}` is the
> identity, and r368's `substrateModularAut` is the **identity map on `T_∞`**.

So r368, under its own hypothesis, constructs nothing but the identity. That is
a vacuity defect in the *definition*, not an error in either proof, and it is
recorded here rather than left for someone to discover downstream.

### Why it happens — a one-line diagnosis

`TowerCompatible` determines `X (k+1)` from `X k`, so the whole family is
determined by `X 0`. And `X 0 : Matrix (Fin (3^0)) (Fin (3^0)) ℂ` is a **1×1**
matrix, hence a scalar. The embedding is ℂ-linear and unital
(`substrateEmbedMatrix_smul`, `substrateEmbedMatrix_one`), so scalars propagate
up the tower and stay scalars. The condition pushes information *upward* from a
one-dimensional base, and a one-dimensional base has none to give.

This is the same shape as the obstruction `THE MAP` §0 already records: a trace
generates no dynamics. r363 proved that for one level; this proves the strong
tower condition cannot escape it.

## What is proved

* `one_by_one_eq_smul_one` — every `1×1` matrix is `c • 1`;
* **`towerCompatible_isScalar`** — `TowerCompatible X → ∀ k, ∃ c, X k = c • 1`;
* `towerCompatible_scalar_ne_zero` — and that `c ≠ 0` when the weight is
  invertible;
* **`substrateModularAut_eq_id_of_towerCompatible`** — therefore r368's
  automorphism is the identity on every element of `T_∞`.

## The repair, stated precisely

The physically correct family is **product-type**: a new factor at each level,

    X_{k+1}  =  embed(X_k) · newFactor(x_k),
    newFactor(x) := reindex (I_{3^k} ⊗ₖ x)   for a 3×3 weight x,

so that `X_k = x_1 ⊗ x_2 ⊗ ⋯ ⊗ x_k`. This is *not* determined by `X 0`, so the
scalar collapse does not apply.

And the intertwining still holds, for a reason worth stating because it is the
whole mechanism: `newFactor(x)` **commutes** with `embed(a)` for every `a` —
they act on different tensor slots — so

    σ_{embed(X)·newFactor(x)}(embed a)
      = embed(X)·newFactor(x)·embed(a)·newFactor(x)⁻¹·embed(X)⁻¹
      = embed(X)·embed(a)·embed(X)⁻¹                    [the new factor cancels]
      = embed(σ_X(a)).

So r368's descent machinery is **reusable unchanged** — what has to be replaced
is only the hypothesis feeding it. The right move is to restate the lift against
the *intertwining* property directly rather than against weight equality, since
the intertwining is what `DirectLimit.Ring.lift` actually consumes. Conjugation
is insensitive to central factors, which is exactly the slack the strong
condition threw away.

## What is NOT claimed

The product-type construction is **not** built here — this file proves the
vacuity and names the repair. Not claimed: that product-type families are
invertible, that their limit state is non-tracial, or any statement about the
`C*` completion. Those belong to the repair.

## Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-28.
-/
import PF.KMS.SubstrateModularAutomorphism_r368

set_option autoImplicit false

namespace PF.KMS

open Matrix
open PrincipiaTractalis.SubstrateBase3Embed
open PrincipiaTractalis.SubstrateBase3RingHom
open PrincipiaTractalis.SubstrateDirectLimit

/-! ## §1 — A 1×1 matrix is a scalar -/

lemma one_by_one_eq_smul_one (A : Matrix (Fin 1) (Fin 1) ℂ) :
    A = (A 0 0) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-! ## §2 — The strong tower condition forces scalars -/

/-- **★★★ r369: `TowerCompatible` forces every weight to be scalar ★★★**

The condition determines the family from `X 0`, which lives in a `1×1` matrix
algebra; the embedding is ℂ-linear and unital, so scalars propagate and stay
scalars. -/
theorem towerCompatible_isScalar
    {X : ∀ k : ℕ, Matrix (Fin (3^k)) (Fin (3^k)) ℂ}
    (hX : TowerCompatible X) :
    ∀ k : ℕ, ∃ c : ℂ, X k = c • (1 : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) := by
  intro k
  induction k with
  | zero =>
      exact ⟨X 0 0 0, one_by_one_eq_smul_one (X 0)⟩
  | succ k ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨c, ?_⟩
      have h := hX k
      rw [hc] at h
      -- `substrateRingHom k` is `substrateEmbedMatrix k`, which is ℂ-linear
      -- and unital, so it carries `c • 1` to `c • 1`.
      have hlin : substrateRingHom k (c • (1 : Matrix (Fin (3^k)) (Fin (3^k)) ℂ))
          = c • (1 : Matrix (Fin (3^(k+1))) (Fin (3^(k+1))) ℂ) := by
        show substrateEmbedMatrix k (c • (1 : Matrix (Fin (3^k)) (Fin (3^k)) ℂ))
            = c • (1 : Matrix (Fin (3^(k+1))) (Fin (3^(k+1))) ℂ)
        rw [substrateEmbedMatrix_smul, substrateEmbedMatrix_one]
      rw [hlin] at h
      exact h.symm

/-- An invertible scalar weight has a nonzero scalar. -/
lemma towerCompatible_scalar_ne_zero {n : ℕ} [Nonempty (Fin n)] {c : ℂ}
    (h : IsUnit ((c • (1 : Matrix (Fin n) (Fin n) ℂ))).det) : c ≠ 0 := by
  intro hc
  rw [hc, zero_smul, Matrix.det_zero (by infer_instance)] at h
  exact (not_isUnit_zero) h

/-! ## §3 — Hence r368's automorphism is the identity -/

/-- **★★★ r369: r368's `substrateModularAut` is the IDENTITY ★★★**

Under its own hypothesis, the descended automorphism of `T_∞` is trivial. The
construction is sound; the hypothesis admits nothing else. -/
theorem substrateModularAut_eq_id_of_towerCompatible
    (X : ∀ k : ℕ, Matrix (Fin (3^k)) (Fin (3^k)) ℂ)
    (hX : TowerCompatible X) (hdet : ∀ k, IsUnit (X k).det)
    (x : TimelessFieldRing) :
    substrateModularAut X hX hdet x = x := by
  induction x using DirectLimit.induction with
  | _ k a =>
      obtain ⟨c, hc⟩ := towerCompatible_isScalar hX k
      haveI hpos : Nonempty (Fin (3^k)) :=
        ⟨⟨0, Nat.pos_of_ne_zero (by positivity)⟩⟩
      have hne : c ≠ 0 := by
        have hu := hdet k
        rw [hc] at hu
        exact towerCompatible_scalar_ne_zero hu
      -- the level-wise statement first: rewriting `X k` inside
      -- `modularAutHom (X k) (hdet k)` is not type correct, because the proof
      -- argument depends on it.  `modularAut` carries no proof, so the
      -- rewrite is fine here, and `congrArg` lifts it.
      have hlevel : modularAut (X k) a = a := by
        rw [hc]
        exact modularAut_of_scalar c hne a
      exact congrArg (DirectLimit.Ring.of _ _ k) hlevel

end PF.KMS

/-! ## §Axiom check -/
#print axioms PF.KMS.one_by_one_eq_smul_one
#print axioms PF.KMS.towerCompatible_isScalar
#print axioms PF.KMS.towerCompatible_scalar_ne_zero
#print axioms PF.KMS.substrateModularAut_eq_id_of_towerCompatible
