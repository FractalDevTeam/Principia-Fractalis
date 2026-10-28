/-
# r367: level-wise dynamics are compatible with the tower — step 5a

★ 2026-10-28 r367 — the modular automorphism intertwines with the substrate
embedding ★

## The question step 5 has to answer

r363–r366 build a KMS pair at a **single** matrix level. The substrate is the
inductive limit of the tower `M_{3^k}`
(`SubstrateDirectLimit.lean:176`, `TimelessFieldRing`), with successor
embeddings `substrateRingHom k : M_{3^k} →+* M_{3^{k+1}}`. A family of
level-wise dynamics is only meaningful on `T_∞` if it **commutes with those
embeddings** — otherwise the level-`k` answer and the level-`(k+1)` answer
disagree on the same element of the limit, and nothing descends.

So the question is: when does a family of weights `X : ∀ k, M_{3^k}` induce one
automorphism of `T_∞`?

## The answer, and why it is cheap

If the weights themselves embed —

    substrateRingHom k (X k) = X (k+1)

— then the modular automorphisms intertwine automatically, and the argument is
**pure ring-hom algebra**: no exponential, no continuity, no analysis. A
`RingHom` `φ` satisfies `φ(X a X⁻¹) = φX · φa · φ(X)⁻¹`, because
`φ(X)·φ(X⁻¹) = φ(X·X⁻¹) = φ(1) = 1` forces `φ(X⁻¹) = (φX)⁻¹`.

That is worth stating plainly: **the hard-looking part of step 5 is not the
dynamics, it is the weights.** Once the weights are tower-compatible the flows
come along for free. The analysis only re-enters when one asks for `exp` of a
tower-compatible generator, which needs `φ ∘ exp = exp ∘ φ` and hence
continuity of `φ` — deliberately avoided here.

## What is proved

* `modularAutHom` — `modularAut X` bundled as a `RingHom`, using r363's
  multiplicativity and unitality plus additivity. So the modular automorphism
  is a genuine ring endomorphism, which is what `DirectLimit.lift` consumes;
* `ringHom_map_inv` — a `RingHom` carries the inverse of a unit to the inverse;
* **`ringHom_modularAut_comm`** — the general intertwining: for any `RingHom`
  `φ` and weights with `φ X = Y`, `φ (σ_X a) = σ_Y (φ a)`;
* **`substrate_modularAut_comm`** — the substrate instance, at the successor
  embedding;
* `substrate_modularAut_comm_iter` — the same along the **iterated** embedding
  `substrateRingHomIter i j h`, by induction on the level gap.

## What is NOT claimed

The descent itself is **not** claimed here: this file supplies the compatibility
hypothesis that `DirectLimit.lift`
(`Mathlib/Algebra/Colimit/DirectLimit.lean:489`, the `→+*` version) requires,
but does not invoke it. Also not claimed: that any *particular* physically
interesting weight family is tower-compatible, that `exp` of a tower-compatible
generator is tower-compatible (that needs continuity of the embedding), that
the induced state on `T_∞` is non-tracial, or anything about the `C*`
completion. Those are 5b onward.

Note the shape of what remains: tower-compatibility as defined here is a strong
condition — it says each weight is literally the image of the previous one. The
physically natural family is `H_{k+1} = ι(H_k) + (a term on the new factor)`,
which is **not** of this form at the level of weights, though it is what makes
product-type dynamics work. Recording that gap honestly: this file handles the
embedded-weight case, which is the one that needs no analysis.

## Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-28.
-/
import PF.KMS.ImaginaryTimeFlow_r366
import PF.SubstrateDirectLimit

set_option autoImplicit false

namespace PF.KMS

open Matrix
open PrincipiaTractalis.SubstrateBase3RingHom
open PrincipiaTractalis.SubstrateDirectLimit

/-! ## §1 — The modular automorphism as a bundled `RingHom` -/

section Bundled

variable {n : ℕ}

lemma modularAut_zero (X : Matrix (Fin n) (Fin n) ℂ) : modularAut X 0 = 0 := by
  simp [modularAut]

lemma modularAut_add (X a b : Matrix (Fin n) (Fin n) ℂ) :
    modularAut X (a + b) = modularAut X a + modularAut X b := by
  simp only [modularAut]
  noncomm_ring

/-- `modularAut X` bundled as a ring endomorphism. This is the form
`DirectLimit.lift` consumes. -/
noncomputable def modularAutHom (X : Matrix (Fin n) (Fin n) ℂ)
    (hX : IsUnit X.det) :
    Matrix (Fin n) (Fin n) ℂ →+* Matrix (Fin n) (Fin n) ℂ where
  toFun := modularAut X
  map_one' := modularAut_one X hX
  map_mul' := modularAut_mul X hX
  map_zero' := modularAut_zero X
  map_add' := modularAut_add X

@[simp] lemma modularAutHom_apply (X : Matrix (Fin n) (Fin n) ℂ)
    (hX : IsUnit X.det) (a : Matrix (Fin n) (Fin n) ℂ) :
    modularAutHom X hX a = modularAut X a := rfl

end Bundled

/-! ## §2 — A `RingHom` carries the modular automorphism along -/

/-- A `RingHom` sends the inverse of an invertible matrix to the inverse of its
image. Pure algebra: `φX · φ(X⁻¹) = φ 1 = 1`. -/
lemma ringHom_map_inv {m k : ℕ}
    (φ : Matrix (Fin m) (Fin m) ℂ →+* Matrix (Fin k) (Fin k) ℂ)
    {X : Matrix (Fin m) (Fin m) ℂ} (hX : IsUnit X.det) :
    φ X⁻¹ = (φ X)⁻¹ := by
  refine (Matrix.inv_eq_right_inv ?_).symm
  rw [← map_mul, Matrix.mul_nonsing_inv X hX, map_one]

/-- **★★★ r367: the general intertwining ★★★**

For any `RingHom` `φ` and weights related by `φ X = Y`, the modular
automorphisms commute with `φ`. No exponential, no continuity. -/
theorem ringHom_modularAut_comm {m k : ℕ}
    (φ : Matrix (Fin m) (Fin m) ℂ →+* Matrix (Fin k) (Fin k) ℂ)
    {X : Matrix (Fin m) (Fin m) ℂ} {Y : Matrix (Fin k) (Fin k) ℂ}
    (hX : IsUnit X.det) (hXY : φ X = Y) (a : Matrix (Fin m) (Fin m) ℂ) :
    φ (modularAut X a) = modularAut Y (φ a) := by
  simp only [modularAut]
  rw [map_mul, map_mul, ringHom_map_inv φ hX, hXY]

/-! ## §3 — The substrate instance -/

/-- A weight family that embeds along the tower. -/
def TowerCompatible (X : ∀ k : ℕ, Matrix (Fin (3^k)) (Fin (3^k)) ℂ) : Prop :=
  ∀ k : ℕ, substrateRingHom k (X k) = X (k + 1)

/-- **★★★ r367: the substrate instance at the successor embedding ★★★** -/
theorem substrate_modularAut_comm
    {X : ∀ k : ℕ, Matrix (Fin (3^k)) (Fin (3^k)) ℂ}
    (hX : TowerCompatible X) (hdet : ∀ k, IsUnit (X k).det) (k : ℕ)
    (a : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    substrateRingHom k (modularAut (X k) a)
      = modularAut (X (k + 1)) (substrateRingHom k a) :=
  ringHom_modularAut_comm (substrateRingHom k) (hdet k) (hX k) a

/-- The same along the iterated embedding, by induction on the level gap. This
is the form the `DirectLimit` compatibility hypothesis is stated in. -/
theorem substrate_modularAut_comm_iter
    {X : ∀ k : ℕ, Matrix (Fin (3^k)) (Fin (3^k)) ℂ}
    (hX : TowerCompatible X) (hdet : ∀ k, IsUnit (X k).det)
    (i j : ℕ) (h : i ≤ j) (a : Matrix (Fin (3^i)) (Fin (3^i)) ℂ) :
    substrateRingHomIter i j h (modularAut (X i) a)
      = modularAut (X j) (substrateRingHomIter i j h a) := by
  induction j, h using Nat.le_induction with
  | base =>
      rw [substrateRingHomIter_self]
      rfl
  | succ j hij ih =>
      have hstep : ∀ b : Matrix (Fin (3^i)) (Fin (3^i)) ℂ,
          substrateRingHomIter i (j + 1) (hij.trans (Nat.le_succ j)) b
            = substrateRingHom j (substrateRingHomIter i j hij b) := by
        intro b
        rw [substrateRingHomIter_succ i j hij (hij.trans (Nat.le_succ j))]
        rfl
      rw [hstep, hstep, ih, substrate_modularAut_comm hX hdet j]

end PF.KMS

/-! ## §Axiom check -/
#print axioms PF.KMS.modularAut_add
#print axioms PF.KMS.modularAutHom
#print axioms PF.KMS.ringHom_map_inv
#print axioms PF.KMS.ringHom_modularAut_comm
#print axioms PF.KMS.substrate_modularAut_comm
#print axioms PF.KMS.substrate_modularAut_comm_iter
