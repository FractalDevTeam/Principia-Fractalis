/-
# r368: the modular automorphism OF `T_∞` — step 5b, the descent

★ 2026-10-28 r368 — a dynamics-induced automorphism of the substrate itself ★

## What this does

r367 proved the compatibility hypothesis: for a tower-compatible weight family,
the level-wise modular automorphisms commute with the iterated substrate
embedding. That is exactly what mathlib's
`DirectLimit.Ring.lift` (`Mathlib/Algebra/Colimit/DirectLimit.lean:489`)
consumes. This file invokes it.

The result, `substrateModularAut`, is a **ring endomorphism of
`TimelessFieldRing` itself** — of `T_∞`, not of its levels — and
`substrateModularAut_inv_left` / `_right` show it is **bijective**, so it is an
automorphism. It is the first object in this corpus that is an automorphism of
the substrate *constructed from a dynamics* rather than classified abstractly.

## What is proved

* `substrateLevelToTimelessField_eq_of` — the project's level embedding is
  mathlib's `DirectLimit.Ring.of`, definitionally;
* **`substrateModularAut`** — the lifted endomorphism of `T_∞`;
* **`substrateModularAut_apply`** — it acts level-wise as expected:
  `σ(ι_k a) = ι_k (σ_{X k} a)`. This is what makes it *the* modular
  automorphism rather than an abstract lift;
* `modularAut_inv_left`, `modularAut_inv_right` — `σ_{X⁻¹}` inverts `σ_X`;
* `towerCompatible_inv` — the inverse weight family is tower-compatible, so it
  too descends;
* **`substrateModularAut_inv_left`, `substrateModularAut_inv_right`** — the two
  descended maps are mutually inverse. Hence `substrateModularAut` is an
  automorphism of `T_∞`.

## Where this does and does not bear on the open problems

`ch04:461` records that `Out(T_∞) = Aut/Inn` is open, and that covariance — the
sixth Haag–Kastler axiom — is blocked on that classification. This file
supplies automorphisms of `T_∞`, so the connection is real and worth naming.

**But it is not claimed to touch `Out`.** Each `σ_{X k}` is *inner* at its own
level (conjugation by a unit of `M_{3^k}`), so the descended map is a limit of
level-wise inner automorphisms and plausibly lies in the closure of
`Inn(T_∞)`. Whether it is inner *in* `T_∞`, and whether any such family can
escape `Inn`, is **unmeasured here** and must not be asserted either way. What
is established is weaker and still new: a dynamics gives a concrete, verified
automorphism of the substrate, and the construction is uniform in the weight
family.

## What is NOT claimed

Not claimed: that `substrateModularAut` is non-inner, anything about `Out`, any
statement about the `C*` completion `TimelessFieldCompletion` (this is the
algebraic limit `TimelessFieldRing`), a state on `T_∞`, the KMS condition on
`T_∞`, continuity in any topology, or that physically natural product-type
weight families satisfy `TowerCompatible` — r367's header records that the
additive family `H_{k+1} = ι(H_k) + (new-factor term)` is *not* of this form at
the level of weights, and that gap is untouched here.

## Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-28.
-/
import PF.KMS.TowerCompatibleDynamics_r367

set_option autoImplicit false

namespace PF.KMS

open Matrix
open PrincipiaTractalis.SubstrateBase3RingHom
open PrincipiaTractalis.SubstrateDirectLimit

/-- The substrate tower, as the directed system mathlib's `DirectLimit` wants. -/
private abbrev TowerObj : ℕ → Type := fun k => Matrix (Fin (3^k)) (Fin (3^k)) ℂ

private noncomputable abbrev towerMap :
    ∀ i j : ℕ, i ≤ j → (TowerObj i →+* TowerObj j) :=
  fun i j h => substrateRingHomIter i j h

/-! ## §1 — The project's level embedding is mathlib's `of` -/

lemma substrateLevelToTimelessField_eq_of (k : ℕ) (a : TowerObj k) :
    substrateLevelToTimelessField k a
      = DirectLimit.Ring.of TowerObj towerMap k a := rfl

/-! ## §2 — `σ_X` inverts, level-wise -/

section LevelInverse

variable {n : ℕ}

lemma modularAut_inv_left {X : Matrix (Fin n) (Fin n) ℂ} (hX : IsUnit X.det)
    (a : Matrix (Fin n) (Fin n) ℂ) :
    modularAut X⁻¹ (modularAut X a) = a := by
  have h1 : X⁻¹ * X = 1 := Matrix.nonsing_inv_mul X hX
  have h2 : (X⁻¹)⁻¹ = X := Matrix.nonsing_inv_nonsing_inv X hX
  simp only [modularAut, h2]
  calc X⁻¹ * (X * a * X⁻¹) * X
      = (X⁻¹ * X) * a * (X⁻¹ * X) := by noncomm_ring
    _ = a := by rw [h1, one_mul, mul_one]

lemma modularAut_inv_right {X : Matrix (Fin n) (Fin n) ℂ} (hX : IsUnit X.det)
    (a : Matrix (Fin n) (Fin n) ℂ) :
    modularAut X (modularAut X⁻¹ a) = a := by
  have h1 : X * X⁻¹ = 1 := Matrix.mul_nonsing_inv X hX
  have h2 : (X⁻¹)⁻¹ = X := Matrix.nonsing_inv_nonsing_inv X hX
  simp only [modularAut, h2]
  calc X * (X⁻¹ * a * X) * X⁻¹
      = (X * X⁻¹) * a * (X * X⁻¹) := by noncomm_ring
    _ = a := by rw [h1, one_mul, mul_one]

end LevelInverse

/-! ## §3 — The inverse weight family is also tower-compatible -/

lemma isUnit_det_inv {n : ℕ} {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : IsUnit X.det) : IsUnit (X⁻¹).det := by
  rw [Matrix.det_nonsing_inv]
  exact hX.ringInverse

/-- If a weight family embeds along the tower, so does the family of
inverses — because a `RingHom` carries inverses to inverses (r367). -/
lemma towerCompatible_inv {X : ∀ k : ℕ, TowerObj k}
    (hX : TowerCompatible X) (hdet : ∀ k, IsUnit (X k).det) :
    TowerCompatible (fun k => (X k)⁻¹) := by
  intro k
  rw [ringHom_map_inv (substrateRingHom k) (hdet k), hX k]

/-! ## §4 — The descent -/

/-- **★★★ r368: the modular automorphism of `T_∞` ★★★**

The level-wise modular automorphisms of a tower-compatible weight family
descend to a ring endomorphism of the substrate itself. -/
noncomputable def substrateModularAut
    (X : ∀ k : ℕ, TowerObj k) (hX : TowerCompatible X)
    (hdet : ∀ k, IsUnit (X k).det) :
    TimelessFieldRing →+* TimelessFieldRing :=
  DirectLimit.Ring.lift TowerObj towerMap TimelessFieldRing
    (fun k => (DirectLimit.Ring.of TowerObj towerMap k).comp
      (modularAutHom (X k) (hdet k)))
    (fun i j hij a => by
      -- `show` rather than `simp`: the two sides are definitionally the
      -- composites, and simp does not beta-reduce `RingHom.comp` here.
      show DirectLimit.Ring.of TowerObj towerMap j
            (modularAut (X j) (substrateRingHomIter i j hij a))
          = DirectLimit.Ring.of TowerObj towerMap i (modularAut (X i) a)
      rw [← substrate_modularAut_comm_iter hX hdet i j hij a]
      exact DirectLimit.Ring.of_f hij _)

/-- **It acts level-wise as the modular automorphism.** This is what makes the
lift *the* modular automorphism of `T_∞` rather than an abstract map. -/
@[simp] theorem substrateModularAut_apply
    (X : ∀ k : ℕ, TowerObj k) (hX : TowerCompatible X)
    (hdet : ∀ k, IsUnit (X k).det) (k : ℕ) (a : TowerObj k) :
    substrateModularAut X hX hdet (substrateLevelToTimelessField k a)
      = substrateLevelToTimelessField k (modularAut (X k) a) := rfl

/-! ## §5 — It is an automorphism -/

/-- The descended inverse. -/
private noncomputable abbrev invAut (X : ∀ k : ℕ, TowerObj k)
    (hX : TowerCompatible X) (hdet : ∀ k, IsUnit (X k).det) :
    TimelessFieldRing →+* TimelessFieldRing :=
  substrateModularAut (fun k => (X k)⁻¹) (towerCompatible_inv hX hdet)
    (fun k => isUnit_det_inv (hdet k))

theorem substrateModularAut_inv_left
    (X : ∀ k : ℕ, TowerObj k) (hX : TowerCompatible X)
    (hdet : ∀ k, IsUnit (X k).det) (x : TimelessFieldRing) :
    invAut X hX hdet (substrateModularAut X hX hdet x) = x := by
  induction x using DirectLimit.induction with
  | _ k a =>
      exact congrArg (DirectLimit.Ring.of TowerObj towerMap k)
        (modularAut_inv_left (hdet k) a)

theorem substrateModularAut_inv_right
    (X : ∀ k : ℕ, TowerObj k) (hX : TowerCompatible X)
    (hdet : ∀ k, IsUnit (X k).det) (x : TimelessFieldRing) :
    substrateModularAut X hX hdet (invAut X hX hdet x) = x := by
  induction x using DirectLimit.induction with
  | _ k a =>
      exact congrArg (DirectLimit.Ring.of TowerObj towerMap k)
        (modularAut_inv_right (hdet k) a)

/-- **`substrateModularAut` is bijective**, hence an automorphism of `T_∞`. -/
theorem substrateModularAut_bijective
    (X : ∀ k : ℕ, TowerObj k) (hX : TowerCompatible X)
    (hdet : ∀ k, IsUnit (X k).det) :
    Function.Bijective (substrateModularAut X hX hdet) := by
  refine ⟨fun x y hxy => ?_, fun y => ⟨invAut X hX hdet y, ?_⟩⟩
  · have hx := substrateModularAut_inv_left X hX hdet x
    rw [hxy, substrateModularAut_inv_left X hX hdet y] at hx
    exact hx.symm
  · exact substrateModularAut_inv_right X hX hdet y

end PF.KMS

/-! ## §Axiom check -/
#print axioms PF.KMS.substrateLevelToTimelessField_eq_of
#print axioms PF.KMS.modularAut_inv_left
#print axioms PF.KMS.towerCompatible_inv
#print axioms PF.KMS.substrateModularAut
#print axioms PF.KMS.substrateModularAut_apply
#print axioms PF.KMS.substrateModularAut_inv_left
#print axioms PF.KMS.substrateModularAut_inv_right
#print axioms PF.KMS.substrateModularAut_bijective
