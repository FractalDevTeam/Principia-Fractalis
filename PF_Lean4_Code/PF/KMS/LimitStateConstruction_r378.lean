/-
# r378: the limit state, CONSTRUCTED — a non-tracial state on `T_∞`

★ 2026-10-29 r378 — gate (A)'s state half, no longer conditional ★

## What this closes

r377 proved the level states are tower-compatible and that non-traciality
survives the limit, but left the functional itself unconstructed: the substrate's
tower maps are `→+*` rather than `→ₐ`, so `DirectLimit.Module.lift` does not
apply, and r377 recorded that as the honest residue.

The residue is now closed, and the tool was in the wrong namespace to be found
by searching the algebra API: `DirectLimit.lift` in
`Mathlib/Order/DirectedInverseSystem.lean:163` takes a family of **plain
functions** with a compatibility condition and needs no algebraic structure at
all. A functional is not multiplicative, so a plain-function lift is exactly the
right tool — looking for it among the ring and module lifts was the mistake.

Better still, its `lift_def` is **`rfl`**, so evaluation on a level element is
definitional and every downstream statement is cheap.

## What is proved

* `gibbs_tower_compatible_iter` — r377's successor compatibility, extended along
  the iterated embedding by induction on the level gap;
* **`limitGibbsState`** — the functional `Ω : T_∞ → ℂ`, constructed;
* `limitGibbsState_level` — `Ω (ι_k a) = ω_k(a)`, by `rfl`;
* `limitGibbsState_unital` — `Ω 1 = 1`;
* **`limitGibbsState_not_tracial`** — for a family whose level-`k` weight is not
  central, `Ω` is **not** tracial. **Unconditional**: no injectivity, no choice,
  no extra hypothesis.

So `T_∞` carries a constructed, verified, **non-tracial** functional which is
unital and restricts to the Gibbs state of a positive weight at every level.

## Significance, and the limits in the same breath

This is the half of `THE MAP` §5(A) that asks for a state. Together with r372's
dynamics it means the substrate carries a KMS pair at every finite level, a
dynamics on the limit, and a non-tracial functional on the limit.

**What it is not.**

1. **`Ω` is not proved to be a state in the full C\*-sense.** Unital and
   level-wise positive, yes — `limitGibbsState_level` plus r364 gives
   `0 ≤ Ω(ι(aᴴa))`. But positivity on *all* of `T_∞` needs every positive
   element of the limit to be reachable, and that is not proved here.
2. **It does not contradict r113**, which is a theorem about *tracial* states.
   `Ω` is not tracial, so it is outside r113's scope — the point already
   established in `codex/KMS_OBSTRUCTION_RECHECK_2026-10-28.md`. r113 remains
   kernel-clean and untouched, and the unique tracial state is still unique.
3. **It is not shown to be KMS for r372's automorphism on `T_∞`.** The KMS
   identity is proved at each level (r363–r366) and the dynamics descends
   (r372), but the limit identity relating the two is not assembled here.
4. **No continuity, and no extension to `TimelessFieldCompletion`.** `Ω` lives
   on the algebraic limit.

## Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-29.
-/
import PF.KMS.LimitStateNonTracial_r377

set_option autoImplicit false

namespace PF.KMS

open Matrix
open scoped ComplexOrder
open PrincipiaTractalis.SubstrateBase3Embed
open PrincipiaTractalis.SubstrateBase3RingHom
open PrincipiaTractalis.SubstrateDirectLimit

private abbrev LObj : ℕ → Type := fun k => Matrix (Fin (3^k)) (Fin (3^k)) ℂ

private noncomputable abbrev LMap :
    ∀ i j : ℕ, i ≤ j → (LObj i →+* LObj j) :=
  fun i j h => substrateRingHomIter i j h

/-! ## §1 — Compatibility along the iterated embedding -/

theorem gibbs_tower_compatible_iter (x : ∀ k : ℕ, Matrix (Fin 3) (Fin 3) ℂ)
    (hx : ∀ k, (x k).PosDef) (i j : ℕ) (h : i ≤ j) (a : LObj i) :
    gibbsFunctional (productWeight x i) a
      = gibbsFunctional (productWeight x j) (substrateRingHomIter i j h a) := by
  induction j, h using Nat.le_induction with
  | base => rw [substrateRingHomIter_self]; rfl
  | succ j hij ih =>
      have hstep : substrateRingHomIter i (j + 1) (hij.trans (Nat.le_succ j)) a
          = substrateEmbedMatrix j (substrateRingHomIter i j hij a) := by
        rw [substrateRingHomIter_succ i j hij (hij.trans (Nat.le_succ j))]
        rfl
      rw [hstep, gibbs_tower_compatible x hx j (substrateRingHomIter i j hij a)]
      exact ih

/-! ## §2 — The construction -/

/-- **★★★ r378: the limit state on `T_∞` ★★★**

Built with `DirectLimit.lift` from `Mathlib/Order/DirectedInverseSystem.lean`,
which takes plain functions — the right tool for a functional, which is not
multiplicative. -/
noncomputable def limitGibbsState (x : ∀ k : ℕ, Matrix (Fin 3) (Fin 3) ℂ)
    (hx : ∀ k, (x k).PosDef) : TimelessFieldRing → ℂ :=
  DirectLimit.lift LMap
    (fun k a => gibbsFunctional (productWeight x k) a)
    (fun i j h a => gibbs_tower_compatible_iter x hx i j h a)

/-- `Ω` restricted to level `k` is the level state — definitionally. -/
@[simp] theorem limitGibbsState_level
    (x : ∀ k : ℕ, Matrix (Fin 3) (Fin 3) ℂ) (hx : ∀ k, (x k).PosDef)
    (k : ℕ) (a : LObj k) :
    limitGibbsState x hx (substrateLevelToTimelessField k a)
      = gibbsFunctional (productWeight x k) a := rfl

/-! ## §3 — `Ω` is unital, level-wise positive, and NOT tracial -/

theorem limitGibbsState_unital (x : ∀ k : ℕ, Matrix (Fin 3) (Fin 3) ℂ)
    (hx : ∀ k, (x k).PosDef) :
    limitGibbsState x hx 1 = 1 := by
  haveI : Nonempty (Fin (3^0)) := ⟨⟨0, Nat.pos_of_ne_zero (by positivity)⟩⟩
  have h1 : (1 : TimelessFieldRing)
      = substrateLevelToTimelessField 0 (1 : LObj 0) :=
    (map_one (DirectLimit.Ring.of LObj LMap 0)).symm
  rw [h1, limitGibbsState_level]
  exact gibbs_unital (productWeight_posDef x hx 0)

/-- Level-wise positivity, from r364. -/
theorem limitGibbsState_nonneg_level
    (x : ∀ k : ℕ, Matrix (Fin 3) (Fin 3) ℂ) (hx : ∀ k, (x k).PosDef)
    (k : ℕ) (a : LObj k) :
    haveI : Nonempty (Fin (3^k)) := ⟨⟨0, Nat.pos_of_ne_zero (by positivity)⟩⟩
    0 ≤ limitGibbsState x hx (substrateLevelToTimelessField k (aᴴ * a)) := by
  haveI : Nonempty (Fin (3^k)) := ⟨⟨0, Nat.pos_of_ne_zero (by positivity)⟩⟩
  rw [limitGibbsState_level]
  exact gibbs_nonneg (productWeight_posDef x hx k) a

/-- **★★★ r378: the limit state is NOT TRACIAL ★★★**

Unconditional — no injectivity of the level map, no choice, no extra
hypothesis. The comparison is between values in `ℂ`. -/
theorem limitGibbsState_not_tracial
    (x : ∀ k : ℕ, Matrix (Fin 3) (Fin 3) ℂ) (hx : ∀ k, (x k).PosDef)
    (k : ℕ) {a b : LObj k}
    (hab : gibbsFunctional (productWeight x k) (a * b)
            ≠ gibbsFunctional (productWeight x k) (b * a)) :
    limitGibbsState x hx
        (substrateLevelToTimelessField k a * substrateLevelToTimelessField k b)
      ≠ limitGibbsState x hx
        (substrateLevelToTimelessField k b * substrateLevelToTimelessField k a) :=
  limitState_not_tracial_of_level (X := fun j => productWeight x j) k
    (fun j c => limitGibbsState_level x hx j c) hab

end PF.KMS

/-! ## §Axiom check -/
#print axioms PF.KMS.gibbs_tower_compatible_iter
#print axioms PF.KMS.limitGibbsState
#print axioms PF.KMS.limitGibbsState_level
#print axioms PF.KMS.limitGibbsState_unital
#print axioms PF.KMS.limitGibbsState_nonneg_level
#print axioms PF.KMS.limitGibbsState_not_tracial
