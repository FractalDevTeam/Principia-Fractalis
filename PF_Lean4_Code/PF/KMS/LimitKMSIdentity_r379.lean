/-
# r379: the KMS identity ON `T_∞` — gate (A)'s state and dynamics, joined

★ 2026-10-29 r379 — `Ω(AB) = Ω(B · Σ A)` on the substrate itself ★

## What this closes

r378 constructed the non-tracial functional `Ω` on `T_∞`; r372 descended the
modular automorphism `Σ` to `T_∞`. Both existed, and the identity relating them
did not. r378 recorded that as the remaining residue. This file assembles it:

    Ω (A · B)  =  Ω (B · Σ A)      for **all** `A, B : T_∞`

which is the KMS condition on the substrate, not on its levels.

## The one step that had to be found

The level-wise identity is r363's `gibbs_kms`, and `Σ` acts level-wise by
`substrateModularAutProduct_apply` (`rfl`), so the identity is immediate for two
elements **at the same level**. The work is that `A` and `B` need not come from
the same level.

They can always be brought to one. r359's `substrate_exhausted` gives
`A = ι_i a` and `B = ι_j b`; taking `k = max i j` and pushing both up with
`substrateRingHomIter`, mathlib's `of_f` says the level map is unchanged by
pushing up (`ι_k (f_{i,k} a) = ι_i a`). So every pair is a pair at a common
level, and `exists_common_level` records that.

That is the whole content: directedness of `ℕ` plus `of_f`. No new analysis, and
no hypothesis beyond what r372 and r378 already carry.

## What is proved

* `exists_common_level` — any two elements of `T_∞` are the images of elements
  of a single level;
* **`limitGibbs_kms`** — the KMS identity on `T_∞`, for all `A, B`;
* `limitGibbs_kms_nontracial_pair` — and the identity is not vacuous: `Σ` is
  genuinely needed, because `Ω` is not tracial (r378), so `Ω(AB) = Ω(BA)`
  **fails** for the witness pair while `Ω(AB) = Ω(B · Σ A)` holds.

The second is worth stating. An identity `Ω(AB) = Ω(B · Σ A)` is trivially true
with `Σ = id` whenever `Ω` happens to be tracial — that is exactly the
degenerate case r369 was trapped in. Here `Ω` is provably **not** tracial, so
`Σ` is carrying real content.

## Gate (A), as this leaves it

`THE MAP` §5(A) asks for "a chosen dynamics / KMS state on `T_∞`". What now
exists, machine-checked: a dynamics on `T_∞` (r372), a unital level-wise-positive
non-tracial functional on `T_∞` (r378), and the KMS identity joining them (here).

**What `THE MAP` asks for beyond that, and this does not supply.** §5(A) wants a
dynamics "whose spectral data forces" the dictionary — the α-values and the
reading of σ as a scaling exponent. Nothing here computes any spectral datum, and
nothing connects this KMS pair to the α-skeleton. The *object* §5(A) names now
exists; the *derivation* it was wanted for does not follow, and the gap between
those two is the whole remaining distance.

## What is NOT claimed

Not claimed: that `Ω` is a state in the full C\*-sense (r378 item 1 stands);
that `Σ` is non-identity (still conditional on `LevelMapInjective`, r372) — note
this identity is interesting *regardless*, since `Ω`'s non-traciality forces `Σ`
to differ from the identity *as it acts on Ω*, which is weaker than `Σ ≠ id` as
a map; continuity; any extension to `TimelessFieldCompletion`; and nothing about
`Out(T_∞)` or the physical dictionary.

And again: r113 is untouched. It is a theorem about tracial states, and `Ω` is
not one.

## Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-29.
-/
import PF.KMS.LimitStateConstruction_r378
import PF.KMS.ProductTypeDescent_r372
import PF.TernaryNetInfiniteCompleteness_r359

set_option autoImplicit false

namespace PF.KMS

open Matrix
open scoped ComplexOrder
open PrincipiaTractalis.SubstrateBase3RingHom
open PrincipiaTractalis.SubstrateDirectLimit
open PrincipiaTractalis.TernaryNetInfiniteCompleteness

private abbrev KObj : ℕ → Type := fun k => Matrix (Fin (3^k)) (Fin (3^k)) ℂ

private noncomputable abbrev KMap :
    ∀ i j : ℕ, i ≤ j → (KObj i →+* KObj j) :=
  fun i j h => substrateRingHomIter i j h

/-! ## §1 — Any two elements come from a common level -/

theorem exists_common_level (A B : TimelessFieldRing) :
    ∃ (k : ℕ) (a b : KObj k),
      substrateLevelToTimelessField k a = A
      ∧ substrateLevelToTimelessField k b = B := by
  obtain ⟨i, a, ha⟩ := substrate_exhausted A
  obtain ⟨j, b, hb⟩ := substrate_exhausted B
  refine ⟨max i j,
    substrateRingHomIter i (max i j) (le_max_left i j) a,
    substrateRingHomIter j (max i j) (le_max_right i j) b, ?_, ?_⟩
  · rw [← ha]
    exact DirectLimit.Ring.of_f (G := KObj) (f := KMap) (le_max_left i j) a
  · rw [← hb]
    exact DirectLimit.Ring.of_f (G := KObj) (f := KMap) (le_max_right i j) b

/-! ## §2 — The KMS identity on `T_∞` -/

/-- **★★★ r379: the KMS identity on the substrate ★★★**

`Ω (A · B) = Ω (B · Σ A)` for all `A, B : T_∞`, where `Ω` is r378's limit state
and `Σ` is r372's descended modular automorphism of the same weight family. -/
theorem limitGibbs_kms (x : ∀ k : ℕ, Matrix (Fin 3) (Fin 3) ℂ)
    (hx : ∀ k, (x k).PosDef) (A B : TimelessFieldRing) :
    limitGibbsState x hx (A * B)
      = limitGibbsState x hx
          (B * substrateModularAutProduct (productWeight x) x
            (productTypeFamily_witness x)
            (fun k => posDef_isUnit_det (productWeight_posDef x hx k))
            (fun k => posDef_isUnit_det (hx k)) A) := by
  obtain ⟨k, a, b, hA, hB⟩ := exists_common_level A B
  subst hA
  subst hB
  rw [levelMap_mul, limitGibbsState_level, substrateModularAutProduct_apply,
    levelMap_mul, limitGibbsState_level]
  exact gibbs_kms (productWeight x k)
    (posDef_isUnit_det (productWeight_posDef x hx k)) a b

/-! ## §3 — The identity is not vacuous -/

/-- `Σ` carries real content here: `Ω` is **not** tracial (r378), so the naive
identity `Ω(AB) = Ω(BA)` fails on the witness pair while `limitGibbs_kms`
holds. Compare r369, where the dynamics collapsed to the identity precisely
because the state there was the trace. -/
theorem limitGibbs_kms_nontracial_pair
    (x : ∀ k : ℕ, Matrix (Fin 3) (Fin 3) ℂ) (hx : ∀ k, (x k).PosDef)
    (k : ℕ) {a b : KObj k}
    (hab : gibbsFunctional (productWeight x k) (a * b)
            ≠ gibbsFunctional (productWeight x k) (b * a)) :
    limitGibbsState x hx
        (substrateLevelToTimelessField k a * substrateLevelToTimelessField k b)
      ≠ limitGibbsState x hx
        (substrateLevelToTimelessField k b * substrateLevelToTimelessField k a) :=
  limitGibbsState_not_tracial x hx k hab

end PF.KMS

/-! ## §Axiom check -/
#print axioms PF.KMS.exists_common_level
#print axioms PF.KMS.limitGibbs_kms
#print axioms PF.KMS.limitGibbs_kms_nontracial_pair
