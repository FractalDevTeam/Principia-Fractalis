/-
# Andrews–Curtis moves, their invariant, and a pair that is NOT AC-equivalent

Author: Pablo Cohen
Date: November 25, 2026

Completes removal condition (1) of
`PF/Referee/TypedPropVacuityDisclosure_2026_11_25.lean`. That disclosure recorded
that `AndrewsCurtisFrameworkAttack` encodes the conclusion of Andrews–Curtis as
`∃ moveCount : ℕ, moveCount ≥ 0` — satisfied by `0`, so it records no
AC-move sequence at all.
`PF/NumberTheory/AndrewsCurtisFaithfulCarrier_2026_11_25.lean` discharged the
hypothesis side. This file discharges the conclusion side.

## The moves

`ACMove` is the standard generating set for Andrews–Curtis equivalence on a
relator tuple `r : Fin n → FreeGroup (Fin n)`, as an inductive relation:

* `inv`  — replace `rᵢ` by `rᵢ⁻¹`
* `mul`  — replace `rᵢ` by `rᵢ * rⱼ` for `j ≠ i`
* `conj` — replace `rᵢ` by `w * rᵢ * w⁻¹` for any word `w`

`ACEquiv` is the reflexive-transitive closure of `ACMove` symmetrised, i.e. of
`ACStep r s := ACMove r s ∨ ACMove s r`.

## The invariant, and why it gives teeth

Every AC move preserves the normal closure of the relator set
(`acMove_preserves_normalClosure`), hence so does AC-equivalence
(`acEquiv_preserves_normalClosure`). This is the honest content of the file:
without an invariant, `ACEquiv` would be a relation nobody can prove anything
negative about, and the conjecture built on it would be as unfalsifiable as
`∃ moveCount, moveCount ≥ 0`.

With the invariant:

    not_acEquiv_sqPres_trivial : ¬ ACEquiv sqPres.rels (trivialRels sqPres.rank)

⟨x | x²⟩ is NOT AC-equivalent to ⟨x | x⟩ — because the first has normal closure
of index 2 (its quotient is ℤ/2, proved in the carrier file) and the second has
normal closure `⊤`. So `ACEquiv` is provably NOT the total relation, which is
exactly what the old `∃ moveCount, moveCount ≥ 0` encoding could never be.

## Scope — read this before reading anything else here

`AndrewsCurtisConjectureFaithful` is DEFINED here and is NOT PROVED here, and
nothing in this file or in the corpus inhabits it. That is the correct state: it
is an open problem. What is proved is that neither of its two sides is vacuous —
`faithful_conjecture_both_sides_have_teeth` exhibits a presentation refuting the
hypothesis and the same presentation refuting the conclusion — so unlike
`AndrewsCurtisFrameworkAttack.AndrewsCurtisConjecture`, which
`andrewsCurtisConjecture_as_encoded_is_provable` discharges in four tokens, this
statement cannot be discharged by inspection.

NOTHING HERE PROVES OR REFUTES THE ANDREWS–CURTIS CONJECTURE.
-/

import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic
import PF.NumberTheory.AndrewsCurtisFaithfulCarrier_2026_11_25

set_option autoImplicit false

namespace PF.NumberTheory.AndrewsCurtisFaithful

open Subgroup

/-! ## §1 — One-index modifications that preserve the normal closure -/

/-- A modification at a single index preserves the normal closure as soon as the
new word lies in the old normal closure and the old word lies in the new one.
Every AC move is an instance of this. -/
theorem normalClosure_update_eq {n : ℕ} (r : Fin n → FreeGroup (Fin n)) (i : Fin n)
    (v : FreeGroup (Fin n))
    (hv : v ∈ normalClosure (Set.range r))
    (hback : r i ∈ normalClosure (Set.range (Function.update r i v))) :
    normalClosure (Set.range (Function.update r i v)) = normalClosure (Set.range r) := by
  refine le_antisymm (normalClosure_le_normal ?_) (normalClosure_le_normal ?_)
  · rintro x ⟨k, rfl⟩
    by_cases hk : k = i
    · subst hk
      rw [Function.update_self]
      exact hv
    · rw [Function.update_of_ne hk]
      exact subset_normalClosure ⟨k, rfl⟩
  · rintro x ⟨k, rfl⟩
    by_cases hk : k = i
    · subst hk
      exact hback
    · exact subset_normalClosure ⟨k, Function.update_of_ne hk v r⟩

/-- Move `inv`: replacing `rᵢ` by `rᵢ⁻¹` preserves the normal closure. -/
theorem normalClosure_inv_move {n : ℕ} (r : Fin n → FreeGroup (Fin n)) (i : Fin n) :
    normalClosure (Set.range (Function.update r i (r i)⁻¹))
      = normalClosure (Set.range r) := by
  refine normalClosure_update_eq r i _ ?_ ?_
  · exact inv_mem (subset_normalClosure ⟨i, rfl⟩)
  · have hmem : (r i)⁻¹ ∈ normalClosure (Set.range (Function.update r i (r i)⁻¹)) :=
      subset_normalClosure ⟨i, Function.update_self i ((r i)⁻¹) r⟩
    simpa using inv_mem hmem

/-- Move `mul`: replacing `rᵢ` by `rᵢ * rⱼ` with `j ≠ i` preserves the normal
closure. The hypothesis `j ≠ i` is what lets `rⱼ` be read back off the modified
tuple, which is how `rᵢ` is recovered. -/
theorem normalClosure_mul_move {n : ℕ} (r : Fin n → FreeGroup (Fin n)) (i j : Fin n)
    (hij : j ≠ i) :
    normalClosure (Set.range (Function.update r i (r i * r j)))
      = normalClosure (Set.range r) := by
  refine normalClosure_update_eq r i _ ?_ ?_
  · exact mul_mem (subset_normalClosure ⟨i, rfl⟩) (subset_normalClosure ⟨j, rfl⟩)
  · have hprod : r i * r j ∈ normalClosure (Set.range (Function.update r i (r i * r j))) :=
      subset_normalClosure ⟨i, Function.update_self i (r i * r j) r⟩
    have hrj : r j ∈ normalClosure (Set.range (Function.update r i (r i * r j))) :=
      subset_normalClosure ⟨j, Function.update_of_ne hij (r i * r j) r⟩
    have h := mul_mem hprod (inv_mem hrj)
    have heq : r i * r j * (r j)⁻¹ = r i := by group
    rwa [heq] at h

/-- Move `conj`: replacing `rᵢ` by `w * rᵢ * w⁻¹` preserves the normal closure.
Both directions are normality of the normal closure. -/
theorem normalClosure_conj_move {n : ℕ} (r : Fin n → FreeGroup (Fin n)) (i : Fin n)
    (w : FreeGroup (Fin n)) :
    normalClosure (Set.range (Function.update r i (w * r i * w⁻¹)))
      = normalClosure (Set.range r) := by
  refine normalClosure_update_eq r i _ ?_ ?_
  · have hri : r i ∈ normalClosure (Set.range r) := subset_normalClosure ⟨i, rfl⟩
    exact normalClosure_normal.conj_mem (r i) hri w
  · have hmem : w * r i * w⁻¹
        ∈ normalClosure (Set.range (Function.update r i (w * r i * w⁻¹))) :=
      subset_normalClosure ⟨i, Function.update_self i (w * r i * w⁻¹) r⟩
    have h := normalClosure_normal.conj_mem (w * r i * w⁻¹) hmem w⁻¹
    have heq : w⁻¹ * (w * r i * w⁻¹) * w⁻¹⁻¹ = r i := by group
    rwa [heq] at h

/-! ## §2 — The move relation and AC-equivalence -/

/-- **The Andrews–Curtis moves.** The standard generating set, acting on a
relator tuple. -/
inductive ACMove {n : ℕ} :
    (Fin n → FreeGroup (Fin n)) → (Fin n → FreeGroup (Fin n)) → Prop
  /-- Replace `rᵢ` by `rᵢ⁻¹`. -/
  | inv (r : Fin n → FreeGroup (Fin n)) (i : Fin n) :
      ACMove r (Function.update r i (r i)⁻¹)
  /-- Replace `rᵢ` by `rᵢ * rⱼ`, for `j ≠ i`. -/
  | mul (r : Fin n → FreeGroup (Fin n)) (i j : Fin n) (hij : j ≠ i) :
      ACMove r (Function.update r i (r i * r j))
  /-- Replace `rᵢ` by `w * rᵢ * w⁻¹`. -/
  | conj (r : Fin n → FreeGroup (Fin n)) (i : Fin n) (w : FreeGroup (Fin n)) :
      ACMove r (Function.update r i (w * r i * w⁻¹))

/-- A move in either direction. Each AC move is invertible, but symmetrising
explicitly avoids having to prove that first. -/
def ACStep {n : ℕ} (r s : Fin n → FreeGroup (Fin n)) : Prop :=
  ACMove r s ∨ ACMove s r

/-- **AC-equivalence**: finitely many moves, in either direction. This is the
content the old encoding replaced with `∃ moveCount : ℕ, moveCount ≥ 0`. -/
def ACEquiv {n : ℕ} : (Fin n → FreeGroup (Fin n)) → (Fin n → FreeGroup (Fin n)) → Prop :=
  Relation.ReflTransGen ACStep

set_option maxHeartbeats 800000 in
/-- **Every AC move preserves the normal closure of the relator set.** -/
theorem acMove_preserves_normalClosure {n : ℕ} {r s : Fin n → FreeGroup (Fin n)}
    (h : ACMove r s) :
    normalClosure (Set.range s) = normalClosure (Set.range r) := by
  cases h with
  | inv i => exact normalClosure_inv_move r i
  | mul i j hij => exact normalClosure_mul_move r i j hij
  | conj i w => exact normalClosure_conj_move r i w

/-- **Hence AC-equivalence preserves it.** The invariant that makes the relation
falsifiable. -/
theorem acEquiv_preserves_normalClosure {n : ℕ} {r s : Fin n → FreeGroup (Fin n)}
    (h : ACEquiv r s) :
    normalClosure (Set.range r) = normalClosure (Set.range s) := by
  induction h with
  | refl => rfl
  | tail _ hbc ih =>
      rcases hbc with hm | hm
      · rw [ih]; exact (acMove_preserves_normalClosure hm).symm
      · rw [ih]; exact acMove_preserves_normalClosure hm

/-- **`ACMove` is inhabited by a real move**: `⟨x | x⟩ → ⟨x | x⁻¹⟩`. Without
this, a negative result about `ACEquiv` could be an artifact of an empty
relation. Together with `trivialPres_acEquivalentToTrivial` (reflexivity) and
`not_acEquiv_sqPres_trivial` (a non-pair), `ACEquiv` is pinned from both
sides. -/
theorem acEquiv_inv_witness :
    ACEquiv (FreeGroup.of : Fin 1 → FreeGroup (Fin 1))
      (Function.update (FreeGroup.of : Fin 1 → FreeGroup (Fin 1)) 0
        (FreeGroup.of (0 : Fin 1))⁻¹) :=
  Relation.ReflTransGen.single (Or.inl (ACMove.inv _ _))

/-! ## §3 — Teeth: a pair that is NOT AC-equivalent -/

/-- The trivial relator tuple `⟨x₁ … xₙ | x₁ … xₙ⟩`. -/
def trivialRels (n : ℕ) : Fin n → FreeGroup (Fin n) := FreeGroup.of

theorem normalClosure_trivialRels (n : ℕ) :
    normalClosure (Set.range (trivialRels n)) = ⊤ := by
  refine top_le_iff.mp ?_
  rw [show Set.range (trivialRels n)
        = Set.range (FreeGroup.of : Fin n → FreeGroup (Fin n)) from rfl,
      ← FreeGroup.closure_range_of (Fin n)]
  exact closure_le_normalClosure

/-- `⟨x | x²⟩` has a proper normal closure — it is the kernel of the map to ℤ/2
built in the carrier file. -/
theorem normalClosure_sqPres_ne_top :
    normalClosure (Set.range sqPres.rels) ≠ ⊤ := by
  intro htop
  refine sqPres_not_presentsTrivial ?_
  show Subsingleton (FreeGroup (Fin sqPres.rank) ⧸ normalClosure sqPres.relSet)
  rw [show sqPres.relSet = Set.range sqPres.rels from rfl, htop]
  exact QuotientGroup.subsingleton_quotient_top

/-- **⟨x | x²⟩ is NOT AC-equivalent to ⟨x | x⟩.** The normal closures differ —
one is `⊤`, the other is not — and AC-equivalence preserves the normal closure.
So `ACEquiv` is provably not the total relation. -/
theorem not_acEquiv_sqPres_trivial :
    ¬ ACEquiv sqPres.rels (trivialRels sqPres.rank) := by
  intro h
  have hinv := acEquiv_preserves_normalClosure h
  rw [normalClosure_trivialRels] at hinv
  exact normalClosure_sqPres_ne_top hinv

/-! ## §4 — The faithful conjecture: DEFINED, not proved -/

/-- The conclusion of Andrews–Curtis, faithfully: AC-equivalent to the trivial
presentation of the same rank. Contrast
`AndrewsCurtisFrameworkAttack.ACEquivalentToTrivial`, which is
`∃ moveCount : ℕ, moveCount ≥ 0`. -/
def ACEquivalentToTrivialFaithful (p : FaithfulBalancedPresentation) : Prop :=
  ACEquiv p.rels (trivialRels p.rank)

/-- **The Andrews–Curtis conjecture, faithfully stated.** DEFINED HERE AND NOT
PROVED HERE. Nothing in this file or in the corpus inhabits it. -/
def AndrewsCurtisConjectureFaithful : Prop :=
  ∀ p : FaithfulBalancedPresentation,
    PresentsTrivialGroupFaithful p → ACEquivalentToTrivialFaithful p

/-- The conclusion is satisfiable: the trivial presentation is AC-equivalent to
itself, by zero moves. -/
theorem trivialPres_acEquivalentToTrivial (n : ℕ) (hn : 1 ≤ n) :
    ACEquivalentToTrivialFaithful (trivialPres n hn) :=
  Relation.ReflTransGen.refl

/-- **The hypothesis is load-bearing.** Dropping it makes the statement FALSE:
not every balanced presentation is AC-equivalent to the trivial one, because
`⟨x | x²⟩` is not. So `AndrewsCurtisConjectureFaithful` cannot be proved by
ignoring its hypothesis — which is precisely how
`AndrewsCurtisFrameworkAttack.AndrewsCurtisConjecture` is dischargeable, its
hypothesis being `True`. -/
theorem conclusion_alone_is_false :
    ¬ (∀ p : FaithfulBalancedPresentation, ACEquivalentToTrivialFaithful p) := by
  intro h
  exact not_acEquiv_sqPres_trivial (h sqPres)

/-- **Neither side of the faithful conjecture is vacuous.** `⟨x | x²⟩` refutes
the hypothesis AND refutes the conclusion. So the statement cannot be discharged
by inspection the way
`AndrewsCurtisFrameworkAttack.AndrewsCurtisConjecture` can be — see
`Referee.TypedPropVacuityDisclosure_2026_11_25.andrewsCurtisConjecture_as_encoded_is_provable`,
which proves that one in four tokens. -/
theorem faithful_conjecture_both_sides_have_teeth :
    ¬ PresentsTrivialGroupFaithful sqPres ∧ ¬ ACEquivalentToTrivialFaithful sqPres :=
  ⟨sqPres_not_presentsTrivial, not_acEquiv_sqPres_trivial⟩

/-! ## §5 — Bundle

Wired by inferred type (`def` + `And.intro`), never by transcribing statements
into field types. -/

def andrewsCurtisMoveRelationBundle :=
  And.intro (normalClosure_trivialRels 1)
    (And.intro normalClosure_sqPres_ne_top
      (And.intro not_acEquiv_sqPres_trivial
        (And.intro (trivialPres_acEquivalentToTrivial 1 (le_refl 1))
          (And.intro acEquiv_inv_witness
            (And.intro conclusion_alone_is_false
              faithful_conjecture_both_sides_have_teeth)))))

end PF.NumberTheory.AndrewsCurtisFaithful
