/-
# Andrews–Curtis: the faithful carrier, with teeth

Author: Pablo Cohen
Date: November 25, 2026

`PF/Referee/TypedPropVacuityDisclosure_2026_11_25.lean` disclosed that
`AndrewsCurtisFrameworkAttack`'s carrier

    structure BalancedPresentation where
      rank : ℕ
      rank_pos : rank ≥ 1

RECORDS NO RELATORS, so `PresentsTrivialGroup := True` cannot be the
Andrews–Curtis hypothesis, and gave the removal condition: replace the carrier
with one that records relators, which mathlib supports at this pin. This file
discharges that condition. The disclosure was scaffolding; this is the repair.

## What is built

`FaithfulBalancedPresentation` carries `rels : Fin rank → FreeGroup (Fin rank)` —
a balanced presentation is `rank` generators together with `rank` relators, which
is what "balanced" means. `PresentsTrivialGroupFaithful` is then a real
statement: `Subsingleton (PresentedGroup (Set.range rels))`, i.e. the group
presented by those relators is trivial.

## Why it has teeth

A predicate that holds of everything proves nothing, so the content is in the
separation. Two presentations, both of rank 1:

* `trivialPres n` is `⟨x₁ … xₙ | x₁ … xₙ⟩`. Its relators generate the whole free
  group, so the presented group is trivial — `trivialPres_presentsTrivial`,
  proved for EVERY rank `n`, not just `n = 1`.
* `sqPres` is `⟨x | x²⟩`, which presents ℤ/2. Its presented group is NOT
  trivial — `sqPres_not_presentsTrivial`, proved by mapping the generator to
  `ofAdd 1 : Multiplicative (ZMod 2)`, which the relator `x²` kills and the
  generator does not.

`faithful_predicate_separates` bundles the two. This is the thing the old
encoding could not do at all.

## The exact defect, measured

`forget` sends a faithful presentation to the old carrier by dropping the
relators — which is all the old carrier can hold. Then

    forget_identifies_what_faithful_separates : forget (trivialPres 1 _) = forget sqPres

holds BY `rfl`. The two presentations that the faithful predicate separates are
the SAME OBJECT in the old encoding, and `PresentsTrivialGroup := True` holds of
that object — so the old encoding asserts that ⟨x | x²⟩ presents the trivial
group, which `sqPres_not_presentsTrivial` refutes. That is the precise cost of
the vacuous carrier, now a theorem rather than a remark.

## Scope

NOTHING HERE PROVES OR REFUTES THE ANDREWS–CURTIS CONJECTURE. This supplies the
hypothesis side faithfully. The conclusion side — the AC-move relation and its
invariants — is the next piece; until it lands, no statement in this file is an
Andrews–Curtis conjecture of any form, and none is named as one.
-/

import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import PF.NumberTheory.AndrewsCurtisFrameworkAttack

set_option autoImplicit false

namespace PF.NumberTheory.AndrewsCurtisFaithful

/-! ## §1 — A carrier that records relators -/

/-- **Balanced presentation, faithfully.** `rank` generators and `rank`
relators, each relator a word in the free group on those generators. The
balanced condition is structural: `rels` is indexed by the same `Fin rank` as
the generators, so the counts agree by construction. -/
structure FaithfulBalancedPresentation where
  /-- Number of generators (= number of relators). -/
  rank : ℕ
  /-- At least one generator. -/
  rank_pos : 1 ≤ rank
  /-- The relators, as words in the free group on the generators. -/
  rels : Fin rank → FreeGroup (Fin rank)

namespace FaithfulBalancedPresentation

/-- The relators as a set, which is what `PresentedGroup` consumes. -/
def relSet (p : FaithfulBalancedPresentation) : Set (FreeGroup (Fin p.rank)) :=
  Set.range p.rels

/-- The group the presentation presents. -/
abbrev group (p : FaithfulBalancedPresentation) := PresentedGroup p.relSet

end FaithfulBalancedPresentation

open FaithfulBalancedPresentation

/-- **The hypothesis of Andrews–Curtis, faithfully.** The presented group is
trivial. Contrast `AndrewsCurtisFrameworkAttack.PresentsTrivialGroup`, which is
`True`. -/
def PresentsTrivialGroupFaithful (p : FaithfulBalancedPresentation) : Prop :=
  Subsingleton p.group

/-! ## §2 — The trivial presentation presents the trivial group, for every rank -/

/-- `⟨x₁ … xₙ | x₁ … xₙ⟩`: the relators are exactly the generators. -/
def trivialPres (n : ℕ) (hn : 1 ≤ n) : FaithfulBalancedPresentation :=
  ⟨n, hn, FreeGroup.of⟩

@[simp] theorem relSet_trivialPres (n : ℕ) (hn : 1 ≤ n) :
    (trivialPres n hn).relSet
      = Set.range (FreeGroup.of : Fin n → FreeGroup (Fin n)) :=
  rfl

/-- The relators of the trivial presentation generate the whole free group, so
their normal closure is everything. -/
theorem normalClosure_relSet_trivialPres (n : ℕ) (hn : 1 ≤ n) :
    Subgroup.normalClosure (trivialPres n hn).relSet = ⊤ := by
  refine top_le_iff.mp ?_
  rw [relSet_trivialPres, ← FreeGroup.closure_range_of (Fin n)]
  exact Subgroup.closure_le_normalClosure

/-- **The positive witness, at every rank.** `⟨x₁ … xₙ | x₁ … xₙ⟩` presents the
trivial group. -/
theorem trivialPres_presentsTrivial (n : ℕ) (hn : 1 ≤ n) :
    PresentsTrivialGroupFaithful (trivialPres n hn) := by
  show Subsingleton (FreeGroup (Fin n) ⧸ Subgroup.normalClosure (trivialPres n hn).relSet)
  rw [normalClosure_relSet_trivialPres n hn]
  exact QuotientGroup.subsingleton_quotient_top

/-! ## §3 — `⟨x | x²⟩` does NOT present the trivial group -/

/-- `⟨x | x²⟩`, a rank-1 balanced presentation. It presents ℤ/2. -/
def sqPres : FaithfulBalancedPresentation :=
  ⟨1, le_refl 1, fun _ => FreeGroup.of 0 ^ 2⟩

/-- The test homomorphism: send the generator to the nontrivial element of
`Multiplicative (ZMod 2)`. -/
private def testMap : Fin 1 → Multiplicative (ZMod 2) :=
  fun _ => Multiplicative.ofAdd 1

/-- The relator `x²` is killed by `testMap`, because `1 + 1 = 0` in `ZMod 2`. -/
private theorem testMap_kills_rels :
    ∀ r ∈ sqPres.relSet, FreeGroup.lift testMap r = 1 := by
  rintro r ⟨i, rfl⟩
  show FreeGroup.lift testMap (FreeGroup.of 0 ^ 2) = 1
  rw [map_pow, FreeGroup.lift_apply_of]
  show (Multiplicative.ofAdd (1 : ZMod 2)) ^ 2 = 1
  have hz : ((1 : ZMod 2) + 1) = 0 := by decide
  rw [pow_two]
  show Multiplicative.ofAdd ((1 : ZMod 2) + 1) = 1
  rw [hz]
  rfl

/-- **The negative witness.** `⟨x | x²⟩` does not present the trivial group. If
it did, its generator would be `1`, and the homomorphism to `Multiplicative
(ZMod 2)` would force `ofAdd 1 = 1`. -/
theorem sqPres_not_presentsTrivial :
    ¬ PresentsTrivialGroupFaithful sqPres := by
  intro hsub
  have hgen : (PresentedGroup.of (0 : Fin 1) : PresentedGroup sqPres.relSet) = 1 :=
    hsub.elim _ _
  have h := PresentedGroup.toGroup.of testMap_kills_rels (x := (0 : Fin 1))
  rw [hgen, map_one] at h
  have h2 : (Multiplicative.ofAdd (1 : ZMod 2)) = 1 := h.symm
  have h3 : (1 : ZMod 2) = 0 := congrArg Multiplicative.toAdd h2
  exact absurd h3 (by decide)

/-- **The separation.** The faithful predicate distinguishes two rank-1 balanced
presentations. The vacuous one could not distinguish anything. -/
theorem faithful_predicate_separates :
    PresentsTrivialGroupFaithful (trivialPres 1 (le_refl 1))
      ∧ ¬ PresentsTrivialGroupFaithful sqPres :=
  ⟨trivialPres_presentsTrivial 1 (le_refl 1), sqPres_not_presentsTrivial⟩

/-! ## §4 — What the old carrier loses, as a theorem -/

/-- Forget the relators — which is all the old carrier can hold. -/
def forget (p : FaithfulBalancedPresentation) :
    AndrewsCurtisFrameworkAttack.BalancedPresentation :=
  ⟨p.rank, p.rank_pos⟩

/-- **The cost of the vacuous carrier, measured.** The two presentations that
§3 separates are the SAME OBJECT after forgetting relators — by `rfl`. Since
`AndrewsCurtisFrameworkAttack.PresentsTrivialGroup` is `True`, it holds of that
object, so the old encoding affirms its hypothesis for `⟨x | x²⟩` too. -/
theorem forget_identifies_what_faithful_separates :
    forget (trivialPres 1 (le_refl 1)) = forget sqPres :=
  rfl

/-- Spelled out: the old hypothesis holds of the forgotten `⟨x | x²⟩`, while the
faithful hypothesis fails for `⟨x | x²⟩`. Both halves are proved; together they
are the precise sense in which the old carrier overstates. -/
theorem old_hypothesis_holds_where_faithful_fails :
    AndrewsCurtisFrameworkAttack.PresentsTrivialGroup (forget sqPres)
      ∧ ¬ PresentsTrivialGroupFaithful sqPres :=
  ⟨trivial, sqPres_not_presentsTrivial⟩

/-! ## §5 — Bundle

Wired by inferred type (`def` + `And.intro`), never by transcribing statements
into field types. -/

def andrewsCurtisFaithfulCarrierBundle :=
  And.intro (trivialPres_presentsTrivial 1 (le_refl 1))
    (And.intro sqPres_not_presentsTrivial
      (And.intro forget_identifies_what_faithful_separates
        old_hypothesis_holds_where_faithful_fails))

end PF.NumberTheory.AndrewsCurtisFaithful
