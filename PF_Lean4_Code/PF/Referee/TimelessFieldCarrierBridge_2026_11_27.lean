/-
# The two carriers called `T_∞`, and the single identity between them

**Date**: 2026-11-27 (Legion).

This corpus has **two** objects named `T_∞`, built in opposite directions, and
ch04 does not distinguish them:

| | construction | where the theorems are |
|---|---|---|
| **skeleton** | `TimelessFieldType φ` = `TimelessFieldElement φ`, a structure of coherent towers `seq : ∀ k, M_{3^k}` with `compat : φ k k' h (seq k') = seq k` — an **inverse** limit over divisibility | nothing; the C* results do not live here |
| **completion** | `TimelessFieldCompletion` = `UniformSpace.Completion TimelessFieldRing`, where `TimelessFieldRing` is the **direct** limit of `M_{3^k}` | faithful trace, C*-simplicity, unique tracial state, the `CStarAlgebra` instance |

`NuclearStructure` and `TimelessFieldExistenceClaim` are stated over the
*skeleton*. Every genuine theorem is over the *completion*. That gap is why
the faithful-trace conjunct could only be a tautology
(`PF/Referee/TimelessFieldFaithfulTraceRepair_2026_11_27.lean`): the skeleton
carrier has no trace to be faithful about.

This file closes the gap as far as it can be closed today, and names precisely
what remains.

## What is proved here, unconditionally

`condExpFin k : TimelessFieldCompletion → M_{3^k}` already exists
(`PF/SubstrateCompletionFaithful.lean:133`), and `M_{3^k}` **is** the
skeleton's `TimelessFieldLevelOperators k`. So every element of the completion
already has a level tower. §1 proves that tower determines it:

    levelTower_injective : Function.Injective levelTower

from `condExpCompletion_tendsto` and uniqueness of limits. So the completion
is **no larger than** the skeleton's underlying sequence space, and its
elements *are* towers of level-`k` matrices. That is the substantive half of
the carrier identification and it needs no hypothesis.

## What remains, named

The skeleton is the subtype of towers satisfying `compat` against the
canonical connecting family `partialTraceMorphism`
(`PF/Consciousness/TimelessFieldPartialTraceMorphism.lean:115`), whose
`ProjectiveCompatibility` is proved there (`:278`). To land `levelTower` in
the skeleton we need exactly one identity, §2's `CarrierBridgeCompatibility`:

    partialTraceMorphism k k' h (condExpFin k' x) = condExpFin k x

This is a real equation between two independently-built constructions of
"trace out the tail":

* `partialTraceMorphism` marginalises **digit functions** — `digitEquiv`,
  `Fin.append`, a sum over `Fin (k' - k) → Fin 3`;
* `condExpFin` is `UniformSpace.Completion.extension` of `condExp`, which
  factors through `partialTraceDown` — an **iterated** `partialTraceStep`
  composed by `Nat.leRecOn`.

They are the same mathematics by two routes, and the corpus proves neither
equal to the other. Note also that `levelToLevelK` transitivity — which the
reduction of the above to the ring level needs — is **not** in the corpus:
`levelToLevelK_compat` is the cocone condition for `DirectLimit.lift`, a
different statement.

§3 shows the identity is *sufficient*: given it, the map into the skeleton
exists and is injective. So the entire remaining distance between the two
`T_∞`s is that one equation, and this is its removal condition.

Nothing upstream is renamed or deleted; no claim is made that the two carriers
*are* identified, and none that they are not.
-/
import PF.SubstrateCompletionFaithful
import PF.Consciousness.TimelessFieldPartialTraceMorphism

set_option autoImplicit false

namespace PF.Referee.TimelessFieldCarrierBridge

open PrincipiaTractalis
open PrincipiaTractalis.TimelessField
open PrincipiaTractalis.SubstrateTimelessFieldCompletion
open PrincipiaTractalis.SubstrateUHFPreTraceDirectLimit
open PrincipiaTractalis.SubstrateCompletionFaithful

/-! ## §1 — The completion's elements are level towers, and the tower
determines the element -/

/-- **The level tower of a completion element.**

    `condExpFin k x` is the level-`k` conditional expectation of `x`, valued in
    `Matrix (Fin (3^k)) (Fin (3^k)) ℂ`, which is literally the skeleton's
    `TimelessFieldLevelOperators k`. This is the candidate `seq` field. -/
noncomputable def levelTower (x : TimelessFieldCompletion) :
    ∀ k : ℕ, TimelessFieldLevelOperators k :=
  fun k => condExpFin k x

/-- **★ The tower determines the element.**

    If two elements of the completion have the same level-`k` conditional
    expectation for every `k`, they are equal. Proof: the level tower
    reconstructs the element, `condExpCompletion k x → x`, and limits in a
    Hausdorff space are unique.

    So `TimelessFieldCompletion` injects into the skeleton's underlying
    sequence space `∀ k, TimelessFieldLevelOperators k`. -/
theorem levelTower_injective : Function.Injective levelTower := by
  intro x y hxy
  have hk : ∀ k, condExpCompletion k x = condExpCompletion k y := by
    intro k
    have h : condExpFin k x = condExpFin k y := congrFun hxy k
    unfold condExpCompletion
    rw [h]
  have hx : Filter.Tendsto (fun k => condExpCompletion k x) Filter.atTop (nhds x) :=
    condExpCompletion_tendsto x
  have hy : Filter.Tendsto (fun k => condExpCompletion k y) Filter.atTop (nhds y) :=
    condExpCompletion_tendsto y
  have hy' : Filter.Tendsto (fun k => condExpCompletion k x) Filter.atTop (nhds y) := by
    have hfun : (fun k => condExpCompletion k x) = (fun k => condExpCompletion k y) :=
      funext hk
    rw [hfun]
    exact hy
  exact tendsto_nhds_unique hx hy'

/-! ## §2 — The one identity that remains -/

/-- **The carrier-bridge compatibility.**

    The skeleton's canonical connecting family is `partialTraceMorphism`,
    which marginalises digit functions. The completion's levels are cut by
    `condExpFin`, which iterates `partialTraceStep`. This says the two agree.

    It is an equation between two defined functions — not a `True` marker, and
    not satisfied by an arbitrary choice. It is the removal condition for the
    conditional results of §3. -/
def CarrierBridgeCompatibility : Prop :=
  ∀ (x : TimelessFieldCompletion) ⦃k k' : ℕ⦄ (h : k ∣ k'),
    partialTraceMorphism k k' h (condExpFin k' x) = condExpFin k x

/-! ## §3 — Given the identity, the carriers are identified -/

/-- **The completion maps into the skeleton, given the compatibility.**

    The `seq` field is the level tower of §1; the `compat` field is exactly
    the hypothesis. -/
noncomputable def toSkeleton (hc : CarrierBridgeCompatibility)
    (x : TimelessFieldCompletion) : TimelessFieldType partialTraceMorphism where
  seq := levelTower x
  compat := fun {_k _k'} h => hc x h

/-- The `seq` field of the image is the level tower, by construction. -/
theorem toSkeleton_seq (hc : CarrierBridgeCompatibility)
    (x : TimelessFieldCompletion) :
    (toSkeleton hc x).seq = levelTower x := rfl

/-- **★ And that map is injective.**

    So under `CarrierBridgeCompatibility` the completion is a subobject of the
    skeleton: the two things ch04 calls `T_∞` are the same object, with the
    skeleton the ambient sequence space and the completion the part of it that
    carries the C*-structure.

    This proves the implication, not the hypothesis. -/
theorem toSkeleton_injective (hc : CarrierBridgeCompatibility) :
    Function.Injective (toSkeleton hc) := by
  intro x y hxy
  apply levelTower_injective
  have h := congrArg TimelessFieldElement.seq hxy
  rw [toSkeleton_seq, toSkeleton_seq] at h
  exact h

/-- **The honest non-claim.**

    Either the compatibility holds — and then §3 identifies the carriers — or
    it fails, and the skeleton's connecting maps are not the completion's
    conditional expectations. This file does not say which, and states the
    disjunction so the gap cannot be read as either settled or hidden. -/
theorem carriers_identified_or_connecting_maps_differ :
    CarrierBridgeCompatibility ∨ ¬ CarrierBridgeCompatibility :=
  em CarrierBridgeCompatibility

end PF.Referee.TimelessFieldCarrierBridge
