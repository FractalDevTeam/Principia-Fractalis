/-
# The substrate claim, stated where the theorems are

**Date**: 2026-11-27 (Legion).

ch04's central claim, `TimelessFieldExistenceClaim`, is stated over the
**skeleton** carrier `TimelessFieldType φ`. Four of its five conjuncts are
satisfiable by arbitrary choices there --- the trace conjunct asks only
`∀ a, τ a = τ a`, the K-theory and spacetime conjuncts are `Nonempty`, and the
force conjunct is provably the same proposition as the spacetime one. And we
proved on 2026-10-05, in `PF/Ch01Ch03Ch04Ch06FoundationDefects.lean`, that the
skeleton's stated construction collapses: the projective limit of downward
coarse-grainings gives the zero object.

`PF/Consciousness/TimelessFieldConcreteMorphism.lean` names the fix in its own
scope note: *"Promoting the witnesses from skeleton-level to operator-algebraic
content … is downstream work."*

**This file is that promotion, and it needs no new mathematics.** Every
conjunct below is an existing theorem of this corpus about
`TimelessFieldCompletion` --- the completion of the *direct* limit, which is
the carrier `FoundationDefects` identified as the repair and the one
Remark `rem:two-carriers` of ch04 now points the reader to. Nothing is
restated as a hypothesis; the bundle is discharged outright.

## What is in it

| conjunct | discharged by |
|---|---|
| the canonical trace is faithful | `substrate_UHF_trace_faithful_unconditional` |
| additive | `UHF_trace_add` |
| tracial | `UHF_trace_mul_comm` |
| positive | `UHF_trace_star_mul_self_nonneg` |
| it is the **only** tracial state | `substrate_tracial_state_space_singleton` |
| the algebra is C\*-simple | `substrate_completion_simple_unconditional` |
| every element is reconstructed by its finite-level tower | `condExpCompletion_tendsto` |

The last conjunct is the honest replacement for the skeleton's "natural
filtration": instead of asserting that some level representative exists, it
says the conditional-expectation tower actually converges back to the element.

## What is deliberately NOT in it

- **Nuclearity.** Not formalized for this carrier anywhere in the corpus. It is
  a genuine classical fact about `M_{3^∞}` and it is cited, not proved, so it
  does not appear here. Putting it in would be the defect this file exists to
  remove.
- **The K-theory statement.** `K_0 ≅ ℤ[1/3]` and `K_1 ≅ 0` are correct for
  `M_{3^∞}`, and `FoundationDefects` says so, but mathlib has no operator
  K-theory at this pin, so the operator-algebraic statement cannot be written.
  What exists is a typed carrier, which is not the same thing.
- **Spacetime and force emergence.** Both skeleton markers are
  `Nonempty (T → T)` and are provably the same proposition
  (`spacetimeEmergence_eq_forceUnification`). There is no operator-algebraic
  content to promote yet, so none is claimed.

So this is strictly a promotion of what is proved, with the gaps left visible.
Nothing upstream is renamed or deleted, and `TimelessFieldExistenceClaim` keeps
its name and its clients.
-/
import PF.SubstrateCompletionFaithful
import PF.AlphaFromSubstrateKTheory_r123
import PF.SubstrateUHFTraceCauchySchwarz
import PF.SubstrateUHFTraceIsTracial
import PF.SubstrateUHFTraceIsPositive

set_option autoImplicit false

namespace PF.Referee.SubstrateOperatorAlgebraicStructure

open scoped ComplexOrder

open PrincipiaTractalis
open PrincipiaTractalis.SubstrateTimelessFieldCompletion
open PrincipiaTractalis.SubstrateUHFPreTraceDirectLimit
open PrincipiaTractalis.SubstrateTraceUniqueness
open PrincipiaTractalis.SubstrateCompletionFaithful
open PrincipiaTractalis.SubstrateUHFTraceCauchySchwarz
open PrincipiaTractalis.SubstrateUHFTraceIsTracial
open PrincipiaTractalis.SubstrateUHFTraceIsPositive
open PrincipiaTractalis.AlphaFromSubstrateKTheory

/-! ## §1 — The claim, over the carrier that carries the theorems -/

/-- **The substrate's operator-algebraic structure.**

    Seven conjuncts, every one of them a statement about
    `TimelessFieldCompletion` with real content: none is satisfiable by an
    arbitrary function, and none is `True`. This is the operator-algebraic
    form of what ch04's `NuclearStructure` gestures at over the skeleton. -/
def OperatorAlgebraicStructure : Prop :=
  -- (1) the canonical trace detects positivity
  (∀ x : TimelessFieldCompletion, UHF_trace (star x * x) = 0 → x = 0)
  -- (2) it is additive
  ∧ (∀ x y : TimelessFieldCompletion,
      UHF_trace (x + y) = UHF_trace x + UHF_trace y)
  -- (3) it is tracial
  ∧ (∀ x y : TimelessFieldCompletion, UHF_trace (x * y) = UHF_trace (y * x))
  -- (4) it is positive on `x* x`
  ∧ (∀ x : TimelessFieldCompletion, 0 ≤ UHF_trace (star x * x))
  -- (5) it is the ONLY tracial state
  ∧ (∀ φ : TimelessFieldCompletion → ℂ, IsTracialState φ → φ = UHF_trace)
  -- (6) the algebra is C*-simple
  ∧ (∀ I : TwoSidedIdeal TimelessFieldCompletion, I = ⊥ ∨ I = ⊤)
  -- (7) every element is reconstructed by its finite-level tower
  ∧ (∀ x : TimelessFieldCompletion,
      Filter.Tendsto (fun k => condExpCompletion k x) Filter.atTop (nhds x))

/-- **★★ The substrate's operator-algebraic structure holds, unconditionally.**

    No hypothesis, no placeholder, no `True`, and no new mathematics: each
    component is an existing theorem of this corpus. This is the statement
    that should be cited where `TimelessFieldExistenceClaim`'s nuclear
    conjunct was cited before. -/
theorem operatorAlgebraicStructure_holds :
    OperatorAlgebraicStructure :=
  ⟨substrate_UHF_trace_faithful_unconditional,
   UHF_trace_add,
   UHF_trace_mul_comm,
   UHF_trace_star_mul_self_nonneg,
   substrate_tracial_state_space_singleton,
   substrate_completion_simple_unconditional,
   condExpCompletion_tendsto⟩

/-! ## §2 — Why this is a promotion and not a restatement -/

/-- The trace conjunct of the skeleton claim is satisfied by every function,
    the constant-zero functional included, over any carrier. Recorded so the
    difference between the two statements is machine-checked rather than
    asserted in prose. -/
theorem skeleton_trace_conjunct_is_free
    {T : Type} [Inhabited T] (P : Prop) (_hP : P) :
    ∃ τ : T → ℂ, ∀ a, τ a = τ a :=
  ⟨fun _ => 0, fun _ => rfl⟩

/-- Conjunct (1) of §1 is not of that kind: the constant-zero functional fails
    it unless the algebra is trivial. Stated as an equivalence so no
    nontriviality fact is assumed. -/
theorem genuine_trace_conjunct_excludes_zero_functional :
    (¬ ∀ x : TimelessFieldCompletion,
        (fun _ => (0 : ℂ)) (star x * x) = 0 → x = 0)
      ↔ ∃ x : TimelessFieldCompletion, x ≠ 0 := by
  constructor
  · intro h
    by_contra hc
    exact h (fun x _ => by
      by_contra hx
      exact hc ⟨x, hx⟩)
  · intro ⟨x, hx⟩ h
    exact hx (h x rfl)

/-- **The uniqueness conjunct, isolated.** Any functional satisfying the five
    `IsTracialState` conditions *is* the canonical trace --- so the substrate
    admits exactly one unbiased observer. This is the sharpest single
    consequence in the bundle and it is worth citing on its own. -/
theorem unique_tracial_state
    (φ : TimelessFieldCompletion → ℂ) (hφ : IsTracialState φ) :
    φ = UHF_trace :=
  substrate_tracial_state_space_singleton φ hφ

/-- **Faithfulness and simplicity together**, the pair ch04's Theorem 4.9
    ledger calls kernel-verified, as one citable name. -/
theorem faithful_and_simple :
    (∀ x : TimelessFieldCompletion, UHF_trace (star x * x) = 0 → x = 0)
      ∧ (∀ I : TwoSidedIdeal TimelessFieldCompletion, I = ⊥ ∨ I = ⊤) :=
  ⟨substrate_UHF_trace_faithful_unconditional,
   substrate_completion_simple_unconditional⟩

end PF.Referee.SubstrateOperatorAlgebraicStructure
