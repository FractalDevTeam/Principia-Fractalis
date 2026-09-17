/-
# The substrate automorphism quotient collapses to a point.

★ 2026-09-17 — Every continuous unital ℂ-algebra endomorphism of the substrate
`T∞ = TimelessFieldCompletion` preserves the canonical UHF trace. Consequently
the set of trace functionals induced by such maps is the **one-point set**
`{τ_UHF}`, and the "gauge" subgroup that Principia Fractalis quotients by is the
whole automorphism group. ★

## What this settles, and what it does not

`ch04_timeless_field.tex:455-461` (Thm 4.18) defines spacetime as

    M⁴ = Aut(T∞) / Aut₀(T∞),   "where Aut₀(T∞) are gauge automorphisms
                                 preserving the trace τ."

and `ch04:477-489` then computes `dim M⁴ = dim Aut − dim Aut₀`.

This file proves, from kernel theorems already in the corpus, that **Aut₀ is not
a proper subgroup**: the trace-preserving condition is satisfied by *every*
continuous unital ℂ-algebra endomorphism, automorphisms included. So the
subtraction `dim Aut − dim Aut₀` is a subtraction of a thing from itself, and the
quotient in Thm 4.18 identifies everything with everything.

**The inference to spacetime is a mathematical inference, not a kernel theorem.**
What is machine-checked below is a statement about trace functionals on an
operator algebra. It says the *particular construction written at ch04:461*
collapses. It does not say spacetime fails to emerge, and it does not rule out
some other construction. Nothing here is about physics.

**Scope limits, stated so they are not silently dropped.**

* Continuity is carried as an explicit hypothesis rather than derived from
  C\*-isometry. That makes the result strictly weaker, and therefore safer: we
  claim nothing about discontinuous automorphisms.
* Bijectivity is never used. The result is proved for *endomorphisms*, which
  subsumes the automorphism case the book needs. This is a strengthening, not a
  gap.
* The `star` structure is not used. `IsTracialState` (r113) deliberately omits
  positivity, so plain ℂ-algebra structure suffices.
* This says nothing about the skeleton type `TimelessFieldType φ` used by
  `PF/Consciousness/TimelessField.lean` and `FrobeniusChurn.lean`. Those are a
  different object. In particular `SpacetimeEmergence` there is still
  `Nonempty (T → T)` witnessed by `id`, and remains vacuous.
* No claim is made about `π₀` of the automorphism group, or about any topology
  on it. Not attempted here.

## On the cardinality `1`

`inducedTraces_encard_eq_one` below is a *computed* cardinality, not a constant
put in by hand. The framework elsewhere labels a unity anchor `α_Poincaré = 1`;
whether that label is attached to this `1` is a naming decision and is **not**
established by anything in this file. No theorem here mentions it.

## Route

Every input already exists. Nothing is assumed.

1. For `α` a continuous unital ℂ-algebra endomorphism, `UHF_trace ∘ α` satisfies
   the five fields of `IsTracialState` (`SubstrateTraceUniqueness.lean:164`):
   `continuous` from composition, `add` / `smul` / `tracial` from `α`'s algebra
   laws composed with `UHF_trace_add` / `UHF_trace_smul` / `UHF_trace_mul_comm`,
   and `unital` from `α 1 = 1` plus `uhf_trace_isTracialState`.
2. `substrate_UHF_trace_unique` (`SubstrateTraceUniqueness.lean:239`) then forces
   `UHF_trace ∘ α = UHF_trace`.
3. The corollaries are `Set.ext`, `Set.subsingleton_singleton`, and
   `Set.encard_singleton`.

Kernel-only: [propext, Classical.choice, Quot.sound]. Zero project axioms.
Zero `sorry`. Zero `native_decide`.
-/

import PF.SubstrateTraceUniqueness
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace SubstrateAutomorphismQuotientCollapse

open SubstrateTimelessFieldCompletion
open SubstrateUHFPreTraceDirectLimit
open SubstrateUHFTraceCauchySchwarz
open SubstrateUHFTraceIsTracial
open SubstrateTraceUniqueness

/-! ## §1 — Continuous unital ℂ-algebra endomorphisms of the substrate -/

/-- **`IsContUnitalAlgEndo α`** — `α` is continuous, additive, ℂ-homogeneous,
    multiplicative and unital on `T∞`.

    This is the honest minimal hypothesis set. Bijectivity is NOT required, so
    every continuous unital ℂ-algebra *automorphism* — the objects `Aut(T∞)` of
    `ch04:455` — satisfies it. `star`-compatibility is NOT required either. -/
structure IsContUnitalAlgEndo (α : TimelessFieldCompletion → TimelessFieldCompletion) : Prop where
  continuous : Continuous α
  add : ∀ x y, α (x + y) = α x + α y
  smul : ∀ (c : ℂ) x, α (c • x) = c • α x
  mul : ∀ x y, α (x * y) = α x * α y
  unital : α 1 = 1

/-- The identity qualifies, so §2 is non-vacuous. -/
theorem id_isContUnitalAlgEndo :
    IsContUnitalAlgEndo (id : TimelessFieldCompletion → TimelessFieldCompletion) where
  continuous := continuous_id
  add := fun _ _ => rfl
  smul := fun _ _ => rfl
  mul := fun _ _ => rfl
  unital := rfl

/-! ## §2 — Main theorem: the trace is preserved -/

/-- **★ MAIN — every continuous unital ℂ-algebra endomorphism of `T∞` preserves
    the canonical UHF trace. ★**

    Proof: `UHF_trace ∘ α` is a tracial state, and r113 says there is only one. -/
theorem trace_preserved {α : TimelessFieldCompletion → TimelessFieldCompletion}
    (hα : IsContUnitalAlgEndo α) (x : TimelessFieldCompletion) :
    UHF_trace (α x) = UHF_trace x :=
  substrate_UHF_trace_unique (fun y => UHF_trace (α y))
    { continuous := UHF_trace_uniformContinuous.continuous.comp hα.continuous
      add := fun y z => by
        show UHF_trace (α (y + z)) = UHF_trace (α y) + UHF_trace (α z)
        rw [hα.add, UHF_trace_add]
      smul := fun c y => by
        show UHF_trace (α (c • y)) = c * UHF_trace (α y)
        rw [hα.smul, UHF_trace_smul]
      tracial := fun y z => by
        show UHF_trace (α (y * z)) = UHF_trace (α (z * y))
        rw [hα.mul, hα.mul, UHF_trace_mul_comm]
      unital := by
        show UHF_trace (α 1) = 1
        rw [hα.unital]
        exact uhf_trace_isTracialState.unital } x

/-- The induced trace functional is literally `UHF_trace`, as a function. -/
theorem inducedTrace_eq {α : TimelessFieldCompletion → TimelessFieldCompletion}
    (hα : IsContUnitalAlgEndo α) :
    (fun x => UHF_trace (α x)) = UHF_trace :=
  funext fun x => trace_preserved hα x

/-- **The book's gauge condition is no condition at all.** Being trace-preserving
    does not distinguish any subgroup: it holds of everything in sight. -/
theorem tracePreserving_of_isContUnitalAlgEndo
    {α : TimelessFieldCompletion → TimelessFieldCompletion}
    (hα : IsContUnitalAlgEndo α) :
    ∀ x, UHF_trace (α x) = UHF_trace x :=
  fun x => trace_preserved hα x

/-- Any two such maps induce the *same* trace functional, so the equivalence
    "induces the same trace" has a single class. -/
theorem inducedTrace_agree {α β : TimelessFieldCompletion → TimelessFieldCompletion}
    (hα : IsContUnitalAlgEndo α) (hβ : IsContUnitalAlgEndo β) :
    (fun x => UHF_trace (α x)) = (fun x => UHF_trace (β x)) := by
  rw [inducedTrace_eq hα, inducedTrace_eq hβ]

/-! ## §3 — The quotient: a one-point set -/

/-- The set of trace functionals induced by continuous unital ℂ-algebra
    endomorphisms of `T∞`. This is the invariant `ch04:461` quotients by. -/
def inducedTraces : Set (TimelessFieldCompletion → ℂ) :=
  {φ | ∃ α, IsContUnitalAlgEndo α ∧ φ = fun x => UHF_trace (α x)}

/-- **★ COLLAPSE — the invariant is the one-point set `{τ_UHF}`. ★** -/
theorem inducedTraces_eq_singleton : inducedTraces = {UHF_trace} := by
  ext φ
  constructor
  · rintro ⟨α, hα, rfl⟩
    exact inducedTrace_eq hα
  · rintro rfl
    exact ⟨id, id_isContUnitalAlgEndo, rfl⟩

/-- It is non-empty. -/
theorem inducedTraces_nonempty : inducedTraces.Nonempty :=
  ⟨UHF_trace, ⟨id, id_isContUnitalAlgEndo, rfl⟩⟩

/-- It has at most one element. -/
theorem inducedTraces_subsingleton : inducedTraces.Subsingleton := by
  rw [inducedTraces_eq_singleton]
  exact Set.subsingleton_singleton

/-- **Its cardinality is exactly one.** A computed cardinality, not an inserted
    constant. -/
theorem inducedTraces_encard_eq_one : inducedTraces.encard = 1 := by
  rw [inducedTraces_eq_singleton]
  exact Set.encard_singleton _

/-- **No two distinct classes exist.** There is no injection from a two-element
    type into the invariant, so the quotient cannot separate even two points —
    let alone carry a positive-dimensional manifold structure. -/
theorem no_two_distinct_inducedTraces (f : Fin 2 → inducedTraces) :
    ¬ Function.Injective f := by
  intro hf
  have h01 : (f 0 : TimelessFieldCompletion → ℂ) = (f 1 : TimelessFieldCompletion → ℂ) :=
    inducedTraces_subsingleton (f 0).2 (f 1).2
  have : f 0 = f 1 := Subtype.ext h01
  exact absurd (hf this) (by decide)

/-! ## §4 — Axiom audit -/

#print axioms trace_preserved
#print axioms inducedTrace_eq
#print axioms inducedTrace_agree
#print axioms inducedTraces_eq_singleton
#print axioms inducedTraces_nonempty
#print axioms inducedTraces_subsingleton
#print axioms inducedTraces_encard_eq_one
#print axioms no_two_distinct_inducedTraces

end SubstrateAutomorphismQuotientCollapse
end PrincipiaTractalis
