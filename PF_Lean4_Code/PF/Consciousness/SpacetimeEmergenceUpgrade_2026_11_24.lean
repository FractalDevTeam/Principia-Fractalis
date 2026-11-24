/-
# Spacetime emergence: the kernel statement, and a structured upgrade

**Date**: 2026-11-24 (Legion).

## The situation, stated exactly

`PF/Consciousness/TimelessField.lean` encodes ch04 Thm 4.18 as

```lean
def SpacetimeEmergence (φ : …) : Prop :=
  Nonempty (TimelessFieldType φ → TimelessFieldType φ)
```

and ch04 Thm 4.20 as

```lean
def ForceUnification (φ : …) : Prop :=
  Nonempty (TimelessFieldType φ → TimelessFieldType φ)
```

**Byte-identical bodies.** Both are discharged in
`TimelessFieldConcreteMorphism.lean` by `⟨id⟩`, at what that file correctly
calls "the skeleton level", and
`SubstrateAutomorphismQuotientCollapse.lean:43` already records the fact in
prose: *"In particular `SpacetimeEmergence` there is still `Nonempty (T → T)`
witnessed by `id`, and remains vacuous."*

So the vacuity is **already disclosed**, honestly, in the right place. What has
not existed until now is the kernel statement of it, and a structured
predicate that demands a datum instead of the identity map.

## What is proved here

1. `spacetimeEmergence_holds_unconditionally` — `∀ φ, SpacetimeEmergence φ`.
   No hypotheses. A Prop provable for *every* `φ` cannot distinguish one `φ`
   from another, so it has no discriminating power whatever. This is the
   sharpest available statement of the vacuity: stronger than "it is witnessed
   by `id`", because it quantifies over all parameters.
2. `forceUnification_holds_unconditionally` — the same, for Thm 4.20.
3. `spacetimeEmergence_eq_forceUnification` — **the two are the same Prop**, by
   `rfl`. Thm 4.18 and Thm 4.20 are not merely both vacuous; they are
   indistinguishable in the kernel. No theorem can hold of one and fail of the
   other.
4. `SpacetimeEmergenceStructured` + `spacetime_structured_implies_original` —
   the upgrade, modelled directly on `TimelessFieldKTheoryUpgrade.lean`, which
   did exactly this for `KTheoryOfTimelessField`: replace a bare `Nonempty` by
   a predicate demanding an explicit carrier, and prove the cascade back.

## The upgrade, and its honest limits

`SpacetimeEmergenceStructured φ` demands a `SpacetimeCarrier`: a point type
with an injective coordinate map into `Fin 4 → ℝ`, together with a map from
`TimelessFieldType φ` into it. **`id` does not satisfy this** — that is the
entire point. A witness must exhibit four real coordinates.

What it does **NOT** do, stated in the same spirit as the K-theory upgrade's
own disclaimer:

* It does **not** derive the carrier from `Aut(T_∞) / Aut_0(T_∞)`. The carrier
  is *posited*, exactly as `KZeroCarrier` is posited there rather than proved
  equal to the operator-algebraic `K_0(T_∞)`.
* It does **not** supply a manifold, a smooth structure, or a metric. Four
  injective real coordinates are not a spacetime; they are the minimum datum
  a spacetime claim must at least carry.
* **It does not evade the collapse.**
  `SubstrateAutomorphismQuotientCollapse.lean` proves
  `inducedTraces_eq_singleton : inducedTraces = {UHF_trace}` and
  `inducedTraces_encard_eq_one` — the automorphism-induced traces number
  **exactly one**. A quotient with a single induced trace cannot itself
  generate a four-parameter family, so the derivation ch04 Thm 4.18 asserts is
  not merely unformalised but obstructed in the direction the collapse
  measures. That file is careful that its computed `1` is *not* to be
  identified with `α_Poincaré = 1`; nothing here identifies them either.

So the honest reading: this file converts "a Prop satisfied by `id`" into "a
Prop requiring four coordinates", and makes the remaining gap precise — the
carrier must come *from* the automorphism quotient, and the collapse theorem is
evidence it cannot.

## One consequence worth noting about the cascade

Because `SpacetimeEmergence φ` is unconditionally true (fact 1), **any**
structured predicate implies it trivially. The cascade therefore carries no
information, and all the content sits in the structured predicate. That is
recorded rather than presented as a result — the same is true of the K-theory
upgrade's cascade, where the original is likewise a bare `Nonempty`.

SPDX-License-Identifier: Apache-2.0
Author: Pablo Cohen.  2026-11-24.
-/

import PF.Consciousness.TimelessField
import Mathlib.Tactic

namespace PF.Consciousness.SpacetimeEmergenceUpgrade

open PrincipiaTractalis.TimelessField

/-! ## §1 — The kernel statement of the vacuity -/

/-- **`SpacetimeEmergence` holds for every `φ`, with no hypotheses.**

    `ch04` Thm 4.18 is encoded as `Nonempty (T → T)`, and the identity map
    inhabits that for any type whatever. Quantifying over `φ` is the sharpest
    form of the statement: a Prop provable for every parameter cannot
    distinguish any two parameters, so it carries no information about the
    Timeless Field at all. -/
theorem spacetimeEmergence_holds_unconditionally
    (φ : ∀ k k', k ∣ k' → LevelMorphism k k') :
    SpacetimeEmergence φ :=
  ⟨id⟩

/-- **`ForceUnification` likewise** — ch04 Thm 4.20, same shape. -/
theorem forceUnification_holds_unconditionally
    (φ : ∀ k k', k ∣ k' → LevelMorphism k k') :
    ForceUnification φ :=
  ⟨id⟩

/-- **★ Thm 4.18 and Thm 4.20 are the SAME proposition.**

    Not merely both vacuous — definitionally equal, so no theorem can hold of
    one and fail of the other. Spacetime emergence and force unification are,
    as currently encoded, indistinguishable in the kernel. -/
theorem spacetimeEmergence_eq_forceUnification :
    SpacetimeEmergence = ForceUnification := rfl

/-! ## §2 — The structured upgrade

Modelled on `TimelessFieldKTheoryUpgrade.lean`, which replaced the bare
`Nonempty (TimelessFieldType φ)` of ch04 Thm 4.16 with a predicate demanding an
explicit `K_0` carrier and the multiply-by-3 connecting map. -/

/-- A minimal datum any four-dimensional spacetime claim must carry: a point
    type with an **injective** coordinate map into `Fin 4 → ℝ`.

    Injectivity is what makes the four coordinates do work — without it a
    one-point type would qualify. -/
structure SpacetimeCarrier : Type 1 where
  /-- The point set. -/
  Point : Type
  /-- Four real coordinates for each point. -/
  coords : Point → (Fin 4 → ℝ)
  /-- Distinct points have distinct coordinates. -/
  coords_injective : Function.Injective coords
  /-- The carrier is inhabited. -/
  nonempty : Nonempty Point

/-- **`SpacetimeEmergenceStructured`** — the upgraded predicate. It demands an
    actual four-coordinate carrier together with a map from the Timeless Field
    into it. The identity map does **not** satisfy this. -/
def SpacetimeEmergenceStructured
    (φ : ∀ k k', k ∣ k' → LevelMorphism k k') : Prop :=
  ∃ C : SpacetimeCarrier, Nonempty (TimelessFieldType φ → C.Point)

/-- **The cascade**: the structured predicate implies the original.

    Proved, but note §"One consequence" in the header — since the original is
    unconditionally true, this implication carries no information. The content
    is entirely in the structured predicate's demand for coordinates. -/
theorem spacetime_structured_implies_original
    (φ : ∀ k k', k ∣ k' → LevelMorphism k k')
    (_h : SpacetimeEmergenceStructured φ) :
    SpacetimeEmergence φ :=
  spacetimeEmergence_holds_unconditionally φ

/-- A carrier exists, so the structured predicate is not vacuously
    unsatisfiable: `Fin 4 → ℝ` with the identity coordinate map.

    This is a **satisfiability witness only**. It is not derived from
    `Aut(T_∞) / Aut_0(T_∞)`, and exhibiting it establishes nothing about
    spacetime emerging from the substrate — exactly as the K-theory upgrade's
    `canonicalKTheoryCarrier` establishes nothing about the operator-algebraic
    `K_0(T_∞)`. -/
def coordinateCarrier : SpacetimeCarrier where
  Point := Fin 4 → ℝ
  coords := id
  coords_injective := Function.injective_id
  nonempty := ⟨fun _ => 0⟩

/-- The structured predicate is satisfiable, given any map into the carrier. -/
theorem spacetimeEmergenceStructured_satisfiable
    (φ : ∀ k k', k ∣ k' → LevelMorphism k k') :
    SpacetimeEmergenceStructured φ :=
  ⟨coordinateCarrier, ⟨fun _ => (fun _ => 0)⟩⟩

/-! ## §3 — One citable bundle -/

/-- **`spacetime_emergence_upgrade_bundle`** — the four facts in one theorem.

    ch04 Thm 4.18 holds for every `φ` with no hypotheses; so does Thm 4.20;
    the two are the **same** Prop; and the structured upgrade is both
    satisfiable and sufficient for the original.

    No claim is made that spacetime emerges from the substrate. See the
    header's limits, in particular the collapse theorem
    `inducedTraces_eq_singleton`. -/
theorem spacetime_emergence_upgrade_bundle
    (φ : ∀ k k', k ∣ k' → LevelMorphism k k') :
    SpacetimeEmergence φ ∧
    ForceUnification φ ∧
    (SpacetimeEmergence = ForceUnification) ∧
    SpacetimeEmergenceStructured φ :=
  ⟨spacetimeEmergence_holds_unconditionally φ,
   forceUnification_holds_unconditionally φ,
   spacetimeEmergence_eq_forceUnification,
   spacetimeEmergenceStructured_satisfiable φ⟩

end PF.Consciousness.SpacetimeEmergenceUpgrade

/-! ## §Axiom audit -/
#print axioms PF.Consciousness.SpacetimeEmergenceUpgrade.spacetimeEmergence_holds_unconditionally
#print axioms PF.Consciousness.SpacetimeEmergenceUpgrade.spacetimeEmergence_eq_forceUnification
#print axioms PF.Consciousness.SpacetimeEmergenceUpgrade.spacetime_structured_implies_original
#print axioms PF.Consciousness.SpacetimeEmergenceUpgrade.spacetime_emergence_upgrade_bundle
