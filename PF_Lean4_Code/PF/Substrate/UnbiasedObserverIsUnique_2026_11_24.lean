/-
# The unbiased observer: traciality as basis-independence

**Date**: 2026-11-24 (Legion).

## The reading this formalises

A **state** on `T∞` is a perspective: a functional assigning a complex reading
to each element of the substrate. The state space is large, which is the formal
content of "the fractal is a source of endless perspectives".

A **tracial** state is the *unbiased* perspective, and that is not a metaphor —
it is what the equation says. `φ (x * y) = φ (y * x)` says the reading does not
depend on the order in which the observer composes, and the theorems below show
this forces the reading to be invariant under every change of basis. An
observer with no bias is an observer whose readings are basis-independent.

Two facts already in the corpus bracket this file:

* `PF/SubstrateTraceUniqueness.lean` (r113.b, `tracialState_coe_level`) proves
  that for **any** tracial state `φ` on `T∞`, the value on each finite level is
  the *normalized matrix trace* — the maximally mixed, no-preferred-direction
  reading. Positivity is deliberately omitted there; uniqueness holds for every
  continuous unital ℂ-linear tracial functional.
* `PF/SubstrateAutomorphismQuotientCollapse.lean` proves
  `inducedTraces_eq_singleton : inducedTraces = {UHF_trace}` and
  `inducedTraces_encard_eq_one` — the automorphism-induced traces number
  **exactly one**.

So the structure is: many states, hence many perspectives; impose zero bias;
**exactly one** survives. The uniqueness is not an obstruction to anything. It
is what it means for an unbiased reading to exist at all.

## What is proved here

1. `tracial_conjugation_invariant` — for any two-sided inverse pair `u, v`,
   `φ (u * x * v) = φ x`. **Basis-independence.** The observer's reading is
   unchanged by any invertible change of coordinates. This is "no bias" as a
   theorem rather than a word.
2. `tracial_similarity_invariant` — the same, phrased as: similar elements
   receive equal readings.
3. `tracial_commutator_vanishes` — `φ (x * y - y * x) = 0`. The unbiased
   observer sees **no commutator**: order carries no information for it. This
   is the sharpest one-line form of the principle.
4. `tracial_sub` — the subtractivity the above needs, derived from the
   `add` and `smul` fields rather than assumed.

## Scope — what is NOT claimed

* **Nothing here is about spacetime.** It does not bear on ch04 Thm 4.18, which
  `PF/Consciousness/SpacetimeEmergenceUpgrade_2026_11_24.lean` shows is
  unconditionally true as encoded and therefore carries no information.
* **No physical interpretation is asserted.** Reading the unique induced trace
  as wave-function collapse, or as a singularity, is an interpretation of the
  mathematics, not a consequence of it. No theorem below mentions measurement,
  collapse, or consciousness, and none should be cited as establishing them.
* The `1` of `inducedTraces_encard_eq_one` is a *computed* cardinality. The
  collapse file is explicit that identifying it with the framework's unity
  anchor `α_Poincaré = 1` is "a naming decision and is **not** established by
  anything in this file". Nothing here identifies them either.

## An observation about the complexity axis, recorded as an observation

The unbiased state is the one that **cannot distinguish**: by (3) it annihilates
every commutator, and by r113.b it is the uniform reading on each level. A
complexity *separation* needs the opposite — a functional that deliberately
does distinguish. In this corpus that object is
`pf_enum_separator`, whose defining property includes
`pf_enum_separator .P ≠ pf_enum_separator .NP` with support contained in
`{P, NP}` (`PF/TuringEncoding/PNeqNPCollapsesToEnumBridge.lean`,
`PF_attack_outside_both_historical_barriers`).

So the two functionals sit at opposite poles: maximal bias is what separates,
zero bias is what collapses. That is a structural remark about two existing
constructions. **It is not a theorem, it proves nothing about P vs NP, and the
P-vs-NP premise remains Clay-level open** per
`substrate_P_neq_NP_V4_position_at_HEAD`.

SPDX-License-Identifier: Apache-2.0
Author: Pablo Cohen.  2026-11-24.
-/

import PF.SubstrateTimelessFieldCompletion
import PF.SubstrateTraceUniqueness
import Mathlib.Tactic

-- Without this, an unqualified type name that is NOT in scope is silently
-- auto-bound as a fresh `Type u_*` variable, and every instance lookup on it
-- then fails for the wrong reason. That happened on the first draft of this
-- file: `TimelessFieldCompletion` was auto-bound and Lean reported "failed to
-- synthesize Ring" on an arbitrary type.
set_option autoImplicit false

namespace PF.Substrate.UnbiasedObserver

open PrincipiaTractalis.SubstrateTimelessFieldCompletion
open PrincipiaTractalis.SubstrateTraceUniqueness

variable {φ : TimelessFieldCompletion → ℂ}

/-! ## §1 — Subtractivity, derived not assumed -/

/-- `φ` is subtractive. Derived from the `add` and `smul` fields: `-y` is
    `(-1 : ℂ) • y`. -/
theorem tracial_sub (h : IsTracialState φ) (x y : TimelessFieldCompletion) :
    φ (x - y) = φ x - φ y := by
  have hneg : φ (-y) = -φ y := by
    have : ((-1 : ℂ)) • y = -y := by
      simp
    calc φ (-y) = φ (((-1 : ℂ)) • y) := by rw [this]
      _ = (-1 : ℂ) * φ y := h.smul _ _
      _ = -φ y := by ring
  calc φ (x - y) = φ (x + -y) := by rw [sub_eq_add_neg]
    _ = φ x + φ (-y) := h.add _ _
    _ = φ x - φ y := by rw [hneg]; ring

/-! ## §2 — Basis-independence: the formal content of "no bias" -/

/-- **★ The unbiased observer's reading is invariant under change of basis.**

    For any two-sided inverse pair `u, v` (so `u` is invertible with inverse
    `v`), conjugating `x` leaves the reading unchanged:
    `φ (u * x * v) = φ x`.

    Proof is traciality applied once, then associativity: the observer cannot
    tell which coordinates were used. -/
theorem tracial_conjugation_invariant (h : IsTracialState φ)
    (u v x : TimelessFieldCompletion) (hvu : v * u = 1) :
    φ (u * x * v) = φ x := by
  calc φ (u * x * v) = φ (v * (u * x)) := h.tracial _ _
    _ = φ (v * u * x) := by rw [mul_assoc]
    _ = φ ((1 : TimelessFieldCompletion) * x) := by rw [hvu]
    _ = φ x := by rw [one_mul]

/-- **Similar elements receive equal readings.** Same fact, stated the way a
    reader meets it: if `y` is `x` viewed in another basis, `φ` cannot
    distinguish them. -/
theorem tracial_similarity_invariant (h : IsTracialState φ)
    (u v x y : TimelessFieldCompletion) (hvu : v * u = 1)
    (hy : y = u * x * v) :
    φ y = φ x := by
  rw [hy]; exact tracial_conjugation_invariant h u v x hvu

/-! ## §3 — The sharpest form: no commutator is visible -/

/-- **★ The unbiased observer annihilates every commutator.**

    `φ (x * y - y * x) = 0`. Order carries no information for a tracial state:
    there is no experiment it can perform whose outcome depends on which way
    round two elements were composed. This is the one-line form of "awareness
    with no bias". -/
theorem tracial_commutator_vanishes (h : IsTracialState φ)
    (x y : TimelessFieldCompletion) :
    φ (x * y - y * x) = 0 := by
  rw [tracial_sub h, h.tracial x y, sub_self]

/-! ## §4 — One citable bundle -/

/-- **`unbiased_observer_bundle`** — the three facts in one theorem.

    A tracial state on `T∞` is subtractive, invariant under every change of
    basis, and blind to every commutator. Together with r113.b
    (`tracialState_coe_level`: any tracial state is the normalized matrix trace
    on each level) and `inducedTraces_encard_eq_one` (exactly one
    automorphism-induced trace exists), this is the formal content of "the
    unbiased perspective is unique".

    Claims nothing about spacetime, measurement, collapse or consciousness.
    See this file's header. -/
theorem unbiased_observer_bundle (h : IsTracialState φ) :
    (∀ x y : TimelessFieldCompletion, φ (x - y) = φ x - φ y) ∧
    (∀ u v x : TimelessFieldCompletion, v * u = 1 → φ (u * x * v) = φ x) ∧
    (∀ x y : TimelessFieldCompletion, φ (x * y - y * x) = 0) :=
  ⟨tracial_sub h,
   fun u v x hvu => tracial_conjugation_invariant h u v x hvu,
   tracial_commutator_vanishes h⟩

end PF.Substrate.UnbiasedObserver

/-! ## §Axiom audit -/
#print axioms PF.Substrate.UnbiasedObserver.tracial_sub
#print axioms PF.Substrate.UnbiasedObserver.tracial_conjugation_invariant
#print axioms PF.Substrate.UnbiasedObserver.tracial_commutator_vanishes
#print axioms PF.Substrate.UnbiasedObserver.unbiased_observer_bundle
