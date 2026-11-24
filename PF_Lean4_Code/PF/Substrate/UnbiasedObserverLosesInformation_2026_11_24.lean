/-
# The unbiased observer necessarily loses information

**Date**: 2026-11-24 (Legion).

## What this is

No new mathematics is introduced. Three results already in the corpus are
composed, and a theorem falls out that none of them states alone.

* `PF/SubstrateNotCommutative_r217.lean` proves
  `substrate_not_commutative : ∃ a b : TimelessFieldCompletion, a * b ≠ b * a`
  — not abstractly, but from two explicit matrix units at substrate level 1
  pushed through the isometric level embedding.
* `PF/Substrate/UnbiasedObserverIsUnique_2026_11_24.lean` proves
  `tracial_commutator_vanishes : φ (x * y - y * x) = 0` for every tracial
  state `φ` — traciality is basis-independence, i.e. "no bias".
* `PF/SubstrateAutomorphismQuotientCollapse.lean` proves
  `inducedTraces_encard_eq_one` — exactly one automorphism-induced trace
  exists.

Put the first two together and the unbiased observer is provably **not
injective**: there are distinct elements of the substrate it cannot tell apart,
and they are exhibited.

## What is proved

1. `unbiased_identifies_distinct_elements` — there exist `a, b` with
   `a * b ≠ b * a` such that **every** tracial state assigns them the same
   reading. Two genuinely different elements of `T∞`, one value.
2. `no_tracial_state_is_injective` — **no tracial state on `T∞` is injective.**
   Three lines: injectivity plus traciality would force `a * b = b * a`,
   contradicting r217. Not "we have not found an injective one" — there is
   none.
3. `commutator_nonzero_in_kernel_of_every_unbiased_observer` — the sharpest
   form: there is a **nonzero** element of the substrate that every unbiased
   observer reads as **zero**. It is the commutator `a * b - b * a`.

## Why this is worth having

`UHF_trace` is *faithful* (r112/r113: `UHF_trace (star x * x) = 0 → x = 0`).
Fact 2 shows it is nevertheless *not injective*. Those are compatible and the
combination is the precise statement: the unbiased reading can always answer
**"is this zero?"** and can never answer **"which element is this?"**

So the information an unbiased observer loses is not arbitrary — by fact 3 it is
exactly the commutator subspace, which is exactly the structure that makes the
substrate non-commutative. r217 also proves `GelfandSpectrum = ∅`: there is no
space of points on which `T∞` is an algebra of functions. The non-commutativity
is not removable, and neither is the loss.

## Scope — what is NOT claimed

* **No physical interpretation is asserted.** Reading this as wave-function
  collapse, decoherence, or measurement is an interpretation of the
  mathematics, not a consequence of it. No theorem below mentions measurement,
  collapse, observation or consciousness, and none should be cited as
  establishing them. The information-loss language in this header is about
  injectivity of a function and nothing more.
* **Nothing here bears on spacetime emergence.** ch04 Thm 4.18 is
  unconditionally true as encoded; see
  `PF/Consciousness/SpacetimeEmergenceUpgrade_2026_11_24.lean`.
* **Nothing here is evidence for or against any Clay statement.**
* Faithfulness is cited, not re-proved: `UHF_trace_faithful` is r112/r113's and
  is used only in this header's discussion, not in any proof below.

SPDX-License-Identifier: Apache-2.0
Author: Pablo Cohen.  2026-11-24.
-/

import PF.SubstrateNotCommutative_r217
import PF.Substrate.UnbiasedObserverIsUnique_2026_11_24
import Mathlib.Tactic

set_option autoImplicit false

namespace PF.Substrate.UnbiasedObserverLoses

open PrincipiaTractalis.SubstrateTimelessFieldCompletion
open PrincipiaTractalis.SubstrateTraceUniqueness
open PrincipiaTractalis.SubstrateNotCommutative
open PF.Substrate.UnbiasedObserver

/-! ## §1 — Distinct elements, one reading -/

/-- **Every unbiased observer identifies two genuinely distinct elements.**

    `r217` supplies `a, b` with `a * b ≠ b * a`; traciality gives
    `φ (a * b) = φ (b * a)` for every tracial `φ`. The witnesses are explicit
    matrix units at substrate level 1, not an abstract existence claim. -/
theorem unbiased_identifies_distinct_elements :
    ∃ a b : TimelessFieldCompletion,
      a * b ≠ b * a ∧
      ∀ φ : TimelessFieldCompletion → ℂ, IsTracialState φ →
        φ (a * b) = φ (b * a) := by
  obtain ⟨a, b, hab⟩ := substrate_not_commutative
  exact ⟨a, b, hab, fun _ h => h.tracial a b⟩

/-! ## §2 — No unbiased observer is injective -/

/-- **★ No tracial state on `T∞` is injective.**

    Not "none has been found" — there is none. Injectivity together with
    traciality would force `a * b = b * a` for the `r217` witnesses, which is
    false.

    Note this is compatible with `UHF_trace` being *faithful*: faithfulness
    answers "is this zero?", injectivity would answer "which element is this?".
    An unbiased reading can always do the first and provably never the
    second. -/
theorem no_tracial_state_is_injective
    (φ : TimelessFieldCompletion → ℂ) (h : IsTracialState φ) :
    ¬ Function.Injective φ := by
  intro hinj
  obtain ⟨a, b, hab⟩ := substrate_not_commutative
  exact hab (hinj (h.tracial a b))

/-! ## §3 — The sharpest form: a nonzero element read as zero -/

/-- **★ There is a nonzero element of the substrate that every unbiased
    observer reads as zero.**

    It is the commutator `a * b - b * a`: nonzero because `a * b ≠ b * a`
    (r217), and annihilated by every tracial state
    (`tracial_commutator_vanishes`).

    This locates the loss precisely. What an unbiased reading cannot see is the
    commutator subspace — which is exactly the structure that makes `T∞`
    non-commutative, and which r217 shows is not removable
    (`GelfandSpectrum = ∅`). -/
theorem commutator_nonzero_in_kernel_of_every_unbiased_observer :
    ∃ c : TimelessFieldCompletion,
      c ≠ 0 ∧
      ∀ φ : TimelessFieldCompletion → ℂ, IsTracialState φ → φ c = 0 := by
  obtain ⟨a, b, hab⟩ := substrate_not_commutative
  refine ⟨a * b - b * a, sub_ne_zero.mpr hab, ?_⟩
  intro φ h
  exact tracial_commutator_vanishes h a b

/-! ## §4 — One citable bundle -/

/-- **`unbiased_observer_loses_information_bundle`** — the three facts together.

    There are distinct elements every unbiased observer identifies; no tracial
    state is injective; and a nonzero element of `T∞` is read as zero by all of
    them.

    Composed entirely from `substrate_not_commutative` (r217) and
    `tracial_commutator_vanishes`. No new mathematics, and no physical
    interpretation — see this file's header. -/
theorem unbiased_observer_loses_information_bundle :
    (∃ a b : TimelessFieldCompletion, a * b ≠ b * a ∧
       ∀ φ : TimelessFieldCompletion → ℂ, IsTracialState φ →
         φ (a * b) = φ (b * a)) ∧
    (∀ φ : TimelessFieldCompletion → ℂ, IsTracialState φ →
       ¬ Function.Injective φ) ∧
    (∃ c : TimelessFieldCompletion, c ≠ 0 ∧
       ∀ φ : TimelessFieldCompletion → ℂ, IsTracialState φ → φ c = 0) :=
  ⟨unbiased_identifies_distinct_elements,
   no_tracial_state_is_injective,
   commutator_nonzero_in_kernel_of_every_unbiased_observer⟩

end PF.Substrate.UnbiasedObserverLoses

/-! ## §Axiom audit -/
#print axioms PF.Substrate.UnbiasedObserverLoses.unbiased_identifies_distinct_elements
#print axioms PF.Substrate.UnbiasedObserverLoses.no_tracial_state_is_injective
#print axioms PF.Substrate.UnbiasedObserverLoses.commutator_nonzero_in_kernel_of_every_unbiased_observer
#print axioms PF.Substrate.UnbiasedObserverLoses.unbiased_observer_loses_information_bundle
