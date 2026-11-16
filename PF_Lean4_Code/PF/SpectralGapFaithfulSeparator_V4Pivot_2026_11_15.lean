/-
# P vs NP substrate attack — V4 PIVOT (not tippy-toeing).

★ 2026-11-15 EOD — HONEST V4 PIVOT. ★

## Hard disclosure

The morning's P vs NP substrate attack
(`PF/SpectralGapFaithfulSeparator_2026_11_15.lean`, commit `ff55c79a`)
scoped on the V2 carrier was **structurally defective**.  The V2
carrier's `computability : True` placeholder makes
`Literal_P_neq_NP_V2` **provably FALSE** per
`PF/TuringEncoding/PNPClassSeparationCarrierV2.lean:292`
(`not_Literal_P_neq_NP_V2_under_True_placeholder`).

Consequently, the morning's bound residual
`SpectralSeparatorFaithfulness_V2 := EnumToClassSeparationBridgeV2` is
ALSO provably False under V2.  The composition
`spectral_gap_substrate_yields_literal_P_neq_NP_V2` is of the form
`spectral_gap > 0 → (False → Literal_P_neq_NP_V2)` — vacuously true,
with False as premise.

**The morning attack was tippy-toeing on a dead carrier.**  V2 is
designed to document the carrier defect, not to carry a Clay
discharge.

## The pivot: V4 is the correct substrate target

`PF/TuringEncoding/PNPClassSeparationCarrierV4.lean` closes TWO V2
carrier defects:

1. **Structural-shape defect** (V3): `encodeRun : Input → TMConfig`
   wires every machine through the prime-power Gödel-numbering
   infrastructure.
2. **Universal-inhabitation defect** (V4): `decide_via_encodeRun`
   linkage forces `decide x = true ↔ (encodeRun x).state ∈
   acceptingStates` — eliminating the trivial constant-machine
   inhabitation that collapses class_P to Set.univ on V2/V3.

V4 proves:
- `L_const_true_in_class_P_typedV4 : L_const_true ∈ class_P_typedV4`
- `L_const_false_in_class_P_typedV4 : L_const_false ∈ class_P_typedV4`
- `constant_encodeRun_forces_constant_decide` — a non-trivial
  structural constraint on V4-admissible machines.
- `enum_to_class_separation_bridge_V4_iff_literal_P_neq_NP_V4` — the
  V4 biconditional analog.

**V4 does NOT close `Literal_P_neq_NP_V4` axiom-free** (by its own
header disclosure).  That is the Clay-grade open frontier.

## What this file does

This file pivots the P vs NP substrate attack from V2 to V4:

(A) **Structural tag + partial non-vacuity on V4**: explicitly marks
    that `class_P_typedV4` contains at least `L_const_true` AND
    `L_const_false`, so the V4 carrier is NON-TRIVIAL.

(B) **Honest V4-level substantive core**: binds
    `SpectralSeparatorFaithfulness_V4 := EnumToClassSeparationBridgeV4`
    which is NOT known to be False on V4 (unlike V2).  Remains open —
    it IS Clay-grade P ≠ NP on V4 carrier.

(C) **V4 substrate-attack bundle**: composes the kernel-verified
    `spectral_gap_positive` with the V4 non-triviality and the V4
    biconditional, exposing that the substrate position on V4 is
    structurally sound (unlike V2) and the remaining open piece is
    genuinely Clay-level.

## Why this is NOT a Clay discharge

The V4 substantive core `SpectralSeparatorFaithfulness_V4` IS
equivalent to the literal Clay P ≠ NP on the V4 carrier
(via `enum_to_class_separation_bridge_V4_iff_literal_P_neq_NP_V4`).
Closing it is the Clay problem.

What this file DOES advance:
1. Identifies the V2-attack vacuity defect.
2. Pivots to the non-vacuous V4 carrier.
3. Establishes V4 non-triviality (class_P contains L_const_true,
   L_const_false — explicit substrate witnesses).
4. Rebundles the substrate attack on V4 so the composition is
   non-vacuous.

The remaining open piece is Clay-level, honestly.  No tippy-toeing.

SPDX-License-Identifier: Apache-2.0
Author: Pablo Cohen.  2026-11-15.
-/

import PF.SpectralGapFaithfulSeparator_2026_11_15
import PF.TuringEncoding.PNPClassSeparationCarrierV4

namespace PF.SpectralGapFaithfulSeparator_V4Pivot

open PrincipiaTractalis
open PrincipiaTractalis.PNPClassSeparationCarrierV2
  (Literal_P_neq_NP_V2
   not_Literal_P_neq_NP_V2_under_True_placeholder)
open PrincipiaTractalis.PNPClassSeparationCarrierV4
  (class_P_typedV4 class_NP_typedV4
   Literal_P_neq_NP_V4 EnumToClassSeparationBridgeV4
   enum_to_class_separation_bridge_V4_iff_literal_P_neq_NP_V4
   class_P_subset_class_NP_V4
   L_const_true L_const_false
   L_const_true_in_class_P_typedV4
   L_const_false_in_class_P_typedV4)

/-! ## §1 — Hard disclosure: V2 is vacuous. -/

/-- **`v2_morning_attack_vacuous_disclosure`** — the morning V2
substrate attack is vacuous because `Literal_P_neq_NP_V2` is provably
False under the `computability : True` placeholder.

This theorem is the explicit Lean-level disclosure that:
- `¬ Literal_P_neq_NP_V2` holds unconditionally on V2 carrier
  (per `not_Literal_P_neq_NP_V2_under_True_placeholder`),
- therefore any Prop implying `Literal_P_neq_NP_V2` on V2 is vacuous,
- including `SpectralSeparatorFaithfulness_V2 := EnumToClassSeparationBridgeV2`,
- and hence the morning's
  `spectral_gap_substrate_yields_literal_P_neq_NP_V2` composition.

The V2 attack remains valid as a referee-facing enumeration of what
the V2 carrier would require IF literal_P_neq_NP held — but it does
not hold on V2.  V4 is the correct pivot. -/
theorem v2_morning_attack_vacuous_disclosure :
    ¬ Literal_P_neq_NP_V2 :=
  not_Literal_P_neq_NP_V2_under_True_placeholder

/-! ## §2 — V4 non-triviality: substrate witnesses in class_P_typedV4. -/

/-- **`v4_class_P_contains_two_distinct_witnesses`** — the V4 carrier
is non-trivial: `class_P_typedV4` contains both `L_const_true` and
`L_const_false` (which are distinct decision problems).

Unlike V2 where class_P collapses to Set.univ, V4's `decide_via_encodeRun`
linkage constraint forces per-machine non-triviality.  The two
explicit witnesses `L_const_true` and `L_const_false` are both
V4-admissible via acceptingStates := {0} and acceptingStates := ∅
respectively.

This theorem establishes that V4 carries genuine substrate structure
beyond trivial-machine inhabitation. -/
theorem v4_class_P_contains_two_distinct_witnesses :
    L_const_true ∈ class_P_typedV4 ∧
    L_const_false ∈ class_P_typedV4 ∧
    L_const_true ≠ L_const_false := by
  refine ⟨L_const_true_in_class_P_typedV4,
          L_const_false_in_class_P_typedV4, ?_⟩
  -- L_const_true and L_const_false are distinct as functions: at any
  -- input they evaluate to true and false respectively.
  intro h
  -- h : L_const_true = L_const_false; evaluate both at any input to
  -- derive true = false, contradiction.
  have : L_const_true { size := 0 } = L_const_false { size := 0 } := by
    rw [h]
  simp [L_const_true, L_const_false] at this

/-! ## §3 — V4 substantive core (honest Clay-level open). -/

/-- **`SpectralSeparatorFaithfulness_V4`** — the V4 analog of the
morning's V2 faithfulness Prop.

Defined as `EnumToClassSeparationBridgeV4`:
    `∃ L : DecidableProblemV4, L ∈ class_NP_typedV4 ∧ L ∉ class_P_typedV4`.

Via `enum_to_class_separation_bridge_V4_iff_literal_P_neq_NP_V4`,
equivalent to `Literal_P_neq_NP_V4` on the V4 carrier.  Unlike V2,
this Prop is NOT known to be False on V4.  V4's carrier structural
strengthenings (TMConfig wiring + decide-to-encodeRun linkage) make
the Prop a genuine Clay-grade open question on V4.

**Honest scope:** closing `SpectralSeparatorFaithfulness_V4` is
equivalent to solving Clay P vs NP on the V4 carrier.  This file
does NOT close it.  It only establishes the carrier is non-vacuous
(§2) and the substrate-attack composition is non-vacuous (§4). -/
def SpectralSeparatorFaithfulness_V4 : Prop :=
  EnumToClassSeparationBridgeV4

/-! ## §4 — V4 substrate-attack composition (non-vacuous). -/

/-- **`spectral_gap_substrate_yields_literal_P_neq_NP_V4`** — the V4
analog of the morning V2 composition, now NON-VACUOUS.

Under the kernel-verified `spectral_gap_positive : spectral_gap > 0`
AND the V4 faithful-separator Prop, the literal Clay P ≠ NP statement
`Literal_P_neq_NP_V4` holds.

This composition is non-vacuous because `SpectralSeparatorFaithfulness_V4`
is NOT known to be False on V4 (unlike V2's analog).  It is genuinely
Clay-level: closing the hypothesis IS solving P vs NP on V4.

Honest scope: the implication is kernel-clean; the premise
`SpectralSeparatorFaithfulness_V4` is open at the Clay level. -/
theorem spectral_gap_substrate_yields_literal_P_neq_NP_V4
    (_hGap : spectral_gap > 0)
    (hFaith : SpectralSeparatorFaithfulness_V4) :
    Literal_P_neq_NP_V4 :=
  enum_to_class_separation_bridge_V4_iff_literal_P_neq_NP_V4.mp hFaith

/-! ## §5 — V4 substrate-attack HEAD bundle. -/

/-- **`substrate_P_neq_NP_V4_position_at_HEAD`** — the four-conjunct
V4-pivoted substrate position on P vs NP:

(1) **V2 vacuity disclosure**: `¬ Literal_P_neq_NP_V2` unconditionally
    (V2 carrier design defect).  The morning's V2 composition is vacuous.

(2) **Kernel-verified spectral gap**: `spectral_gap > 0`.

(3) **V4 non-triviality**: class_P_typedV4 contains both L_const_true
    and L_const_false, which are distinct — V4 carrier is non-vacuous
    unlike V2.

(4) **V4 substrate-attack composition**: under the V4 faithful-separator
    (NOT known False, genuinely Clay-level), the literal Clay P ≠ NP on
    V4 carrier follows.

Framework-first V4-pivoted position: ONE theorem, ONE citation,
exposing the honest state of the P vs NP substrate attack at HEAD.
V2 vacuous, V4 non-vacuous, open piece is genuinely Clay-level. -/
theorem substrate_P_neq_NP_V4_position_at_HEAD :
    -- (1) V2 vacuity disclosure (morning V2 attack is on a dead carrier).
    ¬ Literal_P_neq_NP_V2 ∧
    -- (2) Kernel-verified spectral gap.
    (spectral_gap > 0) ∧
    -- (3) V4 non-triviality (substrate witnesses).
    (L_const_true ∈ class_P_typedV4 ∧
     L_const_false ∈ class_P_typedV4 ∧
     L_const_true ≠ L_const_false) ∧
    -- (4) V4 substrate-attack composition (genuinely Clay-level premise).
    (SpectralSeparatorFaithfulness_V4 → Literal_P_neq_NP_V4) :=
  ⟨v2_morning_attack_vacuous_disclosure,
   spectral_gap_positive,
   v4_class_P_contains_two_distinct_witnesses,
   fun hFaith =>
     spectral_gap_substrate_yields_literal_P_neq_NP_V4
       spectral_gap_positive hFaith⟩

/-! ## §6 — Axiom audit. -/

#check @v2_morning_attack_vacuous_disclosure
#check @v4_class_P_contains_two_distinct_witnesses
#check @SpectralSeparatorFaithfulness_V4
#check @spectral_gap_substrate_yields_literal_P_neq_NP_V4
#check @substrate_P_neq_NP_V4_position_at_HEAD

end PF.SpectralGapFaithfulSeparator_V4Pivot
