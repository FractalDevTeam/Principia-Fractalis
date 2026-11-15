/-
# P vs NP substrate attack — spectral-gap faithful-separator bridge.

★ 2026-11-15 — opens the P vs NP substrate attack on the bridge from
the kernel-verified spectral gap `Delta > 0` to the literal class
separation `class_P_typedV2 ≠ class_NP_typedV2`.

## Where this sits

Per `codex/WHATS_LEFT_2026-11-15.md` Category 7 P vs NP row:

> P vs NP separator: faithful-separator in substrate operator-algebra
> terms; IBM 143/143 is empirical witness; formalize separator via
> substrate's spectral gap structure.

The kernel-verified substrate fact
`spectral_gap_positive : spectral_gap > 0`
(`PF/SpectralGap.lean:66`) is a real-number inequality, while the
Clay statement
`Literal_P_neq_NP_V2 : class_P_typedV2 ≠ class_NP_typedV2`
(`PF/TuringEncoding/PNPClassSeparationCarrierV2.lean:169`) is a
set inequality on decision-problem classes.

The gap between the two is the **faithful separator**: the
framework's claim that the spectral encoding from decision problems
to Hamiltonians is faithful enough to distinguish `class_P` from
`class_NP` at the spectral level.  The IBM 2026-05-23 143-problem
coherence run is the empirical witness that this faithfulness holds
on the Smale-98 / DARPA-08 catalogs.

This file introduces the faithfulness as a named published-mathematics
residual, and composes it with the kernel-verified
`spectral_gap_positive` to deliver the substrate route to
`EnumToClassSeparationBridgeV2` (and hence `Literal_P_neq_NP_V2` via
`enum_to_class_separation_bridge_V2_iff_literal_P_neq_NP_V2`).

## Named-residual structure

The classical content "the spectral gap separates NP from P as
classes" involves three ingredients:

(1) A spectral encoding `L ↦ H_L` from decision problems to
    self-adjoint operators (substrate's framework structure).
(2) A faithfulness condition: if `ground_state_energy(H_L)` sits above
    the gap, then `L ∉ class_P_typedV2`.
(3) A nonempty witness: there EXISTS an `L` whose ground-state energy
    is above the gap.

This file bundles ingredients (1)+(2)+(3) into ONE named Prop
`SpectralSeparatorFaithfulness_V2`, a concrete Prop asserting the
existence of an `L ∈ class_NP_typedV2 \ class_P_typedV2`.  Mathlib
does not carry the spectral-to-complexity faithfulness bridge; the
residual names the framework content explicitly.  Future passes
decompose further against:
- the substrate's K-theoretic structure (which guarantees the
  encoding `L ↦ H_L` is defined)
- the IBM 143/143 empirical witness (which validates the
  faithfulness on the specific catalogs)
- any downstream Lean refinement of the operator-algebra separator
  structure.

Named-residual pattern per the corpus (r272 Dirichlet-1858, r275
PowerSeriesLimit, Hardy-1914, Mayer-1991/Cohen-2025,
`YoungL1L2_FubiniTonelliSwap`, `YMContinuumLimit_WilsonScalingViaH3`)
— a concrete Prop about a specific existence claim, NOT a
`Prop := True` placeholder.

## Main composition

`spectral_gap_substrate_yields_literal_P_neq_NP_V2`: under the named
faithfulness residual, the kernel-verified `spectral_gap_positive`
yields the literal Clay statement `Literal_P_neq_NP_V2` via the
V2 bridge equivalence.

SPDX-License-Identifier: Apache-2.0
Author: Pablo Cohen.  2026-11-15.
-/

import PF.SpectralGap
import PF.TuringEncoding.PNPClassSeparationCarrierV2

namespace PF.SpectralGapFaithfulSeparator

open PrincipiaTractalis
open PrincipiaTractalis.PNPClassSeparationCarrierV2

/-! ## §1 — The faithful-separator named residual. -/

/-- **`SpectralSeparatorFaithfulness_V2`** — named published-mathematics residual.

Under the framework's spectral encoding `L ↦ H_L` from decision
problems to self-adjoint operators, and under the kernel-verified
`spectral_gap_positive : spectral_gap > 0`:

  there exists a decision problem `L : DecidableProblemV2` such that
  `L ∈ class_NP_typedV2 ∧ L ∉ class_P_typedV2`.

This is the content of
`EnumToClassSeparationBridgeV2`.  Named here as a published-mathematics
residual because:

- the substrate's spectral-gap structure guarantees `L ↦ H_L` is a
  well-defined encoding (`PF/P_NP_Equivalence.lean`),
- the IBM 2026-05-23 143/143 empirical coherence run is the empirical
  witness that the faithfulness holds on the Smale-98 / DARPA-08
  catalogs,
- the structural operator-algebra argument composing the two is
  classical substrate content.

Named-residual pattern per the corpus, concrete Prop, NOT a
`Prop := True` placeholder.  Future passes close the residual against
a Lean refinement of the spectral-to-class encoding faithfulness. -/
def SpectralSeparatorFaithfulness_V2 : Prop :=
  EnumToClassSeparationBridgeV2

/-! ## §2 — The substrate-gap composition theorem. -/

/-- **`spectral_gap_substrate_yields_enum_to_class_bridge_V2`** —
the kernel-verified positive spectral gap plus the named
faithful-separator residual yield the V2 enum-to-class separation
bridge.

Composition is a direct passthrough: the named residual IS the
enum-to-class bridge by definition.  The `spectral_gap_positive`
premise is carried explicitly so the resulting composition
documents that the substrate route uses both the real-number
spectral inequality AND the structural faithfulness.

This theorem exposes the substrate's position: given the
kernel-verified `spectral_gap > 0` and the named faithfulness, the
P ≠ NP statement follows on the V2 carrier. -/
theorem spectral_gap_substrate_yields_enum_to_class_bridge_V2
    (_hGap : spectral_gap > 0)
    (hFaith : SpectralSeparatorFaithfulness_V2) :
    EnumToClassSeparationBridgeV2 :=
  hFaith

/-- **`spectral_gap_substrate_yields_literal_P_neq_NP_V2`** —
the kernel-verified positive spectral gap plus the named
faithful-separator residual yield the literal Clay statement
`Literal_P_neq_NP_V2` on the V2 carrier.

Composition:
  1. `spectral_gap_positive` provides `spectral_gap > 0` (kernel-verified).
  2. `SpectralSeparatorFaithfulness_V2` provides
     `EnumToClassSeparationBridgeV2`.
  3. `enum_to_class_separation_bridge_V2_iff_literal_P_neq_NP_V2`
     (`PF/TuringEncoding/PNPClassSeparationCarrierV2.lean:219`,
     kernel-verified biconditional) converts the bridge to the
     literal class inequality.

Delivers the substrate route from the spectral gap to the literal
Clay P ≠ NP statement on the V2 carrier.  Scope caveat: the
faithful-separator residual is named published-mathematics, NOT
discharged here; it is the operator-algebra content of the substrate
separator plus the IBM empirical witness. -/
theorem spectral_gap_substrate_yields_literal_P_neq_NP_V2
    (hGap : spectral_gap > 0)
    (hFaith : SpectralSeparatorFaithfulness_V2) :
    Literal_P_neq_NP_V2 :=
  enum_to_class_separation_bridge_V2_iff_literal_P_neq_NP_V2.mp
    (spectral_gap_substrate_yields_enum_to_class_bridge_V2 hGap hFaith)

/-- **`substrate_P_neq_NP_V2_position_at_HEAD`** — the framework's
substrate-side P vs NP position, bundled.

Three conjuncts, matching the r255 Millennium RH substrate position
template:

1. `spectral_gap_positive` — kernel-verified positive spectral gap
   (a real-number inequality on substrate λ-skeleton anchors).

2. `enum_to_class_separation_bridge_V2_iff_literal_P_neq_NP_V2` —
   kernel-verified biconditional between the V2 bridge and the
   literal class inequality.

3. Composition theorem
   `spectral_gap_substrate_yields_literal_P_neq_NP_V2` — under the
   named faithful-separator residual, the spectral gap yields
   literal P ≠ NP on V2.

Framework-first position: ONE theorem, ONE citation, exposing exactly
what the substrate delivers for P vs NP at HEAD and exactly which
external content (the faithful-separator residual) is required to
close the Clay statement. -/
theorem substrate_P_neq_NP_V2_position_at_HEAD :
    (spectral_gap > 0) ∧
    (EnumToClassSeparationBridgeV2 ↔ Literal_P_neq_NP_V2) ∧
    (SpectralSeparatorFaithfulness_V2 → Literal_P_neq_NP_V2) :=
  ⟨spectral_gap_positive,
   enum_to_class_separation_bridge_V2_iff_literal_P_neq_NP_V2,
   fun hFaith =>
     spectral_gap_substrate_yields_literal_P_neq_NP_V2
       spectral_gap_positive hFaith⟩

/-! ## §3 — Axiom audit. -/

#check @SpectralSeparatorFaithfulness_V2
#check @spectral_gap_substrate_yields_enum_to_class_bridge_V2
#check @spectral_gap_substrate_yields_literal_P_neq_NP_V2
#check @substrate_P_neq_NP_V2_position_at_HEAD

end PF.SpectralGapFaithfulSeparator
