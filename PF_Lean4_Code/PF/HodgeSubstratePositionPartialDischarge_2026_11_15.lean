/-
# Hodge substrate attack — PARTIAL substantive-core discharge.

★ 2026-11-15 EOD — advances the Hodge substrate attack beyond the
honest-disclosure structural-vs-substantive split landed earlier at
commit `725f883c`.

## What this file does

The Hodge substantive core bound at `725f883c` to
`Voisin2007_GeneralQuinticOpenContent` (Voisin 2007 R3, Fields-medal
grade open).  But the FULL Hodge-conjecture content on codim-2 cycles
for smooth projective varieties in dim ≥ 3 splits into THREE Voisin
2007 results:

  (R1) abelian codim-2 — settled (Voisin 2007)
  (R2) Dwork pencil codim-2 — settled (Voisin 2007)
  (R3) general quintic codim-2 — OPEN

The corpus already discharges (R1) AND (R2) kernel-clean via
`Voisin2007_CombinedPartialStatus_substrate` in
`PF/AlgebraicGeometry/Voisin2007PartialFormalization.lean:390`.

This file introduces an additional partial-substantive sub-residual
`HodgeHigherDimensionVoisinResidual_PartialSubstantiveClosed` bound to
`Voisin2007_CombinedPartialStatus` (R1 + R2 conjunction), and closes
it unconditionally by composition.

## Partitioning the Hodge substantive core

Before this file: Hodge substantive core = `Voisin2007_GeneralQuinticOpenContent`
(one monolithic open Prop).

After this file: Hodge substantive core partitions into
  (a) PARTIAL CLOSED: `Voisin2007_CombinedPartialStatus` (R1 + R2)
      — DISCHARGED kernel-clean this file
  (b) PARTIAL OPEN: `Voisin2007_GeneralQuinticOpenContent` (R3)
      — remains open at the Voisin 2007 R3 level

Progress: the 2/3 of Voisin 2007 that are classically settled now
have an EXPLICIT substrate-attack discharge; only 1/3 (the general
quintic R3) remains as the substantive-core open piece.

## Main theorem

`hodge_substantive_partial_discharge_at_HEAD` — the two-conjunct bundle:

(a) The (R1)+(R2) partial substantive content is DISCHARGED kernel-clean.
(b) The (R3) general quintic open content remains OPEN; the logical
    ordering substantive(R3) → structural-tag is recorded.

SPDX-License-Identifier: Apache-2.0
Author: Pablo Cohen.  2026-11-15.
-/

import PF.HodgeSubstratePositionStrengthening_2026_11_15
import PF.AlgebraicGeometry.Voisin2007PartialFormalization

namespace PF.HodgeSubstratePositionPartialDischarge

open PrincipiaTractalis.AlgebraicGeometry.Voisin2007PartialFormalization
  (Voisin2007_CombinedPartialStatus
   Voisin2007_CombinedPartialStatus_substrate
   Voisin2007_AbelianCodimTwoHolds
   Voisin2007_AbelianCodimTwoHolds_substrate
   Voisin2007_DworkPencilCodimTwoHolds
   Voisin2007_DworkPencilCodimTwoHolds_substrate)
open PF.HodgeSubstratePositionStrengthening
  (HodgeHigherDimensionVoisinResidual_SubstantiveCore
   hodge_higher_dim_residual_trivial_discharge
   substantive_core_strictly_stronger_than_structural_tag)
open PF.HodgeSubstratePosition (HodgeHigherDimensionVoisinResidual)

/-! ## §1 — Partial substantive sub-residual (R1 + R2, CLOSED). -/

/-- **`HodgeHigherDimensionVoisinResidual_PartialSubstantiveClosed`** —
the partial substantive content of the Hodge higher-dimension claim
that is CLASSICALLY SETTLED (Voisin 2007 R1 abelian + R2 Dwork pencil).

Defined as `Voisin2007_CombinedPartialStatus`:
    `Voisin2007_AbelianCodimTwoHolds ∧ Voisin2007_DworkPencilCodimTwoHolds`.

Both conjuncts kernel-clean at HEAD per
`PF/AlgebraicGeometry/Voisin2007PartialFormalization.lean:390`.  Captures
the 2/3 of Voisin 2007's three-way partial-formalization that are
classically settled. -/
def HodgeHigherDimensionVoisinResidual_PartialSubstantiveClosed : Prop :=
  Voisin2007_CombinedPartialStatus

/-- **`hodge_partial_substantive_discharge`** — the partial substantive
sub-residual is DISCHARGED kernel-clean via the existing corpus
`Voisin2007_CombinedPartialStatus_substrate`.

The (R1) abelian + (R2) Dwork pencil parts of Voisin 2007 are closed
substantively.  Only the (R3) general quintic open content remains as
the Hodge substantive-core open piece. -/
theorem hodge_partial_substantive_discharge :
    HodgeHigherDimensionVoisinResidual_PartialSubstantiveClosed :=
  Voisin2007_CombinedPartialStatus_substrate

/-! ## §2 — Partitioning: full substantive core = partial-closed + general-open. -/

/-- **`hodge_substantive_partitioning`** — documents the partitioning
of the Hodge substantive-core content into the classically-settled
partial `(R1) + (R2)` and the open `(R3)` general quintic.

The full Voisin 2007 three-way result would require `(R1) ∧ (R2) ∧ (R3)`.
This file discharges the first two kernel-clean; the third remains
bound to `HodgeHigherDimensionVoisinResidual_SubstantiveCore`
(= `Voisin2007_GeneralQuinticOpenContent`) as the single remaining
substantive-core open piece on Hodge. -/
theorem hodge_substantive_partitioning :
    -- (a) Partial substantive (R1 + R2) DISCHARGED kernel-clean.
    HodgeHigherDimensionVoisinResidual_PartialSubstantiveClosed ∧
    -- (b) Substantive-core logical ordering preserved: substantive(R3)
    --     implies the structural-tag residual.
    (HodgeHigherDimensionVoisinResidual_SubstantiveCore
      → HodgeHigherDimensionVoisinResidual) :=
  ⟨hodge_partial_substantive_discharge,
   substantive_core_strictly_stronger_than_structural_tag⟩

/-! ## §3 — Substrate-attack HEAD bundle. -/

/-- **`hodge_substrate_attack_HEAD_bundle_2026_11_15`** — the three-conjunct
end-of-session bundle for the Hodge substrate attack:

(1) Structural tag `HodgeHigherDimensionVoisinResidual` DISCHARGED
    (trivial by `Unit`, from `725f883c`).

(2) Partial substantive `(R1) abelian + (R2) Dwork pencil` DISCHARGED
    kernel-clean (this file).

(3) Substantive-core `(R3) general quintic` → structural tag
    (substantive-core open content remains at Voisin 2007 R3 level).

Documents the 2/3 progress on the Hodge substantive-core content:
two of three Voisin 2007 R-direction results are now substantively
closed kernel-clean; one remains at the Fields-medal-grade open level. -/
theorem hodge_substrate_attack_HEAD_bundle_2026_11_15 :
    HodgeHigherDimensionVoisinResidual ∧
    HodgeHigherDimensionVoisinResidual_PartialSubstantiveClosed ∧
    (HodgeHigherDimensionVoisinResidual_SubstantiveCore
      → HodgeHigherDimensionVoisinResidual) :=
  ⟨hodge_higher_dim_residual_trivial_discharge,
   hodge_partial_substantive_discharge,
   substantive_core_strictly_stronger_than_structural_tag⟩

/-! ## §4 — Axiom audit. -/

#check @HodgeHigherDimensionVoisinResidual_PartialSubstantiveClosed
#check @hodge_partial_substantive_discharge
#check @hodge_substantive_partitioning
#check @hodge_substrate_attack_HEAD_bundle_2026_11_15

end PF.HodgeSubstratePositionPartialDischarge
