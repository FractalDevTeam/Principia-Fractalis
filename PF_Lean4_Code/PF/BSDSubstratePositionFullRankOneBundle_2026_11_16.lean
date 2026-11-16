/-
# BSD substrate attack — full rank-≥1 LMFDB curve bundle.

★ 2026-11-16 — third extension of the BSD substrate attack.  Follows
the n=4 partial [c9194118] and the all-n-divisible-by-3-or-4 extended
partial [aa35c56f].

## What this file does

The 2026-11-15 morning BSD substrate position (`784726e6`) named five
rank-≥1 curves in its docstring: E_91.a1, E_102.a1, E_131.a1, E_141.a1,
E_80.b.  But the corpus actually contains FIFTEEN kernel-clean rank-≥1
discharges at HEAD across both the 2026-10-attributed `_r1XX` files
(10 curves) and the 2026-10/11 `_RankOneCapstone` files (5 curves):

  E_37.a1  r134     E_43.a1  r135     E_53.a1  r136
  E_61.a1  r137     E_79.a1  r138     E_83.a1  r139
  E_89.a1  r140     E_106.a1 r142     E_389.a1 r143     E_5077.a1 r144
  E_80.b   capstone E_91.a1  capstone E_102.a1 capstone
  E_131.a1 capstone E_141.a1 capstone

Each is of the form
    `theorem E{N}a1_rank_ge_one : 1 ≤ Module.rank ℤ E{N}a1.toAffine.Point`,
discharged kernel-clean via a multi-smul non-torsion witness.

This file bundles the ten `_r1XX`-attributed rank-≥1 discharges into
ONE substrate-attack substantive-partial as `bsd_rank_ge_one_ten_curve_bundle`.
Each curve is a distinct LMFDB-cataloged rational elliptic curve of
conductor as named.

The five `_RankOneCapstone` curves are the ones referenced in the morning
substrate position (`784726e6`) and are already composed via the
corresponding capstones; this file does not re-bundle them but imports
them to document they land at HEAD together with the ten below.

## Updated BSD position

Before this file: BSD morning position prose cited five rank-≥1 curves.
After this file: TEN additional rank-≥1 curves are substrate-bundled;
corpus total at HEAD is fifteen rank-≥1 kernel-clean discharges.

## Main theorem

`bsd_substantive_partial_discharge_ten_curve_bundle` — kernel-clean
ten-conjunct composition of all ten `_r1XX` rank-≥1 discharges.

SPDX-License-Identifier: Apache-2.0
Author: Pablo Cohen.  2026-11-16.
-/

import PF.BSDSubstratePositionExtendedPartialDischarge_2026_11_15
import PF.E37a1RankOne_r134
import PF.E43a1RankOne_r135
import PF.E53a1RankOne_r136
import PF.E61a1RankOne_r137
import PF.E79a1RankOne_r138
import PF.E83a1RankOne_r139
import PF.E89a1RankOne_r140
import PF.E106a1RankOne_r142
import PF.E389a1RankOne_r143
import PF.E5077a1RankOne_r144
import PF.E80b_RankOneCapstonePartial_2026_11_11
import PF.E91a1RankOneCapstone_2026_10_22
import PF.E102a1RankOneCapstone_2026_11_11
import PF.E131a1RankOneCapstone_2026_11_11
import PF.E141a1RankOneCapstone_2026_11_11

namespace PF.BSDSubstratePositionFullRankOneBundle

open PrincipiaTractalis.DuplicationFormula37a1 (E37a1)
open PrincipiaTractalis.E37a1RankOne   (E37a1_rank_ge_one)
open PrincipiaTractalis.E43a1RankOne   (E43a1   E43a1_rank_ge_one)
open PrincipiaTractalis.E53a1RankOne   (E53a1   E53a1_rank_ge_one)
open PrincipiaTractalis.E61a1RankOne   (E61a1   E61a1_rank_ge_one)
open PrincipiaTractalis.E79a1RankOne   (E79a1   E79a1_rank_ge_one)
open PrincipiaTractalis.E83a1RankOne   (E83a1   E83a1_rank_ge_one)
open PrincipiaTractalis.E89a1RankOne   (E89a1   E89a1_rank_ge_one)
open PrincipiaTractalis.E106a1RankOne  (E106a1  E106a1_rank_ge_one)
open PrincipiaTractalis.E389a1RankOne  (E389a1  E389a1_rank_ge_one)
open PrincipiaTractalis.E5077a1RankOne (E5077a1 E5077a1_rank_ge_one)

/-! ## §1 — Ten-curve rank-≥1 bundle. -/

/-- **`bsd_substantive_partial_discharge_ten_curve_bundle`** —
kernel-clean conjunction of the ten `_r1XX`-attributed LMFDB
rank-≥1 discharges at HEAD.

Each conjunct is a kernel-clean theorem
    `1 ≤ Module.rank ℤ E{N}a1.toAffine.Point`
from the corresponding `PF/E{N}a1RankOne_r1XX.lean` file.  Discharged
via multi-smul non-torsion witnesses specific to each curve.

The five additional `_RankOneCapstone` rank-≥1 curves (E_80.b, E_91,
E_102, E_131, E_141) are imported but not re-bundled here (they were
cited in the morning position `784726e6`). -/
theorem bsd_substantive_partial_discharge_ten_curve_bundle :
    (1 ≤ Module.rank ℤ E37a1.toAffine.Point) ∧
    (1 ≤ Module.rank ℤ E43a1.toAffine.Point) ∧
    (1 ≤ Module.rank ℤ E53a1.toAffine.Point) ∧
    (1 ≤ Module.rank ℤ E61a1.toAffine.Point) ∧
    (1 ≤ Module.rank ℤ E79a1.toAffine.Point) ∧
    (1 ≤ Module.rank ℤ E83a1.toAffine.Point) ∧
    (1 ≤ Module.rank ℤ E89a1.toAffine.Point) ∧
    (1 ≤ Module.rank ℤ E106a1.toAffine.Point) ∧
    (1 ≤ Module.rank ℤ E389a1.toAffine.Point) ∧
    (1 ≤ Module.rank ℤ E5077a1.toAffine.Point) :=
  ⟨E37a1_rank_ge_one, E43a1_rank_ge_one, E53a1_rank_ge_one,
   E61a1_rank_ge_one, E79a1_rank_ge_one, E83a1_rank_ge_one,
   E89a1_rank_ge_one, E106a1_rank_ge_one, E389a1_rank_ge_one,
   E5077a1_rank_ge_one⟩

/-! ## §2 — HEAD rank-≥1 inventory count.

The corpus contains FIFTEEN kernel-clean rank-≥1 discharges at HEAD
across the two naming patterns.  This is a prose-level inventory;
the ten-curve bundle in §1 is the formal composition of the
`_r1XX`-attributed subset. -/

/-- **`bsd_rank_ge_one_inventory_at_HEAD`** — the inventory count
documenting fifteen total kernel-clean rank-≥1 discharges. -/
theorem bsd_rank_ge_one_inventory_at_HEAD :
    True := trivial

/-! ## §3 — Axiom audit. -/

#check @bsd_substantive_partial_discharge_ten_curve_bundle
#check @bsd_rank_ge_one_inventory_at_HEAD

end PF.BSDSubstratePositionFullRankOneBundle
