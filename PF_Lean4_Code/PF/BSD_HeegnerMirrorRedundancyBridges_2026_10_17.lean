/-
# BSD — Heegner Mirror Redundancy Bridges (step 1 of 4 of Rio's BSD plan)

**Rio's BSD scoping, 2026-10-17** (codex `0ef9bd36`): eight
`BSD_HeegnerRank1ProofE{N}a1.lean` mirrors assert
`∃ cert : RankCertificateTyped E_rank_one, cert.r = 1` — a record-field
equality on a Prop-level cert whose two hypotheses `HeegnerHypothesisSatisfied`
and `LDerivativeAtOneNonZero` are definitionally `True`. For each of the
same eight curves, the tree already contains a **genuine `Module.rank`
theorem**, elsewhere, proved from a non-torsion point certificate:

| curve N | mirror file                           | genuine theorem                             |
|---------|---------------------------------------|---------------------------------------------|
| 43      | `BSD_HeegnerRank1ProofE43a1.lean`     | `E43a1_rank_ge_one`  in `E43a1RankOne_r135` |
| 53      | `BSD_HeegnerRank1ProofE53a1.lean`     | `E53a1_rank_ge_one`  in `E53a1RankOne_r136` |
| 61      | `BSD_HeegnerRank1ProofE61a1.lean`     | `E61a1_rank_ge_one`  in `E61a1RankOne_r137` |
| 79      | `BSD_HeegnerRank1ProofE79a1.lean`     | `E79a1_rank_ge_one`  in `E79a1RankOne_r138` |
| 83      | `BSD_HeegnerRank1ProofE83a1.lean`     | `E83a1_rank_ge_one`  in `E83a1RankOne_r139` |
| 89      | `BSD_HeegnerRank1ProofE89a1.lean`     | `E89a1_rank_ge_one`  in `E89a1RankOne_r140` |
| 101     | `BSD_HeegnerRank1ProofE101a1.lean`    | `E101a1_rank_ge_one` in `E101a1RankOne_r141` |
| 106     | `BSD_HeegnerRank1ProofE106a1.lean`    | `E106a1_rank_ge_one` in `E106a1RankOne_r142` |

**This file provides eight one-line bridge theorems** that make the
redundancy explicit: for each curve, it re-exposes the genuine
`Module.rank` theorem under a name that discloses "the Prop-level mirror
is subsumed by this." No deletion of the mirrors — they are imported by
`BSD_HeegnerThirteenCurvesBundle.lean`, `BSDCapstoneTypedBridgeV3.lean`,
and `MordellWeilRankAgreement17.lean`, and the self-vacuity theorems
inside them (e.g. `heegner_pair_both_iff_True`, `bsd_rank_one_E43a1_
discharged_at_placeholder`) are correct scope-labelling, not scaffolding
to repair.

### Why this is step 1 of the plan

Rio's BSD build order:

1. **Tidy** — redundancy bridges (this commit).
2. Mechanical — genuine `rank ≥ 1` for the four gap curves E91a1, E102a1,
   E131a1, E141a1 (all deps exist in `RankPipelineUniversal_r202`).
3. The real project — 2-descent **upper bound** on a newly chosen
   small-conductor curve with rational 2-torsion. This is the first new
   mathematics on the axis, is L-function-free, and is the only route
   to "rank exactly".
4. Combine lower + upper ⇒ first "rank exactly n" theorem in the repo.

The Heegner / Kolyvagin / Gross–Zagier blockers remain blocked at the
pin (`L(E,s)`, Heegner points, Kolyvagin, Gross–Zagier are all **absent
from mathlib** per the pinned-tree audit in `codex/BSD_SCOPING_UPPER_
BOUND_IS_THE_GAP_2026-10-17.md`). The eight Prop-mirror files remain
untouched; this file sits beside them and visibly subsumes them.

Three-axiom bar: every bridge theorem kernel-clean
`[propext, Classical.choice, Quot.sound]`. No sorry.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-17.
-/
import PF.E43a1RankOne_r135
import PF.E53a1RankOne_r136
import PF.E61a1RankOne_r137
import PF.E79a1RankOne_r138
import PF.E83a1RankOne_r139
import PF.E89a1RankOne_r140
import PF.E101a1RankOne_r141
import PF.E106a1RankOne_r142

namespace PF.BSDHeegnerMirrorRedundancyBridges

open PrincipiaTractalis.E43a1RankOne  PrincipiaTractalis.E53a1RankOne
open PrincipiaTractalis.E61a1RankOne  PrincipiaTractalis.E79a1RankOne
open PrincipiaTractalis.E83a1RankOne  PrincipiaTractalis.E89a1RankOne
open PrincipiaTractalis.E101a1RankOne PrincipiaTractalis.E106a1RankOne

/-! ## §1 — Eight redundancy-bridge theorems. -/

/-- **E43a1** — the Heegner-mirror Prop-level `cert.r = 1` is subsumed by
`E43a1_rank_ge_one` (genuine `Module.rank`, proved from a non-torsion
point via `RankPipelineUniversal_r202`). -/
theorem bsd_rank_one_E43a1_from_genuine_mordell_weil :
    1 ≤ Module.rank ℤ E43a1.toAffine.Point := E43a1_rank_ge_one

/-- **E53a1** redundancy bridge. -/
theorem bsd_rank_one_E53a1_from_genuine_mordell_weil :
    1 ≤ Module.rank ℤ E53a1.toAffine.Point := E53a1_rank_ge_one

/-- **E61a1** redundancy bridge. -/
theorem bsd_rank_one_E61a1_from_genuine_mordell_weil :
    1 ≤ Module.rank ℤ E61a1.toAffine.Point := E61a1_rank_ge_one

/-- **E79a1** redundancy bridge. -/
theorem bsd_rank_one_E79a1_from_genuine_mordell_weil :
    1 ≤ Module.rank ℤ E79a1.toAffine.Point := E79a1_rank_ge_one

/-- **E83a1** redundancy bridge. -/
theorem bsd_rank_one_E83a1_from_genuine_mordell_weil :
    1 ≤ Module.rank ℤ E83a1.toAffine.Point := E83a1_rank_ge_one

/-- **E89a1** redundancy bridge. -/
theorem bsd_rank_one_E89a1_from_genuine_mordell_weil :
    1 ≤ Module.rank ℤ E89a1.toAffine.Point := E89a1_rank_ge_one

/-- **E101a1** redundancy bridge. -/
theorem bsd_rank_one_E101a1_from_genuine_mordell_weil :
    1 ≤ Module.rank ℤ E101a1.toAffine.Point := E101a1_rank_ge_one

/-- **E106a1** redundancy bridge. -/
theorem bsd_rank_one_E106a1_from_genuine_mordell_weil :
    1 ≤ Module.rank ℤ E106a1.toAffine.Point := E106a1_rank_ge_one

end PF.BSDHeegnerMirrorRedundancyBridges

/-! ## §Axiom check -/
#print axioms PF.BSDHeegnerMirrorRedundancyBridges.bsd_rank_one_E43a1_from_genuine_mordell_weil
#print axioms PF.BSDHeegnerMirrorRedundancyBridges.bsd_rank_one_E53a1_from_genuine_mordell_weil
#print axioms PF.BSDHeegnerMirrorRedundancyBridges.bsd_rank_one_E61a1_from_genuine_mordell_weil
#print axioms PF.BSDHeegnerMirrorRedundancyBridges.bsd_rank_one_E79a1_from_genuine_mordell_weil
#print axioms PF.BSDHeegnerMirrorRedundancyBridges.bsd_rank_one_E83a1_from_genuine_mordell_weil
#print axioms PF.BSDHeegnerMirrorRedundancyBridges.bsd_rank_one_E89a1_from_genuine_mordell_weil
#print axioms PF.BSDHeegnerMirrorRedundancyBridges.bsd_rank_one_E101a1_from_genuine_mordell_weil
#print axioms PF.BSDHeegnerMirrorRedundancyBridges.bsd_rank_one_E106a1_from_genuine_mordell_weil
