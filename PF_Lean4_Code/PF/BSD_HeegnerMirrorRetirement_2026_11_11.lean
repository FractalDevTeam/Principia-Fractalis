/-
# PF.BSD_HeegnerMirrorRetirement_2026_11_11

**Rio audit (2026-10-17) step 1 — retirement bridges.**

Eight Heegner-mirror files

    PF/BSD_HeegnerRank1ProofE{43,53,61,79,83,89,101,106}a1.lean

each end in a headline theorem of the form

    `∃ cert : RankCertificateTyped E_{n}a1, cert.r = 1`

which is a typed structural existential (`RankWitnessTyped E 1 =
∃ g : Fin 1 → ℚ, g ≠ 0 pointwise` — essentially just "there exists a
nonzero rational"), NOT a genuine rank fact. Rio's step 1 notes that
each of these eight curves ALSO has a GENUINE theorem

    `E{n}a1_rank_ge_one : 1 ≤ Module.rank ℤ E{n}a1.toAffine.Point`

in the paired `PF/E{n}a1RankOne_r13{5,6,7,8,9,0,1,2}.lean` files, on
the three-axiom bar `[propext, Classical.choice, Quot.sound]`, no sorry.

**Why this file exists.** We cannot retire the mirrors by importing the
genuine theorems from the mirrors themselves — the mirror files are
transitively imported by `PF/Referee/BSDCapstoneTypedBridgeV3.lean`,
which is imported by `V4`, which imports `AlgebraicGeometry.MordellWeilGroup`,
which is imported by `MordellWeilRankLowerBound_r129`, which is imported
by each r13X genuine file. Adding `import PF.E{n}a1RankOne_r13X` to the
mirror would close a cycle.

**The fix.** This file is a LEAF — nothing in the repo imports it —
that imports both sides and provides retirement-pointer theorems
`E_{n}a1_rank_ge_one_from_r13X` stating the genuine theorem IN THE
MIRROR'S NAMESPACE. Downstream code wanting the real rank bound for
E_{n}a1 (the mirror's curve name) can cite the pointer here instead of
the typed-structural certificate.

The eight (mirror, genuine) pairs:

| mirror curve name  | mirror file                           | genuine file                       |
|--------------------|---------------------------------------|------------------------------------|
| `E_43a1`           | `BSD_HeegnerRank1ProofE43a1`          | `E43a1RankOne_r135`                |
| `E_53a1`           | `BSD_HeegnerRank1ProofE53a1`          | `E53a1RankOne_r136`                |
| `E_61a1`           | `BSD_HeegnerRank1ProofE61a1`          | `E61a1RankOne_r137`                |
| `E_79a1`           | `BSD_HeegnerRank1ProofE79a1`          | `E79a1RankOne_r138`                |
| `E_83a1`           | `BSD_HeegnerRank1ProofE83a1`          | `E83a1RankOne_r139`                |
| `E_89a1`           | `BSD_HeegnerRank1ProofE89a1`          | `E89a1RankOne_r140`                |
| `E_101a1`          | `BSD_HeegnerRank1ProofE101a1`         | `E101a1RankOne_r141`               |
| `E_106a1`          | `BSD_HeegnerRank1ProofE106a1`         | `E106a1RankOne_r142`               |

Each (mirror `E_{n}a1`, genuine `E{n}a1`) pair shares the same
Weierstrass tuple, verified by inspection. The pointer theorems below
use `exact` — the definitional equality is enough for Lean.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-11.
-/

import PF.BSD_HeegnerRank1ProofE43a1
import PF.BSD_HeegnerRank1ProofE53a1
import PF.BSD_HeegnerRank1ProofE61a1
import PF.BSD_HeegnerRank1ProofE79a1
import PF.BSD_HeegnerRank1ProofE83a1
import PF.BSD_HeegnerRank1ProofE89a1
import PF.BSD_HeegnerRank1ProofE101a1
import PF.BSD_HeegnerRank1ProofE106a1
import PF.E43a1RankOne_r135
import PF.E53a1RankOne_r136
import PF.E61a1RankOne_r137
import PF.E79a1RankOne_r138
import PF.E83a1RankOne_r139
import PF.E89a1RankOne_r140
import PF.E101a1RankOne_r141
import PF.E106a1RankOne_r142

namespace PrincipiaTractalis
namespace BSD_HeegnerMirrorRetirement20261111

open PrincipiaTractalis.BSD_HeegnerRank1ProofE43a1
     PrincipiaTractalis.BSD_HeegnerRank1ProofE53a1
     PrincipiaTractalis.BSD_HeegnerRank1ProofE61a1
     PrincipiaTractalis.BSD_HeegnerRank1ProofE79a1
     PrincipiaTractalis.BSD_HeegnerRank1ProofE83a1
     PrincipiaTractalis.BSD_HeegnerRank1ProofE89a1
     PrincipiaTractalis.BSD_HeegnerRank1ProofE101a1
     PrincipiaTractalis.BSD_HeegnerRank1ProofE106a1

/-- `E_43a1` (mirror, `⟨0,1,1,0,0⟩`) has `rank ≥ 1`, from `r135`'s
genuine theorem on the definitionally equal `E43a1`. -/
theorem E_43a1_rank_ge_one : 1 ≤ Module.rank ℤ E_43a1.toAffine.Point :=
  PrincipiaTractalis.E43a1RankOne.E43a1_rank_ge_one

/-- `E_53a1` (mirror, `⟨1,-1,1,0,0⟩`) has `rank ≥ 1`, from `r136`. -/
theorem E_53a1_rank_ge_one : 1 ≤ Module.rank ℤ E_53a1.toAffine.Point :=
  PrincipiaTractalis.E53a1RankOne.E53a1_rank_ge_one

/-- `E_61a1` (mirror, `⟨1,0,0,-2,1⟩`) has `rank ≥ 1`, from `r137`. -/
theorem E_61a1_rank_ge_one : 1 ≤ Module.rank ℤ E_61a1.toAffine.Point :=
  PrincipiaTractalis.E61a1RankOne.E61a1_rank_ge_one

/-- `E_79a1` (mirror, `⟨1,1,1,-2,0⟩`) has `rank ≥ 1`, from `r138`. -/
theorem E_79a1_rank_ge_one : 1 ≤ Module.rank ℤ E_79a1.toAffine.Point :=
  PrincipiaTractalis.E79a1RankOne.E79a1_rank_ge_one

/-- `E_83a1` (mirror, `⟨1,1,1,1,0⟩`) has `rank ≥ 1`, from `r139`. -/
theorem E_83a1_rank_ge_one : 1 ≤ Module.rank ℤ E_83a1.toAffine.Point :=
  PrincipiaTractalis.E83a1RankOne.E83a1_rank_ge_one

/-- `E_89a1` (mirror, `⟨1,1,1,-1,0⟩`) has `rank ≥ 1`, from `r140`. -/
theorem E_89a1_rank_ge_one : 1 ≤ Module.rank ℤ E_89a1.toAffine.Point :=
  PrincipiaTractalis.E89a1RankOne.E89a1_rank_ge_one

/-- `E_101a1` (mirror, `⟨0,1,1,-1,-1⟩`) has `rank ≥ 1`, from `r141`. -/
theorem E_101a1_rank_ge_one : 1 ≤ Module.rank ℤ E_101a1.toAffine.Point :=
  PrincipiaTractalis.E101a1RankOne.E101a1_rank_ge_one

/-- `E_106a1` (mirror, `⟨1,1,0,-7,5⟩`) has `rank ≥ 1`, from `r142`. -/
theorem E_106a1_rank_ge_one : 1 ≤ Module.rank ℤ E_106a1.toAffine.Point :=
  PrincipiaTractalis.E106a1RankOne.E106a1_rank_ge_one

end BSD_HeegnerMirrorRetirement20261111
end PrincipiaTractalis

#print axioms PrincipiaTractalis.BSD_HeegnerMirrorRetirement20261111.E_43a1_rank_ge_one
#print axioms PrincipiaTractalis.BSD_HeegnerMirrorRetirement20261111.E_53a1_rank_ge_one
#print axioms PrincipiaTractalis.BSD_HeegnerMirrorRetirement20261111.E_61a1_rank_ge_one
#print axioms PrincipiaTractalis.BSD_HeegnerMirrorRetirement20261111.E_79a1_rank_ge_one
#print axioms PrincipiaTractalis.BSD_HeegnerMirrorRetirement20261111.E_83a1_rank_ge_one
#print axioms PrincipiaTractalis.BSD_HeegnerMirrorRetirement20261111.E_89a1_rank_ge_one
#print axioms PrincipiaTractalis.BSD_HeegnerMirrorRetirement20261111.E_101a1_rank_ge_one
#print axioms PrincipiaTractalis.BSD_HeegnerMirrorRetirement20261111.E_106a1_rank_ge_one
