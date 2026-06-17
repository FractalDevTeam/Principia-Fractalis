/-
# PF.AlphaNSBSDPowersRank7To9

★ 2026-06-17 — α_NS and α_BSD higher powers ranks 7 through 9,
extending `AlphaNSBSDHigherPowersBundle` (rank 4-6).

## Closed forms

  α_NS^7 = 2187·π^7 / 128
  α_NS^8 = 6561·π^8 / 256
  α_NS^9 = 19683·π^9 / 512

  α_BSD^7 = 2187·π^7 / 16384
  α_BSD^8 = 6561·π^8 / 65536
  α_BSD^9 = 19683·π^9 / 262144

Each direct via unfold + ring.

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants

namespace PrincipiaTractalis
namespace AlphaNSBSDPowersRank7To9

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants

/-! ## §1 — α_NS rank 7-9 -/

theorem α_NS_seventh : α_NS ^ 7 = 2187 * Real.pi ^ 7 / 128 := by
  unfold α_NS; ring

theorem α_NS_eighth : α_NS ^ 8 = 6561 * Real.pi ^ 8 / 256 := by
  unfold α_NS; ring

theorem α_NS_ninth : α_NS ^ 9 = 19683 * Real.pi ^ 9 / 512 := by
  unfold α_NS; ring

/-! ## §2 — α_BSD rank 7-9 -/

theorem α_BSD_seventh : α_BSD ^ 7 = 2187 * Real.pi ^ 7 / 16384 := by
  unfold α_BSD; ring

theorem α_BSD_eighth : α_BSD ^ 8 = 6561 * Real.pi ^ 8 / 65536 := by
  unfold α_BSD; ring

theorem α_BSD_ninth : α_BSD ^ 9 = 19683 * Real.pi ^ 9 / 262144 := by
  unfold α_BSD; ring

/-! ## §3 — Doubling preserved at each rank -/

theorem α_NS_seventh_eq_128_α_BSD_seventh : α_NS ^ 7 = 128 * α_BSD ^ 7 := by
  unfold α_NS α_BSD; ring

theorem α_NS_eighth_eq_256_α_BSD_eighth : α_NS ^ 8 = 256 * α_BSD ^ 8 := by
  unfold α_NS α_BSD; ring

theorem α_NS_ninth_eq_512_α_BSD_ninth : α_NS ^ 9 = 512 * α_BSD ^ 9 := by
  unfold α_NS α_BSD; ring

/-! ## §4 — Rank 7-9 bundle capstone -/

/-- **★ α_NS and α_BSD ranks 7-9 bundle capstone ★** — six new
    closed forms plus three doubling-preservation identities. -/
theorem α_NS_BSD_rank_7_to_9_capstone :
    α_NS ^ 7 = 2187 * Real.pi ^ 7 / 128 ∧
    α_NS ^ 8 = 6561 * Real.pi ^ 8 / 256 ∧
    α_NS ^ 9 = 19683 * Real.pi ^ 9 / 512 ∧
    α_BSD ^ 7 = 2187 * Real.pi ^ 7 / 16384 ∧
    α_BSD ^ 8 = 6561 * Real.pi ^ 8 / 65536 ∧
    α_BSD ^ 9 = 19683 * Real.pi ^ 9 / 262144 ∧
    α_NS ^ 7 = 128 * α_BSD ^ 7 ∧
    α_NS ^ 8 = 256 * α_BSD ^ 8 ∧
    α_NS ^ 9 = 512 * α_BSD ^ 9 :=
  ⟨α_NS_seventh, α_NS_eighth, α_NS_ninth,
   α_BSD_seventh, α_BSD_eighth, α_BSD_ninth,
   α_NS_seventh_eq_128_α_BSD_seventh,
   α_NS_eighth_eq_256_α_BSD_eighth,
   α_NS_ninth_eq_512_α_BSD_ninth⟩

end AlphaNSBSDPowersRank7To9
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaNSBSDPowersRank7To9.α_NS_seventh
#print axioms PrincipiaTractalis.AlphaNSBSDPowersRank7To9.α_NS_ninth
#print axioms PrincipiaTractalis.AlphaNSBSDPowersRank7To9.α_BSD_seventh
#print axioms PrincipiaTractalis.AlphaNSBSDPowersRank7To9.α_BSD_ninth
#print axioms PrincipiaTractalis.AlphaNSBSDPowersRank7To9.α_NS_BSD_rank_7_to_9_capstone
