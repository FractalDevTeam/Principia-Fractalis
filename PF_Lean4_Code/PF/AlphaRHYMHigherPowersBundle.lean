/-
# PF.AlphaRHYMHigherPowersBundle

★ 2026-06-17 — α_RH and α_YM higher powers (ranks 5 through 8), extending
the closed forms in `CrossMillenniumMoreInvariants` (which covers
ranks 2-4 for both axes).

Both axes have rational values (α_RH = 3/2, α_YM = 2), so each power
is a simple rational closed form.

## Closed forms

  α_RH^5 = 243/32     [= (3/2)^5]
  α_RH^6 = 729/64     [= (3/2)^6]
  α_RH^7 = 2187/128   [= (3/2)^7]
  α_RH^8 = 6561/256   [= (3/2)^8]

  α_YM^5 = 32         [= 2^5]
  α_YM^6 = 64         [= 2^6]
  α_YM^7 = 128        [= 2^7]
  α_YM^8 = 256        [= 2^8]

Each by direct `unfold + norm_num`.

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants

namespace PrincipiaTractalis
namespace AlphaRHYMHigherPowersBundle

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants

/-! ## §1 — α_RH higher powers -/

/-- **`α_RH^5 = 243/32`**. -/
theorem α_RH_fifth : α_RH ^ 5 = 243 / 32 := by
  unfold α_RH; norm_num

/-- **`α_RH^6 = 729/64`**. -/
theorem α_RH_sixth : α_RH ^ 6 = 729 / 64 := by
  unfold α_RH; norm_num

/-- **`α_RH^7 = 2187/128`**. -/
theorem α_RH_seventh : α_RH ^ 7 = 2187 / 128 := by
  unfold α_RH; norm_num

/-- **`α_RH^8 = 6561/256`**. -/
theorem α_RH_eighth : α_RH ^ 8 = 6561 / 256 := by
  unfold α_RH; norm_num

/-! ## §2 — α_YM higher powers -/

/-- **`α_YM^5 = 32`**. -/
theorem α_YM_fifth : α_YM ^ 5 = 32 := by
  unfold α_YM; norm_num

/-- **`α_YM^6 = 64`**. -/
theorem α_YM_sixth : α_YM ^ 6 = 64 := by
  unfold α_YM; norm_num

/-- **`α_YM^7 = 128`**. -/
theorem α_YM_seventh : α_YM ^ 7 = 128 := by
  unfold α_YM; norm_num

/-- **`α_YM^8 = 256`**. -/
theorem α_YM_eighth : α_YM ^ 8 = 256 := by
  unfold α_YM; norm_num

/-! ## §3 — Higher-powers bundle capstone -/

/-- **★ α_RH and α_YM higher powers (rank 5-8) bundle ★** — eight clean
    rational closed forms extending the existing rank 2-4 coverage. -/
theorem α_RH_YM_higher_powers_capstone :
    α_RH ^ 5 = 243 / 32 ∧
    α_RH ^ 6 = 729 / 64 ∧
    α_RH ^ 7 = 2187 / 128 ∧
    α_RH ^ 8 = 6561 / 256 ∧
    α_YM ^ 5 = 32 ∧
    α_YM ^ 6 = 64 ∧
    α_YM ^ 7 = 128 ∧
    α_YM ^ 8 = 256 :=
  ⟨α_RH_fifth, α_RH_sixth, α_RH_seventh, α_RH_eighth,
   α_YM_fifth, α_YM_sixth, α_YM_seventh, α_YM_eighth⟩

end AlphaRHYMHigherPowersBundle
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaRHYMHigherPowersBundle.α_RH_fifth
#print axioms PrincipiaTractalis.AlphaRHYMHigherPowersBundle.α_RH_eighth
#print axioms PrincipiaTractalis.AlphaRHYMHigherPowersBundle.α_YM_fifth
#print axioms PrincipiaTractalis.AlphaRHYMHigherPowersBundle.α_YM_eighth
#print axioms
  PrincipiaTractalis.AlphaRHYMHigherPowersBundle.α_RH_YM_higher_powers_capstone
