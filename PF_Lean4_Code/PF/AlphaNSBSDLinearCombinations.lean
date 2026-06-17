/-
# PF.AlphaNSBSDLinearCombinations

★ 2026-06-17 — Five clean linear-combination identities between the
π-built Clay axes α_NS = 3π/2 and α_BSD = 3π/4.

## Identities

  α_NS − α_BSD     = α_BSD
  α_NS + α_BSD     = 3·α_BSD
  α_NS + 2·α_BSD   = 4·α_BSD = 3·π
  2·α_NS − α_BSD   = 3·α_BSD
  2·α_NS + α_BSD   = 5·α_BSD

All five follow from α_NS = 2·α_BSD (CrossMillenniumSharedInvariants).

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants

namespace PrincipiaTractalis
namespace AlphaNSBSDLinearCombinations

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants

/-! ## §1 — Linear-combination identities -/

/-- **`α_NS − α_BSD = α_BSD`** — the doubling α_NS = 2·α_BSD makes the
    difference equal to α_BSD. -/
theorem α_NS_sub_α_BSD_eq_α_BSD : α_NS - α_BSD = α_BSD := by
  unfold α_NS α_BSD; ring

/-- **`α_NS + α_BSD = 3·α_BSD`**. -/
theorem α_NS_add_α_BSD_eq_three_α_BSD : α_NS + α_BSD = 3 * α_BSD := by
  unfold α_NS α_BSD; ring

/-- **`α_NS + 2·α_BSD = 4·α_BSD = 3·π`**. -/
theorem α_NS_add_two_α_BSD_eq_three_pi : α_NS + 2 * α_BSD = 3 * Real.pi := by
  unfold α_NS α_BSD; ring

/-- **`2·α_NS − α_BSD = 3·α_BSD`**. -/
theorem two_α_NS_sub_α_BSD_eq_three_α_BSD : 2 * α_NS - α_BSD = 3 * α_BSD := by
  unfold α_NS α_BSD; ring

/-- **`2·α_NS + α_BSD = 5·α_BSD`**. -/
theorem two_α_NS_add_α_BSD_eq_five_α_BSD : 2 * α_NS + α_BSD = 5 * α_BSD := by
  unfold α_NS α_BSD; ring

/-! ## §2 — Bundle capstone -/

/-- **★ α_NS / α_BSD linear-combination bundle capstone ★** — five
    clean linear-combination identities exhibiting α_NS = 2·α_BSD
    through additive scaling. -/
theorem α_NS_BSD_linear_combinations_capstone :
    α_NS - α_BSD = α_BSD ∧
    α_NS + α_BSD = 3 * α_BSD ∧
    α_NS + 2 * α_BSD = 3 * Real.pi ∧
    2 * α_NS - α_BSD = 3 * α_BSD ∧
    2 * α_NS + α_BSD = 5 * α_BSD :=
  ⟨α_NS_sub_α_BSD_eq_α_BSD,
   α_NS_add_α_BSD_eq_three_α_BSD,
   α_NS_add_two_α_BSD_eq_three_pi,
   two_α_NS_sub_α_BSD_eq_three_α_BSD,
   two_α_NS_add_α_BSD_eq_five_α_BSD⟩

end AlphaNSBSDLinearCombinations
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaNSBSDLinearCombinations.α_NS_sub_α_BSD_eq_α_BSD
#print axioms PrincipiaTractalis.AlphaNSBSDLinearCombinations.α_NS_add_two_α_BSD_eq_three_pi
#print axioms PrincipiaTractalis.AlphaNSBSDLinearCombinations.α_NS_BSD_linear_combinations_capstone
