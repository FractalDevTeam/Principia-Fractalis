/-
# PF.AlphaNSBSDHigherPowersBundle

★ 2026-06-17 — α_NS and α_BSD higher powers (ranks 4 through 6), extending
the closed forms in `CrossMillenniumMoreInvariants` (which covers
ranks 2-3 for both axes).

Both axes carry a π factor (α_NS = 3π/2, α_BSD = 3π/4), so each power
factors cleanly through `π^k` with rational coefficients.

## Closed forms

  α_NS^4 = 81·π^4 / 16
  α_NS^5 = 243·π^5 / 32
  α_NS^6 = 729·π^6 / 64

  α_BSD^4 = 81·π^4 / 256
  α_BSD^5 = 243·π^5 / 1024
  α_BSD^6 = 729·π^6 / 4096

The ratio `α_NS^k / α_BSD^k = 2^k` is preserved at every rank (since
α_NS = 2·α_BSD).

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants

namespace PrincipiaTractalis
namespace AlphaNSBSDHigherPowersBundle

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants

/-! ## §1 — α_NS higher powers -/

/-- **`α_NS^4 = 81·π^4 / 16`**. -/
theorem α_NS_fourth : α_NS ^ 4 = 81 * Real.pi ^ 4 / 16 := by
  unfold α_NS; ring

/-- **`α_NS^5 = 243·π^5 / 32`**. -/
theorem α_NS_fifth : α_NS ^ 5 = 243 * Real.pi ^ 5 / 32 := by
  unfold α_NS; ring

/-- **`α_NS^6 = 729·π^6 / 64`**. -/
theorem α_NS_sixth : α_NS ^ 6 = 729 * Real.pi ^ 6 / 64 := by
  unfold α_NS; ring

/-! ## §2 — α_BSD higher powers -/

/-- **`α_BSD^4 = 81·π^4 / 256`**. -/
theorem α_BSD_fourth : α_BSD ^ 4 = 81 * Real.pi ^ 4 / 256 := by
  unfold α_BSD; ring

/-- **`α_BSD^5 = 243·π^5 / 1024`**. -/
theorem α_BSD_fifth : α_BSD ^ 5 = 243 * Real.pi ^ 5 / 1024 := by
  unfold α_BSD; ring

/-- **`α_BSD^6 = 729·π^6 / 4096`**. -/
theorem α_BSD_sixth : α_BSD ^ 6 = 729 * Real.pi ^ 6 / 4096 := by
  unfold α_BSD; ring

/-! ## §3 — Ratio preservation -/

/-- **`α_NS^4 = 16·α_BSD^4`** — the doubling ratio at rank 4. -/
theorem α_NS_fourth_eq_sixteen_α_BSD_fourth : α_NS ^ 4 = 16 * α_BSD ^ 4 := by
  unfold α_NS α_BSD; ring

/-- **`α_NS^5 = 32·α_BSD^5`** — the doubling ratio at rank 5. -/
theorem α_NS_fifth_eq_thirtytwo_α_BSD_fifth : α_NS ^ 5 = 32 * α_BSD ^ 5 := by
  unfold α_NS α_BSD; ring

/-- **`α_NS^6 = 64·α_BSD^6`** — the doubling ratio at rank 6. -/
theorem α_NS_sixth_eq_sixtyfour_α_BSD_sixth : α_NS ^ 6 = 64 * α_BSD ^ 6 := by
  unfold α_NS α_BSD; ring

/-! ## §4 — Higher-powers bundle capstone -/

/-- **★ α_NS and α_BSD higher powers (rank 4-6) bundle ★** — six clean
    π^k closed forms extending the existing rank 2-3 coverage. -/
theorem α_NS_BSD_higher_powers_capstone :
    α_NS ^ 4 = 81 * Real.pi ^ 4 / 16 ∧
    α_NS ^ 5 = 243 * Real.pi ^ 5 / 32 ∧
    α_NS ^ 6 = 729 * Real.pi ^ 6 / 64 ∧
    α_BSD ^ 4 = 81 * Real.pi ^ 4 / 256 ∧
    α_BSD ^ 5 = 243 * Real.pi ^ 5 / 1024 ∧
    α_BSD ^ 6 = 729 * Real.pi ^ 6 / 4096 :=
  ⟨α_NS_fourth, α_NS_fifth, α_NS_sixth,
   α_BSD_fourth, α_BSD_fifth, α_BSD_sixth⟩

end AlphaNSBSDHigherPowersBundle
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaNSBSDHigherPowersBundle.α_NS_fourth
#print axioms PrincipiaTractalis.AlphaNSBSDHigherPowersBundle.α_NS_sixth
#print axioms PrincipiaTractalis.AlphaNSBSDHigherPowersBundle.α_BSD_fourth
#print axioms PrincipiaTractalis.AlphaNSBSDHigherPowersBundle.α_BSD_sixth
#print axioms
  PrincipiaTractalis.AlphaNSBSDHigherPowersBundle.α_NS_BSD_higher_powers_capstone
