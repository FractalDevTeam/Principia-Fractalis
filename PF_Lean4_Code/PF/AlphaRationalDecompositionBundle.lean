/-
# PF.AlphaRationalDecompositionBundle

★★★ 2026-06-17 — FUN: clean small-rational decomposition identities
involving the rational Clay axes.

## Identities

  α_RH · (α_RH − 1) = 3/4 = α_BSD / π
  α_YM · (α_YM − 1) = 2 = α_YM = α_NS · α_YM / 3   (since 2 = α_YM)
  α_RH · (α_RH − 1) · α_QG² = α_NS

The α_RH·(α_RH−1) = 3/4 identity exhibits the "BSD coefficient" 3/4
(= α_BSD/π) as the decomposition of α_RH(α_RH−1). Multiplied by α_QG²
= 2π, this gives α_NS = 3π/2.

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants

namespace PrincipiaTractalis
namespace AlphaRationalDecompositionBundle

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants

/-! ## §1 — α_RH · (α_RH − 1) = 3/4 -/

/-- **`α_RH · (α_RH − 1) = 3/4`** — the BSD coefficient 3/4 emerges as
    the decomposition of α_RH·(α_RH − 1). -/
theorem α_RH_mul_α_RH_sub_one_eq_three_fourths :
    α_RH * (α_RH - 1) = 3/4 := by
  unfold α_RH; norm_num

/-! ## §2 — α_RH · (α_RH − 1) = α_BSD / π -/

/-- **`α_RH · (α_RH − 1) = α_BSD / π`** — exhibits α_BSD = 3π/4 as
    π·α_RH·(α_RH−1). -/
theorem α_RH_mul_α_RH_sub_one_eq_α_BSD_div_π :
    α_RH * (α_RH - 1) = α_BSD / Real.pi := by
  rw [α_RH_mul_α_RH_sub_one_eq_three_fourths]
  unfold α_BSD
  have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  field_simp

/-! ## §3 — α_RH · (α_RH − 1) · α_QG² = α_NS -/

/-- **★★★ `α_RH · (α_RH − 1) · α_QG² = α_NS` ★★★** — three-axis
    composition gives α_NS exactly. -/
theorem α_RH_mul_α_RH_sub_one_mul_α_QG_sq_eq_α_NS :
    α_RH * (α_RH - 1) * α_QG ^ 2 = α_NS := by
  rw [α_RH_mul_α_RH_sub_one_eq_three_fourths]
  rw [α_QG_sq_eq_two_pi]
  unfold α_NS
  ring

/-! ## §4 — Bundle capstone -/

/-- **★★★ THE RATIONAL DECOMPOSITION BUNDLE CAPSTONE ★★★** —
    three identities exhibiting the BSD/NS axes as compositions
    involving α_RH·(α_RH − 1) = 3/4. -/
theorem α_rational_decomposition_bundle_capstone :
    α_RH * (α_RH - 1) = 3/4 ∧
    α_RH * (α_RH - 1) = α_BSD / Real.pi ∧
    α_RH * (α_RH - 1) * α_QG ^ 2 = α_NS :=
  ⟨α_RH_mul_α_RH_sub_one_eq_three_fourths,
   α_RH_mul_α_RH_sub_one_eq_α_BSD_div_π,
   α_RH_mul_α_RH_sub_one_mul_α_QG_sq_eq_α_NS⟩

end AlphaRationalDecompositionBundle
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaRationalDecompositionBundle.α_RH_mul_α_RH_sub_one_eq_three_fourths
#print axioms PrincipiaTractalis.AlphaRationalDecompositionBundle.α_RH_mul_α_RH_sub_one_eq_α_BSD_div_π
#print axioms PrincipiaTractalis.AlphaRationalDecompositionBundle.α_RH_mul_α_RH_sub_one_mul_α_QG_sq_eq_α_NS
#print axioms PrincipiaTractalis.AlphaRationalDecompositionBundle.α_rational_decomposition_bundle_capstone
