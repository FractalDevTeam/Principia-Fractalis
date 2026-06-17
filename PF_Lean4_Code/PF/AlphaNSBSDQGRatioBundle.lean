/-
# PF.AlphaNSBSDQGRatioBundle

★ 2026-06-17 — Direct ratio closed forms for the π-built axes
(α_NS = 3π/2, α_BSD = 3π/4) divided by the gravitational axis
α_QG = √(2π).

## Identities

  (A) α_NS / α_QG = (3·α_QG)/4
      = (3π/2)/√(2π) = (3/2)·√(π/2) = (3·√(2π))/4 = (3·α_QG)/4.
      Numerically ≈ 1.880.

  (B) α_BSD / α_QG = (3·α_QG)/8
      = (3π/4)/√(2π) = (3·α_QG)/8.
      Numerically ≈ 0.940.

  (C) α_NS / α_BSD via α_QG = 2 (consequence: α_NS/α_QG = 2·(α_BSD/α_QG)).

The ratio α_NS/α_QG factors as `(3·α_QG)/4`, exhibiting α_QG as the
canonical reduction of the π-built axes against the gravitational kernel.

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants

namespace PrincipiaTractalis
namespace AlphaNSBSDQGRatioBundle

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants

/-! ## §1 — α_NS / α_QG -/

/-- **`α_NS / α_QG = (3·α_QG)/4`** — pulls through `α_QG² = 2π`
    so that `α_NS/α_QG = (3π/2)/α_QG = (3·α_QG²/2)/α_QG = (3·α_QG)/2 · (1/(2·1))`. -/
theorem α_NS_div_α_QG_eq_three_α_QG_div_four :
    α_NS / α_QG = (3 * α_QG) / 4 := by
  have h_sq : α_QG ^ 2 = 2 * Real.pi := α_QG_sq_eq_two_pi
  have h_pos : (0 : ℝ) < α_QG := by
    unfold α_QG
    exact Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 2 * Real.pi)
  have h_α_NS_eq : α_NS = (3 * α_QG ^ 2) / 4 := by
    unfold α_NS
    rw [h_sq]
    ring
  rw [h_α_NS_eq]
  field_simp

/-! ## §2 — α_BSD / α_QG -/

/-- **`α_BSD / α_QG = (3·α_QG)/8`**. -/
theorem α_BSD_div_α_QG_eq_three_α_QG_div_eight :
    α_BSD / α_QG = (3 * α_QG) / 8 := by
  have h_sq : α_QG ^ 2 = 2 * Real.pi := α_QG_sq_eq_two_pi
  have h_pos : (0 : ℝ) < α_QG := by
    unfold α_QG
    exact Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 2 * Real.pi)
  have h_α_BSD_eq : α_BSD = (3 * α_QG ^ 2) / 8 := by
    unfold α_BSD
    rw [h_sq]
    ring
  rw [h_α_BSD_eq]
  field_simp

/-! ## §3 — Consistency: doubling preserved -/

/-- **`α_NS / α_QG = 2 · (α_BSD / α_QG)`** — the doubling factor
    `α_NS = 2·α_BSD` propagates through division by α_QG. -/
theorem α_NS_α_BSD_QG_ratio_doubling :
    α_NS / α_QG = 2 * (α_BSD / α_QG) := by
  rw [α_NS_div_α_QG_eq_three_α_QG_div_four,
      α_BSD_div_α_QG_eq_three_α_QG_div_eight]
  ring

/-! ## §4 — Bundle capstone -/

/-- **★ α_NS/α_BSD-against-α_QG ratio bundle capstone ★** — three
    direct ratio closed forms connecting the π-built axes to the
    gravitational kernel α_QG = √(2π). -/
theorem α_NS_BSD_QG_ratio_bundle_capstone :
    α_NS / α_QG = (3 * α_QG) / 4 ∧
    α_BSD / α_QG = (3 * α_QG) / 8 ∧
    α_NS / α_QG = 2 * (α_BSD / α_QG) :=
  ⟨α_NS_div_α_QG_eq_three_α_QG_div_four,
   α_BSD_div_α_QG_eq_three_α_QG_div_eight,
   α_NS_α_BSD_QG_ratio_doubling⟩

end AlphaNSBSDQGRatioBundle
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaNSBSDQGRatioBundle.α_NS_div_α_QG_eq_three_α_QG_div_four
#print axioms PrincipiaTractalis.AlphaNSBSDQGRatioBundle.α_BSD_div_α_QG_eq_three_α_QG_div_eight
#print axioms PrincipiaTractalis.AlphaNSBSDQGRatioBundle.α_NS_α_BSD_QG_ratio_doubling
#print axioms PrincipiaTractalis.AlphaNSBSDQGRatioBundle.α_NS_BSD_QG_ratio_bundle_capstone
