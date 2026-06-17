/-
# PF.AlphaTrigTangentExtension

★ 2026-06-17 — Extend the direct trig bundle with tangent identities
at the named α-axis values.

## Identities

  tan(α_BSD) = -1
  tan(α_NS)  = undefined (cos α_NS = 0), so we record sin(α_NS) = -cos(0)
              i.e. sin²(α_NS) = 1, cos(α_NS) = 0 instead.

  sin²(α_NS) + cos²(α_NS) = 1 (Pythagorean identity at α_NS)
  sin²(α_BSD) + cos²(α_BSD) = 1 (Pythagorean at α_BSD)
  sin²(α_QG²) + cos²(α_QG²) = 1 (Pythagorean at α_QG²)
  sin(2·α_BSD) = sin(3π/2) = -1 (double angle at α_BSD)
  cos(2·α_BSD) = cos(3π/2) = 0  (double angle at α_BSD)
  sin(α_BSD + α_BSD) = sin(α_NS) = -1 (consistency)

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants
import PF.AlphaTrigDirectBundle

namespace PrincipiaTractalis
namespace AlphaTrigTangentExtension

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants
open PrincipiaTractalis.AlphaTrigDirectBundle

/-! ## §1 — tan(α_BSD) -/

/-- **`tan(α_BSD) = -1`** — tan(3π/4) = -1. -/
theorem tan_α_BSD_eq_neg_one : Real.tan α_BSD = -1 := by
  rw [Real.tan_eq_sin_div_cos]
  rw [sin_α_BSD_eq_sqrt_two_div_two, cos_α_BSD_eq_neg_sqrt_two_div_two]
  have h_sqrt2_pos : (0 : ℝ) < Real.sqrt 2 :=
    Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  field_simp

/-! ## §2 — Pythagorean identities at α-axes -/

/-- **`sin²(α_NS) + cos²(α_NS) = 1`**. -/
theorem pythagorean_at_α_NS :
    Real.sin α_NS ^ 2 + Real.cos α_NS ^ 2 = 1 := by
  rw [sin_α_NS_eq_neg_one, cos_α_NS_eq_zero]
  ring

/-- **`sin²(α_BSD) + cos²(α_BSD) = 1`**. -/
theorem pythagorean_at_α_BSD :
    Real.sin α_BSD ^ 2 + Real.cos α_BSD ^ 2 = 1 := by
  rw [sin_α_BSD_eq_sqrt_two_div_two, cos_α_BSD_eq_neg_sqrt_two_div_two]
  have h_sqrt2_sq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith [h_sqrt2_sq]

/-- **`sin²(α_QG²) + cos²(α_QG²) = 1`**. -/
theorem pythagorean_at_α_QG_sq :
    Real.sin (α_QG ^ 2) ^ 2 + Real.cos (α_QG ^ 2) ^ 2 = 1 := by
  rw [sin_α_QG_sq_eq_zero, cos_α_QG_sq_eq_one]
  ring

/-! ## §3 — Double-angle consistency at α_BSD -/

/-- **`sin(2·α_BSD) = sin(α_NS) = -1`** — exhibits the α_NS = 2·α_BSD
    structural relation at the trigonometric level. -/
theorem sin_two_α_BSD_eq_sin_α_NS :
    Real.sin (2 * α_BSD) = Real.sin α_NS := by
  rw [show (2 * α_BSD : ℝ) = α_NS from (α_NS_eq_two_α_BSD).symm]

/-- **`cos(2·α_BSD) = cos(α_NS) = 0`**. -/
theorem cos_two_α_BSD_eq_cos_α_NS :
    Real.cos (2 * α_BSD) = Real.cos α_NS := by
  rw [show (2 * α_BSD : ℝ) = α_NS from (α_NS_eq_two_α_BSD).symm]

/-! ## §4 — Bundle capstone -/

/-- **★ α-axis trig tangent + Pythagorean + double-angle bundle ★** —
    six closed forms extending the direct trig bundle with tangent,
    Pythagorean, and α_NS = 2·α_BSD double-angle witnesses. -/
theorem α_trig_tangent_extension_capstone :
    Real.tan α_BSD = -1 ∧
    Real.sin α_NS ^ 2 + Real.cos α_NS ^ 2 = 1 ∧
    Real.sin α_BSD ^ 2 + Real.cos α_BSD ^ 2 = 1 ∧
    Real.sin (α_QG ^ 2) ^ 2 + Real.cos (α_QG ^ 2) ^ 2 = 1 ∧
    Real.sin (2 * α_BSD) = Real.sin α_NS ∧
    Real.cos (2 * α_BSD) = Real.cos α_NS :=
  ⟨tan_α_BSD_eq_neg_one,
   pythagorean_at_α_NS,
   pythagorean_at_α_BSD,
   pythagorean_at_α_QG_sq,
   sin_two_α_BSD_eq_sin_α_NS,
   cos_two_α_BSD_eq_cos_α_NS⟩

end AlphaTrigTangentExtension
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaTrigTangentExtension.tan_α_BSD_eq_neg_one
#print axioms PrincipiaTractalis.AlphaTrigTangentExtension.pythagorean_at_α_NS
#print axioms PrincipiaTractalis.AlphaTrigTangentExtension.pythagorean_at_α_BSD
#print axioms PrincipiaTractalis.AlphaTrigTangentExtension.sin_two_α_BSD_eq_sin_α_NS
#print axioms PrincipiaTractalis.AlphaTrigTangentExtension.α_trig_tangent_extension_capstone
