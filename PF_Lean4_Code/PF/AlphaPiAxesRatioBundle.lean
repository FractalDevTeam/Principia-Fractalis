/-
# PF.AlphaPiAxesRatioBundle

★ 2026-06-17 — π-extraction ratios for the π-built Clay axes
(α_NS = 3π/2, α_BSD = 3π/4), exhibiting π as a clean ratio against
the rational α_RH = 3/2 and as a clean fraction of α_QG^2 = 2π.

## Identities

  (A) α_NS / α_RH = π
      = (3π/2) / (3/2) = π. The π-extraction is exact.

  (B) α_BSD / α_RH = π/2
      = (3π/4) / (3/2) = π/2.

  (C) α_NS / α_QG^2 = 3/4
      = (3π/2) / (2π) = 3/4 (rational ratio after π cancellation).

  (D) α_BSD / α_QG^2 = 3/8
      = (3π/4) / (2π) = 3/8.

Each direct via unfold + field_simp or ring.

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants

namespace PrincipiaTractalis
namespace AlphaPiAxesRatioBundle

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants

/-! ## §1 — π-extraction against α_RH -/

/-- **`α_NS / α_RH = π`** — the π-built NS axis divided by the rational
    RH axis isolates π exactly. -/
theorem α_NS_div_α_RH_eq_pi : α_NS / α_RH = Real.pi := by
  unfold α_NS α_RH
  ring

/-- **`α_BSD / α_RH = π/2`** — analogous π-extraction for BSD. -/
theorem α_BSD_div_α_RH_eq_pi_div_two : α_BSD / α_RH = Real.pi / 2 := by
  unfold α_BSD α_RH
  ring

/-! ## §2 — Rational fraction of α_QG^2 -/

/-- **`α_NS / α_QG^2 = 3/4`** — α_QG^2 = 2π and α_NS = 3π/2 share the
    π factor, leaving rational 3/4. -/
theorem α_NS_div_α_QG_sq : α_NS / α_QG ^ 2 = 3 / 4 := by
  rw [α_QG_sq_eq_two_pi]
  unfold α_NS
  have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  field_simp
  ring

/-- **`α_BSD / α_QG^2 = 3/8`** — analogous rational extraction for BSD. -/
theorem α_BSD_div_α_QG_sq : α_BSD / α_QG ^ 2 = 3 / 8 := by
  rw [α_QG_sq_eq_two_pi]
  unfold α_BSD
  have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  field_simp
  ring

/-! ## §3 — Bundle capstone -/

/-- **★ π-axis ratio bundle capstone ★** — four clean ratio identities
    isolating the π-content of the π-built axes against the rational
    axis and against α_QG^2 = 2π. -/
theorem α_pi_axes_ratio_bundle_capstone :
    α_NS / α_RH = Real.pi ∧
    α_BSD / α_RH = Real.pi / 2 ∧
    α_NS / α_QG ^ 2 = 3 / 4 ∧
    α_BSD / α_QG ^ 2 = 3 / 8 :=
  ⟨α_NS_div_α_RH_eq_pi,
   α_BSD_div_α_RH_eq_pi_div_two,
   α_NS_div_α_QG_sq,
   α_BSD_div_α_QG_sq⟩

end AlphaPiAxesRatioBundle
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaPiAxesRatioBundle.α_NS_div_α_RH_eq_pi
#print axioms PrincipiaTractalis.AlphaPiAxesRatioBundle.α_BSD_div_α_RH_eq_pi_div_two
#print axioms PrincipiaTractalis.AlphaPiAxesRatioBundle.α_NS_div_α_QG_sq
#print axioms PrincipiaTractalis.AlphaPiAxesRatioBundle.α_BSD_div_α_QG_sq
#print axioms PrincipiaTractalis.AlphaPiAxesRatioBundle.α_pi_axes_ratio_bundle_capstone
