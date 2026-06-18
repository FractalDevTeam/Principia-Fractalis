/-
# PF.AlphaYMHyperbolicLogBundle

★★★★ 2026-06-17 — FUN: hyperbolic functions at `log α_YM` (= log 2)
have clean closed forms anchored to the framework's α-axes.

## The six hyperbolic functions at log α_YM

  sinh(log α_YM) = 3/4 = α_BSD / π
  cosh(log α_YM) = 5/4 = (α_Hodge − 1/2)²
  tanh(log α_YM) = 3/5
  coth(log α_YM) = 5/3
  sech(log α_YM) = 4/5
  csch(log α_YM) = 4/3

The framework's α_BSD/π (= 3/4) appears as `sinh(log α_YM)`. And
`cosh(log α_YM) = 5/4 = (α_Hodge − 1/2)²` — a beautiful golden-axis
expression for the canonical 5/4.

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants

namespace PrincipiaTractalis
namespace AlphaYMHyperbolicLogBundle

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants

/-! ## §1 — sinh(log α_YM) = 3/4 = α_BSD/π -/

/-- **★★★ `sinh(log α_YM) = 3/4 = α_BSD/π` ★★★** —
    the BSD coefficient 3/4 emerges as the sinh of `log α_YM`. -/
theorem sinh_log_α_YM_eq_α_BSD_div_pi :
    Real.sinh (Real.log α_YM) = α_BSD / Real.pi := by
  have h_pos : (0 : ℝ) < α_YM := by unfold α_YM; norm_num
  rw [Real.sinh_log h_pos]
  unfold α_YM α_BSD
  have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  field_simp
  ring

/-! ## §2 — cosh(log α_YM) = 5/4 = (α_Hodge − 1/2)² -/

/-- **★★★ `cosh(log α_YM) = (α_Hodge − 1/2)²` ★★★** —
    the cosh of `log α_YM` is the golden-axis-shifted square. -/
theorem cosh_log_α_YM_eq_α_Hodge_sub_half_sq :
    Real.cosh (Real.log α_YM) = (α_Hodge - 1/2) ^ 2 := by
  have h_pos : (0 : ℝ) < α_YM := by unfold α_YM; norm_num
  rw [Real.cosh_log h_pos]
  have h_sq : α_Hodge ^ 2 = α_Hodge + 1 := α_Hodge_sq_eq_self_plus_one
  unfold α_YM
  nlinarith [h_sq]

/-! ## §3 — cosh(log α_YM) = 5/4 (rational form) -/

/-- **`cosh(log α_YM) = 5/4`** — rational form. -/
theorem cosh_log_α_YM_eq_five_fourths :
    Real.cosh (Real.log α_YM) = 5/4 := by
  have h_pos : (0 : ℝ) < α_YM := by unfold α_YM; norm_num
  rw [Real.cosh_log h_pos]
  unfold α_YM
  norm_num

/-! ## §4 — sinh(log α_YM) = 3/4 (rational form) -/

/-- **`sinh(log α_YM) = 3/4`** — rational form. -/
theorem sinh_log_α_YM_eq_three_fourths :
    Real.sinh (Real.log α_YM) = 3/4 := by
  have h_pos : (0 : ℝ) < α_YM := by unfold α_YM; norm_num
  rw [Real.sinh_log h_pos]
  unfold α_YM
  norm_num

/-! ## §5 — tanh(log α_YM) = 3/5 -/

/-- **`tanh(log α_YM) = 3/5`** — Pythagorean ratio. -/
theorem tanh_log_α_YM_eq_three_fifths :
    Real.tanh (Real.log α_YM) = 3/5 := by
  rw [Real.tanh_eq_sinh_div_cosh,
      sinh_log_α_YM_eq_three_fourths, cosh_log_α_YM_eq_five_fourths]
  norm_num

/-! ## §6 — Bundle capstone -/

/-- **★★★★ THE α_YM HYPERBOLIC-LOG BUNDLE CAPSTONE ★★★★** —
    five identities exhibiting hyperbolic functions at `log α_YM = log 2`
    in framework form:

      sinh(log α_YM) = 3/4 = α_BSD/π            (BSD coefficient)
      cosh(log α_YM) = 5/4 = (α_Hodge − 1/2)²   (golden-shifted square)
      tanh(log α_YM) = 3/5                       (Pythagorean ratio)

    The triple (sinh, cosh, tanh) at the YM-axis log gives the
    canonical (3, 5, 3/5) Pythagorean-style triple. -/
theorem α_YM_hyperbolic_log_bundle_capstone :
    Real.sinh (Real.log α_YM) = α_BSD / Real.pi ∧
    Real.cosh (Real.log α_YM) = (α_Hodge - 1/2) ^ 2 ∧
    Real.sinh (Real.log α_YM) = 3/4 ∧
    Real.cosh (Real.log α_YM) = 5/4 ∧
    Real.tanh (Real.log α_YM) = 3/5 :=
  ⟨sinh_log_α_YM_eq_α_BSD_div_pi,
   cosh_log_α_YM_eq_α_Hodge_sub_half_sq,
   sinh_log_α_YM_eq_three_fourths,
   cosh_log_α_YM_eq_five_fourths,
   tanh_log_α_YM_eq_three_fifths⟩

end AlphaYMHyperbolicLogBundle
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaYMHyperbolicLogBundle.sinh_log_α_YM_eq_α_BSD_div_pi
#print axioms PrincipiaTractalis.AlphaYMHyperbolicLogBundle.cosh_log_α_YM_eq_α_Hodge_sub_half_sq
#print axioms PrincipiaTractalis.AlphaYMHyperbolicLogBundle.sinh_log_α_YM_eq_three_fourths
#print axioms PrincipiaTractalis.AlphaYMHyperbolicLogBundle.cosh_log_α_YM_eq_five_fourths
#print axioms PrincipiaTractalis.AlphaYMHyperbolicLogBundle.tanh_log_α_YM_eq_three_fifths
#print axioms PrincipiaTractalis.AlphaYMHyperbolicLogBundle.α_YM_hyperbolic_log_bundle_capstone
