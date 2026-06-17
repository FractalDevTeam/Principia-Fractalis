/-
# PF.AlphaQGGammaHalfIntegerLadder

★★★ 2026-06-17 — The Gamma function at half-integers, expressed in
α-framework form via α_QG / α_P = √π.

## The half-integer Gamma ladder

For any non-negative integer n,
  Γ(n + 1/2) = (2n − 1)!! · √π / 2^n
            = (2n − 1)!! · (α_QG / α_P) / 2^n

where (2n−1)!! = (2n−1)·(2n−3)·...·3·1 is the double factorial (with
(−1)!! = 1).

## Identities in this file

  Γ(1/2)  = α_QG / α_P                 = √π
  Γ(3/2)  = α_QG / (2·α_P)             = √π / 2
  Γ(5/2)  = 3·α_QG / (4·α_P)           = 3√π / 4
  Γ(7/2)  = 15·α_QG / (8·α_P)          = 15√π / 8
  Γ(9/2)  = 105·α_QG / (16·α_P)        = 105√π / 16
  Γ(11/2) = 945·α_QG / (32·α_P)        = 945√π / 32

The numerators 1, 1, 3, 15, 105, 945 are the double factorials of
odd numbers: 1, 3!!, 5!!, 7!!, 9!! (with prefix 1, 1 for the first
two).

This exhibits the entire half-integer Γ ladder as a Q-rescaling of
the framework's gravitational ratio `α_QG / α_P = √π`.

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

namespace PrincipiaTractalis
namespace AlphaQGGammaHalfIntegerLadder

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants
open PrincipiaTractalis.CrossMillenniumMoreInvariants

/-! ## §1 — α_QG / α_P = √π = Γ(1/2) -/

/-- **`Γ(1/2) = α_QG / α_P`** — the framework's gravitational ratio
    equals the canonical half-integer Γ value (= √π).

    Existing in CMMI as `α_QG_div_α_P_eq_Gamma_one_half`; re-exported
    under the half-integer-ladder namespace as the rank-0 anchor. -/
theorem Γ_one_half_eq_α_QG_div_α_P :
    Real.Gamma (1/2) = α_QG / α_P :=
  α_QG_div_α_P_eq_Gamma_one_half.symm

/-! ## §2 — Auxiliary positivity -/

private lemma α_P_pos : 0 < α_P := by
  unfold α_P
  exact Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)

private lemma α_P_ne_zero : α_P ≠ 0 := ne_of_gt α_P_pos

/-! ## §3 — Γ(3/2) = α_QG / (2·α_P) -/

/-- **`Γ(3/2) = α_QG / (2·α_P)`** — rank 1 (= √π/2). -/
theorem Γ_three_halves_eq :
    Real.Gamma (3/2) = α_QG / (2 * α_P) := by
  have h_step : (3/2 : ℝ) = 1/2 + 1 := by norm_num
  rw [h_step, Real.Gamma_add_one (by norm_num : (1/2 : ℝ) ≠ 0)]
  rw [Γ_one_half_eq_α_QG_div_α_P]
  field_simp

/-! ## §4 — Γ(5/2) = 3·α_QG / (4·α_P) -/

/-- **`Γ(5/2) = 3·α_QG / (4·α_P)`** — rank 2 (= 3√π/4). -/
theorem Γ_five_halves_eq :
    Real.Gamma (5/2) = 3 * α_QG / (4 * α_P) := by
  have h_step : (5/2 : ℝ) = 3/2 + 1 := by norm_num
  rw [h_step, Real.Gamma_add_one (by norm_num : (3/2 : ℝ) ≠ 0)]
  rw [Γ_three_halves_eq]
  field_simp
  ring

/-! ## §5 — Γ(7/2) = 15·α_QG / (8·α_P) -/

/-- **`Γ(7/2) = 15·α_QG / (8·α_P)`** — rank 3 (= 15√π/8). -/
theorem Γ_seven_halves_eq :
    Real.Gamma (7/2) = 15 * α_QG / (8 * α_P) := by
  have h_step : (7/2 : ℝ) = 5/2 + 1 := by norm_num
  rw [h_step, Real.Gamma_add_one (by norm_num : (5/2 : ℝ) ≠ 0)]
  rw [Γ_five_halves_eq]
  field_simp
  ring

/-! ## §6 — Γ(9/2) = 105·α_QG / (16·α_P) -/

/-- **`Γ(9/2) = 105·α_QG / (16·α_P)`** — rank 4 (= 105√π/16). -/
theorem Γ_nine_halves_eq :
    Real.Gamma (9/2) = 105 * α_QG / (16 * α_P) := by
  have h_step : (9/2 : ℝ) = 7/2 + 1 := by norm_num
  rw [h_step, Real.Gamma_add_one (by norm_num : (7/2 : ℝ) ≠ 0)]
  rw [Γ_seven_halves_eq]
  field_simp
  ring

/-! ## §7 — Γ(11/2) = 945·α_QG / (32·α_P) -/

/-- **`Γ(11/2) = 945·α_QG / (32·α_P)`** — rank 5 (= 945√π/32). -/
theorem Γ_eleven_halves_eq :
    Real.Gamma (11/2) = 945 * α_QG / (32 * α_P) := by
  have h_step : (11/2 : ℝ) = 9/2 + 1 := by norm_num
  rw [h_step, Real.Gamma_add_one (by norm_num : (9/2 : ℝ) ≠ 0)]
  rw [Γ_nine_halves_eq]
  field_simp
  ring

/-! ## §8 — The half-integer Gamma ladder capstone -/

/-- **★★★ THE HALF-INTEGER GAMMA LADDER ★★★** — six closed forms for
    Γ at half-integers 1/2 through 11/2, all expressed via the
    framework's gravitational ratio α_QG / α_P = √π.

    The double-factorial numerators 1, 1, 3, 15, 105, 945 are
    (2n−1)!! for n = 0, 1, 2, 3, 4, 5 respectively.

    This exhibits the entire half-integer Gamma ladder as a
    Q-rescaling of the framework's gravitational ratio. -/
theorem Γ_half_integer_ladder_capstone :
    Real.Gamma (1/2) = α_QG / α_P ∧
    Real.Gamma (3/2) = α_QG / (2 * α_P) ∧
    Real.Gamma (5/2) = 3 * α_QG / (4 * α_P) ∧
    Real.Gamma (7/2) = 15 * α_QG / (8 * α_P) ∧
    Real.Gamma (9/2) = 105 * α_QG / (16 * α_P) ∧
    Real.Gamma (11/2) = 945 * α_QG / (32 * α_P) :=
  ⟨Γ_one_half_eq_α_QG_div_α_P,
   Γ_three_halves_eq,
   Γ_five_halves_eq,
   Γ_seven_halves_eq,
   Γ_nine_halves_eq,
   Γ_eleven_halves_eq⟩

end AlphaQGGammaHalfIntegerLadder
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaQGGammaHalfIntegerLadder.Γ_one_half_eq_α_QG_div_α_P
#print axioms PrincipiaTractalis.AlphaQGGammaHalfIntegerLadder.Γ_three_halves_eq
#print axioms PrincipiaTractalis.AlphaQGGammaHalfIntegerLadder.Γ_five_halves_eq
#print axioms PrincipiaTractalis.AlphaQGGammaHalfIntegerLadder.Γ_seven_halves_eq
#print axioms PrincipiaTractalis.AlphaQGGammaHalfIntegerLadder.Γ_nine_halves_eq
#print axioms PrincipiaTractalis.AlphaQGGammaHalfIntegerLadder.Γ_eleven_halves_eq
#print axioms PrincipiaTractalis.AlphaQGGammaHalfIntegerLadder.Γ_half_integer_ladder_capstone
