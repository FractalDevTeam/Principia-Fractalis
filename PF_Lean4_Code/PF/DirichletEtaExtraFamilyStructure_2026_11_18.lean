import PF.DirichletEtaExtExtraZeros_2026_11_18
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Structure of the extra-zero family of `dirichletEtaExt`

The extra zeros of `dirichletEtaExt` (contributed by the factor
`1 - 2^(1-s)`) form the explicit family

    `s_k := 1 + 2π i k / Complex.log 2`,  `k ∈ ℤ`.

This file proves that the parameterisation `k ↦ s_k` is injective on
`ℤ`, hence the extra-zero family is countably infinite.

Three-axiom bar `[propext, Classical.choice, Quot.sound]`.

Proof via pure algebra: `s_{k₁} = s_{k₂}` ⟹ `2π I (k₁ - k₂) / log 2 = 0`
⟹ (since `log 2 ≠ 0` and `2π I ≠ 0`) `k₁ = k₂`. No `re`/`im`
component computation required.
-/

namespace PrincipiaTractalis.DirichletEtaExtraFamilyStructure_2026_11_18

open Complex

/-- The `k`-th point of the extra-zero family. -/
noncomputable def extraFamily (k : ℤ) : ℂ :=
  1 + 2 * (Real.pi : ℂ) * I * (k : ℂ) / Complex.log 2

/-- `Complex.log 2 ≠ 0`. -/
private theorem complex_log_two_ne_zero : Complex.log 2 ≠ 0 := by
  intro h
  have hre : (Complex.log 2).re = Real.log 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from by norm_num, Complex.log_ofReal_re]
  have : (Complex.log 2).re = 0 := by rw [h]; simp
  rw [hre] at this
  have hpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  linarith

/-- `2π I ≠ 0` (in ℂ). -/
private theorem two_pi_I_ne_zero : (2 : ℂ) * (Real.pi : ℂ) * I ≠ 0 := by
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt Real.pi_pos
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  exact mul_ne_zero (mul_ne_zero h2 hpi) hI

/-- **The extra-family parameterisation is injective.** Hence the
    extra-zero family is countably infinite. -/
theorem extraFamily_injective : Function.Injective extraFamily := by
  intro k₁ k₂ hk
  unfold extraFamily at hk
  have hlog_ne : Complex.log 2 ≠ 0 := complex_log_two_ne_zero
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt Real.pi_pos
  have h_cast : (k₁ : ℂ) = (k₂ : ℂ) := by
    have h1 : (2 : ℂ) * (Real.pi : ℂ) * I * (k₁ : ℂ) =
              (2 : ℂ) * (Real.pi : ℂ) * I * (k₂ : ℂ) := by
      have := hk
      field_simp at this
      linear_combination this
    have h2piI : (2 : ℂ) * (Real.pi : ℂ) * I ≠ 0 := two_pi_I_ne_zero
    exact mul_left_cancel₀ h2piI h1
  exact_mod_cast h_cast

#print axioms extraFamily_injective

end PrincipiaTractalis.DirichletEtaExtraFamilyStructure_2026_11_18
