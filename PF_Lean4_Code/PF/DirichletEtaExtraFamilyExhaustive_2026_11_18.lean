import PF.DirichletEtaExtraFamilyStructure_2026_11_18
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The extra-zero family of `dirichletEtaExt` is exhaustive

Shows that `(2 : ℂ)^(1-s) = 1` holds **iff** `s` is in the
`extraFamily` image — the family

    `s_k = 1 + 2π i k / Complex.log 2`,  `k ∈ ℤ`

exhausts every point where the factor of the eta extension vanishes.

The forward direction `2^(1-s) = 1 ⟹ ∃ k, s = s_k` uses mathlib's
`Complex.exp_eq_one_iff : exp x = 1 ↔ ∃ n : ℤ, x = n·(2π I)` combined
with `cpow_def_of_ne_zero`. The backward direction was proved in
`DirichletEtaExtExtraZeros_2026_11_18` (applied through
`extraFamily` + `dirichletEtaExt_eq_zero_of_two_cpow_eq_one`).

Three-axiom bar `[propext, Classical.choice, Quot.sound]`.

Combined with today's full iff characterization of `dirichletEtaExt`
zeros, the pointwise structure is now:

```
dirichletEtaExt s = 0
  ↔ (∃ k : ℤ, s = extraFamily k) ∨ riemannZeta s = 0
```

— a clean, mutually exclusive partition (the extra family is disjoint
from ζ-zeros, since ζ has only a pole at `s = 1` and ζ has no zeros on
`Re s = 1` where the family lives, by the classical zeta-nonzero result).
-/

namespace PrincipiaTractalis.DirichletEtaExtraFamilyExhaustive_2026_11_18

open Complex
open PrincipiaTractalis.DirichletEtaExtraFamilyStructure_2026_11_18
  (extraFamily)

/-- Local alias: `Complex.log 2 ≠ 0`. -/
private theorem complex_log_two_ne_zero_local : Complex.log 2 ≠ 0 := by
  intro h
  have hre : (Complex.log 2).re = Real.log 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from by norm_num, Complex.log_ofReal_re]
  have : (Complex.log 2).re = 0 := by rw [h]; simp
  rw [hre] at this
  have hpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  linarith

/-- **Forward direction.** If `(2 : ℂ)^(1-s) = 1`, then `s = 1 + 2π I k / log 2`
    for some integer `k`. -/
theorem exists_extraFamily_of_two_cpow_eq_one
    {s : ℂ} (h2 : (2 : ℂ) ^ (1 - s) = 1) :
    ∃ k : ℤ, s = extraFamily k := by
  have h2_ne : (2 : ℂ) ≠ 0 := by norm_num
  have hlog_ne : Complex.log 2 ≠ 0 := complex_log_two_ne_zero_local
  -- Unfold the cpow.
  rw [Complex.cpow_def_of_ne_zero h2_ne] at h2
  -- `exp (log 2 * (1 - s)) = 1` ⟹ `log 2 * (1 - s) = n · (2π I)` for some n.
  rcases Complex.exp_eq_one_iff.mp h2 with ⟨n, hn⟩
  -- `s = 1 - (n · 2π I) / log 2 = 1 + 2π I · (-n) / log 2`
  use -n
  -- Isolate s from hn.
  have h_sub_s : (1 : ℂ) - s = (n : ℂ) * (2 * (Real.pi : ℂ) * I) / Complex.log 2 := by
    have := hn
    field_simp at this ⊢
    linear_combination this
  unfold extraFamily
  have : s = (1 : ℂ) - (n : ℂ) * (2 * (Real.pi : ℂ) * I) / Complex.log 2 := by
    linear_combination -h_sub_s
  rw [this]
  push_cast
  field_simp
  ring

/-- **Biconditional form.** `(2 : ℂ)^(1-s) = 1` iff `s` is in the
    extra-family image. -/
theorem two_cpow_eq_one_iff_mem_extraFamily (s : ℂ) :
    (2 : ℂ) ^ (1 - s) = 1 ↔ ∃ k : ℤ, s = extraFamily k := by
  constructor
  · exact exists_extraFamily_of_two_cpow_eq_one
  · rintro ⟨k, rfl⟩
    -- Need: (2 : ℂ)^(1 - extraFamily k) = 1.
    have h2_ne : (2 : ℂ) ≠ 0 := by norm_num
    have hlog_ne : Complex.log 2 ≠ 0 := complex_log_two_ne_zero_local
    unfold extraFamily
    rw [Complex.cpow_def_of_ne_zero h2_ne]
    have hsimp :
        Complex.log 2 *
          ((1 : ℂ) - (1 + 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) / Complex.log 2)) =
        (-k : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      field_simp
      push_cast
      ring
    rw [hsimp]
    exact Complex.exp_int_mul_two_pi_mul_I (-k)

#print axioms exists_extraFamily_of_two_cpow_eq_one
#print axioms two_cpow_eq_one_iff_mem_extraFamily

end PrincipiaTractalis.DirichletEtaExtraFamilyExhaustive_2026_11_18
