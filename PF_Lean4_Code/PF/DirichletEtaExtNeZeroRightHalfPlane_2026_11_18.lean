import PF.DirichletEtaExtZerosCharacterization_2026_11_18
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# `dirichletEtaExt` has no zeros on `Re s > 1`

For `Re s > 1`, both ingredients of `dirichletEtaExt s = (1 - 2^(1-s))·ζ(s)`
are nonzero:

  * `riemannZeta s ≠ 0` (mathlib's `riemannZeta_ne_zero_of_one_lt_re`,
    via the Euler product).
  * `(1 - 2^(1-s)) ≠ 0` because `‖2^(1-s)‖ = 2^(1 - Re s) < 1` strictly
    on `Re s > 1`, so `2^(1-s) ≠ 1`.

Hence `dirichletEtaExt s ≠ 0` on the entire open right half-plane
`{s : 1 < Re s}`.

Three-axiom bar `[propext, Classical.choice, Quot.sound]`.

Downstream: this nails that all nontrivial zeros of the eta extension
lie in `Re s ≤ 1`, which is the standard entry point for critical-line
arguments.
-/

namespace PrincipiaTractalis.DirichletEtaExtNeZeroRightHalfPlane_2026_11_18

open PrincipiaTractalis.DirichletEtaExtension (dirichletEtaExt)
open PrincipiaTractalis.DirichletEtaExtZerosCharacterization_2026_11_18
  (dirichletEtaExt_eq_zero_iff)

/-- `(2 : ℂ)^(1-s) ≠ 1` whenever `1 < Re s`. -/
theorem two_cpow_ne_one_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    (2 : ℂ) ^ (1 - s) ≠ 1 := by
  intro h
  have hnorm_one : ‖(2 : ℂ) ^ (1 - s)‖ = 1 := by rw [h]; simp
  have hrpow : ‖(2 : ℂ) ^ (1 - s)‖ = (2 : ℝ) ^ (1 - s).re := by
    have h_cast : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_cast
    rw [← h_cast, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hre : (1 - s).re = 1 - s.re := by simp [Complex.sub_re, Complex.one_re]
  rw [hrpow, hre] at hnorm_one
  have hneg : 1 - s.re < 0 := by linarith
  have h2gt1 : (1 : ℝ) < 2 := by norm_num
  have hlt_one : (2 : ℝ) ^ (1 - s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg h2gt1 hneg
  linarith

/-- **Headline.** `dirichletEtaExt` is nonzero on the right half-plane
    `Re s > 1`. -/
theorem dirichletEtaExt_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    dirichletEtaExt s ≠ 0 := by
  intro h
  rcases (dirichletEtaExt_eq_zero_iff s).mp h with hfact | hzeta
  · exact two_cpow_ne_one_of_one_lt_re hs hfact
  · exact riemannZeta_ne_zero_of_one_lt_re hs hzeta

#print axioms two_cpow_ne_one_of_one_lt_re
#print axioms dirichletEtaExt_ne_zero_of_one_lt_re

end PrincipiaTractalis.DirichletEtaExtNeZeroRightHalfPlane_2026_11_18
