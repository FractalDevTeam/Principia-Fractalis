import PF.DirichletEtaExtension_r269
import PF.DirichletEtaExtFilledNeZeroNearOne_2026_11_18
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Extra zeros of `dirichletEtaExt`

The analytic continuation `dirichletEtaExt s := (1 - 2^(1-s)) · ζ(s)`
of the Dirichlet eta function has zeros wherever the factor
`(1 - 2^(1-s))` vanishes — a family of zeros on the critical line
`Re s = 1` at `s = 1 + 2π i k / Complex.log 2` for `k ∈ ℤ`.

This file ships the pointwise fact in its cleanest form: for any
`s : ℂ` with `2^(1-s) = 1`, we have `dirichletEtaExt s = 0`. The
`k ≠ 0` restriction (so that `s ≠ 1`) is not needed for the identity
itself — at `s = 1` both sides are `0` (`dirichletEtaExt_eval_at_one`
from the 2026-11-16 disclosure).

Downstream: the zero-counting arguments on the Dirichlet-1858 chain
distinguish the "extra" zeros contributed by the factor from the
genuine zeros of `riemannZeta`; this identity pins the first family
precisely.

Three-axiom bar `[propext, Classical.choice, Quot.sound]`.
-/

namespace PrincipiaTractalis.DirichletEtaExtExtraZeros_2026_11_18

open PrincipiaTractalis.DirichletEtaExtension (dirichletEtaExt)
open PrincipiaTractalis.DirichletEtaExtFilledNeZeroNearOne_2026_11_18
  (Complex_log_two_ne_zero)

/-- **Extra-zero identity.** Whenever the factor `(1 - 2^(1-s))` vanishes,
    `dirichletEtaExt s = 0`. Pointwise, no `s ≠ 1` hypothesis needed. -/
theorem dirichletEtaExt_eq_zero_of_two_cpow_eq_one
    {s : ℂ} (h2 : (2 : ℂ) ^ (1 - s) = 1) :
    dirichletEtaExt s = 0 := by
  unfold PrincipiaTractalis.DirichletEtaExtension.dirichletEtaExt
  rw [h2, sub_self, zero_mul]

/-- **The extra-zero family.** For every integer `k`, the point
    `s_k = 1 + 2π i k / Complex.log 2` is a zero of `dirichletEtaExt`.

    These are the zeros contributed by the factor `(1 - 2^(1-s))` in
    the identity `η(s) = (1 - 2^(1-s)) · ζ(s)`. The family lives on
    the critical line `Re s = 1` (except for `k = 0`, where `s_0 = 1`
    and the value `0` holds by the direct `dirichletEtaExt_eval_at_one`
    computation). -/
theorem dirichletEtaExt_eq_zero_at_extra_family (k : ℤ) :
    dirichletEtaExt (1 + 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) /
                     Complex.log 2) = 0 := by
  apply dirichletEtaExt_eq_zero_of_two_cpow_eq_one
  have h2_ne : (2 : ℂ) ≠ 0 := by norm_num
  have hlog2_ne : Complex.log 2 ≠ 0 := Complex_log_two_ne_zero
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

#print axioms dirichletEtaExt_eq_zero_of_two_cpow_eq_one
#print axioms dirichletEtaExt_eq_zero_at_extra_family

end PrincipiaTractalis.DirichletEtaExtExtraZeros_2026_11_18
