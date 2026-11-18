import PF.DirichletEtaExtFilledAnalytic_2026_11_18

/-!
# `dirichletEtaExtFilled` is nonzero in a neighbourhood of `s = 1`

Direct corollary of today's `AnalyticAt` upgrade: the filled extension
is continuous at `1`, its value there is `Complex.log 2 ≠ 0`, so by
mathlib's `ContinuousAt.eventually_ne` it stays away from `0` in a
neighbourhood.

In the η-ζ correspondence, this is the fact that the removable
singularity at `s = 1` is NOT a zero — which matters for downstream
zero-counting arguments (the critical line structure, Dirichlet-1858
residual).

Three-axiom bar `[propext, Classical.choice, Quot.sound]`.
-/

namespace PrincipiaTractalis.DirichletEtaExtFilledNeZeroNearOne_2026_11_18

open Complex Filter Topology
open PrincipiaTractalis.DirichletEtaExtDifferentiableAtOneDisclosure
  (dirichletEtaExtFilled dirichletEtaExtFilled_at_one)
open PrincipiaTractalis.DirichletEtaExtFilledAnalytic_2026_11_18
  (dirichletEtaExtFilled_analyticAt)

/-- `Complex.log 2 ≠ 0`. The real part is `Real.log 2 > 0`. -/
theorem Complex_log_two_ne_zero : Complex.log 2 ≠ 0 := by
  intro h
  have hre : (Complex.log 2).re = Real.log 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from by norm_num, Complex.log_ofReal_re]
  have : (Complex.log 2).re = 0 := by rw [h]; simp
  rw [hre] at this
  have hpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  linarith

/-- `dirichletEtaExtFilled 1 = Complex.log 2 ≠ 0`. -/
theorem dirichletEtaExtFilled_atOne_ne_zero : dirichletEtaExtFilled 1 ≠ 0 := by
  rw [dirichletEtaExtFilled_at_one]
  exact Complex_log_two_ne_zero

/-- **Headline.** `dirichletEtaExtFilled` is nonzero in a neighbourhood
    of `s = 1`. Immediate from continuity at `1` (via `AnalyticAt.continuousAt`)
    plus value `log 2 ≠ 0` at `1`, by mathlib's `ContinuousAt.eventually_ne`. -/
theorem dirichletEtaExtFilled_eventually_ne_zero_near_one :
    ∀ᶠ s in 𝓝 (1 : ℂ), dirichletEtaExtFilled s ≠ 0 :=
  (dirichletEtaExtFilled_analyticAt 1).continuousAt.eventually_ne
    dirichletEtaExtFilled_atOne_ne_zero

#print axioms Complex_log_two_ne_zero
#print axioms dirichletEtaExtFilled_atOne_ne_zero
#print axioms dirichletEtaExtFilled_eventually_ne_zero_near_one

end PrincipiaTractalis.DirichletEtaExtFilledNeZeroNearOne_2026_11_18
