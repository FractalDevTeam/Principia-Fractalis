/-
# PF.Collapse.RateModulation

Step 2 of the objective-collapse program: a finite-dimensional stochastic
collapse step, with the theorems that decide whether "rate modulation" is a
coherent route, and the counterexample that constrains it.

## What this settles

The question was whether a quantity can be physically active in collapse
*without* biasing outcomes — by modulating the collapse rate instead.

1. `collapse_conditional_eq_born` — conditional on a collapse having occurred,
   the outcome distribution is exactly the Born distribution, for every nonzero
   rate. A rate-modulating theory does not disturb Born statistics, so rate
   modulation is coherent.

2. `collapse_ratio_rate_independent` — the ratio of any two outcome
   probabilities is independent of the rate. No measurement of relative outcome
   frequencies can reveal the rate; it must be sought in timing
   (coherence-loss) observables. This is what makes the route testable in
   principle but silent in outcome data.

3. `state_dependent_rate_not_affine` — if the rate may depend on the state
   through a nonlinear functional (here purity), the induced map on mixtures is
   NOT affine, with an explicit two-outcome witness: 1/4 against 1/2. This is
   the Gisin/Polchinski hazard — nonlinear evolution on density matrices
   generically permits superluminal signalling — so it is the precise point at
   which a rate law stops being admissible.

4. `constant_rate_is_affine` — a rate not depending on the state does commute
   with mixing. The admissible shape.

## The constraint this puts on the framework

(3) is not a technicality. A collapse rate may depend on local field or
geometric data — a mass density, a field amplitude — without harm. A rate
depending on an ENTANGLEMENT MEASURE OF THE STATE is exactly the forbidden
case, and the framework's `1 - Tr(rho_A^2)` reading of `ch_2` is such a measure.
That reading is therefore ruled out as a collapse-rate argument, while the
field/geometric readings survive.

## Hypothesis discipline

Every hypothesis is used. The probability data is passed unbundled — a function
`p`, with the normalisation hypothesis supplied only where normalisation is
actually consumed, and omitted where it is not — rather than as a structure
carrying a positivity field no proof uses. Nothing assumes more than it needs.

## Status

NOT a model of consciousness, and nothing here derives a rate. This is the
admissibility skeleton: which shapes of rate law are allowed, before any physics
is chosen. Imports are mathlib-only.
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

namespace PrincipiaTractalis.Collapse

open Finset

/-- One step of a rate-`lam` collapse channel, read on the measurement diagonal:
    with probability `lam` the state collapses, and conditionally on collapsing
    it yields outcome `i` with Born probability `p i`. The unconditional
    probability that the step produces outcome `i` is `lam * p i`. -/
def stepOutcome {n : Type*} (lam : ℝ) (p : n → ℝ) (i : n) : ℝ := lam * p i

/-- The total probability that a step collapses at all is `lam`. Consumes
    normalisation, and nothing else. -/
theorem sum_stepOutcome {n : Type*} [Fintype n] (lam : ℝ) (p : n → ℝ)
    (hsum : ∑ i, p i = 1) :
    ∑ i, stepOutcome lam p i = lam := by
  unfold stepOutcome
  rw [← Finset.mul_sum, hsum, mul_one]

/-- **Born statistics survive rate modulation.** Conditional on a collapse
    having occurred, the outcome distribution is exactly Born, for every nonzero
    rate. -/
theorem collapse_conditional_eq_born {n : Type*} [Fintype n] (lam : ℝ)
    (hlam : lam ≠ 0) (p : n → ℝ) (hsum : ∑ i, p i = 1) (i : n) :
    stepOutcome lam p i / (∑ j, stepOutcome lam p j) = p i := by
  rw [sum_stepOutcome lam p hsum]
  unfold stepOutcome
  field_simp

/-- **The rate is invisible to outcome ratios.** No measurement of relative
    outcome frequencies can reveal `lam`; it must be sought in timing. Needs
    neither normalisation nor positivity — the cancellation alone. -/
theorem collapse_ratio_rate_independent {n : Type*} (lam lam' : ℝ)
    (hlam : lam ≠ 0) (hlam' : lam' ≠ 0) (p : n → ℝ) (i j : n) :
    stepOutcome lam p i / stepOutcome lam p j
      = stepOutcome lam' p i / stepOutcome lam' p j := by
  unfold stepOutcome
  rw [mul_div_mul_left _ _ hlam, mul_div_mul_left _ _ hlam']

/-- **A rate independent of the state commutes with mixing** — the admissible
    shape of a rate law. Pure algebra: no hypothesis on `p`, `q` or `t`. -/
theorem constant_rate_is_affine {n : Type*} (lam t : ℝ) (p q : n → ℝ) (i : n) :
    lam * (t * p i + (1 - t) * q i)
      = t * stepOutcome lam p i + (1 - t) * stepOutcome lam q i := by
  unfold stepOutcome
  ring

/-- Purity — a nonlinear functional of the state, standing in for any
    entanglement-type measure. -/
def purity {n : Type*} [Fintype n] (p : n → ℝ) : ℝ := ∑ i, (p i) ^ 2

/-! ### The admissibility counterexample

Two outcomes: `pt0` certain of outcome 0, `pt1` certain of outcome 1, `mixHalf`
their even mixture. If the rate is the state's own purity, the step map fails to
commute with mixing. -/

/-- Point mass on outcome `0`. -/
def pt0 : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0

/-- Point mass on outcome `1`. -/
def pt1 : Fin 2 → ℝ := fun i => if i = 0 then 0 else 1

/-- The even mixture of `pt0` and `pt1`. -/
noncomputable def mixHalf : Fin 2 → ℝ := fun _ => 1 / 2

theorem pt0_sum : ∑ i, pt0 i = 1 := by
  norm_num [pt0, Fin.sum_univ_two]

theorem pt1_sum : ∑ i, pt1 i = 1 := by
  norm_num [pt1, Fin.sum_univ_two]

theorem mixHalf_sum : ∑ i, mixHalf i = 1 := by
  norm_num [mixHalf, Fin.sum_univ_two]

/-- `mixHalf` really is the even mixture, pointwise. -/
theorem mixHalf_eq_mix (i : Fin 2) :
    mixHalf i = (1 / 2) * pt0 i + (1 / 2) * pt1 i := by
  unfold mixHalf pt0 pt1
  by_cases h : i = 0 <;> simp [h]

theorem purity_pt0 : purity pt0 = 1 := by
  norm_num [purity, pt0, Fin.sum_univ_two]

theorem purity_pt1 : purity pt1 = 1 := by
  norm_num [purity, pt1, Fin.sum_univ_two]

theorem purity_mixHalf : purity mixHalf = 1 / 2 := by
  norm_num [purity, mixHalf, Fin.sum_univ_two]

/-- **A state-dependent rate is not affine.** With the rate taken to be the
    state's own purity, one step on the even mixture yields outcome `0` with
    probability `1/4`, whereas mixing the two pure-state results gives `1/2`.
    The step map does not commute with mixing — the nonlinearity that makes such
    a rate law inadmissible. -/
theorem state_dependent_rate_not_affine :
    stepOutcome (purity mixHalf) mixHalf 0
      ≠ (1 / 2) * stepOutcome (purity pt0) pt0 0
        + (1 / 2) * stepOutcome (purity pt1) pt1 0 := by
  rw [purity_mixHalf, purity_pt0, purity_pt1]
  unfold stepOutcome mixHalf pt0 pt1
  norm_num

/-- The two sides, for the record: `1/4` against `1/2`. -/
theorem state_dependent_rate_gap :
    stepOutcome (purity mixHalf) mixHalf 0 = 1 / 4 ∧
    (1 / 2) * stepOutcome (purity pt0) pt0 0
      + (1 / 2) * stepOutcome (purity pt1) pt1 0 = 1 / 2 := by
  refine ⟨?_, ?_⟩
  · rw [purity_mixHalf]; unfold stepOutcome mixHalf; norm_num
  · rw [purity_pt0, purity_pt1]; unfold stepOutcome pt0 pt1; norm_num

/-! ## Axiom report -/

#print axioms sum_stepOutcome
#print axioms collapse_conditional_eq_born
#print axioms collapse_ratio_rate_independent
#print axioms constant_rate_is_affine
#print axioms pt0_sum
#print axioms pt1_sum
#print axioms mixHalf_sum
#print axioms mixHalf_eq_mix
#print axioms purity_pt0
#print axioms purity_pt1
#print axioms purity_mixHalf
#print axioms state_dependent_rate_not_affine
#print axioms state_dependent_rate_gap

end PrincipiaTractalis.Collapse
