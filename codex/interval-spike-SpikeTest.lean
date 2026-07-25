import Interval

/-!
Spike test: can end-to-end concrete inequalities be certified with kernel
reduction only (decide +kernel), keeping axioms = [propext, Classical.choice, Quot.sound]?
-/

open scoped Real

-- Test 1: constant comparison (cheap): pi < 3.15
theorem spike_pi_lt : (π : ℝ) < 3.15 := by
  refine Interval.approx_lt Interval.pi ((3.15 : Interval)) π 3.15
    Interval.approx_pi (by approx) ?_
  decide +kernel

#print axioms spike_pi_lt

-- Test 2: one exp evaluation: 2.7 < exp 1
theorem spike_exp_one : (2.7 : ℝ) < Real.exp 1 := by
  refine Interval.approx_lt ((2.7 : Interval)) ((1 : Interval).exp) 2.7 (Real.exp 1)
    (by approx) (Interval.approx_exp (by approx)) ?_
  decide +kernel

#print axioms spike_exp_one

-- Test 3: small sum of transcendental evaluations (scaling probe)
-- exp 1 + exp (1/2) + exp (1/3) = 5.76261...
theorem spike_exp_sum :
    (5.76 : ℝ) < Real.exp 1 + Real.exp (1/2) + Real.exp (1/3) := by
  refine Interval.approx_lt ((5.76 : Interval))
    ((1 : Interval).exp + (Interval.ofRat (1/2)).exp + (Interval.ofRat (1/3)).exp)
    5.76 (Real.exp 1 + Real.exp (1/2) + Real.exp (1/3))
    (by approx) (by approx) ?_
  decide +kernel

#print axioms spike_exp_sum

-- Test 4: cos (integrand needs cos/sin of real args): cos 1 < 0.5404
theorem spike_cos_one : Real.cos 1 < 0.5404 := by
  refine Interval.approx_lt ((1 : Interval).cos) ((0.5404 : Interval))
    (Real.cos 1) 0.5404 (Interval.approx_cos (by approx)) (by approx) ?_
  decide +kernel

#print axioms spike_cos_one
