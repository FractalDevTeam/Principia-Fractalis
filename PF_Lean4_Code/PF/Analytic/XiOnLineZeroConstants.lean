/-
# PF.Analytic.XiOnLineZeroConstants

Kernel-certified transcendental constants for the r120 B5 certificate,
via the vendored interval engine (`approx` + `Interval.approx_le` +
`decide +kernel`).  NO `native_decide`.
-/

import PF.Analytic.XiOnLineZeroCore
import Interval.Interval.Division

namespace PrincipiaTractalis.XiOnLineZeroConstants

open scoped Real

set_option maxRecDepth 400000

/-- `exp (-π·1) ≤ 0.04321392` -/
theorem e0_01 : Real.exp (-(π * 1)) ≤ 0.04321392 := by
  refine _root_.Interval.approx_le
    (_root_.Interval.exp (-(_root_.Interval.pi * (1 : _root_.Interval))))
    ((0.04321392 : _root_.Interval)) (Real.exp (-(π * 1))) 0.04321392
    (by approx) (by approx) ?_
  decide +kernel

/-- `exp (-π·1.0625) ≤ 0.03550996` -/
theorem e0_02 : Real.exp (-(π * 1.0625)) ≤ 0.03550996 := by
  refine _root_.Interval.approx_le
    (_root_.Interval.exp (-(_root_.Interval.pi * (1.0625 : _root_.Interval))))
    ((0.03550996 : _root_.Interval)) (Real.exp (-(π * 1.0625))) 0.03550996
    (by approx) (by approx) ?_
  decide +kernel

/-- `exp (-π·1.125) ≤ 0.02917942` -/
theorem e0_03 : Real.exp (-(π * 1.125)) ≤ 0.02917942 := by
  refine _root_.Interval.approx_le
    (_root_.Interval.exp (-(_root_.Interval.pi * (1.125 : _root_.Interval))))
    ((0.02917942 : _root_.Interval)) (Real.exp (-(π * 1.125))) 0.02917942
    (by approx) (by approx) ?_
  decide +kernel

/-- `exp (-π·1.1875) ≤ 0.02397746` -/
theorem e0_04 : Real.exp (-(π * 1.1875)) ≤ 0.02397746 := by
  refine _root_.Interval.approx_le
    (_root_.Interval.exp (-(_root_.Interval.pi * (1.1875 : _root_.Interval))))
    ((0.02397746 : _root_.Interval)) (Real.exp (-(π * 1.1875))) 0.02397746
    (by approx) (by approx) ?_
  decide +kernel

/-- `exp (-π·1.25) ≤ 0.01970288` -/
theorem e0_05 : Real.exp (-(π * 1.25)) ≤ 0.01970288 := by
  refine _root_.Interval.approx_le
    (_root_.Interval.exp (-(_root_.Interval.pi * (1.25 : _root_.Interval))))
    ((0.01970288 : _root_.Interval)) (Real.exp (-(π * 1.25))) 0.01970288
    (by approx) (by approx) ?_
  decide +kernel

/-- `exp (-π·1.375) ≤ 0.01330401` -/
theorem e0_06 : Real.exp (-(π * 1.375)) ≤ 0.01330401 := by
  refine _root_.Interval.approx_le
    (_root_.Interval.exp (-(_root_.Interval.pi * (1.375 : _root_.Interval))))
    ((0.01330401 : _root_.Interval)) (Real.exp (-(π * 1.375))) 0.01330401
    (by approx) (by approx) ?_
  decide +kernel

/-- `exp (-π·1.5) ≤ 0.0089833` -/
theorem e0_07 : Real.exp (-(π * 1.5)) ≤ 0.0089833 := by
  refine _root_.Interval.approx_le
    (_root_.Interval.exp (-(_root_.Interval.pi * (1.5 : _root_.Interval))))
    ((0.0089833 : _root_.Interval)) (Real.exp (-(π * 1.5))) 0.0089833
    (by approx) (by approx) ?_
  decide +kernel

/-- `exp (-π·1.625) ≤ 0.00606581` -/
theorem e0_08 : Real.exp (-(π * 1.625)) ≤ 0.00606581 := by
  refine _root_.Interval.approx_le
    (_root_.Interval.exp (-(_root_.Interval.pi * (1.625 : _root_.Interval))))
    ((0.00606581 : _root_.Interval)) (Real.exp (-(π * 1.625))) 0.00606581
    (by approx) (by approx) ?_
  decide +kernel

/-- `exp (-π·1.75) ≤ 0.00409583` -/
theorem e0_09 : Real.exp (-(π * 1.75)) ≤ 0.00409583 := by
  refine _root_.Interval.approx_le
    (_root_.Interval.exp (-(_root_.Interval.pi * (1.75 : _root_.Interval))))
    ((0.00409583 : _root_.Interval)) (Real.exp (-(π * 1.75))) 0.00409583
    (by approx) (by approx) ?_
  decide +kernel

/-- `exp (-π·2) ≤ 0.00186745` -/
theorem e0_10 : Real.exp (-(π * 2)) ≤ 0.00186745 := by
  refine _root_.Interval.approx_le
    (_root_.Interval.exp (-(_root_.Interval.pi * (2 : _root_.Interval))))
    ((0.00186745 : _root_.Interval)) (Real.exp (-(π * 2))) 0.00186745
    (by approx) (by approx) ?_
  decide +kernel

/-- `exp (-π·2.25) ≤ 0.00085144` -/
theorem e0_11 : Real.exp (-(π * 2.25)) ≤ 0.00085144 := by
  refine _root_.Interval.approx_le
    (_root_.Interval.exp (-(_root_.Interval.pi * (2.25 : _root_.Interval))))
    ((0.00085144 : _root_.Interval)) (Real.exp (-(π * 2.25))) 0.00085144
    (by approx) (by approx) ?_
  decide +kernel

/-- `exp (-π·2.5) ≤ 0.00038821` -/
theorem e0_12 : Real.exp (-(π * 2.5)) ≤ 0.00038821 := by
  refine _root_.Interval.approx_le
    (_root_.Interval.exp (-(_root_.Interval.pi * (2.5 : _root_.Interval))))
    ((0.00038821 : _root_.Interval)) (Real.exp (-(π * 2.5))) 0.00038821
    (by approx) (by approx) ?_
  decide +kernel

/-- `exp (-π·3) ≤ 0.0000807` -/
theorem e0_13 : Real.exp (-(π * 3)) ≤ 0.0000807 := by
  refine _root_.Interval.approx_le
    (_root_.Interval.exp (-(_root_.Interval.pi * (3 : _root_.Interval))))
    ((0.0000807 : _root_.Interval)) (Real.exp (-(π * 3))) 0.0000807
    (by approx) (by approx) ?_
  decide +kernel

/-- `exp (-π·4) ≤ 0.00000349` -/
theorem e0_14 : Real.exp (-(π * 4)) ≤ 0.00000349 := by
  refine _root_.Interval.approx_le
    (_root_.Interval.exp (-(_root_.Interval.pi * (4 : _root_.Interval))))
    ((0.00000349 : _root_.Interval)) (Real.exp (-(π * 4))) 0.00000349
    (by approx) (by approx) ?_
  decide +kernel

/-- `exp (-π) ≤ 0.04321392` -/
theorem exp_neg_pi_le : Real.exp (-π) ≤ 0.04321392 := by
  have h := e0_01
  rw [show -(π * 1) = -π from by ring] at h
  exact h

/-- The `T = 5` tail bound of `Xi_tail_bound` is below `1.1e-7`. -/
theorem tail_le : 2 / π * Real.exp (-π * 5) / (1 - Real.exp (-π)) ≤ 0.00000011 := by
  refine _root_.Interval.approx_le
    ((2 : _root_.Interval) / _root_.Interval.pi
      * _root_.Interval.exp (-_root_.Interval.pi * (5 : _root_.Interval))
      / ((1 : _root_.Interval) - _root_.Interval.exp (-_root_.Interval.pi)))
    ((0.00000011 : _root_.Interval))
    (2 / π * Real.exp (-π * 5) / (1 - Real.exp (-π))) 0.00000011
    (by approx) (by approx) ?_
  decide +kernel

/-- The `T = 1` tail bound of `Xi_tail_bound` is below `0.03`. -/
theorem tail1_le : 2 / π * Real.exp (-π * 1) / (1 - Real.exp (-π)) ≤ 0.03 := by
  refine _root_.Interval.approx_le
    ((2 : _root_.Interval) / _root_.Interval.pi
      * _root_.Interval.exp (-_root_.Interval.pi * (1 : _root_.Interval))
      / ((1 : _root_.Interval) - _root_.Interval.exp (-_root_.Interval.pi)))
    ((0.03 : _root_.Interval))
    (2 / π * Real.exp (-π * 1) / (1 - Real.exp (-π))) 0.03
    (by approx) (by approx) ?_
  decide +kernel

end PrincipiaTractalis.XiOnLineZeroConstants
