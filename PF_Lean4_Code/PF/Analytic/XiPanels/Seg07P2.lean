import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s07c05 : (-0.0318403794 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.548828125 + 0.00390625 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0318403794 : _root_.Interval))
    (nodeFold 3 (1.548828125 : _root_.Interval) (0.00390625 : _root_.Interval))
    (-0.0318403794 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.548828125 + 0.00390625 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.548828125 0.00390625 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s07c06 : (-0.030021801 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.560546875 + 0.00390625 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.030021801 : _root_.Interval))
    (nodeFold 3 (1.560546875 : _root_.Interval) (0.00390625 : _root_.Interval))
    (-0.030021801 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.560546875 + 0.00390625 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.560546875 0.00390625 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s07c07 : (-0.0282087677 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.572265625 + 0.00390625 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0282087677 : _root_.Interval))
    (nodeFold 3 (1.572265625 : _root_.Interval) (0.00390625 : _root_.Interval))
    (-0.0282087677 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.572265625 + 0.00390625 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.572265625 0.00390625 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s07c08 : (-0.0264113809 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.583984375 + 0.00390625 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0264113809 : _root_.Interval))
    (nodeFold 3 (1.583984375 : _root_.Interval) (0.00390625 : _root_.Interval))
    (-0.0264113809 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.583984375 + 0.00390625 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.583984375 0.00390625 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
