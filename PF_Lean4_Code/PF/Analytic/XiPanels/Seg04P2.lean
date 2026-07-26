import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s04c05 : (-0.0022751681 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.2265625 + 0.003125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0022751681 : _root_.Interval))
    (nodeFold 3 (1.2265625 : _root_.Interval) (0.003125 : _root_.Interval))
    (-0.0022751681 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.2265625 + 0.003125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.2265625 0.003125 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s04c06 : (-0.0082803255 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.2359375 + 0.003125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0082803255 : _root_.Interval))
    (nodeFold 3 (1.2359375 : _root_.Interval) (0.003125 : _root_.Interval))
    (-0.0082803255 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.2359375 + 0.003125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.2359375 0.003125 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s04c07 : (-0.0086148898 : ℝ)
    ≤ ∑ i ∈ Finset.range 2, nodeR (1.2453125 + 0.003125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0086148898 : _root_.Interval))
    (nodeFold 2 (1.2453125 : _root_.Interval) (0.003125 : _root_.Interval))
    (-0.0086148898 : ℝ) (∑ i ∈ Finset.range 2, nodeR (1.2453125 + 0.003125 * (i : ℕ)))
    (by approx) (nodeFold_mem 2 1.2453125 0.003125 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
