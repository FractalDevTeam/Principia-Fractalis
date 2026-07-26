import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s09c05 : (-0.0014219834 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.8125 + 0.005 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0014219834 : _root_.Interval))
    (nodeFold 3 (1.8125 : _root_.Interval) (0.005 : _root_.Interval))
    (-0.0014219834 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.8125 + 0.005 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.8125 0.005 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s09c06 : (-0.0005887706 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.8275 + 0.005 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0005887706 : _root_.Interval))
    (nodeFold 3 (1.8275 : _root_.Interval) (0.005 : _root_.Interval))
    (-0.0005887706 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.8275 + 0.005 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.8275 0.005 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s09c07 : (0.0001581512 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.8425 + 0.005 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0001581512 : _root_.Interval))
    (nodeFold 3 (1.8425 : _root_.Interval) (0.005 : _root_.Interval))
    (0.0001581512 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.8425 + 0.005 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.8425 0.005 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s09c08 : (0.0008231797 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.8575 + 0.005 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0008231797 : _root_.Interval))
    (nodeFold 3 (1.8575 : _root_.Interval) (0.005 : _root_.Interval))
    (0.0008231797 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.8575 + 0.005 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.8575 0.005 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
