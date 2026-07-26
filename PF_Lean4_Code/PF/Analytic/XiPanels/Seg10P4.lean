import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s10c13 : (0.0029232209 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.228125 + 0.00625 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0029232209 : _root_.Interval))
    (nodeFold 3 (2.228125 : _root_.Interval) (0.00625 : _root_.Interval))
    (0.0029232209 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.228125 + 0.00625 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.228125 0.00625 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s10c14 : (0.0009357916 : ℝ)
    ≤ ∑ i ∈ Finset.range 1, nodeR (2.246875 + 0.00625 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0009357916 : _root_.Interval))
    (nodeFold 1 (2.246875 : _root_.Interval) (0.00625 : _root_.Interval))
    (0.0009357916 : ℝ) (∑ i ∈ Finset.range 1, nodeR (2.246875 + 0.00625 * (i : ℕ)))
    (by approx) (nodeFold_mem 1 2.246875 0.00625 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
