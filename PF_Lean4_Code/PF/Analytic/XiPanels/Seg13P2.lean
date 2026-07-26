import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s13c05 : (-0.0000815089 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (3.25 + 0.02 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0000815089 : _root_.Interval))
    (nodeFold 3 (3.25 : _root_.Interval) (0.02 : _root_.Interval))
    (-0.0000815089 : ℝ) (∑ i ∈ Finset.range 3, nodeR (3.25 + 0.02 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 3.25 0.02 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s13c06 : (-0.0000688741 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (3.31 + 0.02 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0000688741 : _root_.Interval))
    (nodeFold 3 (3.31 : _root_.Interval) (0.02 : _root_.Interval))
    (-0.0000688741 : ℝ) (∑ i ∈ Finset.range 3, nodeR (3.31 + 0.02 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 3.31 0.02 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s13c07 : (-0.0000570474 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (3.37 + 0.02 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0000570474 : _root_.Interval))
    (nodeFold 3 (3.37 : _root_.Interval) (0.02 : _root_.Interval))
    (-0.0000570474 : ℝ) (∑ i ∈ Finset.range 3, nodeR (3.37 + 0.02 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 3.37 0.02 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s13c08 : (-0.0000463904 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (3.43 + 0.02 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0000463904 : _root_.Interval))
    (nodeFold 3 (3.43 : _root_.Interval) (0.02 : _root_.Interval))
    (-0.0000463904 : ℝ) (∑ i ∈ Finset.range 3, nodeR (3.43 + 0.02 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 3.43 0.02 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
