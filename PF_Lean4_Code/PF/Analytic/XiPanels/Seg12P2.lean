import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s12c05 : (0.000283027 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.625 + 0.01 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.000283027 : _root_.Interval))
    (nodeFold 3 (2.625 : _root_.Interval) (0.01 : _root_.Interval))
    (0.000283027 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.625 + 0.01 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.625 0.01 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s12c06 : (0.0002009506 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.655 + 0.01 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0002009506 : _root_.Interval))
    (nodeFold 3 (2.655 : _root_.Interval) (0.01 : _root_.Interval))
    (0.0002009506 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.655 + 0.01 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.655 0.01 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s12c07 : (0.0001314081 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.685 + 0.01 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0001314081 : _root_.Interval))
    (nodeFold 3 (2.685 : _root_.Interval) (0.01 : _root_.Interval))
    (0.0001314081 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.685 + 0.01 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.685 0.01 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s12c08 : (0.0000731575 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.715 + 0.01 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0000731575 : _root_.Interval))
    (nodeFold 3 (2.715 : _root_.Interval) (0.01 : _root_.Interval))
    (0.0000731575 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.715 + 0.01 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.715 0.01 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
