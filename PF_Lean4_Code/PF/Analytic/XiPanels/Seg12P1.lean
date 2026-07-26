import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s12c01 : (0.0007609809 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.505 + 0.01 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0007609809 : _root_.Interval))
    (nodeFold 3 (2.505 : _root_.Interval) (0.01 : _root_.Interval))
    (0.0007609809 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.505 + 0.01 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.505 0.01 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s12c02 : (0.0006167744 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.535 + 0.01 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0006167744 : _root_.Interval))
    (nodeFold 3 (2.535 : _root_.Interval) (0.01 : _root_.Interval))
    (0.0006167744 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.535 + 0.01 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.535 0.01 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s12c03 : (0.0004897517 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.565 + 0.01 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0004897517 : _root_.Interval))
    (nodeFold 3 (2.565 : _root_.Interval) (0.01 : _root_.Interval))
    (0.0004897517 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.565 + 0.01 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.565 0.01 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s12c04 : (0.0003788865 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.595 + 0.01 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0003788865 : _root_.Interval))
    (nodeFold 3 (2.595 : _root_.Interval) (0.01 : _root_.Interval))
    (0.0003788865 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.595 + 0.01 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.595 0.01 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
