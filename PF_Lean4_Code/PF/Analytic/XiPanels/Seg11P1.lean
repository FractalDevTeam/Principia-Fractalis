import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s11c01 : (0.0026697826 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.25390625 + 0.0078125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0026697826 : _root_.Interval))
    (nodeFold 3 (2.25390625 : _root_.Interval) (0.0078125 : _root_.Interval))
    (0.0026697826 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.25390625 + 0.0078125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.25390625 0.0078125 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s11c02 : (0.0024533226 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.27734375 + 0.0078125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0024533226 : _root_.Interval))
    (nodeFold 3 (2.27734375 : _root_.Interval) (0.0078125 : _root_.Interval))
    (0.0024533226 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.27734375 + 0.0078125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.27734375 0.0078125 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s11c03 : (0.0022406094 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.30078125 + 0.0078125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0022406094 : _root_.Interval))
    (nodeFold 3 (2.30078125 : _root_.Interval) (0.0078125 : _root_.Interval))
    (0.0022406094 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.30078125 + 0.0078125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.30078125 0.0078125 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s11c04 : (0.0020339531 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.32421875 + 0.0078125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0020339531 : _root_.Interval))
    (nodeFold 3 (2.32421875 : _root_.Interval) (0.0078125 : _root_.Interval))
    (0.0020339531 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.32421875 + 0.0078125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.32421875 0.0078125 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
