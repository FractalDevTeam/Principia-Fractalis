import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s02c01 : (0.1766941604 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.06375 + 0.0025 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.1766941604 : _root_.Interval))
    (nodeFold 3 (1.06375 : _root_.Interval) (0.0025 : _root_.Interval))
    (0.1766941604 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.06375 + 0.0025 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.06375 0.0025 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s02c02 : (0.1664391394 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.07125 + 0.0025 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.1664391394 : _root_.Interval))
    (nodeFold 3 (1.07125 : _root_.Interval) (0.0025 : _root_.Interval))
    (0.1664391394 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.07125 + 0.0025 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.07125 0.0025 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s02c03 : (0.1561992347 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.07875 + 0.0025 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.1561992347 : _root_.Interval))
    (nodeFold 3 (1.07875 : _root_.Interval) (0.0025 : _root_.Interval))
    (0.1561992347 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.07875 + 0.0025 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.07875 0.0025 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s02c04 : (0.1460173642 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.08625 + 0.0025 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.1460173642 : _root_.Interval))
    (nodeFold 3 (1.08625 : _root_.Interval) (0.0025 : _root_.Interval))
    (0.1460173642 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.08625 + 0.0025 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.08625 0.0025 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
