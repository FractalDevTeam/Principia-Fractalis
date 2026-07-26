import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s09c09 : (0.0014108557 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.8725 + 0.005 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0014108557 : _root_.Interval))
    (nodeFold 3 (1.8725 : _root_.Interval) (0.005 : _root_.Interval))
    (0.0014108557 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.8725 + 0.005 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.8725 0.005 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s09c10 : (0.0019258011 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.8875 + 0.005 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0019258011 : _root_.Interval))
    (nodeFold 3 (1.8875 : _root_.Interval) (0.005 : _root_.Interval))
    (0.0019258011 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.8875 + 0.005 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.8875 0.005 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s09c11 : (0.0023726647 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.9025 + 0.005 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0023726647 : _root_.Interval))
    (nodeFold 3 (1.9025 : _root_.Interval) (0.005 : _root_.Interval))
    (0.0023726647 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.9025 + 0.005 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.9025 0.005 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s09c12 : (0.0027560755 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.9175 + 0.005 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0027560755 : _root_.Interval))
    (nodeFold 3 (1.9175 : _root_.Interval) (0.005 : _root_.Interval))
    (0.0027560755 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.9175 + 0.005 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.9175 0.005 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
