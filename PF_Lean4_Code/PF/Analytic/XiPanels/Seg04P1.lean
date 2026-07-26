import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s04c01 : (0.0267966883 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.1890625 + 0.003125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0267966883 : _root_.Interval))
    (nodeFold 3 (1.1890625 : _root_.Interval) (0.003125 : _root_.Interval))
    (0.0267966883 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.1890625 + 0.003125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.1890625 0.003125 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s04c02 : (0.0187604928 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.1984375 + 0.003125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0187604928 : _root_.Interval))
    (nodeFold 3 (1.1984375 : _root_.Interval) (0.003125 : _root_.Interval))
    (0.0187604928 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.1984375 + 0.003125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.1984375 0.003125 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s04c03 : (0.0112385484 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.2078125 + 0.003125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0112385484 : _root_.Interval))
    (nodeFold 3 (1.2078125 : _root_.Interval) (0.003125 : _root_.Interval))
    (0.0112385484 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.2078125 + 0.003125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.2078125 0.003125 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s04c04 : (0.0042284552 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.2171875 + 0.003125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0042284552 : _root_.Interval))
    (nodeFold 3 (1.2171875 : _root_.Interval) (0.003125 : _root_.Interval))
    (0.0042284552 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.2171875 + 0.003125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.2171875 0.003125 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
