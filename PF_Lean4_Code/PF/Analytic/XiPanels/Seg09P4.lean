import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s09c13 : (0.0030806036 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.9325 + 0.005 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0030806036 : _root_.Interval))
    (nodeFold 3 (1.9325 : _root_.Interval) (0.005 : _root_.Interval))
    (0.0030806036 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.9325 + 0.005 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.9325 0.005 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s09c14 : (0.0033507262 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.9475 + 0.005 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0033507262 : _root_.Interval))
    (nodeFold 3 (1.9475 : _root_.Interval) (0.005 : _root_.Interval))
    (0.0033507262 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.9475 + 0.005 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.9475 0.005 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s09c15 : (0.0035708003 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.9625 + 0.005 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0035708003 : _root_.Interval))
    (nodeFold 3 (1.9625 : _root_.Interval) (0.005 : _root_.Interval))
    (0.0035708003 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.9625 + 0.005 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.9625 0.005 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s09c16 : (0.0037450403 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.9775 + 0.005 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0037450403 : _root_.Interval))
    (nodeFold 3 (1.9775 : _root_.Interval) (0.005 : _root_.Interval))
    (0.0037450403 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.9775 + 0.005 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.9775 0.005 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
