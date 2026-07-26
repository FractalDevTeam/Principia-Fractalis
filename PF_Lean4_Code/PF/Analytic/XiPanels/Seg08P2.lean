import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s08c05 : (-0.0121777078 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.6875 + 0.005 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0121777078 : _root_.Interval))
    (nodeFold 3 (1.6875 : _root_.Interval) (0.005 : _root_.Interval))
    (-0.0121777078 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.6875 + 0.005 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.6875 0.005 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s08c06 : (-0.0105062559 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.7025 + 0.005 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0105062559 : _root_.Interval))
    (nodeFold 3 (1.7025 : _root_.Interval) (0.005 : _root_.Interval))
    (-0.0105062559 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.7025 + 0.005 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.7025 0.005 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s08c07 : (-0.0089401029 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.7175 + 0.005 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0089401029 : _root_.Interval))
    (nodeFold 3 (1.7175 : _root_.Interval) (0.005 : _root_.Interval))
    (-0.0089401029 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.7175 + 0.005 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.7175 0.005 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s08c08 : (-0.0074798121 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.7325 + 0.005 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0074798121 : _root_.Interval))
    (nodeFold 3 (1.7325 : _root_.Interval) (0.005 : _root_.Interval))
    (-0.0074798121 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.7325 + 0.005 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.7325 0.005 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
