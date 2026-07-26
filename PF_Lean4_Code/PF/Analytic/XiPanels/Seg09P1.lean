import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s09c01 : (-0.0056964276 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.7525 + 0.005 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0056964276 : _root_.Interval))
    (nodeFold 3 (1.7525 : _root_.Interval) (0.005 : _root_.Interval))
    (-0.0056964276 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.7525 + 0.005 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.7525 0.005 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s09c02 : (-0.0044796341 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.7675 + 0.005 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0044796341 : _root_.Interval))
    (nodeFold 3 (1.7675 : _root_.Interval) (0.005 : _root_.Interval))
    (-0.0044796341 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.7675 + 0.005 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.7675 0.005 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s09c03 : (-0.0033637199 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.7825 + 0.005 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0033637199 : _root_.Interval))
    (nodeFold 3 (1.7825 : _root_.Interval) (0.005 : _root_.Interval))
    (-0.0033637199 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.7825 + 0.005 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.7825 0.005 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s09c04 : (-0.0023456704 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.7975 + 0.005 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0023456704 : _root_.Interval))
    (nodeFold 3 (1.7975 : _root_.Interval) (0.005 : _root_.Interval))
    (-0.0023456704 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.7975 + 0.005 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.7975 0.005 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
