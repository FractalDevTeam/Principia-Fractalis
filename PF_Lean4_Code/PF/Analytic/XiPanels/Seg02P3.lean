import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s02c09 : (0.0334370892 : ℝ)
    ≤ ∑ i ∈ Finset.range 1, nodeR (1.12375 + 0.0025 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0334370892 : _root_.Interval))
    (nodeFold 1 (1.12375 : _root_.Interval) (0.0025 : _root_.Interval))
    (0.0334370892 : ℝ) (∑ i ∈ Finset.range 1, nodeR (1.12375 + 0.0025 * (i : ℕ)))
    (by approx) (nodeFold_mem 1 1.12375 0.0025 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
