import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s09c17 : (0.0025726662 : ℝ)
    ≤ ∑ i ∈ Finset.range 2, nodeR (1.9925 + 0.005 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0025726662 : _root_.Interval))
    (nodeFold 2 (1.9925 : _root_.Interval) (0.005 : _root_.Interval))
    (0.0025726662 : ℝ) (∑ i ∈ Finset.range 2, nodeR (1.9925 + 0.005 * (i : ℕ)))
    (by approx) (nodeFold_mem 2 1.9925 0.005 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
