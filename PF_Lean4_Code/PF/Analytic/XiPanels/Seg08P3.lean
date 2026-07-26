import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s08c09 : (-0.0021870713 : ℝ)
    ≤ ∑ i ∈ Finset.range 1, nodeR (1.7475 + 0.005 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0021870713 : _root_.Interval))
    (nodeFold 1 (1.7475 : _root_.Interval) (0.005 : _root_.Interval))
    (-0.0021870713 : ℝ) (∑ i ∈ Finset.range 1, nodeR (1.7475 + 0.005 * (i : ℕ)))
    (by approx) (nodeFold_mem 1 1.7475 0.005 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
