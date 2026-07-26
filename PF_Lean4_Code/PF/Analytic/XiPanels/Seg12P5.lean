import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s12c17 : (-0.0000803133 : ℝ)
    ≤ ∑ i ∈ Finset.range 2, nodeR (2.985 + 0.01 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0000803133 : _root_.Interval))
    (nodeFold 2 (2.985 : _root_.Interval) (0.01 : _root_.Interval))
    (-0.0000803133 : ℝ) (∑ i ∈ Finset.range 2, nodeR (2.985 + 0.01 * (i : ℕ)))
    (by approx) (nodeFold_mem 2 2.985 0.01 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
