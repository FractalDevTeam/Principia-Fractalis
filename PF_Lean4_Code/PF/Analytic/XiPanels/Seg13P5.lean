import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s13c17 : (-0.0000019596 : ℝ)
    ≤ ∑ i ∈ Finset.range 2, nodeR (3.97 + 0.02 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0000019596 : _root_.Interval))
    (nodeFold 2 (3.97 : _root_.Interval) (0.02 : _root_.Interval))
    (-0.0000019596 : ℝ) (∑ i ∈ Finset.range 2, nodeR (3.97 + 0.02 * (i : ℕ)))
    (by approx) (nodeFold_mem 2 3.97 0.02 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
