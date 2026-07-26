import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s06c13 : (-0.0408397409 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.4890625 + 0.003125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0408397409 : _root_.Interval))
    (nodeFold 3 (1.4890625 : _root_.Interval) (0.003125 : _root_.Interval))
    (-0.0408397409 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.4890625 + 0.003125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.4890625 0.003125 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s06c14 : (-0.0133262279 : ℝ)
    ≤ ∑ i ∈ Finset.range 1, nodeR (1.4984375 + 0.003125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0133262279 : _root_.Interval))
    (nodeFold 1 (1.4984375 : _root_.Interval) (0.003125 : _root_.Interval))
    (-0.0133262279 : ℝ) (∑ i ∈ Finset.range 1, nodeR (1.4984375 + 0.003125 * (i : ℕ)))
    (by approx) (nodeFold_mem 1 1.4984375 0.003125 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
