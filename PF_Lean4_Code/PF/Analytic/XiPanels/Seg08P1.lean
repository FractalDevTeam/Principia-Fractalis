import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s08c01 : (-0.0198581445 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.6275 + 0.005 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0198581445 : _root_.Interval))
    (nodeFold 3 (1.6275 : _root_.Interval) (0.005 : _root_.Interval))
    (-0.0198581445 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.6275 + 0.005 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.6275 0.005 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s08c02 : (-0.0177986081 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.6425 + 0.005 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0177986081 : _root_.Interval))
    (nodeFold 3 (1.6425 : _root_.Interval) (0.005 : _root_.Interval))
    (-0.0177986081 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.6425 + 0.005 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.6425 0.005 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s08c03 : (-0.0158279014 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.6575 + 0.005 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0158279014 : _root_.Interval))
    (nodeFold 3 (1.6575 : _root_.Interval) (0.005 : _root_.Interval))
    (-0.0158279014 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.6575 + 0.005 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.6575 0.005 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s08c04 : (-0.0139526606 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.6725 + 0.005 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0139526606 : _root_.Interval))
    (nodeFold 3 (1.6725 : _root_.Interval) (0.005 : _root_.Interval))
    (-0.0139526606 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.6725 + 0.005 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.6725 0.005 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
