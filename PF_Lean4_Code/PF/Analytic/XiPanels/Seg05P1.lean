import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s05c01 : (-0.0172100712 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.2515625 + 0.003125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0172100712 : _root_.Interval))
    (nodeFold 3 (1.2515625 : _root_.Interval) (0.003125 : _root_.Interval))
    (-0.0172100712 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.2515625 + 0.003125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.2515625 0.003125 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s05c02 : (-0.0219415205 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.2609375 + 0.003125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0219415205 : _root_.Interval))
    (nodeFold 3 (1.2609375 : _root_.Interval) (0.003125 : _root_.Interval))
    (-0.0219415205 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.2609375 + 0.003125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.2609375 0.003125 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s05c03 : (-0.0262210947 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.2703125 + 0.003125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0262210947 : _root_.Interval))
    (nodeFold 3 (1.2703125 : _root_.Interval) (0.003125 : _root_.Interval))
    (-0.0262210947 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.2703125 + 0.003125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.2703125 0.003125 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s05c04 : (-0.0300649454 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.2796875 + 0.003125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0300649454 : _root_.Interval))
    (nodeFold 3 (1.2796875 : _root_.Interval) (0.003125 : _root_.Interval))
    (-0.0300649454 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.2796875 + 0.003125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.2796875 0.003125 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
