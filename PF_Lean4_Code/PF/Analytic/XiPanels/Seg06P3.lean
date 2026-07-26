import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s06c09 : (-0.0453882146 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.4515625 + 0.003125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0453882146 : _root_.Interval))
    (nodeFold 3 (1.4515625 : _root_.Interval) (0.003125 : _root_.Interval))
    (-0.0453882146 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.4515625 + 0.003125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.4515625 0.003125 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s06c10 : (-0.0443727446 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.4609375 + 0.003125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0443727446 : _root_.Interval))
    (nodeFold 3 (1.4609375 : _root_.Interval) (0.003125 : _root_.Interval))
    (-0.0443727446 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.4609375 + 0.003125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.4609375 0.003125 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s06c11 : (-0.0432684532 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.4703125 + 0.003125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0432684532 : _root_.Interval))
    (nodeFold 3 (1.4703125 : _root_.Interval) (0.003125 : _root_.Interval))
    (-0.0432684532 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.4703125 + 0.003125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.4703125 0.003125 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s06c12 : (-0.0420870945 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.4796875 + 0.003125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0420870945 : _root_.Interval))
    (nodeFold 3 (1.4796875 : _root_.Interval) (0.003125 : _root_.Interval))
    (-0.0420870945 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.4796875 + 0.003125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.4796875 0.003125 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
