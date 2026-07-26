import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s05c09 : (-0.0433723693 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.3265625 + 0.003125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0433723693 : _root_.Interval))
    (nodeFold 3 (1.3265625 : _root_.Interval) (0.003125 : _root_.Interval))
    (-0.0433723693 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.3265625 + 0.003125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.3265625 0.003125 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s05c10 : (-0.0449832119 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.3359375 + 0.003125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0449832119 : _root_.Interval))
    (nodeFold 3 (1.3359375 : _root_.Interval) (0.003125 : _root_.Interval))
    (-0.0449832119 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.3359375 + 0.003125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.3359375 0.003125 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s05c11 : (-0.0462886939 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.3453125 + 0.003125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0462886939 : _root_.Interval))
    (nodeFold 3 (1.3453125 : _root_.Interval) (0.003125 : _root_.Interval))
    (-0.0462886939 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.3453125 + 0.003125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.3453125 0.003125 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s05c12 : (-0.047307958 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.3546875 + 0.003125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.047307958 : _root_.Interval))
    (nodeFold 3 (1.3546875 : _root_.Interval) (0.003125 : _root_.Interval))
    (-0.047307958 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.3546875 + 0.003125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.3546875 0.003125 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
