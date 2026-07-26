import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s06c05 : (-0.0483027407 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.4140625 + 0.003125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0483027407 : _root_.Interval))
    (nodeFold 3 (1.4140625 : _root_.Interval) (0.003125 : _root_.Interval))
    (-0.0483027407 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.4140625 + 0.003125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.4140625 0.003125 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s06c06 : (-0.0477738383 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.4234375 + 0.003125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0477738383 : _root_.Interval))
    (nodeFold 3 (1.4234375 : _root_.Interval) (0.003125 : _root_.Interval))
    (-0.0477738383 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.4234375 + 0.003125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.4234375 0.003125 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s06c07 : (-0.0471022343 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.4328125 + 0.003125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0471022343 : _root_.Interval))
    (nodeFold 3 (1.4328125 : _root_.Interval) (0.003125 : _root_.Interval))
    (-0.0471022343 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.4328125 + 0.003125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.4328125 0.003125 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s06c08 : (-0.0463024212 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.4421875 + 0.003125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0463024212 : _root_.Interval))
    (nodeFold 3 (1.4421875 : _root_.Interval) (0.003125 : _root_.Interval))
    (-0.0463024212 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.4421875 + 0.003125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.4421875 0.003125 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
