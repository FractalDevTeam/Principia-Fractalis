import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s12c09 : (0.00002499 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.745 + 0.01 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.00002499 : _root_.Interval))
    (nodeFold 3 (2.745 : _root_.Interval) (0.01 : _root_.Interval))
    (0.00002499 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.745 + 0.01 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.745 0.01 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s12c10 : (-0.0000142503 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.775 + 0.01 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0000142503 : _root_.Interval))
    (nodeFold 3 (2.775 : _root_.Interval) (0.01 : _root_.Interval))
    (-0.0000142503 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.775 + 0.01 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.775 0.01 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s12c11 : (-0.0000456533 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.805 + 0.01 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0000456533 : _root_.Interval))
    (nodeFold 3 (2.805 : _root_.Interval) (0.01 : _root_.Interval))
    (-0.0000456533 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.805 + 0.01 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.805 0.01 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s12c12 : (-0.000070234 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.835 + 0.01 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.000070234 : _root_.Interval))
    (nodeFold 3 (2.835 : _root_.Interval) (0.01 : _root_.Interval))
    (-0.000070234 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.835 + 0.01 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.835 0.01 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
