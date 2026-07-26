import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s14c05 : (5.077E-7 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (4.625 + 0.05 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((5.077E-7 : _root_.Interval))
    (nodeFold 3 (4.625 : _root_.Interval) (0.05 : _root_.Interval))
    (5.077E-7 : ℝ) (∑ i ∈ Finset.range 3, nodeR (4.625 + 0.05 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 4.625 0.05 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s14c06 : (3.349E-7 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (4.775 + 0.05 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((3.349E-7 : _root_.Interval))
    (nodeFold 3 (4.775 : _root_.Interval) (0.05 : _root_.Interval))
    (3.349E-7 : ℝ) (∑ i ∈ Finset.range 3, nodeR (4.775 + 0.05 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 4.775 0.05 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s14c07 : (1.062E-7 : ℝ)
    ≤ ∑ i ∈ Finset.range 2, nodeR (4.925 + 0.05 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((1.062E-7 : _root_.Interval))
    (nodeFold 2 (4.925 : _root_.Interval) (0.05 : _root_.Interval))
    (1.062E-7 : ℝ) (∑ i ∈ Finset.range 2, nodeR (4.925 + 0.05 * (i : ℕ)))
    (by approx) (nodeFold_mem 2 4.925 0.05 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
