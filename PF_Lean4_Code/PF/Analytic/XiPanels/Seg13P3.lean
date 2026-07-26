import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s13c09 : (-0.0000370663 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (3.49 + 0.02 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0000370663 : _root_.Interval))
    (nodeFold 3 (3.49 : _root_.Interval) (0.02 : _root_.Interval))
    (-0.0000370663 : ℝ) (∑ i ∈ Finset.range 3, nodeR (3.49 + 0.02 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 3.49 0.02 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s13c10 : (-0.0000291033 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (3.55 + 0.02 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0000291033 : _root_.Interval))
    (nodeFold 3 (3.55 : _root_.Interval) (0.02 : _root_.Interval))
    (-0.0000291033 : ℝ) (∑ i ∈ Finset.range 3, nodeR (3.55 + 0.02 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 3.55 0.02 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s13c11 : (-0.0000224427 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (3.61 + 0.02 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0000224427 : _root_.Interval))
    (nodeFold 3 (3.61 : _root_.Interval) (0.02 : _root_.Interval))
    (-0.0000224427 : ℝ) (∑ i ∈ Finset.range 3, nodeR (3.61 + 0.02 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 3.61 0.02 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s13c12 : (-0.0000169744 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (3.67 + 0.02 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0000169744 : _root_.Interval))
    (nodeFold 3 (3.67 : _root_.Interval) (0.02 : _root_.Interval))
    (-0.0000169744 : ℝ) (∑ i ∈ Finset.range 3, nodeR (3.67 + 0.02 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 3.67 0.02 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
