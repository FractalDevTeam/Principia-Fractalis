import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s13c13 : (-0.0000125626 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (3.73 + 0.02 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0000125626 : _root_.Interval))
    (nodeFold 3 (3.73 : _root_.Interval) (0.02 : _root_.Interval))
    (-0.0000125626 : ℝ) (∑ i ∈ Finset.range 3, nodeR (3.73 + 0.02 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 3.73 0.02 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s13c14 : (-0.0000090628 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (3.79 + 0.02 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0000090628 : _root_.Interval))
    (nodeFold 3 (3.79 : _root_.Interval) (0.02 : _root_.Interval))
    (-0.0000090628 : ℝ) (∑ i ∈ Finset.range 3, nodeR (3.79 + 0.02 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 3.79 0.02 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s13c15 : (-0.0000063329 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (3.85 + 0.02 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0000063329 : _root_.Interval))
    (nodeFold 3 (3.85 : _root_.Interval) (0.02 : _root_.Interval))
    (-0.0000063329 : ℝ) (∑ i ∈ Finset.range 3, nodeR (3.85 + 0.02 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 3.85 0.02 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s13c16 : (-0.0000042411 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (3.91 + 0.02 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0000042411 : _root_.Interval))
    (nodeFold 3 (3.91 : _root_.Interval) (0.02 : _root_.Interval))
    (-0.0000042411 : ℝ) (∑ i ∈ Finset.range 3, nodeR (3.91 + 0.02 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 3.91 0.02 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
