import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s14c01 : (-0.0000011892 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (4.025 + 0.05 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0000011892 : _root_.Interval))
    (nodeFold 3 (4.025 : _root_.Interval) (0.05 : _root_.Interval))
    (-0.0000011892 : ℝ) (∑ i ∈ Finset.range 3, nodeR (4.025 + 0.05 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 4.025 0.05 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s14c02 : (2.162E-7 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (4.175 + 0.05 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((2.162E-7 : _root_.Interval))
    (nodeFold 3 (4.175 : _root_.Interval) (0.05 : _root_.Interval))
    (2.162E-7 : ℝ) (∑ i ∈ Finset.range 3, nodeR (4.175 + 0.05 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 4.175 0.05 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s14c03 : (6.528E-7 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (4.325 + 0.05 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((6.528E-7 : _root_.Interval))
    (nodeFold 3 (4.325 : _root_.Interval) (0.05 : _root_.Interval))
    (6.528E-7 : ℝ) (∑ i ∈ Finset.range 3, nodeR (4.325 + 0.05 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 4.325 0.05 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s14c04 : (6.569E-7 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (4.475 + 0.05 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((6.569E-7 : _root_.Interval))
    (nodeFold 3 (4.475 : _root_.Interval) (0.05 : _root_.Interval))
    (6.569E-7 : ℝ) (∑ i ∈ Finset.range 3, nodeR (4.475 + 0.05 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 4.475 0.05 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
