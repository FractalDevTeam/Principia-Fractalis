import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s11c09 : (0.0011407323 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.44140625 + 0.0078125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0011407323 : _root_.Interval))
    (nodeFold 3 (2.44140625 : _root_.Interval) (0.0078125 : _root_.Interval))
    (0.0011407323 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.44140625 + 0.0078125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.44140625 0.0078125 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s11c10 : (0.0009950563 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.46484375 + 0.0078125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0009950563 : _root_.Interval))
    (nodeFold 3 (2.46484375 : _root_.Interval) (0.0078125 : _root_.Interval))
    (0.0009950563 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.46484375 + 0.0078125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.46484375 0.0078125 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s11c11 : (0.0005880556 : ℝ)
    ≤ ∑ i ∈ Finset.range 2, nodeR (2.48828125 + 0.0078125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0005880556 : _root_.Interval))
    (nodeFold 2 (2.48828125 : _root_.Interval) (0.0078125 : _root_.Interval))
    (0.0005880556 : ℝ) (∑ i ∈ Finset.range 2, nodeR (2.48828125 + 0.0078125 * (i : ℕ)))
    (by approx) (nodeFold_mem 2 2.48828125 0.0078125 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
