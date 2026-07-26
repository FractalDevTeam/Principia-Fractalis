import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s11c05 : (0.0018351628 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.34765625 + 0.0078125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0018351628 : _root_.Interval))
    (nodeFold 3 (2.34765625 : _root_.Interval) (0.0078125 : _root_.Interval))
    (0.0018351628 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.34765625 + 0.0078125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.34765625 0.0078125 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s11c06 : (0.0016456099 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.37109375 + 0.0078125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0016456099 : _root_.Interval))
    (nodeFold 3 (2.37109375 : _root_.Interval) (0.0078125 : _root_.Interval))
    (0.0016456099 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.37109375 + 0.0078125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.37109375 0.0078125 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s11c07 : (0.0014662874 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.39453125 + 0.0078125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0014662874 : _root_.Interval))
    (nodeFold 3 (2.39453125 : _root_.Interval) (0.0078125 : _root_.Interval))
    (0.0014662874 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.39453125 + 0.0078125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.39453125 0.0078125 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s11c08 : (0.0012978637 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.41796875 + 0.0078125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0012978637 : _root_.Interval))
    (nodeFold 3 (2.41796875 : _root_.Interval) (0.0078125 : _root_.Interval))
    (0.0012978637 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.41796875 + 0.0078125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.41796875 0.0078125 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
