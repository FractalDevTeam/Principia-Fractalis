import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s10c05 : (0.0040090891 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.078125 + 0.00625 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0040090891 : _root_.Interval))
    (nodeFold 3 (2.078125 : _root_.Interval) (0.00625 : _root_.Interval))
    (0.0040090891 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.078125 + 0.00625 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.078125 0.00625 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s10c06 : (0.0039334225 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.096875 + 0.00625 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0039334225 : _root_.Interval))
    (nodeFold 3 (2.096875 : _root_.Interval) (0.00625 : _root_.Interval))
    (0.0039334225 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.096875 + 0.00625 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.096875 0.00625 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s10c07 : (0.0038326598 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.115625 + 0.00625 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0038326598 : _root_.Interval))
    (nodeFold 3 (2.115625 : _root_.Interval) (0.00625 : _root_.Interval))
    (0.0038326598 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.115625 + 0.00625 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.115625 0.00625 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s10c08 : (0.0037112975 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.134375 + 0.00625 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0037112975 : _root_.Interval))
    (nodeFold 3 (2.134375 : _root_.Interval) (0.00625 : _root_.Interval))
    (0.0037112975 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.134375 + 0.00625 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.134375 0.00625 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
