import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s10c01 : (0.0039545707 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.003125 + 0.00625 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0039545707 : _root_.Interval))
    (nodeFold 3 (2.003125 : _root_.Interval) (0.00625 : _root_.Interval))
    (0.0039545707 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.003125 + 0.00625 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.003125 0.00625 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s10c02 : (0.0040335955 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.021875 + 0.00625 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0040335955 : _root_.Interval))
    (nodeFold 3 (2.021875 : _root_.Interval) (0.00625 : _root_.Interval))
    (0.0040335955 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.021875 + 0.00625 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.021875 0.00625 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s10c03 : (0.004064843 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.040625 + 0.00625 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.004064843 : _root_.Interval))
    (nodeFold 3 (2.040625 : _root_.Interval) (0.00625 : _root_.Interval))
    (0.004064843 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.040625 + 0.00625 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.040625 0.00625 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s10c04 : (0.0040547049 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.059375 + 0.00625 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0040547049 : _root_.Interval))
    (nodeFold 3 (2.059375 : _root_.Interval) (0.00625 : _root_.Interval))
    (0.0040547049 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.059375 + 0.00625 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.059375 0.00625 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
