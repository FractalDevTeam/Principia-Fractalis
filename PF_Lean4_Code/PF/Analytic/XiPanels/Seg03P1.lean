import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s03c01 : (0.0941466852 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.12625 + 0.0025 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0941466852 : _root_.Interval))
    (nodeFold 3 (1.12625 : _root_.Interval) (0.0025 : _root_.Interval))
    (0.0941466852 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.12625 + 0.0025 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.12625 0.0025 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s03c02 : (0.0850941775 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.13375 + 0.0025 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0850941775 : _root_.Interval))
    (nodeFold 3 (1.13375 : _root_.Interval) (0.0025 : _root_.Interval))
    (0.0850941775 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.13375 + 0.0025 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.13375 0.0025 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s03c03 : (0.0763069369 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.14125 + 0.0025 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0763069369 : _root_.Interval))
    (nodeFold 3 (1.14125 : _root_.Interval) (0.0025 : _root_.Interval))
    (0.0763069369 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.14125 + 0.0025 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.14125 0.0025 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s03c04 : (0.067800641 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.14875 + 0.0025 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.067800641 : _root_.Interval))
    (nodeFold 3 (1.14875 : _root_.Interval) (0.0025 : _root_.Interval))
    (0.067800641 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.14875 + 0.0025 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.14875 0.0025 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
