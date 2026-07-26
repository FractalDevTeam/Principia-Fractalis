import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s03c05 : (0.0595884569 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.15625 + 0.0025 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0595884569 : _root_.Interval))
    (nodeFold 3 (1.15625 : _root_.Interval) (0.0025 : _root_.Interval))
    (0.0595884569 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.15625 + 0.0025 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.15625 0.0025 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s03c06 : (0.0516812022 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.16375 + 0.0025 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0516812022 : _root_.Interval))
    (nodeFold 3 (1.16375 : _root_.Interval) (0.0025 : _root_.Interval))
    (0.0516812022 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.16375 + 0.0025 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.16375 0.0025 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s03c07 : (0.0440875029 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.17125 + 0.0025 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0440875029 : _root_.Interval))
    (nodeFold 3 (1.17125 : _root_.Interval) (0.0025 : _root_.Interval))
    (0.0440875029 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.17125 + 0.0025 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.17125 0.0025 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s03c08 : (0.0368139466 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.17875 + 0.0025 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0368139466 : _root_.Interval))
    (nodeFold 3 (1.17875 : _root_.Interval) (0.0025 : _root_.Interval))
    (0.0368139466 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.17875 + 0.0025 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.17875 0.0025 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
