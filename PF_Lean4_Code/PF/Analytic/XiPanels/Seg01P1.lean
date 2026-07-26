import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s01c01 : (0.2554203244 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.00125 + 0.0025 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.2554203244 : _root_.Interval))
    (nodeFold 3 (1.00125 : _root_.Interval) (0.0025 : _root_.Interval))
    (0.2554203244 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.00125 + 0.0025 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.00125 0.0025 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s01c02 : (0.2472674048 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.00875 + 0.0025 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.2472674048 : _root_.Interval))
    (nodeFold 3 (1.00875 : _root_.Interval) (0.0025 : _root_.Interval))
    (0.2472674048 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.00875 + 0.0025 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.00875 0.0025 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s01c03 : (0.2386076959 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.01625 + 0.0025 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.2386076959 : _root_.Interval))
    (nodeFold 3 (1.01625 : _root_.Interval) (0.0025 : _root_.Interval))
    (0.2386076959 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.01625 + 0.0025 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.01625 0.0025 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s01c04 : (0.2295200131 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.02375 + 0.0025 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.2295200131 : _root_.Interval))
    (nodeFold 3 (1.02375 : _root_.Interval) (0.0025 : _root_.Interval))
    (0.2295200131 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.02375 + 0.0025 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.02375 0.0025 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
