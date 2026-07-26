import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s02c05 : (0.135932603 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.09375 + 0.0025 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.135932603 : _root_.Interval))
    (nodeFold 3 (1.09375 : _root_.Interval) (0.0025 : _root_.Interval))
    (0.135932603 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.09375 + 0.0025 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.09375 0.0025 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s02c06 : (0.1259803302 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.10125 + 0.0025 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.1259803302 : _root_.Interval))
    (nodeFold 3 (1.10125 : _root_.Interval) (0.0025 : _root_.Interval))
    (0.1259803302 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.10125 + 0.0025 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.10125 0.0025 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s02c07 : (0.1161923821 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.10875 + 0.0025 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.1161923821 : _root_.Interval))
    (nodeFold 3 (1.10875 : _root_.Interval) (0.0025 : _root_.Interval))
    (0.1161923821 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.10875 + 0.0025 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.10875 0.0025 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s02c08 : (0.1065972104 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.11625 + 0.0025 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.1065972104 : _root_.Interval))
    (nodeFold 3 (1.11625 : _root_.Interval) (0.0025 : _root_.Interval))
    (0.1065972104 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.11625 + 0.0025 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.11625 0.0025 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
