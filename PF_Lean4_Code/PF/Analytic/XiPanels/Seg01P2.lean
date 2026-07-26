import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s01c05 : (0.2200787015 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.03125 + 0.0025 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.2200787015 : _root_.Interval))
    (nodeFold 3 (1.03125 : _root_.Interval) (0.0025 : _root_.Interval))
    (0.2200787015 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.03125 + 0.0025 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.03125 0.0025 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s01c06 : (0.2103536259 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.03875 + 0.0025 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.2103536259 : _root_.Interval))
    (nodeFold 3 (1.03875 : _root_.Interval) (0.0025 : _root_.Interval))
    (0.2103536259 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.03875 + 0.0025 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.03875 0.0025 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s01c07 : (0.2004101913 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.04625 + 0.0025 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.2004101913 : _root_.Interval))
    (nodeFold 3 (1.04625 : _root_.Interval) (0.0025 : _root_.Interval))
    (0.2004101913 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.04625 + 0.0025 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.04625 0.0025 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s01c08 : (0.19030939 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.05375 + 0.0025 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.19030939 : _root_.Interval))
    (nodeFold 3 (1.05375 : _root_.Interval) (0.0025 : _root_.Interval))
    (0.19030939 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.05375 + 0.0025 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.05375 0.0025 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
