import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s06c01 : (-0.0486787365 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.3765625 + 0.003125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0486787365 : _root_.Interval))
    (nodeFold 3 (1.3765625 : _root_.Interval) (0.003125 : _root_.Interval))
    (-0.0486787365 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.3765625 + 0.003125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.3765625 0.003125 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s06c02 : (-0.0488784901 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.3859375 + 0.003125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0488784901 : _root_.Interval))
    (nodeFold 3 (1.3859375 : _root_.Interval) (0.003125 : _root_.Interval))
    (-0.0488784901 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.3859375 + 0.003125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.3859375 0.003125 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s06c03 : (-0.0488711739 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.3953125 + 0.003125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0488711739 : _root_.Interval))
    (nodeFold 3 (1.3953125 : _root_.Interval) (0.003125 : _root_.Interval))
    (-0.0488711739 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.3953125 + 0.003125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.3953125 0.003125 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s06c04 : (-0.0486737856 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.4046875 + 0.003125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0486737856 : _root_.Interval))
    (nodeFold 3 (1.4046875 : _root_.Interval) (0.003125 : _root_.Interval))
    (-0.0486737856 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.4046875 + 0.003125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.4046875 0.003125 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
