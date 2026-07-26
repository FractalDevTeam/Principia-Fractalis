import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s05c05 : (-0.0334902285 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.2890625 + 0.003125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0334902285 : _root_.Interval))
    (nodeFold 3 (1.2890625 : _root_.Interval) (0.003125 : _root_.Interval))
    (-0.0334902285 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.2890625 + 0.003125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.2890625 0.003125 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s05c06 : (-0.0365148878 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.2984375 + 0.003125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0365148878 : _root_.Interval))
    (nodeFold 3 (1.2984375 : _root_.Interval) (0.003125 : _root_.Interval))
    (-0.0365148878 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.2984375 + 0.003125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.2984375 0.003125 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s05c07 : (-0.0391574579 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.3078125 + 0.003125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0391574579 : _root_.Interval))
    (nodeFold 3 (1.3078125 : _root_.Interval) (0.003125 : _root_.Interval))
    (-0.0391574579 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.3078125 + 0.003125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.3078125 0.003125 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s05c08 : (-0.0414368859 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.3171875 + 0.003125 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0414368859 : _root_.Interval))
    (nodeFold 3 (1.3171875 : _root_.Interval) (0.003125 : _root_.Interval))
    (-0.0414368859 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.3171875 + 0.003125 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.3171875 0.003125 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
