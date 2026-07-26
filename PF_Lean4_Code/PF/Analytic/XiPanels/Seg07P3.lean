import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s07c09 : (-0.0246385613 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.595703125 + 0.00390625 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0246385613 : _root_.Interval))
    (nodeFold 3 (1.595703125 : _root_.Interval) (0.00390625 : _root_.Interval))
    (-0.0246385613 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.595703125 + 0.00390625 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.595703125 0.00390625 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s07c10 : (-0.022898121 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.607421875 + 0.00390625 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.022898121 : _root_.Interval))
    (nodeFold 3 (1.607421875 : _root_.Interval) (0.00390625 : _root_.Interval))
    (-0.022898121 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.607421875 + 0.00390625 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.607421875 0.00390625 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s07c11 : (-0.0143176221 : ℝ)
    ≤ ∑ i ∈ Finset.range 2, nodeR (1.619140625 + 0.00390625 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0143176221 : _root_.Interval))
    (nodeFold 2 (1.619140625 : _root_.Interval) (0.00390625 : _root_.Interval))
    (-0.0143176221 : ℝ) (∑ i ∈ Finset.range 2, nodeR (1.619140625 + 0.00390625 * (i : ℕ)))
    (by approx) (nodeFold_mem 2 1.619140625 0.00390625 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
