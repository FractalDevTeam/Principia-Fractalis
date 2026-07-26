import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s12c13 : (-0.0000889271 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.865 + 0.01 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0000889271 : _root_.Interval))
    (nodeFold 3 (2.865 : _root_.Interval) (0.01 : _root_.Interval))
    (-0.0000889271 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.865 + 0.01 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.865 0.01 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s12c14 : (-0.0001025852 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.895 + 0.01 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0001025852 : _root_.Interval))
    (nodeFold 3 (2.895 : _root_.Interval) (0.01 : _root_.Interval))
    (-0.0001025852 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.895 + 0.01 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.895 0.01 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s12c15 : (-0.0001119786 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.925 + 0.01 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0001119786 : _root_.Interval))
    (nodeFold 3 (2.925 : _root_.Interval) (0.01 : _root_.Interval))
    (-0.0001119786 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.925 + 0.01 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.925 0.01 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s12c16 : (-0.0001177979 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.955 + 0.01 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0001177979 : _root_.Interval))
    (nodeFold 3 (2.955 : _root_.Interval) (0.01 : _root_.Interval))
    (-0.0001177979 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.955 + 0.01 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.955 0.01 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
