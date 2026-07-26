import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s13c01 : (-0.0001207611 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (3.01 + 0.02 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0001207611 : _root_.Interval))
    (nodeFold 3 (3.01 : _root_.Interval) (0.02 : _root_.Interval))
    (-0.0001207611 : ℝ) (∑ i ∈ Finset.range 3, nodeR (3.01 + 0.02 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 3.01 0.02 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s13c02 : (-0.000115795 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (3.07 + 0.02 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.000115795 : _root_.Interval))
    (nodeFold 3 (3.07 : _root_.Interval) (0.02 : _root_.Interval))
    (-0.000115795 : ℝ) (∑ i ∈ Finset.range 3, nodeR (3.07 + 0.02 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 3.07 0.02 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s13c03 : (-0.0001062489 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (3.13 + 0.02 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0001062489 : _root_.Interval))
    (nodeFold 3 (3.13 : _root_.Interval) (0.02 : _root_.Interval))
    (-0.0001062489 : ℝ) (∑ i ∈ Finset.range 3, nodeR (3.13 + 0.02 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 3.13 0.02 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s13c04 : (-0.0000943091 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (3.19 + 0.02 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0000943091 : _root_.Interval))
    (nodeFold 3 (3.19 : _root_.Interval) (0.02 : _root_.Interval))
    (-0.0000943091 : ℝ) (∑ i ∈ Finset.range 3, nodeR (3.19 + 0.02 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 3.19 0.02 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
