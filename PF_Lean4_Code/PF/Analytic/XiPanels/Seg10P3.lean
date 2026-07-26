import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s10c09 : (0.0035733912 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.153125 + 0.00625 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0035733912 : _root_.Interval))
    (nodeFold 3 (2.153125 : _root_.Interval) (0.00625 : _root_.Interval))
    (0.0035733912 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.153125 + 0.00625 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.153125 0.00625 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s10c10 : (0.0034225766 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.171875 + 0.00625 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0034225766 : _root_.Interval))
    (nodeFold 3 (2.171875 : _root_.Interval) (0.00625 : _root_.Interval))
    (0.0034225766 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.171875 + 0.00625 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.171875 0.00625 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s10c11 : (0.0032620916 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.190625 + 0.00625 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0032620916 : _root_.Interval))
    (nodeFold 3 (2.190625 : _root_.Interval) (0.00625 : _root_.Interval))
    (0.0032620916 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.190625 + 0.00625 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.190625 0.00625 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s10c12 : (0.0030948011 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (2.209375 + 0.00625 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((0.0030948011 : _root_.Interval))
    (nodeFold 3 (2.209375 : _root_.Interval) (0.00625 : _root_.Interval))
    (0.0030948011 : ℝ) (∑ i ∈ Finset.range 3, nodeR (2.209375 + 0.00625 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 2.209375 0.00625 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
