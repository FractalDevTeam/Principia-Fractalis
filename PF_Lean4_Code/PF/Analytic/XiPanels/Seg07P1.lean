import PF.Analytic.XiOnLineZeroCore
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real
set_option maxRecDepth 4000000

theorem s07c01 : (-0.0389228491 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.501953125 + 0.00390625 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0389228491 : _root_.Interval))
    (nodeFold 3 (1.501953125 : _root_.Interval) (0.00390625 : _root_.Interval))
    (-0.0389228491 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.501953125 + 0.00390625 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.501953125 0.00390625 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s07c02 : (-0.0372091746 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.513671875 + 0.00390625 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0372091746 : _root_.Interval))
    (nodeFold 3 (1.513671875 : _root_.Interval) (0.00390625 : _root_.Interval))
    (-0.0372091746 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.513671875 + 0.00390625 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.513671875 0.00390625 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s07c03 : (-0.0354474357 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.525390625 + 0.00390625 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0354474357 : _root_.Interval))
    (nodeFold 3 (1.525390625 : _root_.Interval) (0.00390625 : _root_.Interval))
    (-0.0354474357 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.525390625 + 0.00390625 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.525390625 0.00390625 _ _ (by approx) (by approx)) ?_
  decide +kernel

theorem s07c04 : (-0.0336531493 : ℝ)
    ≤ ∑ i ∈ Finset.range 3, nodeR (1.537109375 + 0.00390625 * (i : ℕ)) := by
  refine _root_.Interval.approx_le ((-0.0336531493 : _root_.Interval))
    (nodeFold 3 (1.537109375 : _root_.Interval) (0.00390625 : _root_.Interval))
    (-0.0336531493 : ℝ) (∑ i ∈ Finset.range 3, nodeR (1.537109375 + 0.00390625 * (i : ℕ)))
    (by approx) (nodeFold_mem 3 1.537109375 0.00390625 _ _ (by approx) (by approx)) ?_
  decide +kernel

end PrincipiaTractalis.XiPanels
