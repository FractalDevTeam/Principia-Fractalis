import PF.Analytic.XiPanels.Seg11P1
import PF.Analytic.XiPanels.Seg11P2
import PF.Analytic.XiPanels.Seg11P3
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real

/-- Panel-sum lower bound for segment 11: `[2.25, 2.5]`, `n = 32`. -/
theorem seg11 : (0.0183664357 : ℝ)
    ≤ ∑ i ∈ Finset.range 32, nodeR (2.25390625 + 0.0078125 * (i : ℕ)) := by
  have h1 := nodeSum_split 3 29 32 (2.25390625 : ℝ) 0.0078125 2.27734375 (by norm_num) (by norm_num)
  have h2 := nodeSum_split 3 26 29 (2.27734375 : ℝ) 0.0078125 2.30078125 (by norm_num) (by norm_num)
  have h3 := nodeSum_split 3 23 26 (2.30078125 : ℝ) 0.0078125 2.32421875 (by norm_num) (by norm_num)
  have h4 := nodeSum_split 3 20 23 (2.32421875 : ℝ) 0.0078125 2.34765625 (by norm_num) (by norm_num)
  have h5 := nodeSum_split 3 17 20 (2.34765625 : ℝ) 0.0078125 2.37109375 (by norm_num) (by norm_num)
  have h6 := nodeSum_split 3 14 17 (2.37109375 : ℝ) 0.0078125 2.39453125 (by norm_num) (by norm_num)
  have h7 := nodeSum_split 3 11 14 (2.39453125 : ℝ) 0.0078125 2.41796875 (by norm_num) (by norm_num)
  have h8 := nodeSum_split 3 8 11 (2.41796875 : ℝ) 0.0078125 2.44140625 (by norm_num) (by norm_num)
  have h9 := nodeSum_split 3 5 8 (2.44140625 : ℝ) 0.0078125 2.46484375 (by norm_num) (by norm_num)
  have h10 := nodeSum_split 3 2 5 (2.46484375 : ℝ) 0.0078125 2.48828125 (by norm_num) (by norm_num)
  linarith [s11c01, s11c02, s11c03, s11c04, s11c05, s11c06, s11c07, s11c08, s11c09, s11c10, s11c11, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

end PrincipiaTractalis.XiPanels
