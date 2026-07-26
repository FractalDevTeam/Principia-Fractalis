import PF.Analytic.XiPanels.Seg06P1
import PF.Analytic.XiPanels.Seg06P2
import PF.Analytic.XiPanels.Seg06P3
import PF.Analytic.XiPanels.Seg06P4
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real

/-- Panel-sum lower bound for segment 6: `[1.375, 1.5]`, `n = 40`. -/
theorem seg06 : (-0.6138658963 : ℝ)
    ≤ ∑ i ∈ Finset.range 40, nodeR (1.3765625 + 0.003125 * (i : ℕ)) := by
  have h1 := nodeSum_split 3 37 40 (1.3765625 : ℝ) 0.003125 1.3859375 (by norm_num) (by norm_num)
  have h2 := nodeSum_split 3 34 37 (1.3859375 : ℝ) 0.003125 1.3953125 (by norm_num) (by norm_num)
  have h3 := nodeSum_split 3 31 34 (1.3953125 : ℝ) 0.003125 1.4046875 (by norm_num) (by norm_num)
  have h4 := nodeSum_split 3 28 31 (1.4046875 : ℝ) 0.003125 1.4140625 (by norm_num) (by norm_num)
  have h5 := nodeSum_split 3 25 28 (1.4140625 : ℝ) 0.003125 1.4234375 (by norm_num) (by norm_num)
  have h6 := nodeSum_split 3 22 25 (1.4234375 : ℝ) 0.003125 1.4328125 (by norm_num) (by norm_num)
  have h7 := nodeSum_split 3 19 22 (1.4328125 : ℝ) 0.003125 1.4421875 (by norm_num) (by norm_num)
  have h8 := nodeSum_split 3 16 19 (1.4421875 : ℝ) 0.003125 1.4515625 (by norm_num) (by norm_num)
  have h9 := nodeSum_split 3 13 16 (1.4515625 : ℝ) 0.003125 1.4609375 (by norm_num) (by norm_num)
  have h10 := nodeSum_split 3 10 13 (1.4609375 : ℝ) 0.003125 1.4703125 (by norm_num) (by norm_num)
  have h11 := nodeSum_split 3 7 10 (1.4703125 : ℝ) 0.003125 1.4796875 (by norm_num) (by norm_num)
  have h12 := nodeSum_split 3 4 7 (1.4796875 : ℝ) 0.003125 1.4890625 (by norm_num) (by norm_num)
  have h13 := nodeSum_split 3 1 4 (1.4890625 : ℝ) 0.003125 1.4984375 (by norm_num) (by norm_num)
  linarith [s06c01, s06c02, s06c03, s06c04, s06c05, s06c06, s06c07, s06c08, s06c09, s06c10, s06c11, s06c12, s06c13, s06c14, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]

end PrincipiaTractalis.XiPanels
