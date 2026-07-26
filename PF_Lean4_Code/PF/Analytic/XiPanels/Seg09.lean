import PF.Analytic.XiPanels.Seg09P1
import PF.Analytic.XiPanels.Seg09P2
import PF.Analytic.XiPanels.Seg09P3
import PF.Analytic.XiPanels.Seg09P4
import PF.Analytic.XiPanels.Seg09P5
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real

/-- Panel-sum lower bound for segment 9: `[1.75, 2]`, `n = 50`. -/
theorem seg09 : (0.0078703585 : ℝ)
    ≤ ∑ i ∈ Finset.range 50, nodeR (1.7525 + 0.005 * (i : ℕ)) := by
  have h1 := nodeSum_split 3 47 50 (1.7525 : ℝ) 0.005 1.7675 (by norm_num) (by norm_num)
  have h2 := nodeSum_split 3 44 47 (1.7675 : ℝ) 0.005 1.7825 (by norm_num) (by norm_num)
  have h3 := nodeSum_split 3 41 44 (1.7825 : ℝ) 0.005 1.7975 (by norm_num) (by norm_num)
  have h4 := nodeSum_split 3 38 41 (1.7975 : ℝ) 0.005 1.8125 (by norm_num) (by norm_num)
  have h5 := nodeSum_split 3 35 38 (1.8125 : ℝ) 0.005 1.8275 (by norm_num) (by norm_num)
  have h6 := nodeSum_split 3 32 35 (1.8275 : ℝ) 0.005 1.8425 (by norm_num) (by norm_num)
  have h7 := nodeSum_split 3 29 32 (1.8425 : ℝ) 0.005 1.8575 (by norm_num) (by norm_num)
  have h8 := nodeSum_split 3 26 29 (1.8575 : ℝ) 0.005 1.8725 (by norm_num) (by norm_num)
  have h9 := nodeSum_split 3 23 26 (1.8725 : ℝ) 0.005 1.8875 (by norm_num) (by norm_num)
  have h10 := nodeSum_split 3 20 23 (1.8875 : ℝ) 0.005 1.9025 (by norm_num) (by norm_num)
  have h11 := nodeSum_split 3 17 20 (1.9025 : ℝ) 0.005 1.9175 (by norm_num) (by norm_num)
  have h12 := nodeSum_split 3 14 17 (1.9175 : ℝ) 0.005 1.9325 (by norm_num) (by norm_num)
  have h13 := nodeSum_split 3 11 14 (1.9325 : ℝ) 0.005 1.9475 (by norm_num) (by norm_num)
  have h14 := nodeSum_split 3 8 11 (1.9475 : ℝ) 0.005 1.9625 (by norm_num) (by norm_num)
  have h15 := nodeSum_split 3 5 8 (1.9625 : ℝ) 0.005 1.9775 (by norm_num) (by norm_num)
  have h16 := nodeSum_split 3 2 5 (1.9775 : ℝ) 0.005 1.9925 (by norm_num) (by norm_num)
  linarith [s09c01, s09c02, s09c03, s09c04, s09c05, s09c06, s09c07, s09c08, s09c09, s09c10, s09c11, s09c12, s09c13, s09c14, s09c15, s09c16, s09c17, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]

end PrincipiaTractalis.XiPanels
