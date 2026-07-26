import PF.Analytic.XiPanels.Seg02P1
import PF.Analytic.XiPanels.Seg02P2
import PF.Analytic.XiPanels.Seg02P3
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real

/-- Panel-sum lower bound for segment 2: `[1.0625, 1.125]`, `n = 25`. -/
theorem seg02 : (1.1634895136 : ℝ)
    ≤ ∑ i ∈ Finset.range 25, nodeR (1.06375 + 0.0025 * (i : ℕ)) := by
  have h1 := nodeSum_split 3 22 25 (1.06375 : ℝ) 0.0025 1.07125 (by norm_num) (by norm_num)
  have h2 := nodeSum_split 3 19 22 (1.07125 : ℝ) 0.0025 1.07875 (by norm_num) (by norm_num)
  have h3 := nodeSum_split 3 16 19 (1.07875 : ℝ) 0.0025 1.08625 (by norm_num) (by norm_num)
  have h4 := nodeSum_split 3 13 16 (1.08625 : ℝ) 0.0025 1.09375 (by norm_num) (by norm_num)
  have h5 := nodeSum_split 3 10 13 (1.09375 : ℝ) 0.0025 1.10125 (by norm_num) (by norm_num)
  have h6 := nodeSum_split 3 7 10 (1.10125 : ℝ) 0.0025 1.10875 (by norm_num) (by norm_num)
  have h7 := nodeSum_split 3 4 7 (1.10875 : ℝ) 0.0025 1.11625 (by norm_num) (by norm_num)
  have h8 := nodeSum_split 3 1 4 (1.11625 : ℝ) 0.0025 1.12375 (by norm_num) (by norm_num)
  linarith [s02c01, s02c02, s02c03, s02c04, s02c05, s02c06, s02c07, s02c08, s02c09, h1, h2, h3, h4, h5, h6, h7, h8]

end PrincipiaTractalis.XiPanels
