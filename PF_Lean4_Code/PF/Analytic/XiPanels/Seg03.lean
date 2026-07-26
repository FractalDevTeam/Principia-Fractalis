import PF.Analytic.XiPanels.Seg03P1
import PF.Analytic.XiPanels.Seg03P2
import PF.Analytic.XiPanels.Seg03P3
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real

/-- Panel-sum lower bound for segment 3: `[1.125, 1.1875]`, `n = 25`. -/
theorem seg03 : (0.5262304967 : ℝ)
    ≤ ∑ i ∈ Finset.range 25, nodeR (1.12625 + 0.0025 * (i : ℕ)) := by
  have h1 := nodeSum_split 3 22 25 (1.12625 : ℝ) 0.0025 1.13375 (by norm_num) (by norm_num)
  have h2 := nodeSum_split 3 19 22 (1.13375 : ℝ) 0.0025 1.14125 (by norm_num) (by norm_num)
  have h3 := nodeSum_split 3 16 19 (1.14125 : ℝ) 0.0025 1.14875 (by norm_num) (by norm_num)
  have h4 := nodeSum_split 3 13 16 (1.14875 : ℝ) 0.0025 1.15625 (by norm_num) (by norm_num)
  have h5 := nodeSum_split 3 10 13 (1.15625 : ℝ) 0.0025 1.16375 (by norm_num) (by norm_num)
  have h6 := nodeSum_split 3 7 10 (1.16375 : ℝ) 0.0025 1.17125 (by norm_num) (by norm_num)
  have h7 := nodeSum_split 3 4 7 (1.17125 : ℝ) 0.0025 1.17875 (by norm_num) (by norm_num)
  have h8 := nodeSum_split 3 1 4 (1.17875 : ℝ) 0.0025 1.18625 (by norm_num) (by norm_num)
  linarith [s03c01, s03c02, s03c03, s03c04, s03c05, s03c06, s03c07, s03c08, s03c09, h1, h2, h3, h4, h5, h6, h7, h8]

end PrincipiaTractalis.XiPanels
