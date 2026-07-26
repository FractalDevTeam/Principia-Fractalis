import PF.Analytic.XiPanels.Seg01P1
import PF.Analytic.XiPanels.Seg01P2
import PF.Analytic.XiPanels.Seg01P3
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real

/-- Panel-sum lower bound for segment 1: `[1, 1.0625]`, `n = 25`. -/
theorem seg01 : (1.8531401634 : ℝ)
    ≤ ∑ i ∈ Finset.range 25, nodeR (1.00125 + 0.0025 * (i : ℕ)) := by
  have h1 := nodeSum_split 3 22 25 (1.00125 : ℝ) 0.0025 1.00875 (by norm_num) (by norm_num)
  have h2 := nodeSum_split 3 19 22 (1.00875 : ℝ) 0.0025 1.01625 (by norm_num) (by norm_num)
  have h3 := nodeSum_split 3 16 19 (1.01625 : ℝ) 0.0025 1.02375 (by norm_num) (by norm_num)
  have h4 := nodeSum_split 3 13 16 (1.02375 : ℝ) 0.0025 1.03125 (by norm_num) (by norm_num)
  have h5 := nodeSum_split 3 10 13 (1.03125 : ℝ) 0.0025 1.03875 (by norm_num) (by norm_num)
  have h6 := nodeSum_split 3 7 10 (1.03875 : ℝ) 0.0025 1.04625 (by norm_num) (by norm_num)
  have h7 := nodeSum_split 3 4 7 (1.04625 : ℝ) 0.0025 1.05375 (by norm_num) (by norm_num)
  have h8 := nodeSum_split 3 1 4 (1.05375 : ℝ) 0.0025 1.06125 (by norm_num) (by norm_num)
  linarith [s01c01, s01c02, s01c03, s01c04, s01c05, s01c06, s01c07, s01c08, s01c09, h1, h2, h3, h4, h5, h6, h7, h8]

end PrincipiaTractalis.XiPanels
