import PF.Analytic.XiPanels.Seg08P1
import PF.Analytic.XiPanels.Seg08P2
import PF.Analytic.XiPanels.Seg08P3
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real

/-- Panel-sum lower bound for segment 8: `[1.625, 1.75]`, `n = 25`. -/
theorem seg08 : (-0.1087282646 : ℝ)
    ≤ ∑ i ∈ Finset.range 25, nodeR (1.6275 + 0.005 * (i : ℕ)) := by
  have h1 := nodeSum_split 3 22 25 (1.6275 : ℝ) 0.005 1.6425 (by norm_num) (by norm_num)
  have h2 := nodeSum_split 3 19 22 (1.6425 : ℝ) 0.005 1.6575 (by norm_num) (by norm_num)
  have h3 := nodeSum_split 3 16 19 (1.6575 : ℝ) 0.005 1.6725 (by norm_num) (by norm_num)
  have h4 := nodeSum_split 3 13 16 (1.6725 : ℝ) 0.005 1.6875 (by norm_num) (by norm_num)
  have h5 := nodeSum_split 3 10 13 (1.6875 : ℝ) 0.005 1.7025 (by norm_num) (by norm_num)
  have h6 := nodeSum_split 3 7 10 (1.7025 : ℝ) 0.005 1.7175 (by norm_num) (by norm_num)
  have h7 := nodeSum_split 3 4 7 (1.7175 : ℝ) 0.005 1.7325 (by norm_num) (by norm_num)
  have h8 := nodeSum_split 3 1 4 (1.7325 : ℝ) 0.005 1.7475 (by norm_num) (by norm_num)
  linarith [s08c01, s08c02, s08c03, s08c04, s08c05, s08c06, s08c07, s08c08, s08c09, h1, h2, h3, h4, h5, h6, h7, h8]

end PrincipiaTractalis.XiPanels
