import PF.Analytic.XiPanels.Seg14P1
import PF.Analytic.XiPanels.Seg14P2
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real

/-- Panel-sum lower bound for segment 14: `[4, 5]`, `n = 20`. -/
theorem seg14 : (0.0000012855 : ℝ)
    ≤ ∑ i ∈ Finset.range 20, nodeR (4.025 + 0.05 * (i : ℕ)) := by
  have h1 := nodeSum_split 3 17 20 (4.025 : ℝ) 0.05 4.175 (by norm_num) (by norm_num)
  have h2 := nodeSum_split 3 14 17 (4.175 : ℝ) 0.05 4.325 (by norm_num) (by norm_num)
  have h3 := nodeSum_split 3 11 14 (4.325 : ℝ) 0.05 4.475 (by norm_num) (by norm_num)
  have h4 := nodeSum_split 3 8 11 (4.475 : ℝ) 0.05 4.625 (by norm_num) (by norm_num)
  have h5 := nodeSum_split 3 5 8 (4.625 : ℝ) 0.05 4.775 (by norm_num) (by norm_num)
  have h6 := nodeSum_split 3 2 5 (4.775 : ℝ) 0.05 4.925 (by norm_num) (by norm_num)
  linarith [s14c01, s14c02, s14c03, s14c04, s14c05, s14c06, s14c07, h1, h2, h3, h4, h5, h6]

end PrincipiaTractalis.XiPanels
