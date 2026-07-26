import PF.Analytic.XiPanels.Seg13P1
import PF.Analytic.XiPanels.Seg13P2
import PF.Analytic.XiPanels.Seg13P3
import PF.Analytic.XiPanels.Seg13P4
import PF.Analytic.XiPanels.Seg13P5
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real

/-- Panel-sum lower bound for segment 13: `[3, 4]`, `n = 50`. -/
theorem seg13 : (-0.0008306806 : ℝ)
    ≤ ∑ i ∈ Finset.range 50, nodeR (3.01 + 0.02 * (i : ℕ)) := by
  have h1 := nodeSum_split 3 47 50 (3.01 : ℝ) 0.02 3.07 (by norm_num) (by norm_num)
  have h2 := nodeSum_split 3 44 47 (3.07 : ℝ) 0.02 3.13 (by norm_num) (by norm_num)
  have h3 := nodeSum_split 3 41 44 (3.13 : ℝ) 0.02 3.19 (by norm_num) (by norm_num)
  have h4 := nodeSum_split 3 38 41 (3.19 : ℝ) 0.02 3.25 (by norm_num) (by norm_num)
  have h5 := nodeSum_split 3 35 38 (3.25 : ℝ) 0.02 3.31 (by norm_num) (by norm_num)
  have h6 := nodeSum_split 3 32 35 (3.31 : ℝ) 0.02 3.37 (by norm_num) (by norm_num)
  have h7 := nodeSum_split 3 29 32 (3.37 : ℝ) 0.02 3.43 (by norm_num) (by norm_num)
  have h8 := nodeSum_split 3 26 29 (3.43 : ℝ) 0.02 3.49 (by norm_num) (by norm_num)
  have h9 := nodeSum_split 3 23 26 (3.49 : ℝ) 0.02 3.55 (by norm_num) (by norm_num)
  have h10 := nodeSum_split 3 20 23 (3.55 : ℝ) 0.02 3.61 (by norm_num) (by norm_num)
  have h11 := nodeSum_split 3 17 20 (3.61 : ℝ) 0.02 3.67 (by norm_num) (by norm_num)
  have h12 := nodeSum_split 3 14 17 (3.67 : ℝ) 0.02 3.73 (by norm_num) (by norm_num)
  have h13 := nodeSum_split 3 11 14 (3.73 : ℝ) 0.02 3.79 (by norm_num) (by norm_num)
  have h14 := nodeSum_split 3 8 11 (3.79 : ℝ) 0.02 3.85 (by norm_num) (by norm_num)
  have h15 := nodeSum_split 3 5 8 (3.85 : ℝ) 0.02 3.91 (by norm_num) (by norm_num)
  have h16 := nodeSum_split 3 2 5 (3.91 : ℝ) 0.02 3.97 (by norm_num) (by norm_num)
  linarith [s13c01, s13c02, s13c03, s13c04, s13c05, s13c06, s13c07, s13c08, s13c09, s13c10, s13c11, s13c12, s13c13, s13c14, s13c15, s13c16, s13c17, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]

end PrincipiaTractalis.XiPanels
