import PF.Analytic.XiPanels.Seg12P1
import PF.Analytic.XiPanels.Seg12P2
import PF.Analytic.XiPanels.Seg12P3
import PF.Analytic.XiPanels.Seg12P4
import PF.Analytic.XiPanels.Seg12P5
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real

/-- Panel-sum lower bound for segment 12: `[2.5, 3]`, `n = 50`. -/
theorem seg12 : (0.002328187 : ℝ)
    ≤ ∑ i ∈ Finset.range 50, nodeR (2.505 + 0.01 * (i : ℕ)) := by
  have h1 := nodeSum_split 3 47 50 (2.505 : ℝ) 0.01 2.535 (by norm_num) (by norm_num)
  have h2 := nodeSum_split 3 44 47 (2.535 : ℝ) 0.01 2.565 (by norm_num) (by norm_num)
  have h3 := nodeSum_split 3 41 44 (2.565 : ℝ) 0.01 2.595 (by norm_num) (by norm_num)
  have h4 := nodeSum_split 3 38 41 (2.595 : ℝ) 0.01 2.625 (by norm_num) (by norm_num)
  have h5 := nodeSum_split 3 35 38 (2.625 : ℝ) 0.01 2.655 (by norm_num) (by norm_num)
  have h6 := nodeSum_split 3 32 35 (2.655 : ℝ) 0.01 2.685 (by norm_num) (by norm_num)
  have h7 := nodeSum_split 3 29 32 (2.685 : ℝ) 0.01 2.715 (by norm_num) (by norm_num)
  have h8 := nodeSum_split 3 26 29 (2.715 : ℝ) 0.01 2.745 (by norm_num) (by norm_num)
  have h9 := nodeSum_split 3 23 26 (2.745 : ℝ) 0.01 2.775 (by norm_num) (by norm_num)
  have h10 := nodeSum_split 3 20 23 (2.775 : ℝ) 0.01 2.805 (by norm_num) (by norm_num)
  have h11 := nodeSum_split 3 17 20 (2.805 : ℝ) 0.01 2.835 (by norm_num) (by norm_num)
  have h12 := nodeSum_split 3 14 17 (2.835 : ℝ) 0.01 2.865 (by norm_num) (by norm_num)
  have h13 := nodeSum_split 3 11 14 (2.865 : ℝ) 0.01 2.895 (by norm_num) (by norm_num)
  have h14 := nodeSum_split 3 8 11 (2.895 : ℝ) 0.01 2.925 (by norm_num) (by norm_num)
  have h15 := nodeSum_split 3 5 8 (2.925 : ℝ) 0.01 2.955 (by norm_num) (by norm_num)
  have h16 := nodeSum_split 3 2 5 (2.955 : ℝ) 0.01 2.985 (by norm_num) (by norm_num)
  linarith [s12c01, s12c02, s12c03, s12c04, s12c05, s12c06, s12c07, s12c08, s12c09, s12c10, s12c11, s12c12, s12c13, s12c14, s12c15, s12c16, s12c17, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]

end PrincipiaTractalis.XiPanels
