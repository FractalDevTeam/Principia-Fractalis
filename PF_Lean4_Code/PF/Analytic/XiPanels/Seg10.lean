import PF.Analytic.XiPanels.Seg10P1
import PF.Analytic.XiPanels.Seg10P2
import PF.Analytic.XiPanels.Seg10P3
import PF.Analytic.XiPanels.Seg10P4
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real

/-- Panel-sum lower bound for segment 10: `[2, 2.25]`, `n = 40`. -/
theorem seg10 : (0.048806056 : ℝ)
    ≤ ∑ i ∈ Finset.range 40, nodeR (2.003125 + 0.00625 * (i : ℕ)) := by
  have h1 := nodeSum_split 3 37 40 (2.003125 : ℝ) 0.00625 2.021875 (by norm_num) (by norm_num)
  have h2 := nodeSum_split 3 34 37 (2.021875 : ℝ) 0.00625 2.040625 (by norm_num) (by norm_num)
  have h3 := nodeSum_split 3 31 34 (2.040625 : ℝ) 0.00625 2.059375 (by norm_num) (by norm_num)
  have h4 := nodeSum_split 3 28 31 (2.059375 : ℝ) 0.00625 2.078125 (by norm_num) (by norm_num)
  have h5 := nodeSum_split 3 25 28 (2.078125 : ℝ) 0.00625 2.096875 (by norm_num) (by norm_num)
  have h6 := nodeSum_split 3 22 25 (2.096875 : ℝ) 0.00625 2.115625 (by norm_num) (by norm_num)
  have h7 := nodeSum_split 3 19 22 (2.115625 : ℝ) 0.00625 2.134375 (by norm_num) (by norm_num)
  have h8 := nodeSum_split 3 16 19 (2.134375 : ℝ) 0.00625 2.153125 (by norm_num) (by norm_num)
  have h9 := nodeSum_split 3 13 16 (2.153125 : ℝ) 0.00625 2.171875 (by norm_num) (by norm_num)
  have h10 := nodeSum_split 3 10 13 (2.171875 : ℝ) 0.00625 2.190625 (by norm_num) (by norm_num)
  have h11 := nodeSum_split 3 7 10 (2.190625 : ℝ) 0.00625 2.209375 (by norm_num) (by norm_num)
  have h12 := nodeSum_split 3 4 7 (2.209375 : ℝ) 0.00625 2.228125 (by norm_num) (by norm_num)
  have h13 := nodeSum_split 3 1 4 (2.228125 : ℝ) 0.00625 2.246875 (by norm_num) (by norm_num)
  linarith [s10c01, s10c02, s10c03, s10c04, s10c05, s10c06, s10c07, s10c08, s10c09, s10c10, s10c11, s10c12, s10c13, s10c14, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]

end PrincipiaTractalis.XiPanels
