import PF.Analytic.XiPanels.Seg04P1
import PF.Analytic.XiPanels.Seg04P2
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real

/-- Panel-sum lower bound for segment 4: `[1.1875, 1.25]`, `n = 20`. -/
theorem seg04 : (0.0418538013 : ℝ)
    ≤ ∑ i ∈ Finset.range 20, nodeR (1.1890625 + 0.003125 * (i : ℕ)) := by
  have h1 := nodeSum_split 3 17 20 (1.1890625 : ℝ) 0.003125 1.1984375 (by norm_num) (by norm_num)
  have h2 := nodeSum_split 3 14 17 (1.1984375 : ℝ) 0.003125 1.2078125 (by norm_num) (by norm_num)
  have h3 := nodeSum_split 3 11 14 (1.2078125 : ℝ) 0.003125 1.2171875 (by norm_num) (by norm_num)
  have h4 := nodeSum_split 3 8 11 (1.2171875 : ℝ) 0.003125 1.2265625 (by norm_num) (by norm_num)
  have h5 := nodeSum_split 3 5 8 (1.2265625 : ℝ) 0.003125 1.2359375 (by norm_num) (by norm_num)
  have h6 := nodeSum_split 3 2 5 (1.2359375 : ℝ) 0.003125 1.2453125 (by norm_num) (by norm_num)
  linarith [s04c01, s04c02, s04c03, s04c04, s04c05, s04c06, s04c07, h1, h2, h3, h4, h5, h6]

end PrincipiaTractalis.XiPanels
