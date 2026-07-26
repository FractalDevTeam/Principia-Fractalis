import PF.Analytic.XiPanels.Seg05P1
import PF.Analytic.XiPanels.Seg05P2
import PF.Analytic.XiPanels.Seg05P3
import PF.Analytic.XiPanels.Seg05P4
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real

/-- Panel-sum lower bound for segment 5: `[1.25, 1.375]`, `n = 40`. -/
theorem seg05 : (-0.4921928491 : ℝ)
    ≤ ∑ i ∈ Finset.range 40, nodeR (1.2515625 + 0.003125 * (i : ℕ)) := by
  have h1 := nodeSum_split 3 37 40 (1.2515625 : ℝ) 0.003125 1.2609375 (by norm_num) (by norm_num)
  have h2 := nodeSum_split 3 34 37 (1.2609375 : ℝ) 0.003125 1.2703125 (by norm_num) (by norm_num)
  have h3 := nodeSum_split 3 31 34 (1.2703125 : ℝ) 0.003125 1.2796875 (by norm_num) (by norm_num)
  have h4 := nodeSum_split 3 28 31 (1.2796875 : ℝ) 0.003125 1.2890625 (by norm_num) (by norm_num)
  have h5 := nodeSum_split 3 25 28 (1.2890625 : ℝ) 0.003125 1.2984375 (by norm_num) (by norm_num)
  have h6 := nodeSum_split 3 22 25 (1.2984375 : ℝ) 0.003125 1.3078125 (by norm_num) (by norm_num)
  have h7 := nodeSum_split 3 19 22 (1.3078125 : ℝ) 0.003125 1.3171875 (by norm_num) (by norm_num)
  have h8 := nodeSum_split 3 16 19 (1.3171875 : ℝ) 0.003125 1.3265625 (by norm_num) (by norm_num)
  have h9 := nodeSum_split 3 13 16 (1.3265625 : ℝ) 0.003125 1.3359375 (by norm_num) (by norm_num)
  have h10 := nodeSum_split 3 10 13 (1.3359375 : ℝ) 0.003125 1.3453125 (by norm_num) (by norm_num)
  have h11 := nodeSum_split 3 7 10 (1.3453125 : ℝ) 0.003125 1.3546875 (by norm_num) (by norm_num)
  have h12 := nodeSum_split 3 4 7 (1.3546875 : ℝ) 0.003125 1.3640625 (by norm_num) (by norm_num)
  have h13 := nodeSum_split 3 1 4 (1.3640625 : ℝ) 0.003125 1.3734375 (by norm_num) (by norm_num)
  linarith [s05c01, s05c02, s05c03, s05c04, s05c05, s05c06, s05c07, s05c08, s05c09, s05c10, s05c11, s05c12, s05c13, s05c14, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]

end PrincipiaTractalis.XiPanels
