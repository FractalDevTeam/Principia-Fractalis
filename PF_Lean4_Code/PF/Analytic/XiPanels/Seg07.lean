import PF.Analytic.XiPanels.Seg07P1
import PF.Analytic.XiPanels.Seg07P2
import PF.Analytic.XiPanels.Seg07P3
namespace PrincipiaTractalis.XiPanels
open PrincipiaTractalis.XiOnLineZeroCore
open scoped Real

/-- Panel-sum lower bound for segment 7: `[1.5, 1.625]`, `n = 32`. -/
theorem seg07 : (-0.3235692421 : ℝ)
    ≤ ∑ i ∈ Finset.range 32, nodeR (1.501953125 + 0.00390625 * (i : ℕ)) := by
  have h1 := nodeSum_split 3 29 32 (1.501953125 : ℝ) 0.00390625 1.513671875 (by norm_num) (by norm_num)
  have h2 := nodeSum_split 3 26 29 (1.513671875 : ℝ) 0.00390625 1.525390625 (by norm_num) (by norm_num)
  have h3 := nodeSum_split 3 23 26 (1.525390625 : ℝ) 0.00390625 1.537109375 (by norm_num) (by norm_num)
  have h4 := nodeSum_split 3 20 23 (1.537109375 : ℝ) 0.00390625 1.548828125 (by norm_num) (by norm_num)
  have h5 := nodeSum_split 3 17 20 (1.548828125 : ℝ) 0.00390625 1.560546875 (by norm_num) (by norm_num)
  have h6 := nodeSum_split 3 14 17 (1.560546875 : ℝ) 0.00390625 1.572265625 (by norm_num) (by norm_num)
  have h7 := nodeSum_split 3 11 14 (1.572265625 : ℝ) 0.00390625 1.583984375 (by norm_num) (by norm_num)
  have h8 := nodeSum_split 3 8 11 (1.583984375 : ℝ) 0.00390625 1.595703125 (by norm_num) (by norm_num)
  have h9 := nodeSum_split 3 5 8 (1.595703125 : ℝ) 0.00390625 1.607421875 (by norm_num) (by norm_num)
  have h10 := nodeSum_split 3 2 5 (1.607421875 : ℝ) 0.00390625 1.619140625 (by norm_num) (by norm_num)
  linarith [s07c01, s07c02, s07c03, s07c04, s07c05, s07c06, s07c07, s07c08, s07c09, s07c10, s07c11, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

end PrincipiaTractalis.XiPanels
