/-
# PF.Analytic.XiOnLineZeroT15

t = 15 mirror of `PF.Analytic.XiOnLineZero`.  Produces the kernel-clean
endpoint `Xi_15_pos : 0 < Xi 15` and its trivial definitional inhabitation
of the corpus target `Xi_Positive_At_15`.

Reuses r120's generic quadrature machinery verbatim:
- `Xi_split_intervalIntegral`, `Xi_tail_bound`, `omega_partial_error`,
  `abs_thetaTermD2_sum_le_at`, `composite_midpoint_error`
  are all parametric in `t`.
- The transcendental constants `e0_01..e0_14`, `tail_le` in
  `XiOnLineZeroConstants` are t-independent and reused verbatim.

Duplicates with t = 15 substitution:
- K-bounds `K0_15_le`, `K1_15_le`, `K2_15_le`, `sumK_15_le`;
- truncated integrand `FT_15` and its derivative/integrability lemmas;
- panel-consumer `seg_lower_15`;
- assembled integral lower bound `int_lower_15`;
- endpoint `Xi_15_pos` and definitional bridge to `Xi_Positive_At_15`.

Zero project axioms, no `sorry`, no `native_decide`.
-/
import PF.Analytic.XiOnLineZeroCoreT15
import PF.Analytic.XiOnLineZeroConstants
import PF.Analytic.UnifiedClayClosureViaRouteBSpecificXiAndFullPinning_r288
import PF.Analytic.XiPanelsT15.Seg01
import PF.Analytic.XiPanelsT15.Seg02
import PF.Analytic.XiPanelsT15.Seg03
import PF.Analytic.XiPanelsT15.Seg04
import PF.Analytic.XiPanelsT15.Seg05
import PF.Analytic.XiPanelsT15.Seg06
import PF.Analytic.XiPanelsT15.Seg07
import PF.Analytic.XiPanelsT15.Seg08
import PF.Analytic.XiPanelsT15.Seg09
import PF.Analytic.XiPanelsT15.Seg10
import PF.Analytic.XiPanelsT15.Seg11
import PF.Analytic.XiPanelsT15.Seg12
import PF.Analytic.XiPanelsT15.Seg13
import PF.Analytic.XiPanelsT15.Seg14

namespace PrincipiaTractalis.XiOnLineZeroT15

open Set MeasureTheory Filter
open PrincipiaTractalis.XiRealWitness
open PrincipiaTractalis.XiThetaIntegral
open PrincipiaTractalis.XiQuadrature
open PrincipiaTractalis.XiOnLineZeroCore
open PrincipiaTractalis.XiOnLineZeroCoreT15
open PrincipiaTractalis.XiOnLineZeroConstants
open scoped Real Topology

/-! ## §1 -- the truncated integrand at `t = 15` -/

/-- The `N = 3` truncated critical-line integrand at `t = 15`. -/
noncomputable def FT_15 (y : ℝ) : ℝ := ∑ k ∈ Finset.range 3, thetaTerm (15 : ℝ) k y

theorem FT_15_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt FT_15 (∑ k ∈ Finset.range 3, thetaTermD1 (15 : ℝ) k x) x :=
  hasDerivAt_thetaTerm_sum (15 : ℝ) 3 hx

theorem FT_15_integrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable FT_15 volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  intro x hx
  have hx0 : 0 < x := by
    rcases le_total a b with h | h
    · rw [Set.uIcc_of_le h] at hx; exact lt_of_lt_of_le ha hx.1
    · rw [Set.uIcc_of_ge h] at hx; exact lt_of_lt_of_le hb hx.1
  exact (FT_15_hasDerivAt hx0).continuousAt.continuousWithinAt

/-- `FT_15` IS the `omegaPartial`-truncated theta integrand at `t = 15`. -/
theorem trunc_eq_FT_15 :
    (fun u : ℝ ↦ 2 * u ^ (-(3 / 4) : ℝ) * Real.cos ((15 : ℝ) / 2 * Real.log u)
        * omegaPartial 3 u) = FT_15 :=
  truncated_integrand_eq (15 : ℝ) 3

/-! ## §2 -- the `C²` constants at `t = 15` -/

private theorem habs15 : |(15 : ℝ)| = 15 := abs_of_pos (by norm_num)

theorem K0_15_le : thetaTermK (15 : ℝ) 0 ≤ 276.04 := by
  have hpi : π < 3.141593 := Real.pi_lt_d6
  have hpi0 : (0 : ℝ) < π := Real.pi_pos
  unfold thetaTermK
  rw [habs15]
  push_cast
  nlinarith [hpi, hpi0]

theorem K1_15_le : thetaTermK (15 : ℝ) 1 ≤ 883.15 := by
  have hpi : π < 3.141593 := Real.pi_lt_d6
  have hpi0 : (0 : ℝ) < π := Real.pi_pos
  unfold thetaTermK
  rw [habs15]
  push_cast
  nlinarith [hpi, hpi0]

theorem K2_15_le : thetaTermK (15 : ℝ) 2 ≤ 2684.56 := by
  have hpi : π < 3.141593 := Real.pi_lt_d6
  have hpi0 : (0 : ℝ) < π := Real.pi_pos
  unfold thetaTermK
  rw [habs15]
  push_cast
  nlinarith [hpi, hpi0]

theorem K_15_nonneg (n : ℕ) : 0 ≤ thetaTermK (15 : ℝ) n := by
  unfold thetaTermK
  have h1 : (0 : ℝ) ≤ |(15 : ℝ)| := abs_nonneg _
  positivity

/-- The panel-local `C²` bound at `t = 15` in the rational shape the
    segments use. -/
theorem sumK_15_le {c : ℝ} (hc : 1 ≤ c) {e0 : ℝ} (he0 : Real.exp (-(π * c)) ≤ e0) :
    (∑ k ∈ Finset.range 3, Real.exp (-π * ((k : ℝ) + 1) ^ 2 * c) * thetaTermK (15 : ℝ) k)
      ≤ 276.04 * e0 + 0.00309 := by
  have hE := exp_neg_pi_le
  have hEpos : (0 : ℝ) < Real.exp (-π) := Real.exp_pos _
  have hpi0 : (0 : ℝ) < π := Real.pi_pos
  have h0 : Real.exp (-π * ((0 : ℝ) + 1) ^ 2 * c) = Real.exp (-(π * c)) := by
    congr 1; ring
  have h1 : Real.exp (-π * ((1 : ℝ) + 1) ^ 2 * c) ≤ 0.0000034875 := by
    have hle : -π * ((1 : ℝ) + 1) ^ 2 * c ≤ ((4 : ℕ) : ℝ) * (-π) := by
      push_cast; nlinarith
    refine le_trans (Real.exp_le_exp.mpr hle) ?_
    rw [Real.exp_nat_mul]
    calc Real.exp (-π) ^ (4 : ℕ) ≤ (0.04321392 : ℝ) ^ (4 : ℕ) :=
          pow_le_pow_left₀ hEpos.le hE 4
      _ ≤ 0.0000034875 := by norm_num
  have h2 : Real.exp (-π * ((2 : ℝ) + 1) ^ 2 * c) ≤ 0.00000000000053 := by
    have hle : -π * ((2 : ℝ) + 1) ^ 2 * c ≤ ((9 : ℕ) : ℝ) * (-π) := by
      push_cast; nlinarith
    refine le_trans (Real.exp_le_exp.mpr hle) ?_
    rw [Real.exp_nat_mul]
    calc Real.exp (-π) ^ (9 : ℕ) ≤ (0.04321392 : ℝ) ^ (9 : ℕ) :=
          pow_le_pow_left₀ hEpos.le hE 9
      _ ≤ 0.00000000000053 := by norm_num
  have he0n : (0 : ℝ) ≤ e0 := le_trans (Real.exp_pos _).le he0
  have hK0 := K0_15_le
  have hK1 := K1_15_le
  have hK2 := K2_15_le
  have hk0 := K_15_nonneg 0
  have hk1 := K_15_nonneg 1
  have hk2 := K_15_nonneg 2
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  push_cast
  rw [h0]
  nlinarith [mul_le_mul he0 hK0 hk0 he0n,
    mul_le_mul h1 hK1 hk1 (by norm_num : (0:ℝ) ≤ 0.0000034875),
    mul_le_mul h2 hK2 hk2 (by norm_num : (0:ℝ) ≤ 0.00000000000053)]

/-! ## §3 -- the per-segment lower bound at `t = 15` -/

theorem seg_lower_15 (c d u0 h : ℝ) (n : ℕ) (e0 lo mb bnd : ℝ)
    (hn : 0 < n) (hc : 1 ≤ c) (hcd : c ≤ d)
    (hh : h = (d - c) / (n : ℕ)) (hu0 : u0 = c + h / 2)
    (he0 : Real.exp (-(π * c)) ≤ e0) (hmb : 276.04 * e0 + 0.00309 ≤ mb)
    (hlo : lo ≤ ∑ i ∈ Finset.range n, nodeR15 (u0 + h * (i : ℕ)))
    (hbnd : bnd ≤ h * lo - mb * (d - c) ^ 3 / (24 * (n : ℕ) ^ 2)) :
    bnd ≤ ∫ x in c..d, FT_15 x := by
  have hnR : (0 : ℝ) < (n : ℕ) := by exact_mod_cast hn
  have hhpos : 0 ≤ h := by rw [hh]; exact div_nonneg (by linarith) hnR.le
  have hmem : ∀ x ∈ Set.uIcc c d, 1 ≤ x := by
    intro x hx
    rw [Set.uIcc_of_le hcd] at hx
    exact le_trans hc hx.1
  have hM : ∀ x ∈ Set.uIcc c d,
      |∑ k ∈ Finset.range 3, thetaTermD2 (15 : ℝ) k x| ≤ mb := by
    intro x hx
    refine le_trans (abs_thetaTermD2_sum_le_at (15 : ℝ) 3 hc ?_) ?_
    · rw [Set.uIcc_of_le hcd] at hx; exact hx.1
    · exact le_trans (sumK_15_le hc he0) hmb
  have hf : ∀ x ∈ Set.uIcc c d,
      HasDerivAt FT_15 (∑ k ∈ Finset.range 3, thetaTermD1 (15 : ℝ) k x) x :=
    fun x hx ↦ FT_15_hasDerivAt (lt_of_lt_of_le one_pos (hmem x hx))
  have hf' : ∀ x ∈ Set.uIcc c d,
      HasDerivAt (fun y ↦ ∑ k ∈ Finset.range 3, thetaTermD1 (15 : ℝ) k y)
        (∑ k ∈ Finset.range 3, thetaTermD2 (15 : ℝ) k x) x :=
    fun x hx ↦ hasDerivAt_thetaTermD1_sum (15 : ℝ) 3
      (lt_of_lt_of_le one_pos (hmem x hx))
  have key := composite_midpoint_error hn hcd hf hf' hM
  have hnodes : (∑ i ∈ Finset.range n, FT_15 (c + (d - c) / (n : ℕ) * ((i : ℕ) + 1 / 2)))
      = ∑ i ∈ Finset.range n, nodeR15 (u0 + h * (i : ℕ)) := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have harg : c + (d - c) / (n : ℕ) * ((i : ℕ) + 1 / 2) = u0 + h * (i : ℕ) := by
      rw [hu0, hh]; ring
    have hpos : (0 : ℝ) < u0 + h * (i : ℕ) := by
      have hi : (0 : ℝ) ≤ h * (i : ℕ) := mul_nonneg hhpos (Nat.cast_nonneg i)
      have h2 : (1 : ℝ) ≤ u0 := by rw [hu0]; linarith
      linarith
    rw [harg]
    exact (nodeR15_eq hpos).symm
  rw [hnodes, ← hh] at key
  have hS := abs_le.mp key
  have hmul : h * lo ≤ h * (∑ i ∈ Finset.range n, nodeR15 (u0 + h * (i : ℕ))) :=
    mul_le_mul_of_nonneg_left hlo hhpos
  linarith [hS.1, hS.2]

/-! ## §4 -- the assembled lower bound for `∫_1^5 FT_15` -/

/-- Certified rational lower bound `4441/10^6 ≤ ∫_1^5 FT_15`.  Assembled
    from the 14 `seg_lower_15` calls with numerical data emitted by
    `scripts/gen_r120_panels_t15.py` (see `scripts/ChunkTable_t15_report.txt`
    for the audit trail; every value was computed at mpmath dps = 100 and
    floored / ceilinged toward the safe side). -/
theorem int_lower_15 : (0.004441 : ℝ) ≤ ∫ x in (1 : ℝ)..5, FT_15 x := by
  have i01 := seg_lower_15 1 1.0625 1.00125 0.0025 25
      0.04321392 (1.8564816116) 11.931861 (0.00464100982)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    e0_01 (by norm_num) XiPanelsT15.seg01_15 (by push_cast; norm_num)
  have i02 := seg_lower_15 1.0625 1.125 1.06375 0.0025 25
      0.03550996 (1.1804243044) 9.80526 (0.00295090117)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    e0_02 (by norm_num) XiPanelsT15.seg02_15 (by push_cast; norm_num)
  have i03 := seg_lower_15 1.125 1.1875 1.12625 0.0025 25
      0.02917942 (0.5566449253) 8.057778 (0.00139148116)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    e0_03 (by norm_num) XiPanelsT15.seg03_15 (by push_cast; norm_num)
  have i04 := seg_lower_15 1.1875 1.25 1.1890625 0.003125 20
      0.02397746 (0.071159587) 6.621829 (0.0002222053)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    e0_04 (by norm_num) XiPanelsT15.seg04_15 (by push_cast; norm_num)
  have i05 := seg_lower_15 1.25 1.375 1.2515625 0.003125 40
      0.01970288 (-0.4427951447) 5.441873 (-0.00138401162)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    e0_05 (by norm_num) XiPanelsT15.seg05_15 (by push_cast; norm_num)
  have i06 := seg_lower_15 1.375 1.5 1.3765625 0.003125 40
      0.01330401 (-0.5954915359) 3.675529 (-0.001861098)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    e0_06 (by norm_num) XiPanelsT15.seg06_15 (by push_cast; norm_num)
  have i07 := seg_lower_15 1.5 1.625 1.501953125 0.00390625 32
      0.0089833 (-0.3304736619) 2.482841 (-0.00129111007)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    e0_07 (by norm_num) XiPanelsT15.seg07_15 (by push_cast; norm_num)
  have i08 := seg_lower_15 1.625 1.75 1.6275 0.005 25
      0.00606581 (-0.121455732) 1.677497 (-0.00060749709)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    e0_08 (by norm_num) XiPanelsT15.seg08_15 (by push_cast; norm_num)
  have i09 := seg_lower_15 1.75 2 1.7525 0.005 50
      0.00409583 (-0.0132524792) 1.133703 (-0.00006655764)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    e0_09 (by norm_num) XiPanelsT15.seg09_15 (by push_cast; norm_num)
  have i10 := seg_lower_15 2 2.25 2.003125 0.00625 40
      0.00186745 (0.0439081196) 0.518581 (0.00027421473)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    e0_10 (by norm_num) XiPanelsT15.seg10_15 (by push_cast; norm_num)
  have i11 := seg_lower_15 2.25 2.5 2.25390625 0.0078125 32
      0.00085144 (0.0191469852) 0.238122 (0.00014943442)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    e0_11 (by norm_num) XiPanelsT15.seg11_15 (by push_cast; norm_num)
  have i12 := seg_lower_15 2.5 3 2.505 0.01 50
      0.00038821 (0.0039339259) 0.110252 (0.00003910956)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    e0_12 (by norm_num) XiPanelsT15.seg12_15 (by push_cast; norm_num)
  have i13 := seg_lower_15 3 4 3.01 0.02 50
      0.0000807 (-0.0007382733) 0.025367 (-0.00001518825)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    e0_13 (by norm_num) XiPanelsT15.seg13_15 (by push_cast; norm_num)
  have i14 := seg_lower_15 4 5 4.025 0.05 20
      0.00000349 (-0.0000018258) 0.004054 (-0.00000051359)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    e0_14 (by norm_num) XiPanelsT15.seg14_15 (by push_cast; norm_num)
  have a01 : (∫ x in (1 : ℝ)..(1.0625 : ℝ), FT_15 x) + (∫ x in (1.0625 : ℝ)..(1.125 : ℝ), FT_15 x)
      = ∫ x in (1 : ℝ)..(1.125 : ℝ), FT_15 x :=
    intervalIntegral.integral_add_adjacent_intervals
      (FT_15_integrable (by norm_num) (by norm_num))
      (FT_15_integrable (by norm_num) (by norm_num))
  have a02 : (∫ x in (1 : ℝ)..(1.125 : ℝ), FT_15 x) + (∫ x in (1.125 : ℝ)..(1.1875 : ℝ), FT_15 x)
      = ∫ x in (1 : ℝ)..(1.1875 : ℝ), FT_15 x :=
    intervalIntegral.integral_add_adjacent_intervals
      (FT_15_integrable (by norm_num) (by norm_num))
      (FT_15_integrable (by norm_num) (by norm_num))
  have a03 : (∫ x in (1 : ℝ)..(1.1875 : ℝ), FT_15 x) + (∫ x in (1.1875 : ℝ)..(1.25 : ℝ), FT_15 x)
      = ∫ x in (1 : ℝ)..(1.25 : ℝ), FT_15 x :=
    intervalIntegral.integral_add_adjacent_intervals
      (FT_15_integrable (by norm_num) (by norm_num))
      (FT_15_integrable (by norm_num) (by norm_num))
  have a04 : (∫ x in (1 : ℝ)..(1.25 : ℝ), FT_15 x) + (∫ x in (1.25 : ℝ)..(1.375 : ℝ), FT_15 x)
      = ∫ x in (1 : ℝ)..(1.375 : ℝ), FT_15 x :=
    intervalIntegral.integral_add_adjacent_intervals
      (FT_15_integrable (by norm_num) (by norm_num))
      (FT_15_integrable (by norm_num) (by norm_num))
  have a05 : (∫ x in (1 : ℝ)..(1.375 : ℝ), FT_15 x) + (∫ x in (1.375 : ℝ)..(1.5 : ℝ), FT_15 x)
      = ∫ x in (1 : ℝ)..(1.5 : ℝ), FT_15 x :=
    intervalIntegral.integral_add_adjacent_intervals
      (FT_15_integrable (by norm_num) (by norm_num))
      (FT_15_integrable (by norm_num) (by norm_num))
  have a06 : (∫ x in (1 : ℝ)..(1.5 : ℝ), FT_15 x) + (∫ x in (1.5 : ℝ)..(1.625 : ℝ), FT_15 x)
      = ∫ x in (1 : ℝ)..(1.625 : ℝ), FT_15 x :=
    intervalIntegral.integral_add_adjacent_intervals
      (FT_15_integrable (by norm_num) (by norm_num))
      (FT_15_integrable (by norm_num) (by norm_num))
  have a07 : (∫ x in (1 : ℝ)..(1.625 : ℝ), FT_15 x) + (∫ x in (1.625 : ℝ)..(1.75 : ℝ), FT_15 x)
      = ∫ x in (1 : ℝ)..(1.75 : ℝ), FT_15 x :=
    intervalIntegral.integral_add_adjacent_intervals
      (FT_15_integrable (by norm_num) (by norm_num))
      (FT_15_integrable (by norm_num) (by norm_num))
  have a08 : (∫ x in (1 : ℝ)..(1.75 : ℝ), FT_15 x) + (∫ x in (1.75 : ℝ)..(2 : ℝ), FT_15 x)
      = ∫ x in (1 : ℝ)..(2 : ℝ), FT_15 x :=
    intervalIntegral.integral_add_adjacent_intervals
      (FT_15_integrable (by norm_num) (by norm_num))
      (FT_15_integrable (by norm_num) (by norm_num))
  have a09 : (∫ x in (1 : ℝ)..(2 : ℝ), FT_15 x) + (∫ x in (2 : ℝ)..(2.25 : ℝ), FT_15 x)
      = ∫ x in (1 : ℝ)..(2.25 : ℝ), FT_15 x :=
    intervalIntegral.integral_add_adjacent_intervals
      (FT_15_integrable (by norm_num) (by norm_num))
      (FT_15_integrable (by norm_num) (by norm_num))
  have a10 : (∫ x in (1 : ℝ)..(2.25 : ℝ), FT_15 x) + (∫ x in (2.25 : ℝ)..(2.5 : ℝ), FT_15 x)
      = ∫ x in (1 : ℝ)..(2.5 : ℝ), FT_15 x :=
    intervalIntegral.integral_add_adjacent_intervals
      (FT_15_integrable (by norm_num) (by norm_num))
      (FT_15_integrable (by norm_num) (by norm_num))
  have a11 : (∫ x in (1 : ℝ)..(2.5 : ℝ), FT_15 x) + (∫ x in (2.5 : ℝ)..(3 : ℝ), FT_15 x)
      = ∫ x in (1 : ℝ)..(3 : ℝ), FT_15 x :=
    intervalIntegral.integral_add_adjacent_intervals
      (FT_15_integrable (by norm_num) (by norm_num))
      (FT_15_integrable (by norm_num) (by norm_num))
  have a12 : (∫ x in (1 : ℝ)..(3 : ℝ), FT_15 x) + (∫ x in (3 : ℝ)..(4 : ℝ), FT_15 x)
      = ∫ x in (1 : ℝ)..(4 : ℝ), FT_15 x :=
    intervalIntegral.integral_add_adjacent_intervals
      (FT_15_integrable (by norm_num) (by norm_num))
      (FT_15_integrable (by norm_num) (by norm_num))
  have a13 : (∫ x in (1 : ℝ)..(4 : ℝ), FT_15 x) + (∫ x in (4 : ℝ)..(5 : ℝ), FT_15 x)
      = ∫ x in (1 : ℝ)..(5 : ℝ), FT_15 x :=
    intervalIntegral.integral_add_adjacent_intervals
      (FT_15_integrable (by norm_num) (by norm_num))
      (FT_15_integrable (by norm_num) (by norm_num))
  linarith [i01, i02, i03, i04, i05, i06, i07, i08, i09, i10, i11, i12, i13, i14,
    a01, a02, a03, a04, a05, a06, a07, a08, a09, a10, a11, a12, a13]

/-! ## §5 -- `0 < Xi 15` -/

/-- **★★★★★ THE t = 15 SPECIFIC XI POSITIVITY ★★★★★**
    Certified via the r120 theta-quadrature architecture:
    `Xi 15 = -4/901 + ∫_1^5 FT_15 + (ω-truncation correction) + tail`
    with `int_lower_15 ≥ 4441/10^6`, `|tail| ≤ 11/10^8`, and the
    ω-truncation integrated correction bounded by `10^-19` pointwise. -/
theorem Xi_15_pos : 0 < Xi 15 := by
  have hsplit := Xi_split_intervalIntegral (15 : ℝ) 5 (by norm_num)
  have htail := Xi_tail_bound (15 : ℝ) 5 (by norm_num)
  have htn := tail_le
  have hgint : IntervalIntegrable
      (fun u : ℝ ↦ 2 * u ^ (-(3 / 4) : ℝ) * Real.cos ((15 : ℝ) / 2 * Real.log u) * omega u)
      volume 1 5 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
      ((integrableOn_Xi_theta_integrand (15 : ℝ)).mono_set Set.Ioc_subset_Ioi_self)
  have hFTint : IntervalIntegrable FT_15 volume 1 5 :=
    FT_15_integrable (by norm_num) (by norm_num)
  have hsub : (∫ u in (1 : ℝ)..5,
        2 * u ^ (-(3 / 4) : ℝ) * Real.cos ((15 : ℝ) / 2 * Real.log u) * omega u)
      - (∫ x in (1 : ℝ)..5, FT_15 x)
      = ∫ u in (1 : ℝ)..5,
        (2 * u ^ (-(3 / 4) : ℝ) * Real.cos ((15 : ℝ) / 2 * Real.log u) * omega u - FT_15 u) :=
    (intervalIntegral.integral_sub hgint hFTint).symm
  have hbd : ∀ u ∈ Set.uIoc (1 : ℝ) 5,
      ‖2 * u ^ (-(3 / 4) : ℝ) * Real.cos ((15 : ℝ) / 2 * Real.log u) * omega u - FT_15 u‖
        ≤ 0.00000000000000000001 := by
    intro u hu
    rw [Set.uIoc_of_le (by norm_num : (1:ℝ) ≤ 5)] at hu
    have hu1 : (1 : ℝ) ≤ u := le_of_lt hu.1
    have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu1
    have hFTu : FT_15 u
        = 2 * u ^ (-(3 / 4) : ℝ) * Real.cos ((15 : ℝ) / 2 * Real.log u) * omegaPartial 3 u := by
      rw [← trunc_eq_FT_15]
    have hfac : 2 * u ^ (-(3 / 4) : ℝ) * Real.cos ((15 : ℝ) / 2 * Real.log u) * omega u - FT_15 u
        = (2 * u ^ (-(3 / 4) : ℝ) * Real.cos ((15 : ℝ) / 2 * Real.log u))
          * (omega u - omegaPartial 3 u) := by
      rw [hFTu]; ring
    have hrp : u ^ (-(3 / 4) : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hu1 (by norm_num)
    have hrp0 : (0 : ℝ) < u ^ (-(3 / 4) : ℝ) := Real.rpow_pos_of_pos hu0 _
    have hA : |2 * u ^ (-(3 / 4) : ℝ) * Real.cos ((15 : ℝ) / 2 * Real.log u)| ≤ 2 := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * u ^ (-(3 / 4) : ℝ))]
      nlinarith [Real.abs_cos_le_one ((15 : ℝ) / 2 * Real.log u),
        abs_nonneg (Real.cos ((15 : ℝ) / 2 * Real.log u))]
    have hom := omega_partial_error hu1 3
    have hE := exp_neg_pi_le
    have hEpos : (0 : ℝ) < Real.exp (-π) := Real.exp_pos _
    have hpi0 : (0 : ℝ) < π := Real.pi_pos
    have he16 : Real.exp (-π * (((3 : ℕ) : ℝ) + 1) ^ 2 * u) ≤ 0.000000000000000000001 := by
      have hle : -π * (((3 : ℕ) : ℝ) + 1) ^ 2 * u ≤ ((16 : ℕ) : ℝ) * (-π) := by
        push_cast; nlinarith
      refine le_trans (Real.exp_le_exp.mpr hle) ?_
      rw [Real.exp_nat_mul]
      calc Real.exp (-π) ^ (16 : ℕ) ≤ (0.04321392 : ℝ) ^ (16 : ℕ) :=
            pow_le_pow_left₀ hEpos.le hE 16
        _ ≤ 0.000000000000000000001 := by norm_num
    have hden : (0.95 : ℝ) ≤ 1 - Real.exp (-π) := by linarith
    have hnum : (0 : ℝ) ≤ Real.exp (-π * (((3 : ℕ) : ℝ) + 1) ^ 2 * u) := (Real.exp_pos _).le
    have hq : Real.exp (-π * (((3 : ℕ) : ℝ) + 1) ^ 2 * u) / (1 - Real.exp (-π))
        ≤ 0.0000000000000000000011 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have hd2 : |omega u - omegaPartial 3 u| ≤ 0.0000000000000000000011 := le_trans hom hq
    rw [Real.norm_eq_abs, hfac, abs_mul]
    nlinarith [abs_nonneg (omega u - omegaPartial 3 u),
      abs_nonneg (2 * u ^ (-(3 / 4) : ℝ) * Real.cos ((15 : ℝ) / 2 * Real.log u))]
  have hnb := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  rw [← hsub, Real.norm_eq_abs] at hnb
  have hnb2 := abs_le.mp hnb
  have hta := abs_le.mp htail
  have hil := int_lower_15
  have hcon : -(1 / (1 / 4 + (15 : ℝ) ^ 2)) = -(4 / 901) := by norm_num
  rw [hcon] at hsplit
  norm_num at hnb2 hsplit
  linarith [hnb2.1, hnb2.2, hta.1, hta.2, hil, htn]

/-! ## §6 -- definitional bridge to the corpus target `Xi_Positive_At_15` -/

open PrincipiaTractalis.UnifiedClayClosureViaRouteBSpecificXiAndFullPinning

/-- **★★★★★★★★★★★★★★★★★★★★★★ (r315) Xi_Positive_At_15 DISCHARGED ★★★★★★★★★★★★★★★★★★★★★★**
    — direct kernel-verified discharge via the t = 15 specialization of the
    r120 certified theta-quadrature architecture.  The corpus definition
    `Xi_Positive_At_15 : Prop := 0 < Xi 15` unfolds definitionally to the
    endpoint proved by `Xi_15_pos`. -/
theorem xi_positive_at_15_certified_direct_r120 : Xi_Positive_At_15 :=
  Xi_15_pos

end PrincipiaTractalis.XiOnLineZeroT15

-- Axiom check. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.XiOnLineZeroT15.int_lower_15
#print axioms PrincipiaTractalis.XiOnLineZeroT15.Xi_15_pos
#print axioms PrincipiaTractalis.XiOnLineZeroT15.xi_positive_at_15_certified_direct_r120
