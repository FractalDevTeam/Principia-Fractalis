/-
# PF.Analytic.RiemannXiBox0Panels.Seg1

Stage-1 assembly for r331b Box-0: combines P1..P8 chunk theorems into
raw exact-rational segment sum bounds and midpoint-scaled integral
bounds via `box0_re/im_midpoint_error_on_segment` + `box0_seg1_M_le_three`.

Segment: `[L, U] = [3/2, 25/16]`, `n = 23` midpoints, step `h = 1/368`.
M certificate: `box0_seg1_M_le_three` (kernel-clean, prior landing).
Midpoint error: `E_SEG = M · (U-L)^3 / (24 · n^2) ≤ 3/(4096·12696) = 1/17334272`.

Stage-1 endpoints:
* `RE_INT_LO = -39964981/54169600000`  ≈ -7.3778e-04
* `RE_INT_HI = 1/17334272`  ≈ 5.7689e-08
* `IM_INT_LO = -974941/1354240000000`  ≈ -7.1992e-07
* `IM_INT_HI = 61257/270848000000`  ≈ 2.2617e-07

SPDX-License-Identifier: Apache-2.0
-/

import PF.Analytic.RiemannXiThetaRealFormAndBoxes_r331b
import PF.Numerics.Box0Seg1MPrototype
import PF.Analytic.RiemannXiBox0Panels.Seg1P1
import PF.Analytic.RiemannXiBox0Panels.Seg1P2
import PF.Analytic.RiemannXiBox0Panels.Seg1P3
import PF.Analytic.RiemannXiBox0Panels.Seg1P4
import PF.Analytic.RiemannXiBox0Panels.Seg1P5
import PF.Analytic.RiemannXiBox0Panels.Seg1P6
import PF.Analytic.RiemannXiBox0Panels.Seg1P7
import PF.Analytic.RiemannXiBox0Panels.Seg1P8

namespace PrincipiaTractalis.RiemannXiBox0Panels.Seg1

open scoped Real BigOperators
open PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes
open PrincipiaTractalis.Box0Seg1MPrototype
open PrincipiaTractalis.RiemannXiBox0Panels.Seg1P1
open PrincipiaTractalis.RiemannXiBox0Panels.Seg1P2
open PrincipiaTractalis.RiemannXiBox0Panels.Seg1P3
open PrincipiaTractalis.RiemannXiBox0Panels.Seg1P4
open PrincipiaTractalis.RiemannXiBox0Panels.Seg1P5
open PrincipiaTractalis.RiemannXiBox0Panels.Seg1P6
open PrincipiaTractalis.RiemannXiBox0Panels.Seg1P7
open PrincipiaTractalis.RiemannXiBox0Panels.Seg1P8

/-! ## §1 — Raw exact-rational segment sum bounds (chunks + linarith) -/

theorem seg1_re_sum_lower (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    (-6787/25000 : ℝ)
      ≤ realThetaReIntegrandN 3 σ 15 ((1105/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1107/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1109/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1111/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1113/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1115/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1117/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1119/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1121/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1123/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1125/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1127/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1129/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1131/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1133/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1135/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1137/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1139/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1141/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1143/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1145/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1147/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1149/736 : ℝ)) := by
  have h1 := seg1_p1_chunk_bounds σ hσ0 hσ1
  have h2 := seg1_p2_chunk_bounds σ hσ0 hσ1
  have h3 := seg1_p3_chunk_bounds σ hσ0 hσ1
  have h4 := seg1_p4_chunk_bounds σ hσ0 hσ1
  have h5 := seg1_p5_chunk_bounds σ hσ0 hσ1
  have h6 := seg1_p6_chunk_bounds σ hσ0 hσ1
  have h7 := seg1_p7_chunk_bounds σ hσ0 hσ1
  have h8 := seg1_p8_chunk_bounds σ hσ0 hσ1
  linarith [h1.1, h2.1, h3.1, h4.1, h5.1, h6.1, h7.1, h8.1]

theorem seg1_re_sum_upper (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    realThetaReIntegrandN 3 σ 15 ((1105/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1107/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1109/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1111/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1113/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1115/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1117/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1119/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1121/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1123/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1125/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1127/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1129/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1131/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1133/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1135/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1137/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1139/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1141/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1143/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1145/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1147/736 : ℝ)) + realThetaReIntegrandN 3 σ 15 ((1149/736 : ℝ))
      ≤ (0 : ℝ) := by
  have h1 := seg1_p1_chunk_bounds σ hσ0 hσ1
  have h2 := seg1_p2_chunk_bounds σ hσ0 hσ1
  have h3 := seg1_p3_chunk_bounds σ hσ0 hσ1
  have h4 := seg1_p4_chunk_bounds σ hσ0 hσ1
  have h5 := seg1_p5_chunk_bounds σ hσ0 hσ1
  have h6 := seg1_p6_chunk_bounds σ hσ0 hσ1
  have h7 := seg1_p7_chunk_bounds σ hσ0 hσ1
  have h8 := seg1_p8_chunk_bounds σ hσ0 hσ1
  linarith [h1.2.1, h2.2.1, h3.2.1, h4.2.1, h5.2.1, h6.2.1, h7.2.1, h8.2.1]

theorem seg1_im_sum_lower (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    (-2437/10000000 : ℝ)
      ≤ realThetaImIntegrandN 3 σ 15 ((1105/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1107/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1109/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1111/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1113/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1115/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1117/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1119/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1121/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1123/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1125/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1127/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1129/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1131/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1133/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1135/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1137/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1139/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1141/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1143/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1145/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1147/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1149/736 : ℝ)) := by
  have h1 := seg1_p1_chunk_bounds σ hσ0 hσ1
  have h2 := seg1_p2_chunk_bounds σ hσ0 hσ1
  have h3 := seg1_p3_chunk_bounds σ hσ0 hσ1
  have h4 := seg1_p4_chunk_bounds σ hσ0 hσ1
  have h5 := seg1_p5_chunk_bounds σ hσ0 hσ1
  have h6 := seg1_p6_chunk_bounds σ hσ0 hσ1
  have h7 := seg1_p7_chunk_bounds σ hσ0 hσ1
  have h8 := seg1_p8_chunk_bounds σ hσ0 hσ1
  linarith [h1.2.2.1, h2.2.2.1, h3.2.2.1, h4.2.2.1, h5.2.2.1, h6.2.2.1, h7.2.2.1, h8.2.2.1]

theorem seg1_im_sum_upper (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    realThetaImIntegrandN 3 σ 15 ((1105/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1107/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1109/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1111/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1113/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1115/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1117/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1119/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1121/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1123/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1125/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1127/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1129/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1131/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1133/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1135/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1137/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1139/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1141/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1143/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1145/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1147/736 : ℝ)) + realThetaImIntegrandN 3 σ 15 ((1149/736 : ℝ))
      ≤ (31/500000 : ℝ) := by
  have h1 := seg1_p1_chunk_bounds σ hσ0 hσ1
  have h2 := seg1_p2_chunk_bounds σ hσ0 hσ1
  have h3 := seg1_p3_chunk_bounds σ hσ0 hσ1
  have h4 := seg1_p4_chunk_bounds σ hσ0 hσ1
  have h5 := seg1_p5_chunk_bounds σ hσ0 hσ1
  have h6 := seg1_p6_chunk_bounds σ hσ0 hσ1
  have h7 := seg1_p7_chunk_bounds σ hσ0 hσ1
  have h8 := seg1_p8_chunk_bounds σ hσ0 hσ1
  linarith [h1.2.2.2, h2.2.2.2, h3.2.2.2, h4.2.2.2, h5.2.2.2, h6.2.2.2, h7.2.2.2, h8.2.2.2]

/-! ## §2 — Argument reduction + per-index bound extraction -/

/-- Generic midpoint argument reduction: `L + (U-L)/n·(k+1/2) = (1105+2k)/736`. -/
private lemma mid_arg_eq_u (k : ℕ) :
    ((3 : ℝ)/2 + (25/16 - 3/2) / 23 * ((k : ℝ) + 1/2))
    = ((1105 + 2 * k : ℕ) : ℝ)/736 := by
  push_cast; ring

/-- Per-index literal-form reduction: `((1105 + 2*k : ℕ) : ℝ)/736 = (1105+2k)/736`
where the RHS is a numeric ℝ literal. -/
private lemma u_eq_0 : (((1105 + 2 * 0 : ℕ) : ℝ)/736) = (1105/736 : ℝ) := by
  norm_num
private lemma u_eq_1 : (((1105 + 2 * 1 : ℕ) : ℝ)/736) = (1107/736 : ℝ) := by
  norm_num
private lemma u_eq_2 : (((1105 + 2 * 2 : ℕ) : ℝ)/736) = (1109/736 : ℝ) := by
  norm_num
private lemma u_eq_3 : (((1105 + 2 * 3 : ℕ) : ℝ)/736) = (1111/736 : ℝ) := by
  norm_num
private lemma u_eq_4 : (((1105 + 2 * 4 : ℕ) : ℝ)/736) = (1113/736 : ℝ) := by
  norm_num
private lemma u_eq_5 : (((1105 + 2 * 5 : ℕ) : ℝ)/736) = (1115/736 : ℝ) := by
  norm_num
private lemma u_eq_6 : (((1105 + 2 * 6 : ℕ) : ℝ)/736) = (1117/736 : ℝ) := by
  norm_num
private lemma u_eq_7 : (((1105 + 2 * 7 : ℕ) : ℝ)/736) = (1119/736 : ℝ) := by
  norm_num
private lemma u_eq_8 : (((1105 + 2 * 8 : ℕ) : ℝ)/736) = (1121/736 : ℝ) := by
  norm_num
private lemma u_eq_9 : (((1105 + 2 * 9 : ℕ) : ℝ)/736) = (1123/736 : ℝ) := by
  norm_num
private lemma u_eq_10 : (((1105 + 2 * 10 : ℕ) : ℝ)/736) = (1125/736 : ℝ) := by
  norm_num
private lemma u_eq_11 : (((1105 + 2 * 11 : ℕ) : ℝ)/736) = (1127/736 : ℝ) := by
  norm_num
private lemma u_eq_12 : (((1105 + 2 * 12 : ℕ) : ℝ)/736) = (1129/736 : ℝ) := by
  norm_num
private lemma u_eq_13 : (((1105 + 2 * 13 : ℕ) : ℝ)/736) = (1131/736 : ℝ) := by
  norm_num
private lemma u_eq_14 : (((1105 + 2 * 14 : ℕ) : ℝ)/736) = (1133/736 : ℝ) := by
  norm_num
private lemma u_eq_15 : (((1105 + 2 * 15 : ℕ) : ℝ)/736) = (1135/736 : ℝ) := by
  norm_num
private lemma u_eq_16 : (((1105 + 2 * 16 : ℕ) : ℝ)/736) = (1137/736 : ℝ) := by
  norm_num
private lemma u_eq_17 : (((1105 + 2 * 17 : ℕ) : ℝ)/736) = (1139/736 : ℝ) := by
  norm_num
private lemma u_eq_18 : (((1105 + 2 * 18 : ℕ) : ℝ)/736) = (1141/736 : ℝ) := by
  norm_num
private lemma u_eq_19 : (((1105 + 2 * 19 : ℕ) : ℝ)/736) = (1143/736 : ℝ) := by
  norm_num
private lemma u_eq_20 : (((1105 + 2 * 20 : ℕ) : ℝ)/736) = (1145/736 : ℝ) := by
  norm_num
private lemma u_eq_21 : (((1105 + 2 * 21 : ℕ) : ℝ)/736) = (1147/736 : ℝ) := by
  norm_num
private lemma u_eq_22 : (((1105 + 2 * 22 : ℕ) : ℝ)/736) = (1149/736 : ℝ) := by
  norm_num

/-! ## §3 — Midpoint-form Finset sum equals raw 23-term sum -/

theorem seg1_re_midpoint_sum_eq_raw (σ : ℝ) :
    (∑ i ∈ Finset.range 23, realThetaReIntegrandN 3 σ 15
       ((3 : ℝ)/2 + (25/16 - 3/2) / 23 * ((i : ℝ) + 1/2)))
    = realThetaReIntegrandN 3 σ 15 ((1105/736 : ℝ))
      + realThetaReIntegrandN 3 σ 15 ((1107/736 : ℝ))
      + realThetaReIntegrandN 3 σ 15 ((1109/736 : ℝ))
      + realThetaReIntegrandN 3 σ 15 ((1111/736 : ℝ))
      + realThetaReIntegrandN 3 σ 15 ((1113/736 : ℝ))
      + realThetaReIntegrandN 3 σ 15 ((1115/736 : ℝ))
      + realThetaReIntegrandN 3 σ 15 ((1117/736 : ℝ))
      + realThetaReIntegrandN 3 σ 15 ((1119/736 : ℝ))
      + realThetaReIntegrandN 3 σ 15 ((1121/736 : ℝ))
      + realThetaReIntegrandN 3 σ 15 ((1123/736 : ℝ))
      + realThetaReIntegrandN 3 σ 15 ((1125/736 : ℝ))
      + realThetaReIntegrandN 3 σ 15 ((1127/736 : ℝ))
      + realThetaReIntegrandN 3 σ 15 ((1129/736 : ℝ))
      + realThetaReIntegrandN 3 σ 15 ((1131/736 : ℝ))
      + realThetaReIntegrandN 3 σ 15 ((1133/736 : ℝ))
      + realThetaReIntegrandN 3 σ 15 ((1135/736 : ℝ))
      + realThetaReIntegrandN 3 σ 15 ((1137/736 : ℝ))
      + realThetaReIntegrandN 3 σ 15 ((1139/736 : ℝ))
      + realThetaReIntegrandN 3 σ 15 ((1141/736 : ℝ))
      + realThetaReIntegrandN 3 σ 15 ((1143/736 : ℝ))
      + realThetaReIntegrandN 3 σ 15 ((1145/736 : ℝ))
      + realThetaReIntegrandN 3 σ 15 ((1147/736 : ℝ))
      + realThetaReIntegrandN 3 σ 15 ((1149/736 : ℝ)) := by
  simp_rw [mid_arg_eq_u]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
             u_eq_0, u_eq_1, u_eq_2, u_eq_3, u_eq_4, u_eq_5, u_eq_6, u_eq_7, u_eq_8, u_eq_9, u_eq_10, u_eq_11, u_eq_12, u_eq_13, u_eq_14, u_eq_15, u_eq_16, u_eq_17, u_eq_18, u_eq_19, u_eq_20, u_eq_21, u_eq_22]

theorem seg1_im_midpoint_sum_eq_raw (σ : ℝ) :
    (∑ i ∈ Finset.range 23, realThetaImIntegrandN 3 σ 15
       ((3 : ℝ)/2 + (25/16 - 3/2) / 23 * ((i : ℝ) + 1/2)))
    = realThetaImIntegrandN 3 σ 15 ((1105/736 : ℝ))
      + realThetaImIntegrandN 3 σ 15 ((1107/736 : ℝ))
      + realThetaImIntegrandN 3 σ 15 ((1109/736 : ℝ))
      + realThetaImIntegrandN 3 σ 15 ((1111/736 : ℝ))
      + realThetaImIntegrandN 3 σ 15 ((1113/736 : ℝ))
      + realThetaImIntegrandN 3 σ 15 ((1115/736 : ℝ))
      + realThetaImIntegrandN 3 σ 15 ((1117/736 : ℝ))
      + realThetaImIntegrandN 3 σ 15 ((1119/736 : ℝ))
      + realThetaImIntegrandN 3 σ 15 ((1121/736 : ℝ))
      + realThetaImIntegrandN 3 σ 15 ((1123/736 : ℝ))
      + realThetaImIntegrandN 3 σ 15 ((1125/736 : ℝ))
      + realThetaImIntegrandN 3 σ 15 ((1127/736 : ℝ))
      + realThetaImIntegrandN 3 σ 15 ((1129/736 : ℝ))
      + realThetaImIntegrandN 3 σ 15 ((1131/736 : ℝ))
      + realThetaImIntegrandN 3 σ 15 ((1133/736 : ℝ))
      + realThetaImIntegrandN 3 σ 15 ((1135/736 : ℝ))
      + realThetaImIntegrandN 3 σ 15 ((1137/736 : ℝ))
      + realThetaImIntegrandN 3 σ 15 ((1139/736 : ℝ))
      + realThetaImIntegrandN 3 σ 15 ((1141/736 : ℝ))
      + realThetaImIntegrandN 3 σ 15 ((1143/736 : ℝ))
      + realThetaImIntegrandN 3 σ 15 ((1145/736 : ℝ))
      + realThetaImIntegrandN 3 σ 15 ((1147/736 : ℝ))
      + realThetaImIntegrandN 3 σ 15 ((1149/736 : ℝ)) := by
  simp_rw [mid_arg_eq_u]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
             u_eq_0, u_eq_1, u_eq_2, u_eq_3, u_eq_4, u_eq_5, u_eq_6, u_eq_7, u_eq_8, u_eq_9, u_eq_10, u_eq_11, u_eq_12, u_eq_13, u_eq_14, u_eq_15, u_eq_16, u_eq_17, u_eq_18, u_eq_19, u_eq_20, u_eq_21, u_eq_22]

/-! ## §4 — Midpoint sum bounds (composition of §1 and §3) -/

theorem seg1_re_midpoint_sum_lower (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    (-6787/25000 : ℝ)
      ≤ (∑ i ∈ Finset.range 23, realThetaReIntegrandN 3 σ 15
        ((3 : ℝ)/2 + (25/16 - 3/2) / 23 * ((i : ℝ) + 1/2))) := by
  rw [seg1_re_midpoint_sum_eq_raw]; exact seg1_re_sum_lower σ hσ0 hσ1

theorem seg1_re_midpoint_sum_upper (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    (∑ i ∈ Finset.range 23, realThetaReIntegrandN 3 σ 15
        ((3 : ℝ)/2 + (25/16 - 3/2) / 23 * ((i : ℝ) + 1/2))) ≤ (0 : ℝ) := by
  rw [seg1_re_midpoint_sum_eq_raw]; exact seg1_re_sum_upper σ hσ0 hσ1

theorem seg1_im_midpoint_sum_lower (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    (-2437/10000000 : ℝ)
      ≤ (∑ i ∈ Finset.range 23, realThetaImIntegrandN 3 σ 15
        ((3 : ℝ)/2 + (25/16 - 3/2) / 23 * ((i : ℝ) + 1/2))) := by
  rw [seg1_im_midpoint_sum_eq_raw]; exact seg1_im_sum_lower σ hσ0 hσ1

theorem seg1_im_midpoint_sum_upper (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    (∑ i ∈ Finset.range 23, realThetaImIntegrandN 3 σ 15
        ((3 : ℝ)/2 + (25/16 - 3/2) / 23 * ((i : ℝ) + 1/2))) ≤ (31/500000 : ℝ) := by
  rw [seg1_im_midpoint_sum_eq_raw]; exact seg1_im_sum_upper σ hσ0 hσ1

/-! ## §5 — Stage-1 integral bounds via midpoint error + M ≤ 3 -/

/-- Numeric shape of the midpoint sum with `(U-L)/n = 1/368`. -/
private lemma midpoint_scale_eq : ((25/16 : ℝ) - 3/2) / (23 : ℕ) = 1/368 := by
  push_cast; norm_num

/-- Numeric bound on midpoint error: `M·(U-L)³/(24·n²) ≤ 1/17334272`. -/
private lemma seg1_error_bound_le :
    (2 * ∑ n' ∈ Finset.range 3, thetaPowTermM 15 (25/32) (1425/1024) (3/2) n')
      * ((25/16 : ℝ) - 3/2) ^ 3 / (24 * (23 : ℕ) ^ 2)
      ≤ (1/17334272 : ℝ) := by
  have hM := box0_seg1_M_le_three
  set M := 2 * ∑ n' ∈ Finset.range 3, thetaPowTermM 15 (25/32) (1425/1024) (3/2) n' with hM_def
  -- Re-associate: M * X^3 / Y = M * (X^3 / Y)
  have hassoc : M * ((25/16 : ℝ) - 3/2) ^ 3 / (24 * (23 : ℕ) ^ 2)
              = M * (((25/16 : ℝ) - 3/2) ^ 3 / (24 * (23 : ℕ) ^ 2)) := by ring
  rw [hassoc]
  have hf : ((25/16 : ℝ) - 3/2) ^ 3 / (24 * (23 : ℕ) ^ 2) = (1/52002816 : ℝ) := by
    push_cast; norm_num
  rw [hf]
  have hpos : (0 : ℝ) < 1/52002816 := by norm_num
  calc M * (1/52002816 : ℝ)
        ≤ 3 * (1/52002816 : ℝ) := mul_le_mul_of_nonneg_right hM (le_of_lt hpos)
    _ = (1/17334272 : ℝ) := by norm_num

/-- ★ Stage-1 REAL integral lower bound. -/
theorem box0_seg1_re_integral_lower (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    ((-39964981/54169600000 : ℝ)) ≤ ∫ u in (3/2 : ℝ)..(25/16), realThetaReIntegrandN 3 σ 15 u := by
  have hL : (1 : ℝ) ≤ 3/2 := by norm_num
  have hLU : (3/2 : ℝ) ≤ 25/16 := by norm_num
  have hn : 0 < (23 : ℕ) := by decide
  have herr := box0_re_midpoint_error_on_segment (N := 3) hσ0 hσ1 hL hLU hn
  have hbound := seg1_error_bound_le
  have habs := abs_le.mp (le_trans herr hbound)
  -- habs.1: -(1/17334272) ≤ integral - midpoint_sum
  -- habs.2: integral - midpoint_sum ≤ 1/17334272
  have hmid := seg1_re_midpoint_sum_lower σ hσ0 hσ1
  have hscale : ((25/16 : ℝ) - 3/2) / (23 : ℕ) = 1/368 := midpoint_scale_eq
  rw [hscale] at habs
  linarith [habs.1, hmid]

/-- ★ Stage-1 REAL integral upper bound. -/
theorem box0_seg1_re_integral_upper (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    (∫ u in (3/2 : ℝ)..(25/16), realThetaReIntegrandN 3 σ 15 u) ≤ (1/17334272 : ℝ) := by
  have hL : (1 : ℝ) ≤ 3/2 := by norm_num
  have hLU : (3/2 : ℝ) ≤ 25/16 := by norm_num
  have hn : 0 < (23 : ℕ) := by decide
  have herr := box0_re_midpoint_error_on_segment (N := 3) hσ0 hσ1 hL hLU hn
  have hbound := seg1_error_bound_le
  have habs := abs_le.mp (le_trans herr hbound)
  have hmid := seg1_re_midpoint_sum_upper σ hσ0 hσ1
  have hscale : ((25/16 : ℝ) - 3/2) / (23 : ℕ) = 1/368 := midpoint_scale_eq
  rw [hscale] at habs
  linarith [habs.2, hmid]

/-- ★ Stage-1 IMAG integral lower bound. -/
theorem box0_seg1_im_integral_lower (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    ((-974941/1354240000000 : ℝ)) ≤ ∫ u in (3/2 : ℝ)..(25/16), realThetaImIntegrandN 3 σ 15 u := by
  have hL : (1 : ℝ) ≤ 3/2 := by norm_num
  have hLU : (3/2 : ℝ) ≤ 25/16 := by norm_num
  have hn : 0 < (23 : ℕ) := by decide
  have herr := box0_im_midpoint_error_on_segment (N := 3) hσ0 hσ1 hL hLU hn
  have hbound := seg1_error_bound_le
  have habs := abs_le.mp (le_trans herr hbound)
  have hmid := seg1_im_midpoint_sum_lower σ hσ0 hσ1
  have hscale : ((25/16 : ℝ) - 3/2) / (23 : ℕ) = 1/368 := midpoint_scale_eq
  rw [hscale] at habs
  linarith [habs.1, hmid]

/-- ★ Stage-1 IMAG integral upper bound. -/
theorem box0_seg1_im_integral_upper (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    (∫ u in (3/2 : ℝ)..(25/16), realThetaImIntegrandN 3 σ 15 u) ≤ (61257/270848000000 : ℝ) := by
  have hL : (1 : ℝ) ≤ 3/2 := by norm_num
  have hLU : (3/2 : ℝ) ≤ 25/16 := by norm_num
  have hn : 0 < (23 : ℕ) := by decide
  have herr := box0_im_midpoint_error_on_segment (N := 3) hσ0 hσ1 hL hLU hn
  have hbound := seg1_error_bound_le
  have habs := abs_le.mp (le_trans herr hbound)
  have hmid := seg1_im_midpoint_sum_upper σ hσ0 hσ1
  have hscale : ((25/16 : ℝ) - 3/2) / (23 : ℕ) = 1/368 := midpoint_scale_eq
  rw [hscale] at habs
  linarith [habs.2, hmid]

end PrincipiaTractalis.RiemannXiBox0Panels.Seg1
