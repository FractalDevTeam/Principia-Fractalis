/-
# Box900Bridge_t14p5 -- union of the 40 σ=1 segments + box0 envelope -> UNCONDITIONAL
#   Re ξ(1 + (29/2)·i) < 0   (the first unconditional certified right-edge point).

Chains the 40 `box900_seg{j}_{re,im}_integral_lower` facts (each certified at σ=1,
t = 29/2 by midpoint quadrature + a C² majorant) over [1,5] via
`intervalIntegral.integral_add_adjacent_intervals`, rewrites to the set integral over
`Ioc 1 5`, applies `{re,im}_Lambda0_close_to_truncated_integral` (N=3, σ=1, t=29/2, T=5)
and `RiemannXiBox0Envelope.box0_envelope_le` EXACTLY ONCE to land certified LOWER bounds
on `Re Λ₀` and `Im Λ₀` at the point 1 + (29/2)i, then feeds them to the σ=1 point
pilot `re_xi_14p5_neg_of_edge_lb`.

Certified (exact rational, from the built segment literals):
  SUM RE_LO = 5960154573837048640917936252520696688132400897389/1258105427357669130240000000000000000000000000000000
            = 0.004737404707
  SUM IM_LO = 403888656096678504136787580520696688132400897389/1258105427357669130240000000000000000000000000000000
            = 0.000321029261
  Re Λ₀ ≥ SUM_RE_LO - 1/5000000 = 0.004737204707  ≥ 0.004735700000 (47357/10^7)
  Im Λ₀ ≥ SUM_IM_LO - 1/5000000 = 0.000320829261  ≥ 0.000300000000 (3/10^4)
  pilot key (29/2)^2·reA + (29/2)·imA = 1.000030925 > 1.

Scope (honest): a CLASSICALLY-KNOWN bounded fact.  NOT the Clay Riemann Hypothesis.

SPDX-License-Identifier: Apache-2.0
-/

import PF.Analytic.RiemannXiThetaRealFormAndBoxes_r331b
import PF.Analytic.RiemannXiBox0Envelope
import PF.Analytic.RightEdgeSignsPilot_t14p5
import PF.Analytic.RiemannXiBox900Panels.Seg01
import PF.Analytic.RiemannXiBox900Panels.Seg02
import PF.Analytic.RiemannXiBox900Panels.Seg03
import PF.Analytic.RiemannXiBox900Panels.Seg04
import PF.Analytic.RiemannXiBox900Panels.Seg05
import PF.Analytic.RiemannXiBox900Panels.Seg06
import PF.Analytic.RiemannXiBox900Panels.Seg07
import PF.Analytic.RiemannXiBox900Panels.Seg08
import PF.Analytic.RiemannXiBox900Panels.Seg09
import PF.Analytic.RiemannXiBox900Panels.Seg10
import PF.Analytic.RiemannXiBox900Panels.Seg11
import PF.Analytic.RiemannXiBox900Panels.Seg12
import PF.Analytic.RiemannXiBox900Panels.Seg13
import PF.Analytic.RiemannXiBox900Panels.Seg14
import PF.Analytic.RiemannXiBox900Panels.Seg15
import PF.Analytic.RiemannXiBox900Panels.Seg16
import PF.Analytic.RiemannXiBox900Panels.Seg17
import PF.Analytic.RiemannXiBox900Panels.Seg18
import PF.Analytic.RiemannXiBox900Panels.Seg19
import PF.Analytic.RiemannXiBox900Panels.Seg20
import PF.Analytic.RiemannXiBox900Panels.Seg21
import PF.Analytic.RiemannXiBox900Panels.Seg22
import PF.Analytic.RiemannXiBox900Panels.Seg23
import PF.Analytic.RiemannXiBox900Panels.Seg24
import PF.Analytic.RiemannXiBox900Panels.Seg25
import PF.Analytic.RiemannXiBox900Panels.Seg26
import PF.Analytic.RiemannXiBox900Panels.Seg27
import PF.Analytic.RiemannXiBox900Panels.Seg28
import PF.Analytic.RiemannXiBox900Panels.Seg29
import PF.Analytic.RiemannXiBox900Panels.Seg30
import PF.Analytic.RiemannXiBox900Panels.Seg31
import PF.Analytic.RiemannXiBox900Panels.Seg32
import PF.Analytic.RiemannXiBox900Panels.Seg33
import PF.Analytic.RiemannXiBox900Panels.Seg34
import PF.Analytic.RiemannXiBox900Panels.Seg35
import PF.Analytic.RiemannXiBox900Panels.Seg36
import PF.Analytic.RiemannXiBox900Panels.Seg37
import PF.Analytic.RiemannXiBox900Panels.Seg38
import PF.Analytic.RiemannXiBox900Panels.Seg39
import PF.Analytic.RiemannXiBox900Panels.Seg40

set_option autoImplicit false

namespace PrincipiaTractalis.RiemannXiBox900Bridge14p5

open scoped Real
open MeasureTheory
open PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.RiemannXiBox900Panels.Seg01
open PrincipiaTractalis.RiemannXiBox900Panels.Seg02
open PrincipiaTractalis.RiemannXiBox900Panels.Seg03
open PrincipiaTractalis.RiemannXiBox900Panels.Seg04
open PrincipiaTractalis.RiemannXiBox900Panels.Seg05
open PrincipiaTractalis.RiemannXiBox900Panels.Seg06
open PrincipiaTractalis.RiemannXiBox900Panels.Seg07
open PrincipiaTractalis.RiemannXiBox900Panels.Seg08
open PrincipiaTractalis.RiemannXiBox900Panels.Seg09
open PrincipiaTractalis.RiemannXiBox900Panels.Seg10
open PrincipiaTractalis.RiemannXiBox900Panels.Seg11
open PrincipiaTractalis.RiemannXiBox900Panels.Seg12
open PrincipiaTractalis.RiemannXiBox900Panels.Seg13
open PrincipiaTractalis.RiemannXiBox900Panels.Seg14
open PrincipiaTractalis.RiemannXiBox900Panels.Seg15
open PrincipiaTractalis.RiemannXiBox900Panels.Seg16
open PrincipiaTractalis.RiemannXiBox900Panels.Seg17
open PrincipiaTractalis.RiemannXiBox900Panels.Seg18
open PrincipiaTractalis.RiemannXiBox900Panels.Seg19
open PrincipiaTractalis.RiemannXiBox900Panels.Seg20
open PrincipiaTractalis.RiemannXiBox900Panels.Seg21
open PrincipiaTractalis.RiemannXiBox900Panels.Seg22
open PrincipiaTractalis.RiemannXiBox900Panels.Seg23
open PrincipiaTractalis.RiemannXiBox900Panels.Seg24
open PrincipiaTractalis.RiemannXiBox900Panels.Seg25
open PrincipiaTractalis.RiemannXiBox900Panels.Seg26
open PrincipiaTractalis.RiemannXiBox900Panels.Seg27
open PrincipiaTractalis.RiemannXiBox900Panels.Seg28
open PrincipiaTractalis.RiemannXiBox900Panels.Seg29
open PrincipiaTractalis.RiemannXiBox900Panels.Seg30
open PrincipiaTractalis.RiemannXiBox900Panels.Seg31
open PrincipiaTractalis.RiemannXiBox900Panels.Seg32
open PrincipiaTractalis.RiemannXiBox900Panels.Seg33
open PrincipiaTractalis.RiemannXiBox900Panels.Seg34
open PrincipiaTractalis.RiemannXiBox900Panels.Seg35
open PrincipiaTractalis.RiemannXiBox900Panels.Seg36
open PrincipiaTractalis.RiemannXiBox900Panels.Seg37
open PrincipiaTractalis.RiemannXiBox900Panels.Seg38
open PrincipiaTractalis.RiemannXiBox900Panels.Seg39
open PrincipiaTractalis.RiemannXiBox900Panels.Seg40

/-! ## integrability on subintervals of [1,5] (t = 29/2) -/
theorem re_integrable (σ : ℝ) {a b : ℝ}
    (ha : (1 : ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ 5) :
    IntervalIntegrable (realThetaReIntegrandN 3 σ (29/2)) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hab]
  exact (continuousOn_realThetaReIntegrandN_Icc 3 σ (29/2) 5).mono
    (Set.Icc_subset_Icc ha hb)

theorem im_integrable (σ : ℝ) {a b : ℝ}
    (ha : (1 : ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ 5) :
    IntervalIntegrable (realThetaImIntegrandN 3 σ (29/2)) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hab]
  exact (continuousOn_realThetaImIntegrandN_Icc 3 σ (29/2) 5).mono
    (Set.Icc_subset_Icc ha hb)

/-! ## 39 + 39 adjacent-interval joins -/
theorem re_join_1 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..33/32, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (33/32 : ℝ)..17/16, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..17/16, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_2 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..17/16, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (17/16 : ℝ)..35/32, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..35/32, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_3 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..35/32, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (35/32 : ℝ)..9/8, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..9/8, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_4 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..9/8, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (9/8 : ℝ)..37/32, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..37/32, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_5 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..37/32, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (37/32 : ℝ)..19/16, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..19/16, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_6 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..19/16, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (19/16 : ℝ)..39/32, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..39/32, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_7 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..39/32, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (39/32 : ℝ)..5/4, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..5/4, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_8 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..5/4, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (5/4 : ℝ)..41/32, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..41/32, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_9 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..41/32, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (41/32 : ℝ)..21/16, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..21/16, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_10 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..21/16, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (21/16 : ℝ)..43/32, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..43/32, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_11 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..43/32, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (43/32 : ℝ)..11/8, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..11/8, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_12 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..11/8, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (11/8 : ℝ)..45/32, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..45/32, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_13 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..45/32, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (45/32 : ℝ)..23/16, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..23/16, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_14 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..23/16, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (23/16 : ℝ)..47/32, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..47/32, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_15 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..47/32, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (47/32 : ℝ)..3/2, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..3/2, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_16 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..3/2, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (3/2 : ℝ)..25/16, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..25/16, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_17 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..25/16, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (25/16 : ℝ)..13/8, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..13/8, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_18 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..13/8, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (13/8 : ℝ)..27/16, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..27/16, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_19 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..27/16, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (27/16 : ℝ)..7/4, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..7/4, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_20 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..7/4, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (7/4 : ℝ)..29/16, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..29/16, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_21 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..29/16, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (29/16 : ℝ)..15/8, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..15/8, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_22 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..15/8, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (15/8 : ℝ)..31/16, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..31/16, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_23 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..31/16, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (31/16 : ℝ)..2/1, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..2/1, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_24 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..2/1, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (2/1 : ℝ)..17/8, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..17/8, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_25 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..17/8, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (17/8 : ℝ)..9/4, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..9/4, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_26 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..9/4, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (9/4 : ℝ)..19/8, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..19/8, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_27 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..19/8, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (19/8 : ℝ)..5/2, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..5/2, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_28 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..5/2, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (5/2 : ℝ)..21/8, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..21/8, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_29 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..21/8, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (21/8 : ℝ)..11/4, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..11/4, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_30 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..11/4, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (11/4 : ℝ)..23/8, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..23/8, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_31 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..23/8, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (23/8 : ℝ)..3/1, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..3/1, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_32 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..3/1, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (3/1 : ℝ)..13/4, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..13/4, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_33 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..13/4, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (13/4 : ℝ)..7/2, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..7/2, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_34 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..7/2, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (7/2 : ℝ)..15/4, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..15/4, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_35 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..15/4, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (15/4 : ℝ)..4/1, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..4/1, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_36 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..4/1, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (4/1 : ℝ)..17/4, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..17/4, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_37 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..17/4, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (17/4 : ℝ)..9/2, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..9/2, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_38 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..9/2, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (9/2 : ℝ)..19/4, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..19/4, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_39 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..19/4, realThetaReIntegrandN 3 σ (29/2) u)
      + (∫ u in (19/4 : ℝ)..5/1, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..5/1, realThetaReIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_1 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..33/32, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (33/32 : ℝ)..17/16, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..17/16, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_2 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..17/16, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (17/16 : ℝ)..35/32, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..35/32, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_3 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..35/32, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (35/32 : ℝ)..9/8, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..9/8, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_4 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..9/8, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (9/8 : ℝ)..37/32, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..37/32, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_5 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..37/32, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (37/32 : ℝ)..19/16, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..19/16, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_6 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..19/16, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (19/16 : ℝ)..39/32, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..39/32, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_7 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..39/32, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (39/32 : ℝ)..5/4, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..5/4, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_8 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..5/4, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (5/4 : ℝ)..41/32, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..41/32, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_9 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..41/32, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (41/32 : ℝ)..21/16, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..21/16, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_10 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..21/16, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (21/16 : ℝ)..43/32, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..43/32, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_11 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..43/32, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (43/32 : ℝ)..11/8, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..11/8, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_12 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..11/8, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (11/8 : ℝ)..45/32, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..45/32, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_13 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..45/32, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (45/32 : ℝ)..23/16, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..23/16, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_14 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..23/16, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (23/16 : ℝ)..47/32, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..47/32, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_15 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..47/32, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (47/32 : ℝ)..3/2, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..3/2, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_16 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..3/2, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (3/2 : ℝ)..25/16, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..25/16, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_17 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..25/16, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (25/16 : ℝ)..13/8, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..13/8, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_18 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..13/8, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (13/8 : ℝ)..27/16, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..27/16, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_19 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..27/16, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (27/16 : ℝ)..7/4, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..7/4, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_20 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..7/4, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (7/4 : ℝ)..29/16, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..29/16, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_21 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..29/16, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (29/16 : ℝ)..15/8, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..15/8, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_22 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..15/8, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (15/8 : ℝ)..31/16, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..31/16, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_23 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..31/16, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (31/16 : ℝ)..2/1, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..2/1, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_24 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..2/1, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (2/1 : ℝ)..17/8, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..17/8, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_25 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..17/8, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (17/8 : ℝ)..9/4, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..9/4, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_26 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..9/4, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (9/4 : ℝ)..19/8, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..19/8, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_27 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..19/8, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (19/8 : ℝ)..5/2, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..5/2, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_28 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..5/2, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (5/2 : ℝ)..21/8, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..21/8, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_29 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..21/8, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (21/8 : ℝ)..11/4, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..11/4, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_30 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..11/4, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (11/4 : ℝ)..23/8, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..23/8, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_31 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..23/8, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (23/8 : ℝ)..3/1, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..3/1, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_32 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..3/1, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (3/1 : ℝ)..13/4, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..13/4, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_33 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..13/4, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (13/4 : ℝ)..7/2, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..7/2, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_34 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..7/2, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (7/2 : ℝ)..15/4, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..15/4, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_35 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..15/4, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (15/4 : ℝ)..4/1, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..4/1, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_36 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..4/1, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (4/1 : ℝ)..17/4, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..17/4, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_37 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..17/4, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (17/4 : ℝ)..9/2, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..9/2, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_38 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..9/2, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (9/2 : ℝ)..19/4, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..19/4, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_39 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..19/4, realThetaImIntegrandN 3 σ (29/2) u)
      + (∫ u in (19/4 : ℝ)..5/1, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in (1/1 : ℝ)..5/1, realThetaImIntegrandN 3 σ (29/2) u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

/-! ## interval = Ioc rewrites -/
theorem re_interval_eq_Ioc (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..5/1, realThetaReIntegrandN 3 σ (29/2) u)
      = ∫ u in Set.Ioc (1 : ℝ) 5, realThetaReIntegrandN 3 σ (29/2) u := by
  have h1 : (1/1 : ℝ) = 1 := by norm_num
  have h5 : (5/1 : ℝ) = 5 := by norm_num
  rw [h1, h5, intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 5)]

theorem im_interval_eq_Ioc (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..5/1, realThetaImIntegrandN 3 σ (29/2) u)
      = ∫ u in Set.Ioc (1 : ℝ) 5, realThetaImIntegrandN 3 σ (29/2) u := by
  have h1 : (1/1 : ℝ) = 1 := by norm_num
  have h5 : (5/1 : ℝ) = 5 := by norm_num
  rw [h1, h5, intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 5)]

/-! ## finite lower bounds over [1,5] -/
set_option maxHeartbeats 4000000 in
theorem finite_re_lower (σ : ℝ)
    (hσ0 : (1/1 : ℝ) ≤ σ) (hσ1 : σ ≤ 1/1) :
    (5960154573837048640917936252520696688132400897389/1258105427357669130240000000000000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..5/1, realThetaReIntegrandN 3 σ (29/2) u := by
  have s1 := box900_seg1_re_integral_lower σ hσ0 hσ1
  have c1 : (160716910845402847/63700992000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..33/32, realThetaReIntegrandN 3 σ (29/2) u := s1
  have s2 := box900_seg2_re_integral_lower σ hσ0 hσ1
  have c2 : (85630441858179724279/18409586688000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..17/16, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_1 σ]
    linarith [c1, s2]
  have s3 := box900_seg3_re_integral_lower σ hσ0 hσ1
  have c3 : (14985727898256957768023/2356427096064000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..35/32, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_2 σ]
    linarith [c2, s3]
  have s4 := box900_seg4_re_integral_lower σ hσ0 hσ1
  have c4 : (180378215046626460415139/23564270960640000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..9/8, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_3 σ]
    linarith [c3, s4]
  have s5 := box900_seg5_re_integral_lower σ hσ0 hσ1
  have c5 : (5046948505212939166492139/589106774016000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..37/32, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_4 σ]
    linarith [c4, s5]
  have s6 := box900_seg6_re_integral_lower σ hσ0 hσ1
  have c6 : (37693782547515279417457133/4123747418112000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..19/16, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_5 σ]
    linarith [c5, s6]
  have s7 := box900_seg7_re_integral_lower σ hσ0 hσ1
  have c7 : (272105386606860836895005051/28866231926784000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..39/32, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_6 σ]
    linarith [c6, s7]
  have s8 := box900_seg8_re_integral_lower σ hσ0 hσ1
  have c8 : (46234412910374739186994742579/4878393195626496000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..5/4, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_7 σ]
    linarith [c7, s8]
  have s9 := box900_seg9_re_integral_lower σ hσ0 hσ1
  have c9 : (9117536154942946884470254531/975678639125299200000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..41/32, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_8 σ]
    linarith [c8, s9]
  have s10 := box900_seg10_re_integral_lower σ hσ0 hσ1
  have c10 : (44275796665199512336840947179/4878393195626496000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..21/16, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_9 σ]
    linarith [c9, s10]
  have s11 := box900_seg11_re_integral_lower σ hσ0 hσ1
  have c11 : (5142745460287234299545278276691/590285576670806016000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..43/32, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_10 σ]
    linarith [c10, s11]
  have s12 := box900_seg12_re_integral_lower σ hσ0 hσ1
  have c12 : (4893212113149863066253232069811/590285576670806016000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..11/8, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_11 σ]
    linarith [c11, s12]
  have s13 := box900_seg13_re_integral_lower σ hσ0 hσ1
  have c13 : (578256747343576047105118744022503/73785697083850752000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..45/32, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_12 σ]
    linarith [c12, s13]
  have s14 := box900_seg14_re_integral_lower σ hσ0 hσ1
  have c14 : (544380237572456848894900756005283/73785697083850752000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..23/16, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_13 σ]
    linarith [c13, s14]
  have s15 := box900_seg15_re_integral_lower σ hσ0 hσ1
  have c15 : (511339035942723060786139677069283/73785697083850752000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..47/32, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_14 σ]
    linarith [c14, s15]
  have s16 := box900_seg16_re_integral_lower σ hσ0 hσ1
  have c16 : (480096632117294566361343860442403/73785697083850752000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..3/2, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_15 σ]
    linarith [c15, s16]
  have s17 := box900_seg17_re_integral_lower σ hσ0 hσ1
  have c17 : (9001348729443483914437246606509643/1561305350294281912320000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..25/16, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_16 σ]
    linarith [c16, s17]
  have s18 := box900_seg18_re_integral_lower σ hσ0 hσ1
  have c18 : (8100217821309441920192381755154539/1561305350294281912320000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..13/8, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_17 σ]
    linarith [c17, s18]
  have s19 := box900_seg19_re_integral_lower σ hσ0 hσ1
  have c19 : (13455395370031699860964535464193713583/2818156157281178851737600000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..27/16, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_18 σ]
    linarith [c18, s19]
  have s20 := box900_seg20_re_integral_lower σ hσ0 hσ1
  have c20 : (1586864681918949196597239453392049378931/352269519660147356467200000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..7/4, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_19 σ]
    linarith [c19, s20]
  have s21 := box900_seg21_re_integral_lower σ hσ0 hσ1
  have c21 : (61301731200753234301095403501726969307251/14090780786405894258688000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..29/16, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_20 σ]
    linarith [c20, s21]
  have s22 := box900_seg22_re_integral_lower σ hσ0 hσ1
  have c22 : (8620914842142560006671055388651418303069/2012968683772270608384000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..15/8, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_21 σ]
    linarith [c21, s22]
  have s23 := box900_seg23_re_integral_lower σ hσ0 hσ1
  have c23 : (43025793376078681371351363418067898250193/10064843418861353041920000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..31/16, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_22 σ]
    linarith [c22, s23]
  have s24 := box900_seg24_re_integral_lower σ hσ0 hσ1
  have c24 : (216653406308333068325423492850405999001759/50324217094306765209600000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..2/1, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_23 σ]
    linarith [c23, s24]
  have s25 := box900_seg25_re_integral_lower σ hσ0 hσ1
  have c25 : (27788286806489387043238513424887514967002963/6290527136788345651200000000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..17/8, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_24 σ]
    linarith [c24, s25]
  have s26 := box900_seg26_re_integral_lower σ hσ0 hσ1
  have c26 : (57075690997300391349958953459025196203382911/12581054273576691302400000000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..9/4, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_25 σ]
    linarith [c25, s26]
  have s27 := box900_seg27_re_integral_lower σ hσ0 hσ1
  have c27 : (7280894656817673680950863368776939383900126527/1572631784197086412800000000000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..19/8, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_26 σ]
    linarith [c26, s27]
  have s28 := box900_seg28_re_integral_lower σ hσ0 hσ1
  have c28 : (7377316095034467766062590739128773392463747751/1572631784197086412800000000000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..5/2, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_27 σ]
    linarith [c27, s28]
  have s29 := box900_seg29_re_integral_lower σ hσ0 hσ1
  have c29 : (74324309933785736806352166162298506688259951267/15726317841970864128000000000000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..21/8, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_28 σ]
    linarith [c28, s29]
  have s30 := box900_seg30_re_integral_lower σ hσ0 hσ1
  have c30 : (93239858712890091420155735838522925787669463421/19657897302463580160000000000000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..11/4, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_29 σ]
    linarith [c29, s30]
  have s31 := box900_seg31_re_integral_lower σ hσ0 hσ1
  have c31 : (15560316120814257675716863250968814381221544851/3276316217077263360000000000000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..23/8, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_30 σ]
    linarith [c30, s31]
  have s32 := box900_seg32_re_integral_lower σ hσ0 hσ1
  have c32 : (1991955031173622039680181282889256174287172494423/419368475785889710080000000000000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..3/1, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_31 σ]
    linarith [c31, s32]
  have s33 := box900_seg33_re_integral_lower σ hσ0 hσ1
  have c33 : (5970308098799501688880467605068147466817972610949/1258105427357669130240000000000000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..13/4, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_32 σ]
    linarith [c32, s33]
  have s34 := box900_seg34_re_integral_lower σ hσ0 hσ1
  have c34 : (5964907374552967452969341844538332890719996648229/1258105427357669130240000000000000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..7/2, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_33 σ]
    linarith [c33, s34]
  have s35 := box900_seg35_re_integral_lower σ hσ0 hσ1
  have c35 : (5961962884297619017362027600931243094499550732109/1258105427357669130240000000000000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..15/4, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_34 σ]
    linarith [c34, s35]
  have s36 := box900_seg36_re_integral_lower σ hσ0 hσ1
  have c36 : (5960728932455869858117402109237344252507646881229/1258105427357669130240000000000000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..4/1, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_35 σ]
    linarith [c35, s36]
  have s37 := box900_seg37_re_integral_lower σ hσ0 hσ1
  have c37 : (5960300979703963604262896601968590210633863216749/1258105427357669130240000000000000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..17/4, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_36 σ]
    linarith [c36, s37]
  have s38 := box900_seg38_re_integral_lower σ hσ0 hσ1
  have c38 : (5960184159955383713729308596252056601104647813229/1258105427357669130240000000000000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..9/2, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_37 σ]
    linarith [c37, s38]
  have s39 := box900_seg39_re_integral_lower σ hσ0 hσ1
  have c39 : (5960152043538034192147445486889809498653353155309/1258105427357669130240000000000000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..19/4, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_38 σ]
    linarith [c38, s39]
  have s40 := box900_seg40_re_integral_lower σ hσ0 hσ1
  have c40 : (5960154573837048640917936252520696688132400897389/1258105427357669130240000000000000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..5/1, realThetaReIntegrandN 3 σ (29/2) u := by
    rw [← re_join_39 σ]
    linarith [c39, s40]
  exact c40

set_option maxHeartbeats 4000000 in
theorem finite_im_lower (σ : ℝ)
    (hσ0 : (1/1 : ℝ) ≤ σ) (hσ1 : σ ≤ 1/1) :
    (403888656096678504136787580520696688132400897389/1258105427357669130240000000000000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..5/1, realThetaImIntegrandN 3 σ (29/2) u := by
  have s1 := box900_seg1_im_integral_lower σ hσ0 hσ1
  have c1 : (87108610727647/63700992000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..33/32, realThetaImIntegrandN 3 σ (29/2) u := s1
  have s2 := box900_seg2_im_integral_lower σ hσ0 hσ1
  have c2 : (181970889740121079/18409586688000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..17/16, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_1 σ]
    linarith [c1, s2]
  have s3 := box900_seg3_im_integral_lower σ hσ0 hσ1
  have c3 : (69170827379931873623/2356427096064000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..35/32, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_2 σ]
    linarith [c2, s3]
  have s4 := box900_seg4_im_integral_lower σ hσ0 hσ1
  have c4 : (1430164382100538111139/23564270960640000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..9/8, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_3 σ]
    linarith [c3, s4]
  have s5 := box900_seg5_im_integral_lower σ hσ0 hσ1
  have c5 : (60538920903215702812139/589106774016000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..37/32, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_4 σ]
    linarith [c4, s5]
  have s6 := box900_seg6_im_integral_lower σ hσ0 hσ1
  have c6 : (631668403762224963697133/4123747418112000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..19/16, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_5 σ]
    linarith [c5, s6]
  have s7 := box900_seg7_im_integral_lower σ hσ0 hσ1
  have c7 : (6031030195315625523485051/28866231926784000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..39/32, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_6 σ]
    linarith [c6, s7]
  have s8 := box900_seg8_im_integral_lower σ hσ0 hσ1
  have c8 : (1301909054661535891639862579/4878393195626496000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..5/4, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_7 σ]
    linarith [c7, s8]
  have s9 := box900_seg9_im_integral_lower σ hσ0 hσ1
  have c9 : (316194300808086055568878531/975678639125299200000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..41/32, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_8 σ]
    linarith [c8, s9]
  have s10 := box900_seg10_im_integral_lower σ hσ0 hσ1
  have c10 : (1844269588347428611406067179/4878393195626496000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..21/16, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_9 σ]
    linarith [c9, s10]
  have s11 := box900_seg11_im_integral_lower σ hσ0 hσ1
  have c11 : (251945608760105394988406596691/590285576670806016000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..43/32, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_10 σ]
    linarith [c10, s11]
  have s12 := box900_seg12_im_integral_lower σ hσ0 hσ1
  have c12 : (276847967761285835380328389811/590285576670806016000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..11/8, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_11 σ]
    linarith [c11, s12]
  have s13 := box900_seg13_im_integral_lower σ hσ0 hσ1
  have c13 : (37170087382619445204390424022503/73785697083850752000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..45/32, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_12 σ]
    linarith [c12, s13]
  have s14 := box900_seg14_im_integral_lower σ hσ0 hσ1
  have c14 : (39159901734795669853354516005283/73785697083850752000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..23/16, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_13 σ]
    linarith [c13, s14]
  have s15 := box900_seg15_im_integral_lower σ hσ0 hσ1
  have c15 : (40578800216347965718532637069283/73785697083850752000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..47/32, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_14 σ]
    linarith [c14, s15]
  have s16 := box900_seg16_im_integral_lower σ hσ0 hσ1
  have c16 : (41455440378810813926287220442403/73785697083850752000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..3/2, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_15 σ]
    linarith [c15, s16]
  have s17 := box900_seg17_im_integral_lower σ hσ0 hσ1
  have c17 : (884019015106694962479192104109643/1561305350294281912320000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..25/16, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_16 σ]
    linarith [c16, s17]
  have s18 := box900_seg18_im_integral_lower σ hσ0 hσ1
  have c18 : (859107314694924580072070356754539/1561305350294281912320000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..13/8, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_17 σ]
    linarith [c17, s18]
  have s19 := box900_seg19_im_integral_lower σ hσ0 hσ1
  have c19 : (1468455488598172740637258051841713583/2818156157281178851737600000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..27/16, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_18 σ]
    linarith [c18, s19]
  have s20 := box900_seg20_im_integral_lower σ hσ0 hσ1
  have c20 : (170891042532600844833371215568049378931/352269519660147356467200000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..7/4, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_19 σ]
    linarith [c19, s20]
  have s21 := box900_seg21_im_integral_lower σ hσ0 hσ1
  have c21 : (6306108216253019347928424593566969307251/14090780786405894258688000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..29/16, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_20 σ]
    linarith [c20, s21]
  have s22 := box900_seg22_im_integral_lower σ hσ0 hσ1
  have c22 : (829293485351159746777784942571418303069/2012968683772270608384000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..15/8, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_21 σ]
    linarith [c21, s22]
  have s23 := box900_seg23_im_integral_lower σ hσ0 hσ1
  have c23 : (3831691127669258213447317747667898250193/10064843418861353041920000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..31/16, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_22 σ]
    linarith [c22, s23]
  have s24 := box900_seg24_im_integral_lower σ hσ0 hσ1
  have c24 : (17855918698800985378547048178405999001759/50324217094306765209600000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..2/1, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_23 σ]
    linarith [c23, s24]
  have s25 := box900_seg25_im_integral_lower σ hσ0 hσ1
  have c25 : (2011189768395028522060560656887514967002963/6290527136788345651200000000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..17/8, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_24 σ]
    linarith [c24, s25]
  have s26 := box900_seg26_im_integral_lower σ hσ0 hσ1
  have c26 : (3814268300400511859990734323025196203382911/12581054273576691302400000000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..9/4, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_25 σ]
    linarith [c25, s26]
  have s27 := box900_seg27_im_integral_lower σ hσ0 hσ1
  have c27 : (470000754139998858410152328776939383900126527/1572631784197086412800000000000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..19/8, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_26 σ]
    linarith [c26, s27]
  have s28 := box900_seg28_im_integral_lower σ hσ0 hσ1
  have c28 : (473422628663364489969188499128773392463747751/1572631784197086412800000000000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..5/2, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_27 σ]
    linarith [c27, s28]
  have s29 := box900_seg29_im_integral_lower σ hσ0 hσ1
  have c29 : (4807533615849003011018041362298506688259951267/15726317841970864128000000000000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..21/8, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_28 σ]
    linarith [c28, s29]
  have s30 := box900_seg30_im_integral_lower σ hσ0 hσ1
  have c30 : (6105058065309361854289391838522925787669463421/19657897302463580160000000000000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..11/4, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_29 σ]
    linarith [c29, s30]
  have s31 := box900_seg31_im_integral_lower σ hσ0 hσ1
  have c31 : (1030751179830536381359171250968814381221544851/3276316217077263360000000000000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..23/8, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_30 σ]
    linarith [c30, s31]
  have s32 := box900_seg32_im_integral_lower σ hσ0 hσ1
  have c32 : (133170541663459287814725154889256174287172494423/419368475785889710080000000000000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..3/1, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_31 σ]
    linarith [c31, s32]
  have s33 := box900_seg33_im_integral_lower σ hσ0 hσ1
  have c33 : (403426706831563325868063893068147466817972610949/1258105427357669130240000000000000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..13/4, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_32 σ]
    linarith [c32, s33]
  have s34 := box900_seg34_im_integral_lower σ hσ0 hσ1
  have c34 : (404544654035803880595853716538332890719996648229/1258105427357669130240000000000000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..7/2, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_33 σ]
    linarith [c33, s34]
  have s35 := box900_seg35_im_integral_lower σ hσ0 hσ1
  have c35 : (404586984696591761358049872931243094499550732109/1258105427357669130240000000000000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..15/4, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_34 σ]
    linarith [c34, s35]
  have s36 := box900_seg36_im_integral_lower σ hσ0 hσ1
  have c36 : (404371002650859323472051197237344252507646881229/1258105427357669130240000000000000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..4/1, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_35 σ]
    linarith [c35, s36]
  have s37 := box900_seg37_im_integral_lower σ hσ0 hσ1
  have c37 : (404172253118340873976779225968590210633863216749/1258105427357669130240000000000000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..17/4, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_36 σ]
    linarith [c36, s37]
  have s38 := box900_seg38_im_integral_lower σ hσ0 hσ1
  have c38 : (404027367134519012774344116252056601104647813229/1258105427357669130240000000000000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..9/2, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_37 σ]
    linarith [c37, s38]
  have s39 := box900_seg39_im_integral_lower σ hσ0 hσ1
  have c39 : (403938824688752499731989742889809498653353155309/1258105427357669130240000000000000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..19/4, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_38 σ]
    linarith [c38, s39]
  have s40 := box900_seg40_im_integral_lower σ hσ0 hσ1
  have c40 : (403888656096678504136787580520696688132400897389/1258105427357669130240000000000000000000000000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..5/1, realThetaImIntegrandN 3 σ (29/2) u := by
    rw [← im_join_39 σ]
    linarith [c39, s40]
  exact c40

/-! ## Lambda0 enclosures at sigma=1 (envelope applied ONCE) -/
theorem box14p5_re_enclosure :
    (47357/10000000 : ℝ) ≤ (completedRiemannZeta₀ (⟨1, 29 / 2⟩ : ℂ)).re := by
  have hfin := finite_re_lower (1 : ℝ) (by norm_num) (by norm_num)
  rw [re_interval_eq_Ioc (1 : ℝ)] at hfin
  have h8 := re_Lambda0_close_to_truncated_integral (N := 3) (σ := (1 : ℝ)) (t := (29/2 : ℝ))
    (T := (5 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  push_cast at h8
  have henv := PrincipiaTractalis.RiemannXiBox0Envelope.box0_envelope_le
  have habs := abs_le.mp (le_trans h8 henv)
  linarith [habs.1, hfin]

theorem box14p5_im_enclosure :
    (3/10000 : ℝ) ≤ (completedRiemannZeta₀ (⟨1, 29 / 2⟩ : ℂ)).im := by
  have hfin := finite_im_lower (1 : ℝ) (by norm_num) (by norm_num)
  rw [im_interval_eq_Ioc (1 : ℝ)] at hfin
  have h8 := im_Lambda0_close_to_truncated_integral (N := 3) (σ := (1 : ℝ)) (t := (29/2 : ℝ))
    (T := (5 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  push_cast at h8
  have henv := PrincipiaTractalis.RiemannXiBox0Envelope.box0_envelope_le
  have habs := abs_le.mp (le_trans h8 henv)
  linarith [habs.1, hfin]

/-! ## the unconditional point fact -/
/-- **The bounded-region fact, UNCONDITIONAL.**  The first unconditional certified
point: `Re ξ(1 + (29/2)·i) < 0`.  This is NOT R3 interval, NOT finite-region RH,
NOT Clay RH -- it is the single certified right-edge point at t = 29/2, σ = 1,
from the 40-segment σ=1 midpoint quadrature + box0 envelope (applied once). -/
theorem re_xi_14p5_neg_unconditional :
    (riemannXiEntire (⟨1, 29 / 2⟩ : ℂ)).re < 0 :=
  PrincipiaTractalis.RightEdgeSignsPilot14p5.re_xi_14p5_neg_of_edge_lb
    box14p5_re_enclosure box14p5_im_enclosure (by norm_num)

#print axioms re_xi_14p5_neg_unconditional

end PrincipiaTractalis.RiemannXiBox900Bridge14p5
