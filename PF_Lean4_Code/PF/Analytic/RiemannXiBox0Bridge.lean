/-
# PF.Analytic.RiemannXiBox0Bridge

**§8 consumption layer for r331b Box 0.**

Chains the 40 certified OPT-40-TIGHT segment integrals in GEOMETRIC order
(segment index order = geometric order; file IDs coincide here, verified by the
manifest gate) into a single `intervalIntegral` over `[1, 5]`, rewrites it as
the set integral over `Ioc 1 5` — the literal domain of
`re_/im_Lambda0_close_to_truncated_integral` — instantiates `T := 5`, and
applies the §8 analytic envelope EXACTLY ONCE via
`RiemannXiBox0Envelope.box0_envelope_le`.

Error ledger (locked): node rounding and composite-midpoint error are already
inside each `box0_seg{j}_*_integral_*` endpoint and are NEVER re-subtracted
here.  The only error applied at this layer is the §8 analytic envelope.

All bounds are exact rationals; every partial sum is re-verified by `linarith`
against the certified segment constants.

SPDX-License-Identifier: Apache-2.0
-/

import PF.Analytic.RiemannXiBox0Envelope
import PF.Analytic.RiemannXiBox0Panels.Seg01
import PF.Analytic.RiemannXiBox0Panels.Seg02
import PF.Analytic.RiemannXiBox0Panels.Seg03
import PF.Analytic.RiemannXiBox0Panels.Seg04
import PF.Analytic.RiemannXiBox0Panels.Seg05
import PF.Analytic.RiemannXiBox0Panels.Seg06
import PF.Analytic.RiemannXiBox0Panels.Seg07
import PF.Analytic.RiemannXiBox0Panels.Seg08
import PF.Analytic.RiemannXiBox0Panels.Seg09
import PF.Analytic.RiemannXiBox0Panels.Seg10
import PF.Analytic.RiemannXiBox0Panels.Seg11
import PF.Analytic.RiemannXiBox0Panels.Seg12
import PF.Analytic.RiemannXiBox0Panels.Seg13
import PF.Analytic.RiemannXiBox0Panels.Seg14
import PF.Analytic.RiemannXiBox0Panels.Seg15
import PF.Analytic.RiemannXiBox0Panels.Seg16
import PF.Analytic.RiemannXiBox0Panels.Seg17
import PF.Analytic.RiemannXiBox0Panels.Seg18
import PF.Analytic.RiemannXiBox0Panels.Seg19
import PF.Analytic.RiemannXiBox0Panels.Seg20
import PF.Analytic.RiemannXiBox0Panels.Seg21
import PF.Analytic.RiemannXiBox0Panels.Seg22
import PF.Analytic.RiemannXiBox0Panels.Seg23
import PF.Analytic.RiemannXiBox0Panels.Seg24
import PF.Analytic.RiemannXiBox0Panels.Seg25
import PF.Analytic.RiemannXiBox0Panels.Seg26
import PF.Analytic.RiemannXiBox0Panels.Seg27
import PF.Analytic.RiemannXiBox0Panels.Seg28
import PF.Analytic.RiemannXiBox0Panels.Seg29
import PF.Analytic.RiemannXiBox0Panels.Seg30
import PF.Analytic.RiemannXiBox0Panels.Seg31
import PF.Analytic.RiemannXiBox0Panels.Seg32
import PF.Analytic.RiemannXiBox0Panels.Seg33
import PF.Analytic.RiemannXiBox0Panels.Seg34
import PF.Analytic.RiemannXiBox0Panels.Seg35
import PF.Analytic.RiemannXiBox0Panels.Seg36
import PF.Analytic.RiemannXiBox0Panels.Seg37
import PF.Analytic.RiemannXiBox0Panels.Seg38
import PF.Analytic.RiemannXiBox0Panels.Seg39
import PF.Analytic.RiemannXiBox0Panels.Seg40

namespace PrincipiaTractalis.RiemannXiBox0Bridge

open scoped Real
open MeasureTheory
open PrincipiaTractalis.RiemannXiThetaRealFormAndBoxes
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.RiemannXiBox0Panels.Seg01
open PrincipiaTractalis.RiemannXiBox0Panels.Seg02
open PrincipiaTractalis.RiemannXiBox0Panels.Seg03
open PrincipiaTractalis.RiemannXiBox0Panels.Seg04
open PrincipiaTractalis.RiemannXiBox0Panels.Seg05
open PrincipiaTractalis.RiemannXiBox0Panels.Seg06
open PrincipiaTractalis.RiemannXiBox0Panels.Seg07
open PrincipiaTractalis.RiemannXiBox0Panels.Seg08
open PrincipiaTractalis.RiemannXiBox0Panels.Seg09
open PrincipiaTractalis.RiemannXiBox0Panels.Seg10
open PrincipiaTractalis.RiemannXiBox0Panels.Seg11
open PrincipiaTractalis.RiemannXiBox0Panels.Seg12
open PrincipiaTractalis.RiemannXiBox0Panels.Seg13
open PrincipiaTractalis.RiemannXiBox0Panels.Seg14
open PrincipiaTractalis.RiemannXiBox0Panels.Seg15
open PrincipiaTractalis.RiemannXiBox0Panels.Seg16
open PrincipiaTractalis.RiemannXiBox0Panels.Seg17
open PrincipiaTractalis.RiemannXiBox0Panels.Seg18
open PrincipiaTractalis.RiemannXiBox0Panels.Seg19
open PrincipiaTractalis.RiemannXiBox0Panels.Seg20
open PrincipiaTractalis.RiemannXiBox0Panels.Seg21
open PrincipiaTractalis.RiemannXiBox0Panels.Seg22
open PrincipiaTractalis.RiemannXiBox0Panels.Seg23
open PrincipiaTractalis.RiemannXiBox0Panels.Seg24
open PrincipiaTractalis.RiemannXiBox0Panels.Seg25
open PrincipiaTractalis.RiemannXiBox0Panels.Seg26
open PrincipiaTractalis.RiemannXiBox0Panels.Seg27
open PrincipiaTractalis.RiemannXiBox0Panels.Seg28
open PrincipiaTractalis.RiemannXiBox0Panels.Seg29
open PrincipiaTractalis.RiemannXiBox0Panels.Seg30
open PrincipiaTractalis.RiemannXiBox0Panels.Seg31
open PrincipiaTractalis.RiemannXiBox0Panels.Seg32
open PrincipiaTractalis.RiemannXiBox0Panels.Seg33
open PrincipiaTractalis.RiemannXiBox0Panels.Seg34
open PrincipiaTractalis.RiemannXiBox0Panels.Seg35
open PrincipiaTractalis.RiemannXiBox0Panels.Seg36
open PrincipiaTractalis.RiemannXiBox0Panels.Seg37
open PrincipiaTractalis.RiemannXiBox0Panels.Seg38
open PrincipiaTractalis.RiemannXiBox0Panels.Seg39
open PrincipiaTractalis.RiemannXiBox0Panels.Seg40

/-! ## §B.1 — interval integrability on subintervals of `[1, 5]` -/

/-- The Re integrand is interval-integrable on any `[a,b] ⊆ [1,5]`. -/
theorem re_integrable (σ : ℝ) {a b : ℝ}
    (ha : (1 : ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ 5) :
    IntervalIntegrable (realThetaReIntegrandN 3 σ 15) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hab]
  exact (continuousOn_realThetaReIntegrandN_Icc 3 σ 15 5).mono
    (Set.Icc_subset_Icc ha hb)

/-- The Im integrand is interval-integrable on any `[a,b] ⊆ [1,5]`. -/
theorem im_integrable (σ : ℝ) {a b : ℝ}
    (ha : (1 : ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ 5) :
    IntervalIntegrable (realThetaImIntegrandN 3 σ 15) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hab]
  exact (continuousOn_realThetaImIntegrandN_Icc 3 σ 15 5).mono
    (Set.Icc_subset_Icc ha hb)

/-! ## §B.2 — 39 adjacent-interval joins, geometric order -/

theorem re_join_1 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..33/32, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (33/32 : ℝ)..17/16, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..17/16, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_2 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..17/16, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (17/16 : ℝ)..35/32, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..35/32, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_3 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..35/32, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (35/32 : ℝ)..9/8, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..9/8, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_4 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..9/8, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (9/8 : ℝ)..37/32, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..37/32, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_5 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..37/32, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (37/32 : ℝ)..19/16, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..19/16, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_6 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..19/16, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (19/16 : ℝ)..39/32, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..39/32, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_7 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..39/32, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (39/32 : ℝ)..5/4, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..5/4, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_8 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..5/4, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (5/4 : ℝ)..41/32, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..41/32, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_9 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..41/32, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (41/32 : ℝ)..21/16, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..21/16, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_10 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..21/16, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (21/16 : ℝ)..43/32, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..43/32, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_11 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..43/32, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (43/32 : ℝ)..11/8, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..11/8, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_12 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..11/8, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (11/8 : ℝ)..45/32, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..45/32, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_13 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..45/32, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (45/32 : ℝ)..23/16, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..23/16, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_14 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..23/16, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (23/16 : ℝ)..47/32, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..47/32, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_15 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..47/32, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (47/32 : ℝ)..3/2, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..3/2, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_16 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..3/2, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (3/2 : ℝ)..25/16, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..25/16, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_17 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..25/16, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (25/16 : ℝ)..13/8, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..13/8, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_18 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..13/8, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (13/8 : ℝ)..27/16, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..27/16, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_19 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..27/16, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (27/16 : ℝ)..7/4, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..7/4, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_20 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..7/4, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (7/4 : ℝ)..29/16, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..29/16, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_21 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..29/16, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (29/16 : ℝ)..15/8, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..15/8, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_22 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..15/8, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (15/8 : ℝ)..31/16, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..31/16, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_23 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..31/16, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (31/16 : ℝ)..2/1, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..2/1, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_24 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..2/1, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (2/1 : ℝ)..17/8, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..17/8, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_25 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..17/8, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (17/8 : ℝ)..9/4, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..9/4, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_26 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..9/4, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (9/4 : ℝ)..19/8, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..19/8, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_27 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..19/8, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (19/8 : ℝ)..5/2, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..5/2, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_28 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..5/2, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (5/2 : ℝ)..21/8, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..21/8, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_29 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..21/8, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (21/8 : ℝ)..11/4, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..11/4, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_30 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..11/4, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (11/4 : ℝ)..23/8, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..23/8, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_31 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..23/8, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (23/8 : ℝ)..3/1, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..3/1, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_32 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..3/1, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (3/1 : ℝ)..13/4, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..13/4, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_33 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..13/4, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (13/4 : ℝ)..7/2, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..7/2, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_34 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..7/2, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (7/2 : ℝ)..15/4, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..15/4, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_35 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..15/4, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (15/4 : ℝ)..4/1, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..4/1, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_36 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..4/1, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (4/1 : ℝ)..17/4, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..17/4, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_37 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..17/4, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (17/4 : ℝ)..9/2, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..9/2, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_38 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..9/2, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (9/2 : ℝ)..19/4, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..19/4, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem re_join_39 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..19/4, realThetaReIntegrandN 3 σ 15 u)
      + (∫ u in (19/4 : ℝ)..5/1, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..5/1, realThetaReIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (re_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_1 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..33/32, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (33/32 : ℝ)..17/16, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..17/16, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_2 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..17/16, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (17/16 : ℝ)..35/32, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..35/32, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_3 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..35/32, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (35/32 : ℝ)..9/8, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..9/8, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_4 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..9/8, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (9/8 : ℝ)..37/32, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..37/32, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_5 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..37/32, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (37/32 : ℝ)..19/16, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..19/16, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_6 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..19/16, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (19/16 : ℝ)..39/32, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..39/32, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_7 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..39/32, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (39/32 : ℝ)..5/4, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..5/4, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_8 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..5/4, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (5/4 : ℝ)..41/32, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..41/32, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_9 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..41/32, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (41/32 : ℝ)..21/16, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..21/16, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_10 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..21/16, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (21/16 : ℝ)..43/32, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..43/32, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_11 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..43/32, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (43/32 : ℝ)..11/8, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..11/8, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_12 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..11/8, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (11/8 : ℝ)..45/32, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..45/32, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_13 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..45/32, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (45/32 : ℝ)..23/16, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..23/16, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_14 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..23/16, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (23/16 : ℝ)..47/32, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..47/32, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_15 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..47/32, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (47/32 : ℝ)..3/2, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..3/2, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_16 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..3/2, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (3/2 : ℝ)..25/16, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..25/16, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_17 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..25/16, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (25/16 : ℝ)..13/8, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..13/8, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_18 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..13/8, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (13/8 : ℝ)..27/16, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..27/16, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_19 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..27/16, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (27/16 : ℝ)..7/4, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..7/4, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_20 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..7/4, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (7/4 : ℝ)..29/16, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..29/16, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_21 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..29/16, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (29/16 : ℝ)..15/8, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..15/8, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_22 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..15/8, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (15/8 : ℝ)..31/16, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..31/16, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_23 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..31/16, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (31/16 : ℝ)..2/1, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..2/1, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_24 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..2/1, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (2/1 : ℝ)..17/8, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..17/8, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_25 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..17/8, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (17/8 : ℝ)..9/4, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..9/4, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_26 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..9/4, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (9/4 : ℝ)..19/8, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..19/8, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_27 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..19/8, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (19/8 : ℝ)..5/2, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..5/2, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_28 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..5/2, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (5/2 : ℝ)..21/8, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..21/8, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_29 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..21/8, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (21/8 : ℝ)..11/4, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..11/4, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_30 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..11/4, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (11/4 : ℝ)..23/8, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..23/8, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_31 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..23/8, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (23/8 : ℝ)..3/1, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..3/1, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_32 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..3/1, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (3/1 : ℝ)..13/4, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..13/4, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_33 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..13/4, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (13/4 : ℝ)..7/2, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..7/2, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_34 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..7/2, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (7/2 : ℝ)..15/4, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..15/4, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_35 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..15/4, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (15/4 : ℝ)..4/1, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..4/1, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_36 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..4/1, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (4/1 : ℝ)..17/4, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..17/4, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_37 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..17/4, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (17/4 : ℝ)..9/2, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..9/2, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_38 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..9/2, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (9/2 : ℝ)..19/4, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..19/4, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

theorem im_join_39 (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..19/4, realThetaImIntegrandN 3 σ 15 u)
      + (∫ u in (19/4 : ℝ)..5/1, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in (1/1 : ℝ)..5/1, realThetaImIntegrandN 3 σ 15 u :=
  intervalIntegral.integral_add_adjacent_intervals
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))
    (im_integrable σ (by norm_num) (by norm_num) (by norm_num))

/-! ## §B.3 — cumulative bounds over `[1, 5]` (exact rationals) -/

set_option maxHeartbeats 4000000 in
theorem finite_re_lower (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    (19565434522200618210855599639/4403368995751841955840000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..5/1, realThetaReIntegrandN 3 σ 15 u := by
  have s1 := box0_seg1_re_integral_lower σ hσ0 hσ1
  have c1 : (12548703294439/4976640000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..33/32, realThetaReIntegrandN 3 σ 15 u := s1
  have s2 := box0_seg2_re_integral_lower σ hσ0 hσ1
  have c2 : (1335007089280571/287649792000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..17/16, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_1 σ]
    linarith [c1, s2]
  have s3 := box0_seg3_re_integral_lower σ hσ0 hσ1
  have c3 : (582577809882833743/92047933440000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..35/32, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_2 σ]
    linarith [c2, s3]
  have s4 := box0_seg4_re_integral_lower σ hσ0 hσ1
  have c4 : (279532885795352299/36819173376000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..9/8, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_3 σ]
    linarith [c3, s4]
  have s5 := box0_seg5_re_integral_lower σ hσ0 hσ1
  have c5 : (7788498032353263091/920479334400000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..37/32, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_4 σ]
    linarith [c4, s5]
  have s6 := box0_seg6_re_integral_lower σ hσ0 hσ1
  have c6 : (405190025133341612419/45103487385600000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..19/16, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_5 σ]
    linarith [c5, s6]
  have s7 := box0_seg7_re_integral_lower σ hσ0 hσ1
  have c7 : (415537012738014519619/45103487385600000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..39/32, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_6 σ]
    linarith [c6, s7]
  have s8 := box0_seg8_re_integral_lower σ hσ0 hσ1
  have c8 : (70171565716799227166011/7622489368166400000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..5/4, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_7 σ]
    linarith [c7, s8]
  have s9 := box0_seg9_re_integral_lower σ hσ0 hσ1
  have c9 : (68728643443127632770331/7622489368166400000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..41/32, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_8 σ]
    linarith [c8, s9]
  have s10 := box0_seg10_re_integral_lower σ hσ0 hσ1
  have c10 : (66276249967987250134651/7622489368166400000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..21/16, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_9 σ]
    linarith [c9, s10]
  have s11 := box0_seg11_re_integral_lower σ hσ0 hσ1
  have c11 : (694617423955383883007561/83847383049830400000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..43/32, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_10 σ]
    linarith [c10, s11]
  have s12 := box0_seg12_re_integral_lower σ hσ0 hσ1
  have c12 : (7214292697956583133075491/922321213548134400000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..11/8, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_11 σ]
    linarith [c11, s12]
  have s13 := box0_seg13_re_integral_lower σ hσ0 hσ1
  have c13 : (6767636895123836697314659/922321213548134400000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..45/32, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_12 σ]
    linarith [c12, s13]
  have s14 := box0_seg14_re_integral_lower σ hσ0 hσ1
  have c14 : (6322567954366589821677091/922321213548134400000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..23/16, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_13 σ]
    linarith [c13, s14]
  have s15 := box0_seg15_re_integral_lower σ hσ0 hσ1
  have c15 : (5895379030155277518637091/922321213548134400000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..47/32, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_14 σ]
    linarith [c14, s15]
  have s16 := box0_seg16_re_integral_lower σ hσ0 hσ1
  have c16 : (5497639831733643353861411/922321213548134400000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..3/2, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_15 σ]
    linarith [c15, s16]
  have s17 := box0_seg17_re_integral_lower σ hσ0 hσ1
  have c17 : (2548420625638919867676953939/487907921966963097600000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..25/16, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_16 σ]
    linarith [c16, s17]
  have s18 := box0_seg18_re_integral_lower σ hσ0 hσ1
  have c18 : (2278294076554115279517793619/487907921966963097600000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..13/8, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_17 σ]
    linarith [c17, s18]
  have s19 := box0_seg19_re_integral_lower σ hσ0 hσ1
  have c19 : (755859520251996095852671216139/176134759830073678233600000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..27/16, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_18 σ]
    linarith [c18, s19]
  have s20 := box0_seg20_re_integral_lower σ hσ0 hσ1
  have c20 : (715467114539883250055072383499/176134759830073678233600000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..7/4, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_19 σ]
    linarith [c19, s20]
  have s21 := box0_seg21_re_integral_lower σ hσ0 hσ1
  have c21 : (695423373259782001342447120859/176134759830073678233600000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..29/16, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_20 σ]
    linarith [c20, s21]
  have s22 := box0_seg22_re_integral_lower σ hσ0 hσ1
  have c22 : (689958744279281715972884806619/176134759830073678233600000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..15/8, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_21 σ]
    linarith [c21, s22]
  have s23 := box0_seg23_re_integral_lower σ hσ0 hσ1
  have c23 : (694065197535024799711899989819/176134759830073678233600000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..31/16, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_22 σ]
    linarith [c22, s23]
  have s24 := box0_seg24_re_integral_lower σ hσ0 hσ1
  have c24 : (87969383142703884046396451593/22016844978759209779200000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..2/1, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_23 σ]
    linarith [c23, s24]
  have s25 := box0_seg25_re_integral_lower σ hσ0 hσ1
  have c25 : (91125646686419461748443812313/22016844978759209779200000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..17/8, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_24 σ]
    linarith [c24, s25]
  have s26 := box0_seg26_re_integral_lower σ hσ0 hσ1
  have c26 : (376035686145154903684058448457/88067379915036839116800000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..9/4, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_25 σ]
    linarith [c25, s26]
  have s27 := box0_seg27_re_integral_lower σ hσ0 hσ1
  have c27 : (3074030667447183505011789833/704539039320294712934400000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..19/8, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_26 σ]
    linarith [c26, s27]
  have s28 := box0_seg28_re_integral_lower σ hσ0 hσ1
  have c28 : (77840064165040088003192803553/17613475983007367823360000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..5/2, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_27 σ]
    linarith [c27, s28]
  have s29 := box0_seg29_re_integral_lower σ hσ0 hσ1
  have c29 : (15668558182624756147557397549/3522695196601473564672000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..21/8, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_28 σ]
    linarith [c28, s29]
  have s30 := box0_seg30_re_integral_lower σ hσ0 hσ1
  have c30 : (78539875004049993986809344929/17613475983007367823360000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..11/4, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_29 σ]
    linarith [c29, s30]
  have s31 := box0_seg31_re_integral_lower σ hσ0 hσ1
  have c31 : (78571594032247303687269806177/17613475983007367823360000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..23/8, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_30 σ]
    linarith [c30, s31]
  have s32 := box0_seg32_re_integral_lower σ hσ0 hσ1
  have c32 : (3926464944906548563045376797/880673799150368391168000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..3/1, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_31 σ]
    linarith [c31, s32]
  have s33 := box0_seg33_re_integral_lower σ hσ0 hσ1
  have c33 : (19600811227633959117964170737/4403368995751841955840000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..13/4, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_32 σ]
    linarith [c32, s33]
  have s34 := box0_seg34_re_integral_lower σ hσ0 hσ1
  have c34 : (19579523914763352311855260913/4403368995751841955840000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..7/2, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_33 σ]
    linarith [c33, s34]
  have s35 := box0_seg35_re_integral_lower σ hσ0 hσ1
  have c35 : (19569807512648627829174547703/4403368995751841955840000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..15/4, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_34 σ]
    linarith [c34, s35]
  have s36 := box0_seg36_re_integral_lower σ hσ0 hσ1
  have c36 : (3913282157166714219963050923/880673799150368391168000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..4/1, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_35 σ]
    linarith [c35, s36]
  have s37 := box0_seg37_re_integral_lower σ hσ0 hσ1
  have c37 : (19565510843281576951195882199/4403368995751841955840000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..17/4, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_36 σ]
    linarith [c36, s37]
  have s38 := box0_seg38_re_integral_lower σ hσ0 hσ1
  have c38 : (19565393172100320147708993623/4403368995751841955840000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..9/2, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_37 σ]
    linarith [c37, s38]
  have s39 := box0_seg39_re_integral_lower σ hσ0 hσ1
  have c39 : (19565391045382032713787147959/4403368995751841955840000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..19/4, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_38 σ]
    linarith [c38, s39]
  have s40 := box0_seg40_re_integral_lower σ hσ0 hσ1
  have c40 : (19565434522200618210855599639/4403368995751841955840000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..5/1, realThetaReIntegrandN 3 σ 15 u := by
    rw [← re_join_39 σ]
    linarith [c39, s40]
  exact c40

set_option maxHeartbeats 4000000 in
theorem finite_re_upper (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    (∫ u in (1/1 : ℝ)..5/1, realThetaReIntegrandN 3 σ 15 u) ≤ (215658935790989208238087376333/22016844978759209779200000000000 : ℝ) := by
  have s1 := box0_seg1_re_integral_upper σ hσ0 hσ1
  have c1 : (∫ u in (1/1 : ℝ)..33/32, realThetaReIntegrandN 3 σ 15 u) ≤ (4016010421/1592524800000 : ℝ) := s1
  have s2 := box0_seg2_re_integral_upper σ hσ0 hσ1
  have c2 : (∫ u in (1/1 : ℝ)..17/16, realThetaReIntegrandN 3 σ 15 u) ≤ (2136257882677/460239667200000 : ℝ) := by
    rw [← re_join_1 σ]
    linarith [c1, s2]
  have s3 := box0_seg3_re_integral_upper σ hσ0 hσ1
  have c3 : (∫ u in (1/1 : ℝ)..35/32, realThetaReIntegrandN 3 σ 15 u) ≤ (186448694072077/29455338700800000 : ℝ) := by
    rw [← re_join_2 σ]
    linarith [c2, s3]
  have s4 := box0_seg4_re_integral_upper σ hσ0 hσ1
  have c4 : (∫ u in (1/1 : ℝ)..9/8, realThetaReIntegrandN 3 σ 15 u) ≤ (447314115116261/58910677401600000 : ℝ) := by
    rw [← re_join_3 σ]
    linarith [c3, s4]
  have s5 := box0_seg5_re_integral_upper σ hσ0 hσ1
  have c5 : (∫ u in (1/1 : ℝ)..37/32, realThetaReIntegrandN 3 σ 15 u) ≤ (2492717987113849/294553387008000000 : ℝ) := by
    rw [← re_join_4 σ]
    linarith [c4, s5]
  have s6 := box0_seg6_re_integral_upper σ hσ0 hσ1
  have c6 : (∫ u in (1/1 : ℝ)..19/16, realThetaReIntegrandN 3 σ 15 u) ≤ (129684596702796841/14433115963392000000 : ℝ) := by
    rw [← re_join_5 σ]
    linarith [c5, s6]
  have s7 := box0_seg7_re_integral_upper σ hσ0 hσ1
  have c7 : (∫ u in (1/1 : ℝ)..39/32, realThetaReIntegrandN 3 σ 15 u) ≤ (132999745041984361/14433115963392000000 : ℝ) := by
    rw [← re_join_6 σ]
    linarith [c6, s7]
  have s8 := box0_seg8_re_integral_upper σ hσ0 hσ1
  have c8 : (∫ u in (1/1 : ℝ)..5/4, realThetaReIntegrandN 3 σ 15 u) ≤ (22532722946118811729/2439196597813248000000 : ℝ) := by
    rw [← re_join_7 σ]
    linarith [c7, s8]
  have s9 := box0_seg9_re_integral_upper σ hσ0 hσ1
  have c9 : (∫ u in (1/1 : ℝ)..41/32, realThetaReIntegrandN 3 σ 15 u) ≤ (22532852610182431729/2439196597813248000000 : ℝ) := by
    rw [← re_join_8 σ]
    linarith [c8, s9]
  have s10 := box0_seg10_re_integral_upper σ hσ0 hσ1
  have c10 : (∫ u in (1/1 : ℝ)..21/16, realThetaReIntegrandN 3 σ 15 u) ≤ (22532970212472691729/2439196597813248000000 : ℝ) := by
    rw [← re_join_9 σ]
    linarith [c9, s10]
  have s11 := box0_seg11_re_integral_upper σ hσ0 hσ1
  have c11 : (∫ u in (1/1 : ℝ)..43/32, realThetaReIntegrandN 3 σ 15 u) ≤ (247864068056688409019/26831162575945728000000 : ℝ) := by
    rw [← re_join_10 σ]
    linarith [c10, s11]
  have s12 := box0_seg12_re_integral_upper σ hσ0 hσ1
  have c12 : (∫ u in (1/1 : ℝ)..11/8, realThetaReIntegrandN 3 σ 15 u) ≤ (2726518674802471859209/295142788335403008000000 : ℝ) := by
    rw [← re_join_11 σ]
    linarith [c11, s12]
  have s13 := box0_seg13_re_integral_upper σ hσ0 hσ1
  have c13 : (∫ u in (1/1 : ℝ)..45/32, realThetaReIntegrandN 3 σ 15 u) ≤ (2726533949246397400009/295142788335403008000000 : ℝ) := by
    rw [← re_join_12 σ]
    linarith [c12, s13]
  have s14 := box0_seg14_re_integral_upper σ hσ0 hσ1
  have c14 : (∫ u in (1/1 : ℝ)..23/16, realThetaReIntegrandN 3 σ 15 u) ≤ (2726547797575165273609/295142788335403008000000 : ℝ) := by
    rw [← re_join_13 σ]
    linarith [c13, s14]
  have s15 := box0_seg15_re_integral_upper σ hσ0 hσ1
  have c15 : (∫ u in (1/1 : ℝ)..47/32, realThetaReIntegrandN 3 σ 15 u) ≤ (2726563272638929433609/295142788335403008000000 : ℝ) := by
    rw [← re_join_14 σ]
    linarith [c14, s15]
  have s16 := box0_seg16_re_integral_upper σ hσ0 hσ1
  have c16 : (∫ u in (1/1 : ℝ)..3/2, realThetaReIntegrandN 3 σ 15 u) ≤ (2726577311394380153609/295142788335403008000000 : ℝ) := by
    rw [← re_join_15 σ]
    linarith [c15, s16]
  have s17 := box0_seg17_re_integral_upper σ hσ0 hσ1
  have c17 : (∫ u in (1/1 : ℝ)..25/16, realThetaReIntegrandN 3 σ 15 u) ≤ (1442367654183803069259161/156130535029428191232000000 : ℝ) := by
    rw [← re_join_16 σ]
    linarith [c16, s17]
  have s18 := box0_seg18_re_integral_upper σ hσ0 hσ1
  have c18 : (∫ u in (1/1 : ℝ)..13/8, realThetaReIntegrandN 3 σ 15 u) ≤ (1442375793473530232139161/156130535029428191232000000 : ℝ) := by
    rw [← re_join_17 σ]
    linarith [c17, s18]
  have s19 := box0_seg19_re_integral_upper σ hσ0 hσ1
  have c19 : (∫ u in (1/1 : ℝ)..27/16, realThetaReIntegrandN 3 σ 15 u) ≤ (520700615573940698149117121/56363123145623577034752000000 : ℝ) := by
    rw [← re_join_18 σ]
    linarith [c18, s19]
  have s20 := box0_seg20_re_integral_upper σ hσ0 hσ1
  have c20 : (∫ u in (1/1 : ℝ)..7/4, realThetaReIntegrandN 3 σ 15 u) ≤ (520703650984553578554877121/56363123145623577034752000000 : ℝ) := by
    rw [← re_join_19 σ]
    linarith [c19, s20]
  have s21 := box0_seg21_re_integral_upper σ hσ0 hσ1
  have c21 : (∫ u in (1/1 : ℝ)..29/16, realThetaReIntegrandN 3 σ 15 u) ≤ (520706472967857740807107121/56363123145623577034752000000 : ℝ) := by
    rw [← re_join_20 σ]
    linarith [c20, s21]
  have s22 := box0_seg22_re_integral_upper σ hσ0 hσ1
  have c22 : (∫ u in (1/1 : ℝ)..15/8, realThetaReIntegrandN 3 σ 15 u) ≤ (520709486008664517218947121/56363123145623577034752000000 : ℝ) := by
    rw [← re_join_21 σ]
    linarith [c21, s22]
  have s23 := box0_seg23_re_integral_upper σ hσ0 hσ1
  have c23 : (∫ u in (1/1 : ℝ)..31/16, realThetaReIntegrandN 3 σ 15 u) ≤ (65256033823419885169530824077/7045390393202947129344000000000 : ℝ) := by
    rw [← re_join_22 σ]
    linarith [c22, s23]
  have s24 := box0_seg24_re_integral_upper σ hσ0 hσ1
  have c24 : (∫ u in (1/1 : ℝ)..2/1, realThetaReIntegrandN 3 σ 15 u) ≤ (1641161108343711725498477251/176134759830073678233600000000 : ℝ) := by
    rw [← re_join_23 σ]
    linarith [c23, s24]
  have s25 := box0_seg25_re_integral_upper σ hσ0 hσ1
  have c25 : (∫ u in (1/1 : ℝ)..17/8, realThetaReIntegrandN 3 σ 15 u) ≤ (208318537704418138837017578087/22016844978759209779200000000000 : ℝ) := by
    rw [← re_join_24 σ]
    linarith [c24, s25]
  have s26 := box0_seg26_re_integral_upper σ hσ0 hσ1
  have c26 : (∫ u in (1/1 : ℝ)..9/4, realThetaReIntegrandN 3 σ 15 u) ≤ (844879078862257868582819940023/88067379915036839116800000000000 : ℝ) := by
    rw [← re_join_25 σ]
    linarith [c25, s26]
  have s27 := box0_seg27_re_integral_upper σ hσ0 hσ1
  have c27 : (∫ u in (1/1 : ℝ)..19/8, realThetaReIntegrandN 3 σ 15 u) ≤ (853167575297655095350396081307/88067379915036839116800000000000 : ℝ) := by
    rw [← re_join_26 σ]
    linarith [c26, s27]
  have s28 := box0_seg28_re_integral_upper σ hσ0 hσ1
  have c28 : (∫ u in (1/1 : ℝ)..5/2, realThetaReIntegrandN 3 σ 15 u) ≤ (858184009944354552643708081307/88067379915036839116800000000000 : ℝ) := by
    rw [← re_join_27 σ]
    linarith [c27, s28]
  have s29 := box0_seg29_re_integral_upper σ hσ0 hσ1
  have c29 : (∫ u in (1/1 : ℝ)..21/8, realThetaReIntegrandN 3 σ 15 u) ≤ (860767477427913580101100081307/88067379915036839116800000000000 : ℝ) := by
    rw [← re_join_28 σ]
    linarith [c28, s29]
  have s30 := box0_seg30_re_integral_upper σ hσ0 hσ1
  have c30 : (∫ u in (1/1 : ℝ)..11/4, realThetaReIntegrandN 3 σ 15 u) ≤ (861803016399303426030974002907/88067379915036839116800000000000 : ℝ) := by
    rw [← re_join_29 σ]
    linarith [c29, s30]
  have s31 := box0_seg31_re_integral_upper σ hσ0 hσ1
  have c31 : (∫ u in (1/1 : ℝ)..23/8, realThetaReIntegrandN 3 σ 15 u) ≤ (862015748925938055169777268507/88067379915036839116800000000000 : ℝ) := by
    rw [← re_join_30 σ]
    linarith [c30, s31]
  have s32 := box0_seg32_re_integral_upper σ hσ0 hσ1
  have c32 : (∫ u in (1/1 : ℝ)..3/1, realThetaReIntegrandN 3 σ 15 u) ≤ (215504961880212235238235787883/22016844978759209779200000000000 : ℝ) := by
    rw [← re_join_31 σ]
    linarith [c31, s32]
  have s33 := box0_seg33_re_integral_upper σ hσ0 hσ1
  have c33 : (∫ u in (1/1 : ℝ)..13/4, realThetaReIntegrandN 3 σ 15 u) ≤ (215506059041705712912693420683/22016844978759209779200000000000 : ℝ) := by
    rw [← re_join_32 σ]
    linarith [c32, s33]
  have s34 := box0_seg34_re_integral_upper σ hσ0 hσ1
  have c34 : (∫ u in (1/1 : ℝ)..7/2, realThetaReIntegrandN 3 σ 15 u) ≤ (215507183853393086226633420683/22016844978759209779200000000000 : ℝ) := by
    rw [← re_join_33 σ]
    linarith [c33, s34]
  have s35 := box0_seg35_re_integral_upper σ hσ0 hσ1
  have c35 : (∫ u in (1/1 : ℝ)..15/4, realThetaReIntegrandN 3 σ 15 u) ≤ (215508335043631608233032186733/22016844978759209779200000000000 : ℝ) := by
    rw [← re_join_34 σ]
    linarith [c34, s35]
  have s36 := box0_seg36_re_integral_upper σ hσ0 hσ1
  have c36 : (∫ u in (1/1 : ℝ)..4/1, realThetaReIntegrandN 3 σ 15 u) ≤ (215509266746454003008958881933/22016844978759209779200000000000 : ℝ) := by
    rw [← re_join_35 σ]
    linarith [c35, s36]
  have s37 := box0_seg37_re_integral_upper σ hσ0 hσ1
  have c37 : (∫ u in (1/1 : ℝ)..17/4, realThetaReIntegrandN 3 σ 15 u) ≤ (215510225324909702567652881933/22016844978759209779200000000000 : ℝ) := by
    rw [← re_join_36 σ]
    linarith [c36, s37]
  have s38 := box0_seg38_re_integral_upper σ hσ0 hσ1
  have c38 : (∫ u in (1/1 : ℝ)..9/2, realThetaReIntegrandN 3 σ 15 u) ≤ (215547694097839906137388462733/22016844978759209779200000000000 : ℝ) := by
    rw [← re_join_37 σ]
    linarith [c37, s38]
  have s39 := box0_seg39_re_integral_upper σ hσ0 hσ1
  have c39 : (∫ u in (1/1 : ℝ)..19/4, realThetaReIntegrandN 3 σ 15 u) ≤ (215603531744401734097274319533/22016844978759209779200000000000 : ℝ) := by
    rw [← re_join_38 σ]
    linarith [c38, s39]
  have s40 := box0_seg40_re_integral_upper σ hσ0 hσ1
  have c40 : (∫ u in (1/1 : ℝ)..5/1, realThetaReIntegrandN 3 σ 15 u) ≤ (215658935790989208238087376333/22016844978759209779200000000000 : ℝ) := by
    rw [← re_join_39 σ]
    linarith [c39, s40]
  exact c40

set_option maxHeartbeats 4000000 in
theorem finite_im_lower (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    (-818077407934480106580176333/22016844978759209779200000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..5/1, realThetaImIntegrandN 3 σ 15 u := by
  have s1 := box0_seg1_im_integral_lower σ hσ0 hσ1
  have c1 : (-133/2548039680 : ℝ) ≤ ∫ u in (1/1 : ℝ)..33/32, realThetaImIntegrandN 3 σ 15 u := s1
  have s2 := box0_seg2_im_integral_lower σ hσ0 hσ1
  have c2 : (-77317/736383467520 : ℝ) ≤ ∫ u in (1/1 : ℝ)..17/16, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_1 σ]
    linarith [c1, s2]
  have s3 := box0_seg3_im_integral_lower σ hσ0 hσ1
  have c3 : (-7499869/47128541921280 : ℝ) ≤ ∫ u in (1/1 : ℝ)..35/32, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_2 σ]
    linarith [c2, s3]
  have s4 := box0_seg4_im_integral_lower σ hσ0 hσ1
  have c4 : (-98009737/471285419212800 : ℝ) ≤ ∫ u in (1/1 : ℝ)..9/8, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_3 σ]
    linarith [c3, s4]
  have s5 := box0_seg5_im_integral_lower σ hσ0 hσ1
  have c5 : (-3043521121/11782135480320000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..37/32, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_4 σ]
    linarith [c4, s5]
  have s6 := box0_seg6_im_integral_lower σ hσ0 hσ1
  have c6 : (-179395690129/577324638535680000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..19/16, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_5 σ]
    linarith [c5, s6]
  have s7 := box0_seg7_im_integral_lower σ hσ0 hσ1
  have c7 : (-206849765329/577324638535680000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..39/32, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_6 σ]
    linarith [c6, s7]
  have s8 := box0_seg8_im_integral_lower σ hσ0 hσ1
  have c8 : (-39832075774201/97567863912529920000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..5/4, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_7 σ]
    linarith [c7, s8]
  have s9 := box0_seg9_im_integral_lower σ hσ0 hσ1
  have c9 : (-45018638319001/97567863912529920000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..41/32, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_8 σ]
    linarith [c8, s9]
  have s10 := box0_seg10_im_integral_lower σ hσ0 hσ1
  have c10 : (-49722729929401/97567863912529920000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..21/16, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_9 σ]
    linarith [c9, s10]
  have s11 := box0_seg11_im_integral_lower σ hσ0 hσ1
  have c11 : (-602778808775411/1073246503037829120000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..43/32, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_10 σ]
    linarith [c10, s11]
  have s12 := box0_seg12_im_integral_lower σ hσ0 hσ1
  have c12 : (-7187614052503921/11805711533416120320000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..11/8, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_11 σ]
    linarith [c11, s12]
  have s13 := box0_seg13_im_integral_lower σ hσ0 hσ1
  have c13 : (-7798591809525553/11805711533416120320000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..45/32, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_12 σ]
    linarith [c12, s13]
  have s14 := box0_seg14_im_integral_lower σ hσ0 hσ1
  have c14 : (-8352524960240497/11805711533416120320000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..23/16, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_13 σ]
    linarith [c13, s14]
  have s15 := box0_seg15_im_integral_lower σ hσ0 hσ1
  have c15 : (-8971527510806897/11805711533416120320000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..47/32, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_14 σ]
    linarith [c14, s15]
  have s16 := box0_seg16_im_integral_lower σ hσ0 hσ1
  have c16 : (-9533077728835697/11805711533416120320000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..3/2, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_15 σ]
    linarith [c15, s16]
  have s17 := box0_seg17_im_integral_lower σ hσ0 hσ1
  have c17 : (-1188627309104965276669/780652675147140956160000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..25/16, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_16 σ]
    linarith [c16, s17]
  have s18 := box0_seg18_im_integral_lower σ hσ0 hσ1
  have c18 : (-705009339829638065561/156130535029428191232000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..13/8, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_17 σ]
    linarith [c17, s18]
  have s19 := box0_seg19_im_integral_lower σ hσ0 hσ1
  have c19 : (-2531750937825975840952261/281815615728117885173760000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..27/16, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_18 σ]
    linarith [c18, s19]
  have s20 := box0_seg20_im_integral_lower σ hσ0 hσ1
  have c20 : (-3968542720083578422130629/281815615728117885173760000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..7/4, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_19 σ]
    linarith [c19, s20]
  have s21 := box0_seg21_im_integral_lower σ hσ0 hσ1
  have c21 : (-5398335768738606872083189/281815615728117885173760000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..29/16, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_20 σ]
    linarith [c20, s21]
  have s22 := box0_seg22_im_integral_lower σ hσ0 hσ1
  have c22 : (-6700442824959384451518709/281815615728117885173760000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..15/8, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_21 σ]
    linarith [c21, s22]
  have s23 := box0_seg23_im_integral_lower σ hσ0 hσ1
  have c23 : (-195086049414882237444449677/7045390393202947129344000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..31/16, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_22 σ]
    linarith [c22, s23]
  have s24 := box0_seg24_im_integral_lower σ hσ0 hσ1
  have c24 : (-5425474317619720661326531/176134759830073678233600000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..2/1, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_23 σ]
    linarith [c23, s24]
  have s25 := box0_seg25_im_integral_lower σ hσ0 hσ1
  have c25 : (-763922763964631020263914087/22016844978759209779200000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..17/8, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_24 σ]
    linarith [c24, s25]
  have s26 := box0_seg26_im_integral_lower σ hσ0 hσ1
  have c26 : (-3189063103250624632162404023/88067379915036839116800000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..9/4, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_25 σ]
    linarith [c25, s26]
  have s27 := box0_seg27_im_integral_lower σ hσ0 hσ1
  have c27 : (-3205940964352910081742001307/88067379915036839116800000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..19/8, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_26 σ]
    linarith [c26, s27]
  have s28 := box0_seg28_im_integral_lower σ hσ0 hσ1
  have c28 : (-3210305607064241384142001307/88067379915036839116800000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..5/2, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_27 σ]
    linarith [c27, s28]
  have s29 := box0_seg29_im_integral_lower σ hσ0 hσ1
  have c29 : (-3214656964540047124542001307/88067379915036839116800000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..21/8, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_28 σ]
    linarith [c28, s29]
  have s30 := box0_seg30_im_integral_lower σ hσ0 hσ1
  have c30 : (-3219407284651620960207922907/88067379915036839116800000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..11/4, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_29 σ]
    linarith [c29, s30]
  have s31 := box0_seg31_im_integral_lower σ hσ0 hσ1
  have c31 : (-3224202942042413117763188507/88067379915036839116800000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..23/8, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_30 σ]
    linarith [c30, s31]
  have s32 := box0_seg32_im_integral_lower σ hσ0 hσ1
  have c32 : (-807075384238324725232267883/22016844978759209779200000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..3/1, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_31 σ]
    linarith [c31, s32]
  have s33 := box0_seg33_im_integral_lower σ hσ0 hσ1
  have c33 : (-808172545731802399689900683/22016844978759209779200000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..13/4, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_32 σ]
    linarith [c32, s33]
  have s34 := box0_seg34_im_integral_lower σ hσ0 hσ1
  have c34 : (-809297357419175713629900683/22016844978759209779200000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..7/2, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_33 σ]
    linarith [c33, s34]
  have s35 := box0_seg35_im_integral_lower σ hσ0 hσ1
  have c35 : (-811136574063283945334266733/22016844978759209779200000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..15/4, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_34 σ]
    linarith [c34, s35]
  have s36 := box0_seg36_im_integral_lower σ hσ0 hσ1
  have c36 : (-812985645426460355001761933/22016844978759209779200000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..4/1, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_35 σ]
    linarith [c35, s36]
  have s37 := box0_seg37_im_integral_lower σ hσ0 hσ1
  have c37 : (-814494645006628893940241933/22016844978759209779200000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..17/4, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_36 σ]
    linarith [c36, s37]
  have s38 := box0_seg38_im_integral_lower σ hσ0 hσ1
  have c38 : (-815819097430036094288302733/22016844978759209779200000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..9/2, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_37 σ]
    linarith [c37, s38]
  have s39 := box0_seg39_im_integral_lower σ hσ0 hσ1
  have c39 : (-817165052669435009970639533/22016844978759209779200000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..19/4, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_38 σ]
    linarith [c38, s39]
  have s40 := box0_seg40_im_integral_lower σ hσ0 hσ1
  have c40 : (-818077407934480106580176333/22016844978759209779200000000000 : ℝ) ≤ ∫ u in (1/1 : ℝ)..5/1, realThetaImIntegrandN 3 σ 15 u := by
    rw [← im_join_39 σ]
    linarith [c39, s40]
  exact c40

set_option maxHeartbeats 4000000 in
theorem finite_im_upper (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    (∫ u in (1/1 : ℝ)..5/1, realThetaImIntegrandN 3 σ 15 u) ≤ (1627254071576942842104080333/22016844978759209779200000000000 : ℝ) := by
  have s1 := box0_seg1_im_integral_upper σ hσ0 hσ1
  have c1 : (∫ u in (1/1 : ℝ)..33/32, realThetaImIntegrandN 3 σ 15 u) ≤ (1880969/7962624000000 : ℝ) := s1
  have s2 := box0_seg2_im_integral_upper σ hσ0 hσ1
  have c2 : (∫ u in (1/1 : ℝ)..17/16, realThetaImIntegrandN 3 σ 15 u) ≤ (3213761801/2301198336000000 : ℝ) := by
    rw [← im_join_1 σ]
    linarith [c1, s2]
  have s3 := box0_seg3_im_integral_upper σ hσ0 hσ1
  have c3 : (∫ u in (1/1 : ℝ)..35/32, realThetaImIntegrandN 3 σ 15 u) ≤ (2921168364613/736383467520000000 : ℝ) := by
    rw [← im_join_2 σ]
    linarith [c2, s3]
  have s4 := box0_seg4_im_integral_upper σ hσ0 hσ1
  have c4 : (∫ u in (1/1 : ℝ)..9/8, realThetaImIntegrandN 3 σ 15 u) ≤ (11850187358813/1472766935040000000 : ℝ) := by
    rw [← im_join_3 σ]
    linarith [c3, s4]
  have s5 := box0_seg5_im_integral_upper σ hσ0 hσ1
  have c5 : (∫ u in (1/1 : ℝ)..37/32, realThetaImIntegrandN 3 σ 15 u) ≤ (19854276536669/1472766935040000000 : ℝ) := by
    rw [← im_join_4 σ]
    linarith [c4, s5]
  have s6 := box0_seg6_im_integral_upper σ hσ0 hσ1
  have c6 : (∫ u in (1/1 : ℝ)..19/16, realThetaImIntegrandN 3 σ 15 u) ≤ (1439516983991501/72165579816960000000 : ℝ) := by
    rw [← im_join_5 σ]
    linarith [c5, s6]
  have s7 := box0_seg7_im_integral_upper σ hσ0 hσ1
  have c7 : (∫ u in (1/1 : ℝ)..39/32, realThetaImIntegrandN 3 σ 15 u) ≤ (1951071745566989/72165579816960000000 : ℝ) := by
    rw [← im_join_6 σ]
    linarith [c6, s7]
  have s8 := box0_seg8_im_integral_upper σ hσ0 hσ1
  have c8 : (∫ u in (1/1 : ℝ)..5/4, realThetaImIntegrandN 3 σ 15 u) ≤ (83758711768846417/2439196597813248000000 : ℝ) := by
    rw [← im_join_7 σ]
    linarith [c7, s8]
  have s9 := box0_seg9_im_integral_upper σ hσ0 hσ1
  have c9 : (∫ u in (1/1 : ℝ)..41/32, realThetaImIntegrandN 3 σ 15 u) ≤ (505826915964314549/12195982989066240000000 : ℝ) := by
    rw [← im_join_8 σ]
    linarith [c8, s9]
  have s10 := box0_seg10_im_integral_upper σ hσ0 hσ1
  have c10 : (∫ u in (1/1 : ℝ)..21/16, realThetaImIntegrandN 3 σ 15 u) ≤ (586809957989112917/12195982989066240000000 : ℝ) := by
    rw [← im_join_9 σ]
    linarith [c9, s10]
  have s11 := box0_seg11_im_integral_upper σ hσ0 hσ1
  have c11 : (∫ u in (1/1 : ℝ)..43/32, realThetaImIntegrandN 3 σ 15 u) ≤ (7247385664713789607/134155812879728640000000 : ℝ) := by
    rw [← im_join_10 σ]
    linarith [c10, s11]
  have s12 := box0_seg12_im_integral_upper σ hσ0 hσ1
  have c12 : (∫ u in (1/1 : ℝ)..11/8, realThetaImIntegrandN 3 σ 15 u) ≤ (87093980269988713517/1475713941677015040000000 : ℝ) := by
    rw [← im_join_11 σ]
    linarith [c11, s12]
  have s13 := box0_seg13_im_integral_upper σ hσ0 hσ1
  have c13 : (∫ u in (1/1 : ℝ)..45/32, realThetaImIntegrandN 3 σ 15 u) ≤ (464987889584067653281/7378569708385075200000000 : ℝ) := by
    rw [← im_join_12 σ]
    linarith [c12, s13]
  have s14 := box0_seg14_im_integral_upper σ hσ0 hσ1
  have c14 : (∫ u in (1/1 : ℝ)..23/16, realThetaImIntegrandN 3 σ 15 u) ≤ (97373598467315912237/1475713941677015040000000 : ℝ) := by
    rw [← im_join_13 σ]
    linarith [c13, s14]
  have s15 := box0_seg15_im_integral_upper σ hσ0 hσ1
  have c15 : (∫ u in (1/1 : ℝ)..47/32, realThetaImIntegrandN 3 σ 15 u) ≤ (20054450379649123337/295142788335403008000000 : ℝ) := by
    rw [← im_join_14 σ]
    linarith [c14, s15]
  have s16 := box0_seg16_im_integral_upper σ hσ0 hσ1
  have c16 : (∫ u in (1/1 : ℝ)..3/2, realThetaImIntegrandN 3 σ 15 u) ≤ (101773580758521405229/1475713941677015040000000 : ℝ) := by
    rw [← im_join_15 σ]
    linarith [c15, s16]
  have s17 := box0_seg17_im_integral_upper σ hσ0 hσ1
  have c17 : (∫ u in (1/1 : ℝ)..25/16, realThetaImIntegrandN 3 σ 15 u) ≤ (54011029507189627331581/780652675147140956160000000 : ℝ) := by
    rw [← im_join_16 σ]
    linarith [c16, s17]
  have s18 := box0_seg18_im_integral_upper σ hσ0 hσ1
  have c18 : (∫ u in (1/1 : ℝ)..13/8, realThetaImIntegrandN 3 σ 15 u) ≤ (54051725955825441731581/780652675147140956160000000 : ℝ) := by
    rw [← im_join_17 σ]
    linarith [c17, s18]
  have s19 := box0_seg19_im_integral_upper σ hσ0 hσ1
  have c19 : (∫ u in (1/1 : ℝ)..27/16, realThetaImIntegrandN 3 σ 15 u) ≤ (19527443720034406199500741/281815615728117885173760000000 : ℝ) := by
    rw [← im_join_18 σ]
    linarith [c18, s19]
  have s20 := box0_seg20_im_integral_upper σ hσ0 hσ1
  have c20 : (∫ u in (1/1 : ℝ)..7/4, realThetaImIntegrandN 3 σ 15 u) ≤ (19542620773098808228300741/281815615728117885173760000000 : ℝ) := by
    rw [← im_join_19 σ]
    linarith [c19, s20]
  have s21 := box0_seg21_im_integral_upper σ hσ0 hσ1
  have c21 : (∫ u in (1/1 : ℝ)..29/16, realThetaImIntegrandN 3 σ 15 u) ≤ (19556730689619619489450741/281815615728117885173760000000 : ℝ) := by
    rw [← im_join_20 σ]
    linarith [c20, s21]
  have s22 := box0_seg22_im_integral_upper σ hσ0 hσ1
  have c22 : (∫ u in (1/1 : ℝ)..15/8, realThetaImIntegrandN 3 σ 15 u) ≤ (19571795893653501548650741/281815615728117885173760000000 : ℝ) := by
    rw [← im_join_21 σ]
    linarith [c21, s22]
  have s23 := box0_seg23_im_integral_upper σ hσ0 hσ1
  have c23 : (∫ u in (1/1 : ℝ)..31/16, realThetaImIntegrandN 3 σ 15 u) ≤ (489653668531568972476462477/7045390393202947129344000000000 : ℝ) := by
    rw [← im_join_22 σ]
    linarith [c22, s23]
  have s24 := box0_seg24_im_integral_upper σ hσ0 hσ1
  have c24 : (∫ u in (1/1 : ℝ)..2/1, realThetaImIntegrandN 3 σ 15 u) ≤ (12249976882995053907414211/176134759830073678233600000000 : ℝ) := by
    rw [← im_join_23 σ]
    linarith [c23, s24]
  have s25 := box0_seg25_im_integral_upper σ hσ0 hσ1
  have c25 : (∫ u in (1/1 : ℝ)..17/8, realThetaImIntegrandN 3 σ 15 u) ≤ (1532385857805665412448298087/22016844978759209779200000000000 : ℝ) := by
    rw [← im_join_24 σ]
    linarith [c24, s25]
  have s26 := box0_seg26_im_integral_upper σ hσ0 hσ1
  have c26 : (∫ u in (1/1 : ℝ)..9/4, realThetaImIntegrandN 3 σ 15 u) ≤ (6134346277624216232126820023/88067379915036839116800000000000 : ℝ) := by
    rw [← im_join_25 σ]
    linarith [c25, s26]
  have s27 := box0_seg27_im_integral_upper σ hσ0 hσ1
  have c27 : (∫ u in (1/1 : ℝ)..19/8, realThetaImIntegrandN 3 σ 15 u) ≤ (6149297664790860250850737307/88067379915036839116800000000000 : ℝ) := by
    rw [← im_join_26 σ]
    linarith [c26, s27]
  have s28 := box0_seg28_im_integral_upper σ hσ0 hσ1
  have c28 : (∫ u in (1/1 : ℝ)..5/2, realThetaImIntegrandN 3 σ 15 u) ≤ (6210129039330068114802097307/88067379915036839116800000000000 : ℝ) := by
    rw [← im_join_27 σ]
    linarith [c27, s28]
  have s29 := box0_seg29_im_integral_upper σ hσ0 hσ1
  have c29 : (∫ u in (1/1 : ℝ)..21/8, realThetaImIntegrandN 3 σ 15 u) ≤ (6285406090273162452419377307/88067379915036839116800000000000 : ℝ) := by
    rw [← im_join_28 σ]
    linarith [c28, s29]
  have s30 := box0_seg30_im_integral_upper σ hσ0 hσ1
  have c30 : (∫ u in (1/1 : ℝ)..11/4, realThetaImIntegrandN 3 σ 15 u) ≤ (6353705031118882189038898907/88067379915036839116800000000000 : ℝ) := by
    rw [← im_join_29 σ]
    linarith [c29, s30]
  have s31 := box0_seg31_im_integral_upper σ hσ0 hσ1
  have c31 : (∫ u in (1/1 : ℝ)..23/8, realThetaImIntegrandN 3 σ 15 u) ≤ (6406570800046631954612084507/88067379915036839116800000000000 : ℝ) := by
    rw [← im_join_30 σ]
    linarith [c30, s31]
  have s32 := box0_seg32_im_integral_upper σ hσ0 hσ1
  have c32 : (∫ u in (1/1 : ℝ)..3/1, realThetaImIntegrandN 3 σ 15 u) ≤ (1610717257684738270520011883/22016844978759209779200000000000 : ℝ) := by
    rw [← im_join_31 σ]
    linarith [c31, s32]
  have s33 := box0_seg33_im_integral_upper σ hσ0 hσ1
  have c33 : (∫ u in (1/1 : ℝ)..13/4, realThetaImIntegrandN 3 σ 15 u) ≤ (1619459157018062892817644683/22016844978759209779200000000000 : ℝ) := by
    rw [← im_join_32 σ]
    linarith [c32, s33]
  have s34 := box0_seg34_im_integral_upper σ hσ0 hσ1
  have c34 : (∫ u in (1/1 : ℝ)..7/2, realThetaImIntegrandN 3 σ 15 u) ≤ (1622281100505882229178124683/22016844978759209779200000000000 : ℝ) := by
    rw [← im_join_33 σ]
    linarith [c33, s34]
  have s35 := box0_seg35_im_integral_upper σ hσ0 hσ1
  have c35 : (∫ u in (1/1 : ℝ)..15/4, realThetaImIntegrandN 3 σ 15 u) ≤ (1623432290744404235576890733/22016844978759209779200000000000 : ℝ) := by
    rw [← im_join_34 σ]
    linarith [c34, s35]
  have s36 := box0_seg36_im_integral_upper σ hσ0 hσ1
  have c36 : (∫ u in (1/1 : ℝ)..4/1, realThetaImIntegrandN 3 σ 15 u) ≤ (1624363993566799011503585933/22016844978759209779200000000000 : ℝ) := by
    rw [← im_join_35 σ]
    linarith [c35, s36]
  have s37 := box0_seg37_im_integral_upper σ hσ0 hσ1
  have c37 : (∫ u in (1/1 : ℝ)..17/4, realThetaImIntegrandN 3 σ 15 u) ≤ (1625322572022498570197585933/22016844978759209779200000000000 : ℝ) := by
    rw [← im_join_36 σ]
    linarith [c36, s37]
  have s38 := box0_seg38_im_integral_upper σ hσ0 hσ1
  have c38 : (∫ u in (1/1 : ℝ)..9/2, realThetaImIntegrandN 3 σ 15 u) ≤ (1626096603321436790301166733/22016844978759209779200000000000 : ℝ) := by
    rw [← im_join_37 σ]
    linarith [c37, s38]
  have s39 := box0_seg39_im_integral_upper σ hσ0 hσ1
  have c39 : (∫ u in (1/1 : ℝ)..19/4, realThetaImIntegrandN 3 σ 15 u) ≤ (1626892137436366725739023533/22016844978759209779200000000000 : ℝ) := by
    rw [← im_join_38 σ]
    linarith [c38, s39]
  have s40 := box0_seg40_im_integral_upper σ hσ0 hσ1
  have c40 : (∫ u in (1/1 : ℝ)..5/1, realThetaImIntegrandN 3 σ 15 u) ≤ (1627254071576942842104080333/22016844978759209779200000000000 : ℝ) := by
    rw [← im_join_39 σ]
    linarith [c39, s40]
  exact c40

/-! ## §B.4 — `intervalIntegral 1..5` = set integral over `Ioc 1 5` -/

theorem re_interval_eq_Ioc (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..5/1, realThetaReIntegrandN 3 σ 15 u)
      = ∫ u in Set.Ioc (1 : ℝ) 5, realThetaReIntegrandN 3 σ 15 u := by
  have h1 : (1/1 : ℝ) = 1 := by norm_num
  have h5 : (5/1 : ℝ) = 5 := by norm_num
  rw [h1, h5, intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 5)]

theorem im_interval_eq_Ioc (σ : ℝ) :
    (∫ u in (1/1 : ℝ)..5/1, realThetaImIntegrandN 3 σ 15 u)
      = ∫ u in Set.Ioc (1 : ℝ) 5, realThetaImIntegrandN 3 σ 15 u := by
  have h1 : (1/1 : ℝ) = 1 := by norm_num
  have h5 : (5/1 : ℝ) = 5 := by norm_num
  rw [h1, h5, intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 5)]

/-! ## §B.5 — §8 envelope applied EXACTLY ONCE, `T := 5` -/

theorem re_Lambda0_lower (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    (19564553848401467842464431639/4403368995751841955840000000000 : ℝ) ≤ (completedRiemannZeta₀ (⟨σ, 15⟩ : ℂ)).re := by
  have hσa : (0 : ℝ) ≤ σ := by linarith
  have hσb : σ ≤ 1 := by linarith
  have h8 := re_Lambda0_close_to_truncated_integral (N := 3) (σ := σ) (t := 15)
    (T := 5) hσa hσb (by norm_num)
  push_cast at h8
  have henv := PrincipiaTractalis.RiemannXiBox0Envelope.box0_envelope_le
  have habs := abs_le.mp (le_trans h8 henv)
  have hfin := finite_re_lower σ hσ0 hσ1
  rw [re_interval_eq_Ioc σ] at hfin
  linarith [habs.1, hfin]

theorem im_Lambda0_lower (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    (-822480776930231948536016333/22016844978759209779200000000000 : ℝ) ≤ (completedRiemannZeta₀ (⟨σ, 15⟩ : ℂ)).im := by
  have hσa : (0 : ℝ) ≤ σ := by linarith
  have hσb : σ ≤ 1 := by linarith
  have h8 := im_Lambda0_close_to_truncated_integral (N := 3) (σ := σ) (t := 15)
    (T := 5) hσa hσb (by norm_num)
  push_cast at h8
  have henv := PrincipiaTractalis.RiemannXiBox0Envelope.box0_envelope_le
  have habs := abs_le.mp (le_trans h8 henv)
  have hfin := finite_im_lower σ hσ0 hσ1
  rw [im_interval_eq_Ioc σ] at hfin
  linarith [habs.1, hfin]

theorem im_Lambda0_upper (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    (completedRiemannZeta₀ (⟨σ, 15⟩ : ℂ)).im ≤ (1631657440572694684059920333/22016844978759209779200000000000 : ℝ) := by
  have hσa : (0 : ℝ) ≤ σ := by linarith
  have hσb : σ ≤ 1 := by linarith
  have h8 := im_Lambda0_close_to_truncated_integral (N := 3) (σ := σ) (t := 15)
    (T := 5) hσa hσb (by norm_num)
  push_cast at h8
  have henv := PrincipiaTractalis.RiemannXiBox0Envelope.box0_envelope_le
  have habs := abs_le.mp (le_trans h8 henv)
  have hfin := finite_im_upper σ hσ0 hσ1
  rw [im_interval_eq_Ioc σ] at hfin
  linarith [habs.2, hfin]

theorem re_Lambda0_upper (σ : ℝ)
    (hσ0 : (1 : ℝ)/2 ≤ σ) (hσ1 : σ ≤ 9/16) :
    (completedRiemannZeta₀ (⟨σ, 15⟩ : ℂ)).re ≤ 1 := by
  have hσa : (0 : ℝ) ≤ σ := by linarith
  have hσb : σ ≤ 1 := by linarith
  have h8 := re_Lambda0_close_to_truncated_integral (N := 3) (σ := σ) (t := 15)
    (T := 5) hσa hσb (by norm_num)
  push_cast at h8
  have henv := PrincipiaTractalis.RiemannXiBox0Envelope.box0_envelope_le
  have habs := abs_le.mp (le_trans h8 henv)
  have hfin := finite_re_upper σ hσ0 hσ1
  rw [re_interval_eq_Ioc σ] at hfin
  linarith [habs.2, hfin]

/-! ## §B.6 — exact rational margins -/

theorem RE_MARGIN_pos : (0 : ℝ) < (19564553848401467842464431639/4403368995751841955840000000000 : ℝ) - (2221/500000 : ℝ) := by norm_num

theorem IM_LO_MARGIN_pos : (0 : ℝ) < (-822480776930231948536016333/22016844978759209779200000000000 : ℝ) - (-1/10000 : ℝ) := by norm_num

theorem IM_HI_MARGIN_pos : (0 : ℝ) < (1/10000 : ℝ) - (1631657440572694684059920333/22016844978759209779200000000000 : ℝ) := by norm_num

/-! ## §B.7 — enclosures and the unconditional Box-0 top-edge bound -/

theorem box0_re_enclosure :
    PrincipiaTractalis.RiemannXiThetaBoxEnclosure.BoxReEnclosure
      ((1 : ℝ) / 2) (9/16) 15 (2221/500000) 1 := by
  constructor
  intro σ h0 h1
  refine ⟨?_, re_Lambda0_upper σ h0 h1⟩
  have := re_Lambda0_lower σ h0 h1
  linarith

theorem box0_im_enclosure :
    PrincipiaTractalis.RiemannXiThetaBoxEnclosure.BoxImEnclosure
      ((1 : ℝ) / 2) (9/16) 15 (-(1/10000)) (1/10000) := by
  constructor
  intro σ h0 h1
  refine ⟨?_, ?_⟩
  · have := im_Lambda0_lower σ h0 h1
    linarith
  · have := im_Lambda0_upper σ h0 h1
    linarith

/-- **★ BOX 0 CLOSED ★** — unconditional top-edge negativity at `t = 15`
for `σ ∈ [1/2, 9/16]`. -/
theorem top15_box0_re_lt_neg_1e4 {σ : ℝ}
    (h0 : (1 : ℝ) / 2 ≤ σ) (h1 : σ ≤ 9/16) :
    (riemannXiEntire (⟨σ, 15⟩ : ℂ)).re < -(1/10000 : ℝ) :=
  top15_box0_re_lt_neg_1e4_conditional box0_re_enclosure box0_im_enclosure h0 h1

end PrincipiaTractalis.RiemannXiBox0Bridge
