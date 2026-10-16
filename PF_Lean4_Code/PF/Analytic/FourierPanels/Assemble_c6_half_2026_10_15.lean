/-
# PF.Analytic.FourierPanels.Assemble_c6_half_2026_10_15

**M2.5 assembly** — combines the 16 per-panel integral bounds from
`Seg01Range_c6_2026_10_15` (u ∈ [0, 1/4]) and `Seg02Range_c6_2026_10_15`
(u ∈ [1/4, 1/2]) into two headline [0, 1/2]-integral enclosures:

  reLambda0_half_lb_ub :
    R_lb ≤ ∫ u in 0..(1/2), nodeR_fourier_plus_at_c6_N3  u ≤ R_ub

  imLambda0_half_lb_ub :
    I_lb ≤ ∫ u in 0..(1/2), nodeR_fourier_minus_at_c6_N3 u ≤ I_ub

where

  R_lb =   0.015257951790625,  R_ub =   0.018201128625
  I_lb =  -0.000051228868750,  I_ub =   0.001373452065625

These numbers are the exact sums `width · (L_k)` and `width · (U_k)` with
`width = 1/32` and `{L_k, U_k}` as emitted by the panel generator; every
product is a terminating decimal, so the sums are exact.

Composition is purely integration-additivity:

  ∫_0^{1/2} f = Σ_{k=0..15} ∫_{a_k}^{b_k} f    with  a_k = k/32.

We do NOT use the Finset version `sum_integral_adjacent_intervals`; a
15-fold chain of `intervalIntegral.integral_add_adjacent_intervals` is
simpler and reads linearly.

Three-axiom bar: every top-level declaration prints
`[propext, Classical.choice, Quot.sound]`.  No sorry, no native_decide,
no `interval` tactic, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-15.
-/
import PF.Analytic.FourierPanels.Seg01Range_c6_2026_10_15
import PF.Analytic.FourierPanels.Seg02Range_c6_2026_10_15

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace PrincipiaTractalis
namespace FourierPanels_c6
namespace Assemble_half

open MeasureTheory
open PrincipiaTractalis.FourierPanels_c6

/-! ## §1 — Local notation and the 16-panel endpoint list

Panel endpoints in order:
  0, 1/32, 2/32, 3/32, 4/32, 5/32, 6/32, 7/32, 8/32,
  9/32, 10/32, 11/32, 12/32, 13/32, 14/32, 15/32, 16/32 = 1/2.

As decimals (matching the Seg01/Seg02 statements verbatim):
  0, 0.03125, 0.0625, 0.09375, 0.125, 0.15625, 0.1875, 0.21875, 0.25,
  0.28125, 0.3125, 0.34375, 0.375, 0.40625, 0.4375, 0.46875, 0.5.
-/

-- Abbreviations for the two integrands.
private noncomputable abbrev fP : ℝ → ℝ := nodeR_fourier_plus_at_c6_N3
private noncomputable abbrev fM : ℝ → ℝ := nodeR_fourier_minus_at_c6_N3

-- IntervalIntegrability on every sub-interval we touch.
private theorem iiP (a b : ℝ) : IntervalIntegrable fP MeasureTheory.volume a b :=
  Seg01Range.nodeR_fourier_plus_at_c6_N3_intervalIntegrable a b

private theorem iiM (a b : ℝ) : IntervalIntegrable fM MeasureTheory.volume a b :=
  Seg01Range.nodeR_fourier_minus_at_c6_N3_intervalIntegrable a b

/-! ## §2 — Headline PLUS enclosure on `[0, 1/2]` -/

theorem reLambda0_half_lb_ub :
    (0.015257951790625 : ℝ)
      ≤ (∫ u in (0 : ℝ)..(1/2 : ℝ), nodeR_fourier_plus_at_c6_N3 u)
    ∧ (∫ u in (0 : ℝ)..(1/2 : ℝ), nodeR_fourier_plus_at_c6_N3 u)
      ≤ (0.018201128625 : ℝ) := by
  -- Pull the 16 panel bounds.
  have b00 := Seg01Range.s01p0_plus_integral_bound
  have b01 := Seg01Range.s01p1_plus_integral_bound
  have b02 := Seg01Range.s01p2_plus_integral_bound
  have b03 := Seg01Range.s01p3_plus_integral_bound
  have b04 := Seg01Range.s01p4_plus_integral_bound
  have b05 := Seg01Range.s01p5_plus_integral_bound
  have b06 := Seg01Range.s01p6_plus_integral_bound
  have b07 := Seg01Range.s01p7_plus_integral_bound
  have b08 := Seg02Range.s02p0_plus_integral_bound
  have b09 := Seg02Range.s02p1_plus_integral_bound
  have b10 := Seg02Range.s02p2_plus_integral_bound
  have b11 := Seg02Range.s02p3_plus_integral_bound
  have b12 := Seg02Range.s02p4_plus_integral_bound
  have b13 := Seg02Range.s02p5_plus_integral_bound
  have b14 := Seg02Range.s02p6_plus_integral_bound
  have b15 := Seg02Range.s02p7_plus_integral_bound
  -- Convert `∫_0^{1/2}` to its 16-panel sum via chained adjacency.
  -- First build the "right fold" sum, then chain backwards from 0.
  -- We use: ∫_a^c + ∫_c^b = ∫_a^b.
  have h01 : (∫ u in (0 : ℝ)..(0.03125 : ℝ), fP u)
             + (∫ u in (0.03125 : ℝ)..(0.0625 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(0.0625 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h02 : (∫ u in (0 : ℝ)..(0.0625 : ℝ), fP u)
             + (∫ u in (0.0625 : ℝ)..(0.09375 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(0.09375 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h03 : (∫ u in (0 : ℝ)..(0.09375 : ℝ), fP u)
             + (∫ u in (0.09375 : ℝ)..(0.125 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(0.125 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h04 : (∫ u in (0 : ℝ)..(0.125 : ℝ), fP u)
             + (∫ u in (0.125 : ℝ)..(0.15625 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(0.15625 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h05 : (∫ u in (0 : ℝ)..(0.15625 : ℝ), fP u)
             + (∫ u in (0.15625 : ℝ)..(0.1875 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(0.1875 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h06 : (∫ u in (0 : ℝ)..(0.1875 : ℝ), fP u)
             + (∫ u in (0.1875 : ℝ)..(0.21875 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(0.21875 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h07 : (∫ u in (0 : ℝ)..(0.21875 : ℝ), fP u)
             + (∫ u in (0.21875 : ℝ)..(0.25 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(0.25 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h08 : (∫ u in (0 : ℝ)..(0.25 : ℝ), fP u)
             + (∫ u in (0.25 : ℝ)..(0.28125 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(0.28125 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h09 : (∫ u in (0 : ℝ)..(0.28125 : ℝ), fP u)
             + (∫ u in (0.28125 : ℝ)..(0.3125 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(0.3125 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h10 : (∫ u in (0 : ℝ)..(0.3125 : ℝ), fP u)
             + (∫ u in (0.3125 : ℝ)..(0.34375 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(0.34375 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h11 : (∫ u in (0 : ℝ)..(0.34375 : ℝ), fP u)
             + (∫ u in (0.34375 : ℝ)..(0.375 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(0.375 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h12 : (∫ u in (0 : ℝ)..(0.375 : ℝ), fP u)
             + (∫ u in (0.375 : ℝ)..(0.40625 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(0.40625 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h13 : (∫ u in (0 : ℝ)..(0.40625 : ℝ), fP u)
             + (∫ u in (0.40625 : ℝ)..(0.4375 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(0.4375 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h14 : (∫ u in (0 : ℝ)..(0.4375 : ℝ), fP u)
             + (∫ u in (0.4375 : ℝ)..(0.46875 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(0.46875 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h15 : (∫ u in (0 : ℝ)..(0.46875 : ℝ), fP u)
             + (∫ u in (0.46875 : ℝ)..(0.5 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(0.5 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  -- Normalize the right endpoint `1/2 = 0.5`.
  have hhalf : (1 / 2 : ℝ) = (0.5 : ℝ) := by norm_num
  refine ⟨?_, ?_⟩
  · -- Lower bound.
    rw [hhalf]
    -- Rewrite `∫_0^{0.5} f` as the sum of 16 adjacent integrals.
    have hsplit : ∫ u in (0 : ℝ)..(0.5 : ℝ), fP u
      = (∫ u in (0 : ℝ)..(0.03125 : ℝ), fP u)
      + (∫ u in (0.03125 : ℝ)..(0.0625 : ℝ), fP u)
      + (∫ u in (0.0625 : ℝ)..(0.09375 : ℝ), fP u)
      + (∫ u in (0.09375 : ℝ)..(0.125 : ℝ), fP u)
      + (∫ u in (0.125 : ℝ)..(0.15625 : ℝ), fP u)
      + (∫ u in (0.15625 : ℝ)..(0.1875 : ℝ), fP u)
      + (∫ u in (0.1875 : ℝ)..(0.21875 : ℝ), fP u)
      + (∫ u in (0.21875 : ℝ)..(0.25 : ℝ), fP u)
      + (∫ u in (0.25 : ℝ)..(0.28125 : ℝ), fP u)
      + (∫ u in (0.28125 : ℝ)..(0.3125 : ℝ), fP u)
      + (∫ u in (0.3125 : ℝ)..(0.34375 : ℝ), fP u)
      + (∫ u in (0.34375 : ℝ)..(0.375 : ℝ), fP u)
      + (∫ u in (0.375 : ℝ)..(0.40625 : ℝ), fP u)
      + (∫ u in (0.40625 : ℝ)..(0.4375 : ℝ), fP u)
      + (∫ u in (0.4375 : ℝ)..(0.46875 : ℝ), fP u)
      + (∫ u in (0.46875 : ℝ)..(0.5 : ℝ), fP u) := by
      linarith [h01, h02, h03, h04, h05, h06, h07, h08,
                h09, h10, h11, h12, h13, h14, h15]
    rw [hsplit]
    have hnum : (0.015257951790625 : ℝ)
      = (0.03125 : ℝ) * (0.0778858113 : ℝ)
      + (0.03125 : ℝ) * (0.0698883764 : ℝ)
      + (0.03125 : ℝ) * (0.061944169 : ℝ)
      + (0.03125 : ℝ) * (0.0542022126 : ℝ)
      + (0.03125 : ℝ) * (0.0467878643 : ℝ)
      + (0.03125 : ℝ) * (0.0398025109 : ℝ)
      + (0.03125 : ℝ) * (0.0333239212 : ℝ)
      + (0.03125 : ℝ) * (0.0274071905 : ℝ)
      + (0.03125 : ℝ) * (0.0220862003 : ℝ)
      + (0.03125 : ℝ) * (0.0173755038 : ℝ)
      + (0.03125 : ℝ) * (0.0132725413 : ℝ)
      + (0.03125 : ℝ) * (0.0097600847 : ℝ)
      + (0.03125 : ℝ) * (0.0068088109 : ℝ)
      + (0.03125 : ℝ) * (0.0043799092 : ℝ)
      + (0.03125 : ℝ) * (0.002427633 : ℝ)
      + (0.03125 : ℝ) * (0.0009017179 : ℝ) := by norm_num
    rw [hnum]
    linarith [b00.1, b01.1, b02.1, b03.1, b04.1, b05.1, b06.1, b07.1,
              b08.1, b09.1, b10.1, b11.1, b12.1, b13.1, b14.1, b15.1]
  · -- Upper bound.
    rw [hhalf]
    have hsplit : ∫ u in (0 : ℝ)..(0.5 : ℝ), fP u
      = (∫ u in (0 : ℝ)..(0.03125 : ℝ), fP u)
      + (∫ u in (0.03125 : ℝ)..(0.0625 : ℝ), fP u)
      + (∫ u in (0.0625 : ℝ)..(0.09375 : ℝ), fP u)
      + (∫ u in (0.09375 : ℝ)..(0.125 : ℝ), fP u)
      + (∫ u in (0.125 : ℝ)..(0.15625 : ℝ), fP u)
      + (∫ u in (0.15625 : ℝ)..(0.1875 : ℝ), fP u)
      + (∫ u in (0.1875 : ℝ)..(0.21875 : ℝ), fP u)
      + (∫ u in (0.21875 : ℝ)..(0.25 : ℝ), fP u)
      + (∫ u in (0.25 : ℝ)..(0.28125 : ℝ), fP u)
      + (∫ u in (0.28125 : ℝ)..(0.3125 : ℝ), fP u)
      + (∫ u in (0.3125 : ℝ)..(0.34375 : ℝ), fP u)
      + (∫ u in (0.34375 : ℝ)..(0.375 : ℝ), fP u)
      + (∫ u in (0.375 : ℝ)..(0.40625 : ℝ), fP u)
      + (∫ u in (0.40625 : ℝ)..(0.4375 : ℝ), fP u)
      + (∫ u in (0.4375 : ℝ)..(0.46875 : ℝ), fP u)
      + (∫ u in (0.46875 : ℝ)..(0.5 : ℝ), fP u) := by
      linarith [h01, h02, h03, h04, h05, h06, h07, h08,
                h09, h10, h11, h12, h13, h14, h15]
    rw [hsplit]
    have hnum : (0.018201128625 : ℝ)
      = (0.03125 : ℝ) * (0.0871153865 : ℝ)
      + (0.03125 : ℝ) * (0.0791219921 : ℝ)
      + (0.03125 : ℝ) * (0.0710062901 : ℝ)
      + (0.03125 : ℝ) * (0.0629426894 : ℝ)
      + (0.03125 : ℝ) * (0.0550826535 : ℝ)
      + (0.03125 : ℝ) * (0.0475536665 : ℝ)
      + (0.03125 : ℝ) * (0.0404589094 : ℝ)
      + (0.03125 : ℝ) * (0.0338776033 : ℝ)
      + (0.03125 : ℝ) * (0.0278659549 : ℝ)
      + (0.03125 : ℝ) * (0.0224586268 : ℝ)
      + (0.03125 : ℝ) * (0.0176706417 : ℝ)
      + (0.03125 : ℝ) * (0.0134996237 : ℝ)
      + (0.03125 : ℝ) * (0.009928274 : ℝ)
      + (0.03125 : ℝ) * (0.0069269804 : ℝ)
      + (0.03125 : ℝ) * (0.0044564622 : ℝ)
      + (0.03125 : ℝ) * (0.0024703615 : ℝ) := by norm_num
    rw [hnum]
    linarith [b00.2, b01.2, b02.2, b03.2, b04.2, b05.2, b06.2, b07.2,
              b08.2, b09.2, b10.2, b11.2, b12.2, b13.2, b14.2, b15.2]

/-! ## §3 — Headline MINUS enclosure on `[0, 1/2]` -/

theorem imLambda0_half_lb_ub :
    (-0.00005122886875 : ℝ)
      ≤ (∫ u in (0 : ℝ)..(1/2 : ℝ), nodeR_fourier_minus_at_c6_N3 u)
    ∧ (∫ u in (0 : ℝ)..(1/2 : ℝ), nodeR_fourier_minus_at_c6_N3 u)
      ≤ (0.001373452065625 : ℝ) := by
  have b00 := Seg01Range.s01p0_minus_integral_bound
  have b01 := Seg01Range.s01p1_minus_integral_bound
  have b02 := Seg01Range.s01p2_minus_integral_bound
  have b03 := Seg01Range.s01p3_minus_integral_bound
  have b04 := Seg01Range.s01p4_minus_integral_bound
  have b05 := Seg01Range.s01p5_minus_integral_bound
  have b06 := Seg01Range.s01p6_minus_integral_bound
  have b07 := Seg01Range.s01p7_minus_integral_bound
  have b08 := Seg02Range.s02p0_minus_integral_bound
  have b09 := Seg02Range.s02p1_minus_integral_bound
  have b10 := Seg02Range.s02p2_minus_integral_bound
  have b11 := Seg02Range.s02p3_minus_integral_bound
  have b12 := Seg02Range.s02p4_minus_integral_bound
  have b13 := Seg02Range.s02p5_minus_integral_bound
  have b14 := Seg02Range.s02p6_minus_integral_bound
  have b15 := Seg02Range.s02p7_minus_integral_bound
  have h01 : (∫ u in (0 : ℝ)..(0.03125 : ℝ), fM u)
             + (∫ u in (0.03125 : ℝ)..(0.0625 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(0.0625 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h02 : (∫ u in (0 : ℝ)..(0.0625 : ℝ), fM u)
             + (∫ u in (0.0625 : ℝ)..(0.09375 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(0.09375 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h03 : (∫ u in (0 : ℝ)..(0.09375 : ℝ), fM u)
             + (∫ u in (0.09375 : ℝ)..(0.125 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(0.125 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h04 : (∫ u in (0 : ℝ)..(0.125 : ℝ), fM u)
             + (∫ u in (0.125 : ℝ)..(0.15625 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(0.15625 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h05 : (∫ u in (0 : ℝ)..(0.15625 : ℝ), fM u)
             + (∫ u in (0.15625 : ℝ)..(0.1875 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(0.1875 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h06 : (∫ u in (0 : ℝ)..(0.1875 : ℝ), fM u)
             + (∫ u in (0.1875 : ℝ)..(0.21875 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(0.21875 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h07 : (∫ u in (0 : ℝ)..(0.21875 : ℝ), fM u)
             + (∫ u in (0.21875 : ℝ)..(0.25 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(0.25 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h08 : (∫ u in (0 : ℝ)..(0.25 : ℝ), fM u)
             + (∫ u in (0.25 : ℝ)..(0.28125 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(0.28125 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h09 : (∫ u in (0 : ℝ)..(0.28125 : ℝ), fM u)
             + (∫ u in (0.28125 : ℝ)..(0.3125 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(0.3125 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h10 : (∫ u in (0 : ℝ)..(0.3125 : ℝ), fM u)
             + (∫ u in (0.3125 : ℝ)..(0.34375 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(0.34375 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h11 : (∫ u in (0 : ℝ)..(0.34375 : ℝ), fM u)
             + (∫ u in (0.34375 : ℝ)..(0.375 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(0.375 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h12 : (∫ u in (0 : ℝ)..(0.375 : ℝ), fM u)
             + (∫ u in (0.375 : ℝ)..(0.40625 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(0.40625 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h13 : (∫ u in (0 : ℝ)..(0.40625 : ℝ), fM u)
             + (∫ u in (0.40625 : ℝ)..(0.4375 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(0.4375 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h14 : (∫ u in (0 : ℝ)..(0.4375 : ℝ), fM u)
             + (∫ u in (0.4375 : ℝ)..(0.46875 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(0.46875 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h15 : (∫ u in (0 : ℝ)..(0.46875 : ℝ), fM u)
             + (∫ u in (0.46875 : ℝ)..(0.5 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(0.5 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have hhalf : (1 / 2 : ℝ) = (0.5 : ℝ) := by norm_num
  refine ⟨?_, ?_⟩
  · rw [hhalf]
    have hsplit : ∫ u in (0 : ℝ)..(0.5 : ℝ), fM u
      = (∫ u in (0 : ℝ)..(0.03125 : ℝ), fM u)
      + (∫ u in (0.03125 : ℝ)..(0.0625 : ℝ), fM u)
      + (∫ u in (0.0625 : ℝ)..(0.09375 : ℝ), fM u)
      + (∫ u in (0.09375 : ℝ)..(0.125 : ℝ), fM u)
      + (∫ u in (0.125 : ℝ)..(0.15625 : ℝ), fM u)
      + (∫ u in (0.15625 : ℝ)..(0.1875 : ℝ), fM u)
      + (∫ u in (0.1875 : ℝ)..(0.21875 : ℝ), fM u)
      + (∫ u in (0.21875 : ℝ)..(0.25 : ℝ), fM u)
      + (∫ u in (0.25 : ℝ)..(0.28125 : ℝ), fM u)
      + (∫ u in (0.28125 : ℝ)..(0.3125 : ℝ), fM u)
      + (∫ u in (0.3125 : ℝ)..(0.34375 : ℝ), fM u)
      + (∫ u in (0.34375 : ℝ)..(0.375 : ℝ), fM u)
      + (∫ u in (0.375 : ℝ)..(0.40625 : ℝ), fM u)
      + (∫ u in (0.40625 : ℝ)..(0.4375 : ℝ), fM u)
      + (∫ u in (0.4375 : ℝ)..(0.46875 : ℝ), fM u)
      + (∫ u in (0.46875 : ℝ)..(0.5 : ℝ), fM u) := by
      linarith [h01, h02, h03, h04, h05, h06, h07, h08,
                h09, h10, h11, h12, h13, h14, h15]
    rw [hsplit]
    have hnum : (-0.00005122886875 : ℝ)
      = (0.03125 : ℝ) * (-0.0003840684 : ℝ)
      + (0.03125 : ℝ) * (-0.0006093962 : ℝ)
      + (0.03125 : ℝ) * (-0.0007070049 : ℝ)
      + (0.03125 : ℝ) * (-0.0007059938 : ℝ)
      + (0.03125 : ℝ) * (-0.0006329082 : ℝ)
      + (0.03125 : ℝ) * (-0.00051128 : ℝ)
      + (0.03125 : ℝ) * (-0.0003613394 : ℝ)
      + (0.03125 : ℝ) * (-0.0001998849 : ℝ)
      + (0.03125 : ℝ) * (-0.0000402991 : ℝ)
      + (0.03125 : ℝ) * (0.0000994642 : ℝ)
      + (0.03125 : ℝ) * (0.0002216113 : ℝ)
      + (0.03125 : ℝ) * (0.000324257 : ℝ)
      + (0.03125 : ℝ) * (0.0004043837 : ℝ)
      + (0.03125 : ℝ) * (0.0004609955 : ℝ)
      + (0.03125 : ℝ) * (0.0004947211 : ℝ)
      + (0.03125 : ℝ) * (0.0005074183 : ℝ) := by norm_num
    rw [hnum]
    linarith [b00.1, b01.1, b02.1, b03.1, b04.1, b05.1, b06.1, b07.1,
              b08.1, b09.1, b10.1, b11.1, b12.1, b13.1, b14.1, b15.1]
  · rw [hhalf]
    have hsplit : ∫ u in (0 : ℝ)..(0.5 : ℝ), fM u
      = (∫ u in (0 : ℝ)..(0.03125 : ℝ), fM u)
      + (∫ u in (0.03125 : ℝ)..(0.0625 : ℝ), fM u)
      + (∫ u in (0.0625 : ℝ)..(0.09375 : ℝ), fM u)
      + (∫ u in (0.09375 : ℝ)..(0.125 : ℝ), fM u)
      + (∫ u in (0.125 : ℝ)..(0.15625 : ℝ), fM u)
      + (∫ u in (0.15625 : ℝ)..(0.1875 : ℝ), fM u)
      + (∫ u in (0.1875 : ℝ)..(0.21875 : ℝ), fM u)
      + (∫ u in (0.21875 : ℝ)..(0.25 : ℝ), fM u)
      + (∫ u in (0.25 : ℝ)..(0.28125 : ℝ), fM u)
      + (∫ u in (0.28125 : ℝ)..(0.3125 : ℝ), fM u)
      + (∫ u in (0.3125 : ℝ)..(0.34375 : ℝ), fM u)
      + (∫ u in (0.34375 : ℝ)..(0.375 : ℝ), fM u)
      + (∫ u in (0.375 : ℝ)..(0.40625 : ℝ), fM u)
      + (∫ u in (0.40625 : ℝ)..(0.4375 : ℝ), fM u)
      + (∫ u in (0.4375 : ℝ)..(0.46875 : ℝ), fM u)
      + (∫ u in (0.46875 : ℝ)..(0.5 : ℝ), fM u) := by
      linarith [h01, h02, h03, h04, h05, h06, h07, h08,
                h09, h10, h11, h12, h13, h14, h15]
    rw [hsplit]
    have hnum : (0.001373452065625 : ℝ)
      = (0.03125 : ℝ) * (0.0004477789 : ℝ)
      + (0.03125 : ℝ) * (0.000944431 : ℝ)
      + (0.03125 : ℝ) * (0.0014566768 : ℝ)
      + (0.03125 : ℝ) * (0.0019556149 : ℝ)
      + (0.03125 : ℝ) * (0.002417203 : ℝ)
      + (0.03125 : ℝ) * (0.0028225079 : ℝ)
      + (0.03125 : ℝ) * (0.0031577387 : ℝ)
      + (0.03125 : ℝ) * (0.0034140822 : ℝ)
      + (0.03125 : ℝ) * (0.0035873669 : ℝ)
      + (0.03125 : ℝ) * (0.0036775853 : ℝ)
      + (0.03125 : ℝ) * (0.0036883111 : ℝ)
      + (0.03125 : ℝ) * (0.0036260439 : ℝ)
      + (0.03125 : ℝ) * (0.0034995184 : ℝ)
      + (0.03125 : ℝ) * (0.0033190108 : ℝ)
      + (0.03125 : ℝ) * (0.0030956735 : ℝ)
      + (0.03125 : ℝ) * (0.0028409228 : ℝ) := by norm_num
    rw [hnum]
    linarith [b00.2, b01.2, b02.2, b03.2, b04.2, b05.2, b06.2, b07.2,
              b08.2, b09.2, b10.2, b11.2, b12.2, b13.2, b14.2, b15.2]

/-! ## §Axiom check -/

#print axioms reLambda0_half_lb_ub
#print axioms imLambda0_half_lb_ub

end Assemble_half
end FourierPanels_c6
end PrincipiaTractalis
