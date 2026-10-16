/-
# PF.Analytic.FourierPanels.Assemble_c51_8_threehalves_2026_10_16

**M2.5 assembly** at `c = 51/8` — combines the 48 per-panel integral bounds
from `Seg01Range`..`Seg06Range` (u ∈ [0, 3/2], 6 segments × 8 panels of
width 1/32) into two headline [0, 3/2]-integral enclosures.

  reLambda0_threehalves_lb_ub :
    R_lb ≤ ∫ u in 0..(3/2), nodeR_fourier_plus_at_c51_8_N3  u ≤ R_ub

  imLambda0_threehalves_lb_ub :
    I_lb ≤ ∫ u in 0..(3/2), nodeR_fourier_minus_at_c51_8_N3 u ≤ I_ub

Three-axiom bar: every top-level declaration prints
`[propext, Classical.choice, Quot.sound]`.  No sorry, no native_decide,
no `interval` tactic, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-16.
-/
import PF.Analytic.FourierPanels.Seg01Range_c51_8_2026_10_16
import PF.Analytic.FourierPanels.Seg02Range_c51_8_2026_10_16
import PF.Analytic.FourierPanels.Seg03Range_c51_8_2026_10_16
import PF.Analytic.FourierPanels.Seg04Range_c51_8_2026_10_16
import PF.Analytic.FourierPanels.Seg05Range_c51_8_2026_10_16
import PF.Analytic.FourierPanels.Seg06Range_c51_8_2026_10_16

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace PrincipiaTractalis
namespace FourierPanels_c51_8
namespace Assemble_threehalves

open MeasureTheory
open PrincipiaTractalis.FourierPanels_c51_8

/-! ## §1 — Local notation -/

private noncomputable abbrev fP : ℝ → ℝ := nodeR_fourier_plus_at_c51_8_N3
private noncomputable abbrev fM : ℝ → ℝ := nodeR_fourier_minus_at_c51_8_N3

private theorem iiP (a b : ℝ) : IntervalIntegrable fP MeasureTheory.volume a b :=
  Seg01Range.nodeR_fourier_plus_at_c51_8_N3_intervalIntegrable a b

private theorem iiM (a b : ℝ) : IntervalIntegrable fM MeasureTheory.volume a b :=
  Seg01Range.nodeR_fourier_minus_at_c51_8_N3_intervalIntegrable a b

/-! ## §2 — Headline PLUS enclosure on `[0, 3/2]` -/

theorem reLambda0_threehalves_lb_ub :
    (4352202307 / 320000000000 : ℝ)
      ≤ (∫ u in (0 : ℝ)..(3/2 : ℝ), nodeR_fourier_plus_at_c51_8_N3 u)
    ∧ (∫ u in (0 : ℝ)..(3/2 : ℝ), nodeR_fourier_plus_at_c51_8_N3 u)
      ≤ (542831867 / 32000000000 : ℝ) := by
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
  have b16 := Seg03Range.s03p0_plus_integral_bound
  have b17 := Seg03Range.s03p1_plus_integral_bound
  have b18 := Seg03Range.s03p2_plus_integral_bound
  have b19 := Seg03Range.s03p3_plus_integral_bound
  have b20 := Seg03Range.s03p4_plus_integral_bound
  have b21 := Seg03Range.s03p5_plus_integral_bound
  have b22 := Seg03Range.s03p6_plus_integral_bound
  have b23 := Seg03Range.s03p7_plus_integral_bound
  have b24 := Seg04Range.s04p0_plus_integral_bound
  have b25 := Seg04Range.s04p1_plus_integral_bound
  have b26 := Seg04Range.s04p2_plus_integral_bound
  have b27 := Seg04Range.s04p3_plus_integral_bound
  have b28 := Seg04Range.s04p4_plus_integral_bound
  have b29 := Seg04Range.s04p5_plus_integral_bound
  have b30 := Seg04Range.s04p6_plus_integral_bound
  have b31 := Seg04Range.s04p7_plus_integral_bound
  have b32 := Seg05Range.s05p0_plus_integral_bound
  have b33 := Seg05Range.s05p1_plus_integral_bound
  have b34 := Seg05Range.s05p2_plus_integral_bound
  have b35 := Seg05Range.s05p3_plus_integral_bound
  have b36 := Seg05Range.s05p4_plus_integral_bound
  have b37 := Seg05Range.s05p5_plus_integral_bound
  have b38 := Seg05Range.s05p6_plus_integral_bound
  have b39 := Seg05Range.s05p7_plus_integral_bound
  have b40 := Seg06Range.s06p0_plus_integral_bound
  have b41 := Seg06Range.s06p1_plus_integral_bound
  have b42 := Seg06Range.s06p2_plus_integral_bound
  have b43 := Seg06Range.s06p3_plus_integral_bound
  have b44 := Seg06Range.s06p4_plus_integral_bound
  have b45 := Seg06Range.s06p5_plus_integral_bound
  have b46 := Seg06Range.s06p6_plus_integral_bound
  have b47 := Seg06Range.s06p7_plus_integral_bound
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
  have h16 : (∫ u in (0 : ℝ)..(0.5 : ℝ), fP u)
             + (∫ u in (0.5 : ℝ)..(0.53125 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(0.53125 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h17 : (∫ u in (0 : ℝ)..(0.53125 : ℝ), fP u)
             + (∫ u in (0.53125 : ℝ)..(0.5625 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(0.5625 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h18 : (∫ u in (0 : ℝ)..(0.5625 : ℝ), fP u)
             + (∫ u in (0.5625 : ℝ)..(0.59375 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(0.59375 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h19 : (∫ u in (0 : ℝ)..(0.59375 : ℝ), fP u)
             + (∫ u in (0.59375 : ℝ)..(0.625 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(0.625 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h20 : (∫ u in (0 : ℝ)..(0.625 : ℝ), fP u)
             + (∫ u in (0.625 : ℝ)..(0.65625 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(0.65625 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h21 : (∫ u in (0 : ℝ)..(0.65625 : ℝ), fP u)
             + (∫ u in (0.65625 : ℝ)..(0.6875 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(0.6875 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h22 : (∫ u in (0 : ℝ)..(0.6875 : ℝ), fP u)
             + (∫ u in (0.6875 : ℝ)..(0.71875 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(0.71875 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h23 : (∫ u in (0 : ℝ)..(0.71875 : ℝ), fP u)
             + (∫ u in (0.71875 : ℝ)..(0.75 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(0.75 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h24 : (∫ u in (0 : ℝ)..(0.75 : ℝ), fP u)
             + (∫ u in (0.75 : ℝ)..(0.78125 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(0.78125 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h25 : (∫ u in (0 : ℝ)..(0.78125 : ℝ), fP u)
             + (∫ u in (0.78125 : ℝ)..(0.8125 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(0.8125 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h26 : (∫ u in (0 : ℝ)..(0.8125 : ℝ), fP u)
             + (∫ u in (0.8125 : ℝ)..(0.84375 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(0.84375 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h27 : (∫ u in (0 : ℝ)..(0.84375 : ℝ), fP u)
             + (∫ u in (0.84375 : ℝ)..(0.875 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(0.875 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h28 : (∫ u in (0 : ℝ)..(0.875 : ℝ), fP u)
             + (∫ u in (0.875 : ℝ)..(0.90625 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(0.90625 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h29 : (∫ u in (0 : ℝ)..(0.90625 : ℝ), fP u)
             + (∫ u in (0.90625 : ℝ)..(0.9375 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(0.9375 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h30 : (∫ u in (0 : ℝ)..(0.9375 : ℝ), fP u)
             + (∫ u in (0.9375 : ℝ)..(0.96875 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(0.96875 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h31 : (∫ u in (0 : ℝ)..(0.96875 : ℝ), fP u)
             + (∫ u in (0.96875 : ℝ)..(1 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(1 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h32 : (∫ u in (0 : ℝ)..(1 : ℝ), fP u)
             + (∫ u in (1 : ℝ)..(1.03125 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(1.03125 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h33 : (∫ u in (0 : ℝ)..(1.03125 : ℝ), fP u)
             + (∫ u in (1.03125 : ℝ)..(1.0625 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(1.0625 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h34 : (∫ u in (0 : ℝ)..(1.0625 : ℝ), fP u)
             + (∫ u in (1.0625 : ℝ)..(1.09375 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(1.09375 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h35 : (∫ u in (0 : ℝ)..(1.09375 : ℝ), fP u)
             + (∫ u in (1.09375 : ℝ)..(1.125 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(1.125 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h36 : (∫ u in (0 : ℝ)..(1.125 : ℝ), fP u)
             + (∫ u in (1.125 : ℝ)..(1.15625 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(1.15625 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h37 : (∫ u in (0 : ℝ)..(1.15625 : ℝ), fP u)
             + (∫ u in (1.15625 : ℝ)..(1.1875 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(1.1875 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h38 : (∫ u in (0 : ℝ)..(1.1875 : ℝ), fP u)
             + (∫ u in (1.1875 : ℝ)..(1.21875 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(1.21875 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h39 : (∫ u in (0 : ℝ)..(1.21875 : ℝ), fP u)
             + (∫ u in (1.21875 : ℝ)..(1.25 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(1.25 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h40 : (∫ u in (0 : ℝ)..(1.25 : ℝ), fP u)
             + (∫ u in (1.25 : ℝ)..(1.28125 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(1.28125 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h41 : (∫ u in (0 : ℝ)..(1.28125 : ℝ), fP u)
             + (∫ u in (1.28125 : ℝ)..(1.3125 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(1.3125 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h42 : (∫ u in (0 : ℝ)..(1.3125 : ℝ), fP u)
             + (∫ u in (1.3125 : ℝ)..(1.34375 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(1.34375 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h43 : (∫ u in (0 : ℝ)..(1.34375 : ℝ), fP u)
             + (∫ u in (1.34375 : ℝ)..(1.375 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(1.375 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h44 : (∫ u in (0 : ℝ)..(1.375 : ℝ), fP u)
             + (∫ u in (1.375 : ℝ)..(1.40625 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(1.40625 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h45 : (∫ u in (0 : ℝ)..(1.40625 : ℝ), fP u)
             + (∫ u in (1.40625 : ℝ)..(1.4375 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(1.4375 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h46 : (∫ u in (0 : ℝ)..(1.4375 : ℝ), fP u)
             + (∫ u in (1.4375 : ℝ)..(1.46875 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(1.46875 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have h47 : (∫ u in (0 : ℝ)..(1.46875 : ℝ), fP u)
             + (∫ u in (1.46875 : ℝ)..(1.5 : ℝ), fP u)
           = ∫ u in (0 : ℝ)..(1.5 : ℝ), fP u :=
    intervalIntegral.integral_add_adjacent_intervals (iiP _ _) (iiP _ _)
  have hthreehalves : (3 / 2 : ℝ) = (1.5 : ℝ) := by norm_num
  refine ⟨?_, ?_⟩
  · rw [hthreehalves]
    have hsplit : ∫ u in (0 : ℝ)..(1.5 : ℝ), fP u
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
        + (∫ u in (0.46875 : ℝ)..(0.5 : ℝ), fP u)
        + (∫ u in (0.5 : ℝ)..(0.53125 : ℝ), fP u)
        + (∫ u in (0.53125 : ℝ)..(0.5625 : ℝ), fP u)
        + (∫ u in (0.5625 : ℝ)..(0.59375 : ℝ), fP u)
        + (∫ u in (0.59375 : ℝ)..(0.625 : ℝ), fP u)
        + (∫ u in (0.625 : ℝ)..(0.65625 : ℝ), fP u)
        + (∫ u in (0.65625 : ℝ)..(0.6875 : ℝ), fP u)
        + (∫ u in (0.6875 : ℝ)..(0.71875 : ℝ), fP u)
        + (∫ u in (0.71875 : ℝ)..(0.75 : ℝ), fP u)
        + (∫ u in (0.75 : ℝ)..(0.78125 : ℝ), fP u)
        + (∫ u in (0.78125 : ℝ)..(0.8125 : ℝ), fP u)
        + (∫ u in (0.8125 : ℝ)..(0.84375 : ℝ), fP u)
        + (∫ u in (0.84375 : ℝ)..(0.875 : ℝ), fP u)
        + (∫ u in (0.875 : ℝ)..(0.90625 : ℝ), fP u)
        + (∫ u in (0.90625 : ℝ)..(0.9375 : ℝ), fP u)
        + (∫ u in (0.9375 : ℝ)..(0.96875 : ℝ), fP u)
        + (∫ u in (0.96875 : ℝ)..(1 : ℝ), fP u)
        + (∫ u in (1 : ℝ)..(1.03125 : ℝ), fP u)
        + (∫ u in (1.03125 : ℝ)..(1.0625 : ℝ), fP u)
        + (∫ u in (1.0625 : ℝ)..(1.09375 : ℝ), fP u)
        + (∫ u in (1.09375 : ℝ)..(1.125 : ℝ), fP u)
        + (∫ u in (1.125 : ℝ)..(1.15625 : ℝ), fP u)
        + (∫ u in (1.15625 : ℝ)..(1.1875 : ℝ), fP u)
        + (∫ u in (1.1875 : ℝ)..(1.21875 : ℝ), fP u)
        + (∫ u in (1.21875 : ℝ)..(1.25 : ℝ), fP u)
        + (∫ u in (1.25 : ℝ)..(1.28125 : ℝ), fP u)
        + (∫ u in (1.28125 : ℝ)..(1.3125 : ℝ), fP u)
        + (∫ u in (1.3125 : ℝ)..(1.34375 : ℝ), fP u)
        + (∫ u in (1.34375 : ℝ)..(1.375 : ℝ), fP u)
        + (∫ u in (1.375 : ℝ)..(1.40625 : ℝ), fP u)
        + (∫ u in (1.40625 : ℝ)..(1.4375 : ℝ), fP u)
        + (∫ u in (1.4375 : ℝ)..(1.46875 : ℝ), fP u)
        + (∫ u in (1.46875 : ℝ)..(1.5 : ℝ), fP u)
    := by
      linarith [h01, h02, h03, h04, h05, h06, h07, h08, h09, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47]
    rw [hsplit]
    have hnum : (4352202307 / 320000000000 : ℝ)
      = (0.03125 : ℝ) * (0.0778415648 : ℝ)
        + (0.03125 : ℝ) * (0.0697281926 : ℝ)
        + (0.03125 : ℝ) * (0.0616200341 : ℝ)
        + (0.03125 : ℝ) * (0.0536873228 : ℝ)
        + (0.03125 : ℝ) * (0.0460737517 : ℝ)
        + (0.03125 : ℝ) * (0.0388959221 : ℝ)
        + (0.03125 : ℝ) * (0.0322435978 : ℝ)
        + (0.03125 : ℝ) * (0.0261806906 : ℝ)
        + (0.03125 : ℝ) * (0.02074688 : ℝ)
        + (0.03125 : ℝ) * (0.0159597587 : ℝ)
        + (0.03125 : ℝ) * (0.0118173841 : ℝ)
        + (0.03125 : ℝ) * (0.0083011119 : ℝ)
        + (0.03125 : ℝ) * (0.0053785882 : ℝ)
        + (0.03125 : ℝ) * (0.0030067814 : ℝ)
        + (0.03125 : ℝ) * (0.0011349466 : ℝ)
        + (0.03125 : ℝ) * (-0.0003461371 : ℝ)
        + (0.03125 : ℝ) * (-0.0015860772 : ℝ)
        + (0.03125 : ℝ) * (-0.0024468755 : ℝ)
        + (0.03125 : ℝ) * (-0.0029905313 : ℝ)
        + (0.03125 : ℝ) * (-0.0032761038 : ℝ)
        + (0.03125 : ℝ) * (-0.0033582989 : ℝ)
        + (0.03125 : ℝ) * (-0.0032864479 : ℝ)
        + (0.03125 : ℝ) * (-0.0031038598 : ℝ)
        + (0.03125 : ℝ) * (-0.0028475153 : ℝ)
        + (0.03125 : ℝ) * (-0.002548059 : ℝ)
        + (0.03125 : ℝ) * (-0.0022300415 : ℝ)
        + (0.03125 : ℝ) * (-0.0019123556 : ℝ)
        + (0.03125 : ℝ) * (-0.0016088152 : ℝ)
        + (0.03125 : ℝ) * (-0.0013288227 : ℝ)
        + (0.03125 : ℝ) * (-0.0010780788 : ℝ)
        + (0.03125 : ℝ) * (-0.000859293 : ℝ)
        + (0.03125 : ℝ) * (-0.0006735711 : ℝ)
        + (0.03125 : ℝ) * (-0.0005224629 : ℝ)
        + (0.03125 : ℝ) * (-0.0003985028 : ℝ)
        + (0.03125 : ℝ) * (-0.0002983222 : ℝ)
        + (0.03125 : ℝ) * (-0.0002190387 : ℝ)
        + (0.03125 : ℝ) * (-0.0001575893 : ℝ)
        + (0.03125 : ℝ) * (-0.0001109563 : ℝ)
        + (0.03125 : ℝ) * (-0.000076324 : ℝ)
        + (0.03125 : ℝ) * (-0.0000511755 : ℝ)
        + (0.03125 : ℝ) * (-0.0000333414 : ℝ)
        + (0.03125 : ℝ) * (-0.0000210121 : ℝ)
        + (0.03125 : ℝ) * (-0.0000127225 : ℝ)
        + (0.03125 : ℝ) * (-0.0000073204 : ℝ)
        + (0.03125 : ℝ) * (-0.0000039254 : ℝ)
        + (0.03125 : ℝ) * (-0.0000018833 : ℝ)
        + (0.03125 : ℝ) * (-0.0000007226 : ℝ)
        + (0.03125 : ℝ) * (-0.0000001136 : ℝ)
    := by norm_num
    rw [hnum]
    linarith [b00.1, b01.1, b02.1, b03.1, b04.1, b05.1, b06.1, b07.1, b08.1, b09.1, b10.1, b11.1, b12.1, b13.1, b14.1, b15.1, b16.1, b17.1, b18.1, b19.1, b20.1, b21.1, b22.1, b23.1, b24.1, b25.1, b26.1, b27.1, b28.1, b29.1, b30.1, b31.1, b32.1, b33.1, b34.1, b35.1, b36.1, b37.1, b38.1, b39.1, b40.1, b41.1, b42.1, b43.1, b44.1, b45.1, b46.1, b47.1]
  · rw [hthreehalves]
    have hsplit : ∫ u in (0 : ℝ)..(1.5 : ℝ), fP u
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
        + (∫ u in (0.46875 : ℝ)..(0.5 : ℝ), fP u)
        + (∫ u in (0.5 : ℝ)..(0.53125 : ℝ), fP u)
        + (∫ u in (0.53125 : ℝ)..(0.5625 : ℝ), fP u)
        + (∫ u in (0.5625 : ℝ)..(0.59375 : ℝ), fP u)
        + (∫ u in (0.59375 : ℝ)..(0.625 : ℝ), fP u)
        + (∫ u in (0.625 : ℝ)..(0.65625 : ℝ), fP u)
        + (∫ u in (0.65625 : ℝ)..(0.6875 : ℝ), fP u)
        + (∫ u in (0.6875 : ℝ)..(0.71875 : ℝ), fP u)
        + (∫ u in (0.71875 : ℝ)..(0.75 : ℝ), fP u)
        + (∫ u in (0.75 : ℝ)..(0.78125 : ℝ), fP u)
        + (∫ u in (0.78125 : ℝ)..(0.8125 : ℝ), fP u)
        + (∫ u in (0.8125 : ℝ)..(0.84375 : ℝ), fP u)
        + (∫ u in (0.84375 : ℝ)..(0.875 : ℝ), fP u)
        + (∫ u in (0.875 : ℝ)..(0.90625 : ℝ), fP u)
        + (∫ u in (0.90625 : ℝ)..(0.9375 : ℝ), fP u)
        + (∫ u in (0.9375 : ℝ)..(0.96875 : ℝ), fP u)
        + (∫ u in (0.96875 : ℝ)..(1 : ℝ), fP u)
        + (∫ u in (1 : ℝ)..(1.03125 : ℝ), fP u)
        + (∫ u in (1.03125 : ℝ)..(1.0625 : ℝ), fP u)
        + (∫ u in (1.0625 : ℝ)..(1.09375 : ℝ), fP u)
        + (∫ u in (1.09375 : ℝ)..(1.125 : ℝ), fP u)
        + (∫ u in (1.125 : ℝ)..(1.15625 : ℝ), fP u)
        + (∫ u in (1.15625 : ℝ)..(1.1875 : ℝ), fP u)
        + (∫ u in (1.1875 : ℝ)..(1.21875 : ℝ), fP u)
        + (∫ u in (1.21875 : ℝ)..(1.25 : ℝ), fP u)
        + (∫ u in (1.25 : ℝ)..(1.28125 : ℝ), fP u)
        + (∫ u in (1.28125 : ℝ)..(1.3125 : ℝ), fP u)
        + (∫ u in (1.3125 : ℝ)..(1.34375 : ℝ), fP u)
        + (∫ u in (1.34375 : ℝ)..(1.375 : ℝ), fP u)
        + (∫ u in (1.375 : ℝ)..(1.40625 : ℝ), fP u)
        + (∫ u in (1.40625 : ℝ)..(1.4375 : ℝ), fP u)
        + (∫ u in (1.4375 : ℝ)..(1.46875 : ℝ), fP u)
        + (∫ u in (1.46875 : ℝ)..(1.5 : ℝ), fP u)
    := by
      linarith [h01, h02, h03, h04, h05, h06, h07, h08, h09, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47]
    rw [hsplit]
    have hnum : (542831867 / 32000000000 : ℝ)
      = (0.03125 : ℝ) * (0.0871153865 : ℝ)
        + (0.03125 : ℝ) * (0.0790770433 : ℝ)
        + (0.03125 : ℝ) * (0.0708435441 : ℝ)
        + (0.03125 : ℝ) * (0.0626133296 : ℝ)
        + (0.03125 : ℝ) * (0.0545594 : ℝ)
        + (0.03125 : ℝ) * (0.0468278657 : ℝ)
        + (0.03125 : ℝ) * (0.0395373697 : ℝ)
        + (0.03125 : ℝ) * (0.0327793302 : ℝ)
        + (0.03125 : ℝ) * (0.0266189249 : ℝ)
        + (0.03125 : ℝ) * (0.0210967224 : ℝ)
        + (0.03125 : ℝ) * (0.016230849 : ℝ)
        + (0.03125 : ℝ) * (0.01201957 : ℝ)
        + (0.03125 : ℝ) * (0.0084441597 : ℝ)
        + (0.03125 : ℝ) * (0.0054719357 : ℝ)
        + (0.03125 : ℝ) * (0.0030593347 : ℝ)
        + (0.03125 : ℝ) * (0.0011549228 : ℝ)
        + (0.03125 : ℝ) * (-0.0002503989 : ℝ)
        + (0.03125 : ℝ) * (-0.0011356524 : ℝ)
        + (0.03125 : ℝ) * (-0.0017335155 : ℝ)
        + (0.03125 : ℝ) * (-0.002095621 : ℝ)
        + (0.03125 : ℝ) * (-0.0022699681 : ℝ)
        + (0.03125 : ℝ) * (-0.0022999772 : ℝ)
        + (0.03125 : ℝ) * (-0.0022238856 : ℝ)
        + (0.03125 : ℝ) * (-0.0020744533 : ℝ)
        + (0.03125 : ℝ) * (-0.0018789385 : ℝ)
        + (0.03125 : ℝ) * (-0.0016592988 : ℝ)
        + (0.03125 : ℝ) * (-0.0014325663 : ℝ)
        + (0.03125 : ℝ) * (-0.0012113494 : ℝ)
        + (0.03125 : ℝ) * (-0.0010044127 : ℝ)
        + (0.03125 : ℝ) * (-0.0008172945 : ℝ)
        + (0.03125 : ℝ) * (-0.0006529221 : ℝ)
        + (0.03125 : ℝ) * (-0.000512199 : ℝ)
        + (0.03125 : ℝ) * (-0.0003907811 : ℝ)
        + (0.03125 : ℝ) * (-0.0002925082 : ℝ)
        + (0.03125 : ℝ) * (-0.0002147454 : ℝ)
        + (0.03125 : ℝ) * (-0.0001544829 : ℝ)
        + (0.03125 : ℝ) * (-0.0001087568 : ℝ)
        + (0.03125 : ℝ) * (-0.0000748025 : ℝ)
        + (0.03125 : ℝ) * (-0.0000501496 : ℝ)
        + (0.03125 : ℝ) * (-0.0000326693 : ℝ)
        + (0.03125 : ℝ) * (-0.0000205862 : ℝ)
        + (0.03125 : ℝ) * (-0.0000124631 : ℝ)
        + (0.03125 : ℝ) * (-0.0000071703 : ℝ)
        + (0.03125 : ℝ) * (-0.0000038443 : ℝ)
        + (0.03125 : ℝ) * (-0.0000018441 : ℝ)
        + (0.03125 : ℝ) * (-0.0000007073 : ℝ)
        + (0.03125 : ℝ) * (-0.000000111 : ℝ)
        + (0.03125 : ℝ) * (0.0000002541 : ℝ)
    := by norm_num
    rw [hnum]
    linarith [b00.2, b01.2, b02.2, b03.2, b04.2, b05.2, b06.2, b07.2, b08.2, b09.2, b10.2, b11.2, b12.2, b13.2, b14.2, b15.2, b16.2, b17.2, b18.2, b19.2, b20.2, b21.2, b22.2, b23.2, b24.2, b25.2, b26.2, b27.2, b28.2, b29.2, b30.2, b31.2, b32.2, b33.2, b34.2, b35.2, b36.2, b37.2, b38.2, b39.2, b40.2, b41.2, b42.2, b43.2, b44.2, b45.2, b46.2, b47.2]

/-! ## §3 — Headline MINUS enclosure on `[0, 3/2]` -/

theorem imLambda0_threehalves_lb_ub :
    (2689993 / 80000000000 : ℝ)
      ≤ (∫ u in (0 : ℝ)..(3/2 : ℝ), nodeR_fourier_minus_at_c51_8_N3 u)
    ∧ (∫ u in (0 : ℝ)..(3/2 : ℝ), nodeR_fourier_minus_at_c51_8_N3 u)
      ≤ (60314889 / 32000000000 : ℝ) := by
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
  have b16 := Seg03Range.s03p0_minus_integral_bound
  have b17 := Seg03Range.s03p1_minus_integral_bound
  have b18 := Seg03Range.s03p2_minus_integral_bound
  have b19 := Seg03Range.s03p3_minus_integral_bound
  have b20 := Seg03Range.s03p4_minus_integral_bound
  have b21 := Seg03Range.s03p5_minus_integral_bound
  have b22 := Seg03Range.s03p6_minus_integral_bound
  have b23 := Seg03Range.s03p7_minus_integral_bound
  have b24 := Seg04Range.s04p0_minus_integral_bound
  have b25 := Seg04Range.s04p1_minus_integral_bound
  have b26 := Seg04Range.s04p2_minus_integral_bound
  have b27 := Seg04Range.s04p3_minus_integral_bound
  have b28 := Seg04Range.s04p4_minus_integral_bound
  have b29 := Seg04Range.s04p5_minus_integral_bound
  have b30 := Seg04Range.s04p6_minus_integral_bound
  have b31 := Seg04Range.s04p7_minus_integral_bound
  have b32 := Seg05Range.s05p0_minus_integral_bound
  have b33 := Seg05Range.s05p1_minus_integral_bound
  have b34 := Seg05Range.s05p2_minus_integral_bound
  have b35 := Seg05Range.s05p3_minus_integral_bound
  have b36 := Seg05Range.s05p4_minus_integral_bound
  have b37 := Seg05Range.s05p5_minus_integral_bound
  have b38 := Seg05Range.s05p6_minus_integral_bound
  have b39 := Seg05Range.s05p7_minus_integral_bound
  have b40 := Seg06Range.s06p0_minus_integral_bound
  have b41 := Seg06Range.s06p1_minus_integral_bound
  have b42 := Seg06Range.s06p2_minus_integral_bound
  have b43 := Seg06Range.s06p3_minus_integral_bound
  have b44 := Seg06Range.s06p4_minus_integral_bound
  have b45 := Seg06Range.s06p5_minus_integral_bound
  have b46 := Seg06Range.s06p6_minus_integral_bound
  have b47 := Seg06Range.s06p7_minus_integral_bound
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
  have h16 : (∫ u in (0 : ℝ)..(0.5 : ℝ), fM u)
             + (∫ u in (0.5 : ℝ)..(0.53125 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(0.53125 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h17 : (∫ u in (0 : ℝ)..(0.53125 : ℝ), fM u)
             + (∫ u in (0.53125 : ℝ)..(0.5625 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(0.5625 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h18 : (∫ u in (0 : ℝ)..(0.5625 : ℝ), fM u)
             + (∫ u in (0.5625 : ℝ)..(0.59375 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(0.59375 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h19 : (∫ u in (0 : ℝ)..(0.59375 : ℝ), fM u)
             + (∫ u in (0.59375 : ℝ)..(0.625 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(0.625 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h20 : (∫ u in (0 : ℝ)..(0.625 : ℝ), fM u)
             + (∫ u in (0.625 : ℝ)..(0.65625 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(0.65625 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h21 : (∫ u in (0 : ℝ)..(0.65625 : ℝ), fM u)
             + (∫ u in (0.65625 : ℝ)..(0.6875 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(0.6875 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h22 : (∫ u in (0 : ℝ)..(0.6875 : ℝ), fM u)
             + (∫ u in (0.6875 : ℝ)..(0.71875 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(0.71875 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h23 : (∫ u in (0 : ℝ)..(0.71875 : ℝ), fM u)
             + (∫ u in (0.71875 : ℝ)..(0.75 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(0.75 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h24 : (∫ u in (0 : ℝ)..(0.75 : ℝ), fM u)
             + (∫ u in (0.75 : ℝ)..(0.78125 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(0.78125 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h25 : (∫ u in (0 : ℝ)..(0.78125 : ℝ), fM u)
             + (∫ u in (0.78125 : ℝ)..(0.8125 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(0.8125 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h26 : (∫ u in (0 : ℝ)..(0.8125 : ℝ), fM u)
             + (∫ u in (0.8125 : ℝ)..(0.84375 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(0.84375 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h27 : (∫ u in (0 : ℝ)..(0.84375 : ℝ), fM u)
             + (∫ u in (0.84375 : ℝ)..(0.875 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(0.875 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h28 : (∫ u in (0 : ℝ)..(0.875 : ℝ), fM u)
             + (∫ u in (0.875 : ℝ)..(0.90625 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(0.90625 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h29 : (∫ u in (0 : ℝ)..(0.90625 : ℝ), fM u)
             + (∫ u in (0.90625 : ℝ)..(0.9375 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(0.9375 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h30 : (∫ u in (0 : ℝ)..(0.9375 : ℝ), fM u)
             + (∫ u in (0.9375 : ℝ)..(0.96875 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(0.96875 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h31 : (∫ u in (0 : ℝ)..(0.96875 : ℝ), fM u)
             + (∫ u in (0.96875 : ℝ)..(1 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(1 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h32 : (∫ u in (0 : ℝ)..(1 : ℝ), fM u)
             + (∫ u in (1 : ℝ)..(1.03125 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(1.03125 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h33 : (∫ u in (0 : ℝ)..(1.03125 : ℝ), fM u)
             + (∫ u in (1.03125 : ℝ)..(1.0625 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(1.0625 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h34 : (∫ u in (0 : ℝ)..(1.0625 : ℝ), fM u)
             + (∫ u in (1.0625 : ℝ)..(1.09375 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(1.09375 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h35 : (∫ u in (0 : ℝ)..(1.09375 : ℝ), fM u)
             + (∫ u in (1.09375 : ℝ)..(1.125 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(1.125 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h36 : (∫ u in (0 : ℝ)..(1.125 : ℝ), fM u)
             + (∫ u in (1.125 : ℝ)..(1.15625 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(1.15625 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h37 : (∫ u in (0 : ℝ)..(1.15625 : ℝ), fM u)
             + (∫ u in (1.15625 : ℝ)..(1.1875 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(1.1875 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h38 : (∫ u in (0 : ℝ)..(1.1875 : ℝ), fM u)
             + (∫ u in (1.1875 : ℝ)..(1.21875 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(1.21875 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h39 : (∫ u in (0 : ℝ)..(1.21875 : ℝ), fM u)
             + (∫ u in (1.21875 : ℝ)..(1.25 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(1.25 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h40 : (∫ u in (0 : ℝ)..(1.25 : ℝ), fM u)
             + (∫ u in (1.25 : ℝ)..(1.28125 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(1.28125 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h41 : (∫ u in (0 : ℝ)..(1.28125 : ℝ), fM u)
             + (∫ u in (1.28125 : ℝ)..(1.3125 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(1.3125 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h42 : (∫ u in (0 : ℝ)..(1.3125 : ℝ), fM u)
             + (∫ u in (1.3125 : ℝ)..(1.34375 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(1.34375 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h43 : (∫ u in (0 : ℝ)..(1.34375 : ℝ), fM u)
             + (∫ u in (1.34375 : ℝ)..(1.375 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(1.375 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h44 : (∫ u in (0 : ℝ)..(1.375 : ℝ), fM u)
             + (∫ u in (1.375 : ℝ)..(1.40625 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(1.40625 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h45 : (∫ u in (0 : ℝ)..(1.40625 : ℝ), fM u)
             + (∫ u in (1.40625 : ℝ)..(1.4375 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(1.4375 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h46 : (∫ u in (0 : ℝ)..(1.4375 : ℝ), fM u)
             + (∫ u in (1.4375 : ℝ)..(1.46875 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(1.46875 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have h47 : (∫ u in (0 : ℝ)..(1.46875 : ℝ), fM u)
             + (∫ u in (1.46875 : ℝ)..(1.5 : ℝ), fM u)
           = ∫ u in (0 : ℝ)..(1.5 : ℝ), fM u :=
    intervalIntegral.integral_add_adjacent_intervals (iiM _ _) (iiM _ _)
  have hthreehalves : (3 / 2 : ℝ) = (1.5 : ℝ) := by norm_num
  refine ⟨?_, ?_⟩
  · rw [hthreehalves]
    have hsplit : ∫ u in (0 : ℝ)..(1.5 : ℝ), fM u
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
        + (∫ u in (0.46875 : ℝ)..(0.5 : ℝ), fM u)
        + (∫ u in (0.5 : ℝ)..(0.53125 : ℝ), fM u)
        + (∫ u in (0.53125 : ℝ)..(0.5625 : ℝ), fM u)
        + (∫ u in (0.5625 : ℝ)..(0.59375 : ℝ), fM u)
        + (∫ u in (0.59375 : ℝ)..(0.625 : ℝ), fM u)
        + (∫ u in (0.625 : ℝ)..(0.65625 : ℝ), fM u)
        + (∫ u in (0.65625 : ℝ)..(0.6875 : ℝ), fM u)
        + (∫ u in (0.6875 : ℝ)..(0.71875 : ℝ), fM u)
        + (∫ u in (0.71875 : ℝ)..(0.75 : ℝ), fM u)
        + (∫ u in (0.75 : ℝ)..(0.78125 : ℝ), fM u)
        + (∫ u in (0.78125 : ℝ)..(0.8125 : ℝ), fM u)
        + (∫ u in (0.8125 : ℝ)..(0.84375 : ℝ), fM u)
        + (∫ u in (0.84375 : ℝ)..(0.875 : ℝ), fM u)
        + (∫ u in (0.875 : ℝ)..(0.90625 : ℝ), fM u)
        + (∫ u in (0.90625 : ℝ)..(0.9375 : ℝ), fM u)
        + (∫ u in (0.9375 : ℝ)..(0.96875 : ℝ), fM u)
        + (∫ u in (0.96875 : ℝ)..(1 : ℝ), fM u)
        + (∫ u in (1 : ℝ)..(1.03125 : ℝ), fM u)
        + (∫ u in (1.03125 : ℝ)..(1.0625 : ℝ), fM u)
        + (∫ u in (1.0625 : ℝ)..(1.09375 : ℝ), fM u)
        + (∫ u in (1.09375 : ℝ)..(1.125 : ℝ), fM u)
        + (∫ u in (1.125 : ℝ)..(1.15625 : ℝ), fM u)
        + (∫ u in (1.15625 : ℝ)..(1.1875 : ℝ), fM u)
        + (∫ u in (1.1875 : ℝ)..(1.21875 : ℝ), fM u)
        + (∫ u in (1.21875 : ℝ)..(1.25 : ℝ), fM u)
        + (∫ u in (1.25 : ℝ)..(1.28125 : ℝ), fM u)
        + (∫ u in (1.28125 : ℝ)..(1.3125 : ℝ), fM u)
        + (∫ u in (1.3125 : ℝ)..(1.34375 : ℝ), fM u)
        + (∫ u in (1.34375 : ℝ)..(1.375 : ℝ), fM u)
        + (∫ u in (1.375 : ℝ)..(1.40625 : ℝ), fM u)
        + (∫ u in (1.40625 : ℝ)..(1.4375 : ℝ), fM u)
        + (∫ u in (1.4375 : ℝ)..(1.46875 : ℝ), fM u)
        + (∫ u in (1.46875 : ℝ)..(1.5 : ℝ), fM u)
    := by
      linarith [h01, h02, h03, h04, h05, h06, h07, h08, h09, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47]
    rw [hsplit]
    have hnum : (2689993 / 80000000000 : ℝ)
      = (0.03125 : ℝ) * (-0.0004079956 : ℝ)
        + (0.03125 : ℝ) * (-0.0006469934 : ℝ)
        + (0.03125 : ℝ) * (-0.00074991 : ℝ)
        + (0.03125 : ℝ) * (-0.0007478327 : ℝ)
        + (0.03125 : ℝ) * (-0.0006692475 : ℝ)
        + (0.03125 : ℝ) * (-0.0005394697 : ℝ)
        + (0.03125 : ℝ) * (-0.0003802747 : ℝ)
        + (0.03125 : ℝ) * (-0.0002097192 : ℝ)
        + (0.03125 : ℝ) * (-0.0000421327 : ℝ)
        + (0.03125 : ℝ) * (0.0001039899 : ℝ)
        + (0.03125 : ℝ) * (0.0002307588 : ℝ)
        + (0.03125 : ℝ) * (0.0003360898 : ℝ)
        + (0.03125 : ℝ) * (0.000416961 : ℝ)
        + (0.03125 : ℝ) * (0.0004725458 : ℝ)
        + (0.03125 : ℝ) * (0.0005037673 : ℝ)
        + (0.03125 : ℝ) * (0.0005128554 : ℝ)
        + (0.03125 : ℝ) * (0.000499286 : ℝ)
        + (0.03125 : ℝ) * (0.0004693895 : ℝ)
        + (0.03125 : ℝ) * (0.0004286169 : ℝ)
        + (0.03125 : ℝ) * (0.000380839 : ℝ)
        + (0.03125 : ℝ) * (0.0003295355 : ℝ)
        + (0.03125 : ℝ) * (0.0002776712 : ℝ)
        + (0.03125 : ℝ) * (0.0002276307 : ℝ)
        + (0.03125 : ℝ) * (0.0001812017 : ℝ)
        + (0.03125 : ℝ) * (0.0001395995 : ℝ)
        + (0.03125 : ℝ) * (0.0001035211 : ℝ)
        + (0.03125 : ℝ) * (0.0000732202 : ℝ)
        + (0.03125 : ℝ) * (0.0000485932 : ℝ)
        + (0.03125 : ℝ) * (0.0000292686 : ℝ)
        + (0.03125 : ℝ) * (0.0000146919 : ℝ)
        + (0.03125 : ℝ) * (0.0000042037 : ℝ)
        + (0.03125 : ℝ) * (-0.0000102673 : ℝ)
        + (0.03125 : ℝ) * (-0.000025863 : ℝ)
        + (0.03125 : ℝ) * (-0.0000341974 : ℝ)
        + (0.03125 : ℝ) * (-0.0000372787 : ℝ)
        + (0.03125 : ℝ) * (-0.0000367685 : ℝ)
        + (0.03125 : ℝ) * (-0.0000339918 : ℝ)
        + (0.03125 : ℝ) * (-0.0000299634 : ℝ)
        + (0.03125 : ℝ) * (-0.0000254243 : ℝ)
        + (0.03125 : ℝ) * (-0.0000208851 : ℝ)
        + (0.03125 : ℝ) * (-0.0000166698 : ℝ)
        + (0.03125 : ℝ) * (-0.0000129587 : ℝ)
        + (0.03125 : ℝ) * (-0.0000098266 : ℝ)
        + (0.03125 : ℝ) * (-0.0000072758 : ℝ)
        + (0.03125 : ℝ) * (-0.0000052632 : ℝ)
        + (0.03125 : ℝ) * (-0.0000037207 : ℝ)
        + (0.03125 : ℝ) * (-0.0000025705 : ℝ)
        + (0.03125 : ℝ) * (-0.0000017392 : ℝ)
    := by norm_num
    rw [hnum]
    linarith [b00.1, b01.1, b02.1, b03.1, b04.1, b05.1, b06.1, b07.1, b08.1, b09.1, b10.1, b11.1, b12.1, b13.1, b14.1, b15.1, b16.1, b17.1, b18.1, b19.1, b20.1, b21.1, b22.1, b23.1, b24.1, b25.1, b26.1, b27.1, b28.1, b29.1, b30.1, b31.1, b32.1, b33.1, b34.1, b35.1, b36.1, b37.1, b38.1, b39.1, b40.1, b41.1, b42.1, b43.1, b44.1, b45.1, b46.1, b47.1]
  · rw [hthreehalves]
    have hsplit : ∫ u in (0 : ℝ)..(1.5 : ℝ), fM u
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
        + (∫ u in (0.46875 : ℝ)..(0.5 : ℝ), fM u)
        + (∫ u in (0.5 : ℝ)..(0.53125 : ℝ), fM u)
        + (∫ u in (0.53125 : ℝ)..(0.5625 : ℝ), fM u)
        + (∫ u in (0.5625 : ℝ)..(0.59375 : ℝ), fM u)
        + (∫ u in (0.59375 : ℝ)..(0.625 : ℝ), fM u)
        + (∫ u in (0.625 : ℝ)..(0.65625 : ℝ), fM u)
        + (∫ u in (0.65625 : ℝ)..(0.6875 : ℝ), fM u)
        + (∫ u in (0.6875 : ℝ)..(0.71875 : ℝ), fM u)
        + (∫ u in (0.71875 : ℝ)..(0.75 : ℝ), fM u)
        + (∫ u in (0.75 : ℝ)..(0.78125 : ℝ), fM u)
        + (∫ u in (0.78125 : ℝ)..(0.8125 : ℝ), fM u)
        + (∫ u in (0.8125 : ℝ)..(0.84375 : ℝ), fM u)
        + (∫ u in (0.84375 : ℝ)..(0.875 : ℝ), fM u)
        + (∫ u in (0.875 : ℝ)..(0.90625 : ℝ), fM u)
        + (∫ u in (0.90625 : ℝ)..(0.9375 : ℝ), fM u)
        + (∫ u in (0.9375 : ℝ)..(0.96875 : ℝ), fM u)
        + (∫ u in (0.96875 : ℝ)..(1 : ℝ), fM u)
        + (∫ u in (1 : ℝ)..(1.03125 : ℝ), fM u)
        + (∫ u in (1.03125 : ℝ)..(1.0625 : ℝ), fM u)
        + (∫ u in (1.0625 : ℝ)..(1.09375 : ℝ), fM u)
        + (∫ u in (1.09375 : ℝ)..(1.125 : ℝ), fM u)
        + (∫ u in (1.125 : ℝ)..(1.15625 : ℝ), fM u)
        + (∫ u in (1.15625 : ℝ)..(1.1875 : ℝ), fM u)
        + (∫ u in (1.1875 : ℝ)..(1.21875 : ℝ), fM u)
        + (∫ u in (1.21875 : ℝ)..(1.25 : ℝ), fM u)
        + (∫ u in (1.25 : ℝ)..(1.28125 : ℝ), fM u)
        + (∫ u in (1.28125 : ℝ)..(1.3125 : ℝ), fM u)
        + (∫ u in (1.3125 : ℝ)..(1.34375 : ℝ), fM u)
        + (∫ u in (1.34375 : ℝ)..(1.375 : ℝ), fM u)
        + (∫ u in (1.375 : ℝ)..(1.40625 : ℝ), fM u)
        + (∫ u in (1.40625 : ℝ)..(1.4375 : ℝ), fM u)
        + (∫ u in (1.4375 : ℝ)..(1.46875 : ℝ), fM u)
        + (∫ u in (1.46875 : ℝ)..(1.5 : ℝ), fM u)
    := by
      linarith [h01, h02, h03, h04, h05, h06, h07, h08, h09, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47]
    rw [hsplit]
    have hnum : (60314889 / 32000000000 : ℝ)
      = (0.03125 : ℝ) * (0.0004756752 : ℝ)
        + (0.03125 : ℝ) * (0.0010026984 : ℝ)
        + (0.03125 : ℝ) * (0.0015450762 : ℝ)
        + (0.03125 : ℝ) * (0.0020715093 : ℝ)
        + (0.03125 : ℝ) * (0.0025559903 : ℝ)
        + (0.03125 : ℝ) * (0.002978128 : ℝ)
        + (0.03125 : ℝ) * (0.0033232144 : ℝ)
        + (0.03125 : ℝ) * (0.0035820551 : ℝ)
        + (0.03125 : ℝ) * (0.0037505966 : ℝ)
        + (0.03125 : ℝ) * (0.0038293863 : ℝ)
        + (0.03125 : ℝ) * (0.003822906 : ℝ)
        + (0.03125 : ℝ) * (0.0037388227 : ℝ)
        + (0.03125 : ℝ) * (0.0035871986 : ℝ)
        + (0.03125 : ℝ) * (0.0033797006 : ℝ)
        + (0.03125 : ℝ) * (0.0031288447 : ℝ)
        + (0.03125 : ℝ) * (0.0028480572 : ℝ)
        + (0.03125 : ℝ) * (0.0025659012 : ℝ)
        + (0.03125 : ℝ) * (0.002279423 : ℝ)
        + (0.03125 : ℝ) * (0.0019905221 : ℝ)
        + (0.03125 : ℝ) * (0.0017080611 : ℝ)
        + (0.03125 : ℝ) * (0.0014393161 : ℝ)
        + (0.03125 : ℝ) * (0.0011898973 : ℝ)
        + (0.03125 : ℝ) * (0.0009637644 : ℝ)
        + (0.03125 : ℝ) * (0.0007633227 : ℝ)
        + (0.03125 : ℝ) * (0.0005895806 : ℝ)
        + (0.03125 : ℝ) * (0.000442351 : ℝ)
        + (0.03125 : ℝ) * (0.0003204783 : ℝ)
        + (0.03125 : ℝ) * (0.0002220742 : ℝ)
        + (0.03125 : ℝ) * (0.0001447469 : ℝ)
        + (0.03125 : ℝ) * (0.0000858128 : ℝ)
        + (0.03125 : ℝ) * (0.0000424816 : ℝ)
        + (0.03125 : ℝ) * (0.000012009 : ℝ)
        + (0.03125 : ℝ) * (-0.0000023082 : ℝ)
        + (0.03125 : ℝ) * (-0.0000057534 : ℝ)
        + (0.03125 : ℝ) * (-0.0000075141 : ℝ)
        + (0.03125 : ℝ) * (-0.0000080771 : ℝ)
        + (0.03125 : ℝ) * (-0.0000078427 : ℝ)
        + (0.03125 : ℝ) * (-0.0000071264 : ℝ)
        + (0.03125 : ℝ) * (-0.0000061646 : ℝ)
        + (0.03125 : ℝ) * (-0.0000051251 : ℝ)
        + (0.03125 : ℝ) * (-0.0000041187 : ℝ)
        + (0.03125 : ℝ) * (-0.000003211 : ℝ)
        + (0.03125 : ℝ) * (-0.0000024344 : ℝ)
        + (0.03125 : ℝ) * (-0.0000017975 : ℝ)
        + (0.03125 : ℝ) * (-0.0000012939 : ℝ)
        + (0.03125 : ℝ) * (-0.0000009084 : ℝ)
        + (0.03125 : ℝ) * (-0.0000006223 : ℝ)
        + (0.03125 : ℝ) * (-0.0000004151 : ℝ)
    := by norm_num
    rw [hnum]
    linarith [b00.2, b01.2, b02.2, b03.2, b04.2, b05.2, b06.2, b07.2, b08.2, b09.2, b10.2, b11.2, b12.2, b13.2, b14.2, b15.2, b16.2, b17.2, b18.2, b19.2, b20.2, b21.2, b22.2, b23.2, b24.2, b25.2, b26.2, b27.2, b28.2, b29.2, b30.2, b31.2, b32.2, b33.2, b34.2, b35.2, b36.2, b37.2, b38.2, b39.2, b40.2, b41.2, b42.2, b43.2, b44.2, b45.2, b46.2, b47.2]

/-! ## §Axiom check -/

#print axioms reLambda0_threehalves_lb_ub
#print axioms imLambda0_threehalves_lb_ub

end Assemble_threehalves
end FourierPanels_c51_8
end PrincipiaTractalis
