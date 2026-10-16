/-
# PF.Analytic.FourierPanels.Assemble_c49_8_threehalves_2026_10_16

**M2.5 assembly** at `c = 49/8` — combines the 48 per-panel integral bounds
from `Seg01Range`..`Seg06Range` (u ∈ [0, 3/2], 6 segments × 8 panels of
width 1/32) into two headline [0, 3/2]-integral enclosures.

  reLambda0_threehalves_lb_ub :
    R_lb ≤ ∫ u in 0..(3/2), nodeR_fourier_plus_at_c49_8_N3  u ≤ R_ub

  imLambda0_threehalves_lb_ub :
    I_lb ≤ ∫ u in 0..(3/2), nodeR_fourier_minus_at_c49_8_N3 u ≤ I_ub

Three-axiom bar: every top-level declaration prints
`[propext, Classical.choice, Quot.sound]`.  No sorry, no native_decide,
no `interval` tactic, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-16.
-/
import PF.Analytic.FourierPanels.Seg01Range_c49_8_2026_10_16
import PF.Analytic.FourierPanels.Seg02Range_c49_8_2026_10_16
import PF.Analytic.FourierPanels.Seg03Range_c49_8_2026_10_16
import PF.Analytic.FourierPanels.Seg04Range_c49_8_2026_10_16
import PF.Analytic.FourierPanels.Seg05Range_c49_8_2026_10_16
import PF.Analytic.FourierPanels.Seg06Range_c49_8_2026_10_16

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace PrincipiaTractalis
namespace FourierPanels_c49_8
namespace Assemble_threehalves

open MeasureTheory
open PrincipiaTractalis.FourierPanels_c49_8

/-! ## §1 — Local notation -/

private noncomputable abbrev fP : ℝ → ℝ := nodeR_fourier_plus_at_c49_8_N3
private noncomputable abbrev fM : ℝ → ℝ := nodeR_fourier_minus_at_c49_8_N3

private theorem iiP (a b : ℝ) : IntervalIntegrable fP MeasureTheory.volume a b :=
  Seg01Range.nodeR_fourier_plus_at_c49_8_N3_intervalIntegrable a b

private theorem iiM (a b : ℝ) : IntervalIntegrable fM MeasureTheory.volume a b :=
  Seg01Range.nodeR_fourier_minus_at_c49_8_N3_intervalIntegrable a b

/-! ## §2 — Headline PLUS enclosure on `[0, 3/2]` -/

theorem reLambda0_threehalves_lb_ub :
    (1127184067 / 80000000000 : ℝ)
      ≤ (∫ u in (0 : ℝ)..(3/2 : ℝ), nodeR_fourier_plus_at_c49_8_N3 u)
    ∧ (∫ u in (0 : ℝ)..(3/2 : ℝ), nodeR_fourier_plus_at_c49_8_N3 u)
      ≤ (5570099369 / 320000000000 : ℝ) := by
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
    have hnum : (1127184067 / 80000000000 : ℝ)
      = (0.03125 : ℝ) * (0.0778713595 : ℝ)
        + (0.03125 : ℝ) * (0.0698360472 : ℝ)
        + (0.03125 : ℝ) * (0.0618382458 : ℝ)
        + (0.03125 : ℝ) * (0.0540338771 : ℝ)
        + (0.03125 : ℝ) * (0.0465542589 : ℝ)
        + (0.03125 : ℝ) * (0.039505726 : ℝ)
        + (0.03125 : ℝ) * (0.0329699536 : ℝ)
        + (0.03125 : ℝ) * (0.0270049168 : ℝ)
        + (0.03125 : ℝ) * (0.0216464026 : ℝ)
        + (0.03125 : ℝ) * (0.0169099792 : ℝ)
        + (0.03125 : ℝ) * (0.0127933192 : ℝ)
        + (0.03125 : ℝ) * (0.0092787682 : ℝ)
        + (0.03125 : ℝ) * (0.0063360521 : ℝ)
        + (0.03125 : ℝ) * (0.0039250203 : ℝ)
        + (0.03125 : ℝ) * (0.0019983292 : ℝ)
        + (0.03125 : ℝ) * (0.0005039828 : ℝ)
        + (0.03125 : ℝ) * (-0.0007281598 : ℝ)
        + (0.03125 : ℝ) * (-0.0016798601 : ℝ)
        + (0.03125 : ℝ) * (-0.0023171185 : ℝ)
        + (0.03125 : ℝ) * (-0.0026956932 : ℝ)
        + (0.03125 : ℝ) * (-0.0028675134 : ℝ)
        + (0.03125 : ℝ) * (-0.0028797063 : ℝ)
        + (0.03125 : ℝ) * (-0.0027739608 : ℝ)
        + (0.03125 : ℝ) * (-0.0025861989 : ℝ)
        + (0.03125 : ℝ) * (-0.0023465215 : ℝ)
        + (0.03125 : ℝ) * (-0.0020793826 : ℝ)
        + (0.03125 : ℝ) * (-0.0018039488 : ℝ)
        + (0.03125 : ℝ) * (-0.0015345938 : ℝ)
        + (0.03125 : ℝ) * (-0.0012814833 : ℝ)
        + (0.03125 : ℝ) * (-0.0010512072 : ℝ)
        + (0.03125 : ℝ) * (-0.0008474208 : ℝ)
        + (0.03125 : ℝ) * (-0.0006714654 : ℝ)
        + (0.03125 : ℝ) * (-0.000523014 : ℝ)
        + (0.03125 : ℝ) * (-0.000402704 : ℝ)
        + (0.03125 : ℝ) * (-0.0003055773 : ℝ)
        + (0.03125 : ℝ) * (-0.0002277143 : ℝ)
        + (0.03125 : ℝ) * (-0.0001665497 : ℝ)
        + (0.03125 : ℝ) * (-0.0001194649 : ℝ)
        + (0.03125 : ℝ) * (-0.0000839516 : ℝ)
        + (0.03125 : ℝ) * (-0.0000577192 : ℝ)
        + (0.03125 : ℝ) * (-0.0000387561 : ℝ)
        + (0.03125 : ℝ) * (-0.0000253544 : ℝ)
        + (0.03125 : ℝ) * (-0.0000161079 : ℝ)
        + (0.03125 : ℝ) * (-0.0000098916 : ℝ)
        + (0.03125 : ℝ) * (-0.0000058302 : ℝ)
        + (0.03125 : ℝ) * (-0.000003261 : ℝ)
        + (0.03125 : ℝ) * (-0.0000016958 : ℝ)
        + (0.03125 : ℝ) * (-0.0000007853 : ℝ)
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
    have hnum : (5570099369 / 320000000000 : ℝ)
      = (0.03125 : ℝ) * (0.0871153865 : ℝ)
        + (0.03125 : ℝ) * (0.0791073109 : ℝ)
        + (0.03125 : ℝ) * (0.0709531238 : ℝ)
        + (0.03125 : ℝ) * (0.0628350588 : ℝ)
        + (0.03125 : ℝ) * (0.0549115836 : ℝ)
        + (0.03125 : ℝ) * (0.0473162376 : ℝ)
        + (0.03125 : ℝ) * (0.0401572301 : ℝ)
        + (0.03125 : ℝ) * (0.0335177545 : ℝ)
        + (0.03125 : ℝ) * (0.0274569477 : ℝ)
        + (0.03125 : ℝ) * (0.0220114131 : ℝ)
        + (0.03125 : ℝ) * (0.0171972098 : ℝ)
        + (0.03125 : ℝ) * (0.0130122025 : ℝ)
        + (0.03125 : ℝ) * (0.0094386633 : ℝ)
        + (0.03125 : ℝ) * (0.0064460167 : ℝ)
        + (0.03125 : ℝ) * (0.0039936227 : ℝ)
        + (0.03125 : ℝ) * (0.0020335017 : ℝ)
        + (0.03125 : ℝ) * (0.0005129153 : ℝ)
        + (0.03125 : ℝ) * (-0.000521372 : ℝ)
        + (0.03125 : ℝ) * (-0.0011901151 : ℝ)
        + (0.03125 : ℝ) * (-0.0016237255 : ℝ)
        + (0.03125 : ℝ) * (-0.0018678094 : ℝ)
        + (0.03125 : ℝ) * (-0.0019638559 : ℝ)
        + (0.03125 : ℝ) * (-0.0019486502 : ℝ)
        + (0.03125 : ℝ) * (-0.0018539664 : ℝ)
        + (0.03125 : ℝ) * (-0.0017065084 : ℝ)
        + (0.03125 : ℝ) * (-0.0015280574 : ℝ)
        + (0.03125 : ℝ) * (-0.0013357839 : ℝ)
        + (0.03125 : ℝ) * (-0.0011426809 : ℝ)
        + (0.03125 : ℝ) * (-0.000958075 : ℝ)
        + (0.03125 : ℝ) * (-0.0007881783 : ℝ)
        + (0.03125 : ℝ) * (-0.0006366477 : ℝ)
        + (0.03125 : ℝ) * (-0.0005051223 : ℝ)
        + (0.03125 : ℝ) * (-0.0003937206 : ℝ)
        + (0.03125 : ℝ) * (-0.0002996219 : ℝ)
        + (0.03125 : ℝ) * (-0.000223251 : ℝ)
        + (0.03125 : ℝ) * (-0.0001632667 : ℝ)
        + (0.03125 : ℝ) * (-0.0001170967 : ℝ)
        + (0.03125 : ℝ) * (-0.0000822781 : ℝ)
        + (0.03125 : ℝ) * (-0.0000565622 : ℝ)
        + (0.03125 : ℝ) * (-0.0000379749 : ℝ)
        + (0.03125 : ℝ) * (-0.0000248405 : ℝ)
        + (0.03125 : ℝ) * (-0.0000157795 : ℝ)
        + (0.03125 : ℝ) * (-0.0000096888 : ℝ)
        + (0.03125 : ℝ) * (-0.00000571 : ℝ)
        + (0.03125 : ℝ) * (-0.0000031933 : ℝ)
        + (0.03125 : ℝ) * (-0.0000016603 : ℝ)
        + (0.03125 : ℝ) * (-0.0000007686 : ℝ)
        + (0.03125 : ℝ) * (-0.0000002802 : ℝ)
    := by norm_num
    rw [hnum]
    linarith [b00.2, b01.2, b02.2, b03.2, b04.2, b05.2, b06.2, b07.2, b08.2, b09.2, b10.2, b11.2, b12.2, b13.2, b14.2, b15.2, b16.2, b17.2, b18.2, b19.2, b20.2, b21.2, b22.2, b23.2, b24.2, b25.2, b26.2, b27.2, b28.2, b29.2, b30.2, b31.2, b32.2, b33.2, b34.2, b35.2, b36.2, b37.2, b38.2, b39.2, b40.2, b41.2, b42.2, b43.2, b44.2, b45.2, b46.2, b47.2]

/-! ## §3 — Headline MINUS enclosure on `[0, 3/2]` -/

theorem imLambda0_threehalves_lb_ub :
    (1871853 / 40000000000 : ℝ)
      ≤ (∫ u in (0 : ℝ)..(3/2 : ℝ), nodeR_fourier_minus_at_c49_8_N3 u)
    ∧ (∫ u in (0 : ℝ)..(3/2 : ℝ), nodeR_fourier_minus_at_c49_8_N3 u)
      ≤ (74866313 / 40000000000 : ℝ) := by
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
    have hnum : (1871853 / 40000000000 : ℝ)
      = (0.03125 : ℝ) * (-0.0003920456 : ℝ)
        + (0.03125 : ℝ) * (-0.0006219382 : ℝ)
        + (0.03125 : ℝ) * (-0.0007213315 : ℝ)
        + (0.03125 : ℝ) * (-0.0007199843 : ℝ)
        + (0.03125 : ℝ) * (-0.0006450832 : ℝ)
        + (0.03125 : ℝ) * (-0.0005207485 : ℝ)
        + (0.03125 : ℝ) * (-0.0003677203 : ℝ)
        + (0.03125 : ℝ) * (-0.0002032128 : ℝ)
        + (0.03125 : ℝ) * (-0.000040923 : ℝ)
        + (0.03125 : ℝ) * (0.0001010041 : ℝ)
        + (0.03125 : ℝ) * (0.0002247466 : ℝ)
        + (0.03125 : ℝ) * (0.0003283534 : ℝ)
        + (0.03125 : ℝ) * (0.0004088014 : ℝ)
        + (0.03125 : ℝ) * (0.0004651463 : ℝ)
        + (0.03125 : ℝ) * (0.0004981096 : ℝ)
        + (0.03125 : ℝ) * (0.0005096686 : ℝ)
        + (0.03125 : ℝ) * (0.0005022667 : ℝ)
        + (0.03125 : ℝ) * (0.0004756792 : ℝ)
        + (0.03125 : ℝ) * (0.0004380321 : ℝ)
        + (0.03125 : ℝ) * (0.0003930004 : ℝ)
        + (0.03125 : ℝ) * (0.0003439235 : ℝ)
        + (0.03125 : ℝ) * (0.000293683 : ℝ)
        + (0.03125 : ℝ) * (0.0002446335 : ℝ)
        + (0.03125 : ℝ) * (0.000198579 : ℝ)
        + (0.03125 : ℝ) * (0.0001567885 : ℝ)
        + (0.03125 : ℝ) * (0.0001200397 : ℝ)
        + (0.03125 : ℝ) * (0.0000886836 : ℝ)
        + (0.03125 : ℝ) * (0.0000627207 : ℝ)
        + (0.03125 : ℝ) * (0.000041882 : ℝ)
        + (0.03125 : ℝ) * (0.0000257078 : ℝ)
        + (0.03125 : ℝ) * (0.00001362 : ℝ)
        + (0.03125 : ℝ) * (0.0000049851 : ℝ)
        + (0.03125 : ℝ) * (-0.0000029627 : ℝ)
        + (0.03125 : ℝ) * (-0.0000157937 : ℝ)
        + (0.03125 : ℝ) * (-0.0000227811 : ℝ)
        + (0.03125 : ℝ) * (-0.000025581 : ℝ)
        + (0.03125 : ℝ) * (-0.0000255428 : ℝ)
        + (0.03125 : ℝ) * (-0.0000237262 : ℝ)
        + (0.03125 : ℝ) * (-0.0000209312 : ℝ)
        + (0.03125 : ℝ) * (-0.0000177338 : ℝ)
        + (0.03125 : ℝ) * (-0.0000145247 : ℝ)
        + (0.03125 : ℝ) * (-0.000011548 : ℝ)
        + (0.03125 : ℝ) * (-0.0000089365 : ℝ)
        + (0.03125 : ℝ) * (-0.000006743 : ℝ)
        + (0.03125 : ℝ) * (-0.0000049667 : ℝ)
        + (0.03125 : ℝ) * (-0.0000035737 : ℝ)
        + (0.03125 : ℝ) * (-0.0000025129 : ℝ)
        + (0.03125 : ℝ) * (-0.000001727 : ℝ)
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
    have hnum : (74866313 / 40000000000 : ℝ)
      = (0.03125 : ℝ) * (0.0004570794 : ℝ)
        + (0.03125 : ℝ) * (0.0009638683 : ℝ)
        + (0.03125 : ℝ) * (0.0014861946 : ℝ)
        + (0.03125 : ℝ) * (0.0019943689 : ℝ)
        + (0.03125 : ℝ) * (0.0024637019 : ℝ)
        + (0.03125 : ℝ) * (0.0028747784 : ℝ)
        + (0.03125 : ℝ) * (0.0032135013 : ℝ)
        + (0.03125 : ℝ) * (0.0034709251 : ℝ)
        + (0.03125 : ℝ) * (0.003642908 : ℝ)
        + (0.03125 : ℝ) * (0.0037296148 : ℝ)
        + (0.03125 : ℝ) * (0.0037349069 : ℝ)
        + (0.03125 : ℝ) * (0.0036656572 : ℝ)
        + (0.03125 : ℝ) * (0.0035310277 : ℝ)
        + (0.03125 : ℝ) * (0.0033417442 : ℝ)
        + (0.03125 : ℝ) * (0.0031094024 : ℝ)
        + (0.03125 : ℝ) * (0.0028458304 : ℝ)
        + (0.03125 : ℝ) * (0.0025665773 : ℝ)
        + (0.03125 : ℝ) * (0.0022930309 : ℝ)
        + (0.03125 : ℝ) * (0.0020171945 : ℝ)
        + (0.03125 : ℝ) * (0.0017455812 : ℝ)
        + (0.03125 : ℝ) * (0.001485278 : ℝ)
        + (0.03125 : ℝ) * (0.00124185 : ℝ)
        + (0.03125 : ℝ) * (0.0010193397 : ℝ)
        + (0.03125 : ℝ) * (0.0008203389 : ℝ)
        + (0.03125 : ℝ) * (0.0006461216 : ℝ)
        + (0.03125 : ℝ) * (0.000496818 : ℝ)
        + (0.03125 : ℝ) * (0.0003716163 : ℝ)
        + (0.03125 : ℝ) * (0.0002689741 : ℝ)
        + (0.03125 : ℝ) * (0.0001868289 : ℝ)
        + (0.03125 : ℝ) * (0.0001227941 : ℝ)
        + (0.03125 : ℝ) * (0.0000743335 : ℝ)
        + (0.03125 : ℝ) * (0.0000389081 : ℝ)
        + (0.03125 : ℝ) * (0.0000140924 : ℝ)
        + (0.03125 : ℝ) * (-0.0000006589 : ℝ)
        + (0.03125 : ℝ) * (-0.0000034702 : ℝ)
        + (0.03125 : ℝ) * (-0.0000049359 : ℝ)
        + (0.03125 : ℝ) * (-0.0000054564 : ℝ)
        + (0.03125 : ℝ) * (-0.000005355 : ℝ)
        + (0.03125 : ℝ) * (-0.0000048813 : ℝ)
        + (0.03125 : ℝ) * (-0.0000042193 : ℝ)
        + (0.03125 : ℝ) * (-0.0000034972 : ℝ)
        + (0.03125 : ℝ) * (-0.0000027978 : ℝ)
        + (0.03125 : ℝ) * (-0.0000021694 : ℝ)
        + (0.03125 : ℝ) * (-0.0000016347 : ℝ)
        + (0.03125 : ℝ) * (-0.0000011991 : ℝ)
        + (0.03125 : ℝ) * (-0.0000008572 : ℝ)
        + (0.03125 : ℝ) * (-0.0000005977 : ℝ)
        + (0.03125 : ℝ) * (-0.0000004065 : ℝ)
    := by norm_num
    rw [hnum]
    linarith [b00.2, b01.2, b02.2, b03.2, b04.2, b05.2, b06.2, b07.2, b08.2, b09.2, b10.2, b11.2, b12.2, b13.2, b14.2, b15.2, b16.2, b17.2, b18.2, b19.2, b20.2, b21.2, b22.2, b23.2, b24.2, b25.2, b26.2, b27.2, b28.2, b29.2, b30.2, b31.2, b32.2, b33.2, b34.2, b35.2, b36.2, b37.2, b38.2, b39.2, b40.2, b41.2, b42.2, b43.2, b44.2, b45.2, b46.2, b47.2]

/-! ## §Axiom check -/

#print axioms reLambda0_threehalves_lb_ub
#print axioms imLambda0_threehalves_lb_ub

end Assemble_threehalves
end FourierPanels_c49_8
end PrincipiaTractalis
