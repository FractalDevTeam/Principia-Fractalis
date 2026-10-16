/-
# PF.Analytic.FourierPanels.Assemble_c25_4_threehalves_2026_10_16

**M2.5 assembly** at `c = 25/4` — combines the 48 per-panel integral bounds
from `Seg01Range`..`Seg06Range` (u ∈ [0, 3/2], 6 segments × 8 panels of
width 1/32) into two headline [0, 3/2]-integral enclosures.

  reLambda0_threehalves_lb_ub :
    R_lb ≤ ∫ u in 0..(3/2), nodeR_fourier_plus_at_c25_4_N3  u ≤ R_ub

  imLambda0_threehalves_lb_ub :
    I_lb ≤ ∫ u in 0..(3/2), nodeR_fourier_minus_at_c25_4_N3 u ≤ I_ub

Three-axiom bar: every top-level declaration prints
`[propext, Classical.choice, Quot.sound]`.  No sorry, no native_decide,
no `interval` tactic, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-16.
-/
import PF.Analytic.FourierPanels.Seg01Range_c25_4_2026_10_16
import PF.Analytic.FourierPanels.Seg02Range_c25_4_2026_10_16
import PF.Analytic.FourierPanels.Seg03Range_c25_4_2026_10_16
import PF.Analytic.FourierPanels.Seg04Range_c25_4_2026_10_16
import PF.Analytic.FourierPanels.Seg05Range_c25_4_2026_10_16
import PF.Analytic.FourierPanels.Seg06Range_c25_4_2026_10_16

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace PrincipiaTractalis
namespace FourierPanels_c25_4
namespace Assemble_threehalves

open MeasureTheory
open PrincipiaTractalis.FourierPanels_c25_4

/-! ## §1 — Local notation -/

private noncomputable abbrev fP : ℝ → ℝ := nodeR_fourier_plus_at_c25_4_N3
private noncomputable abbrev fM : ℝ → ℝ := nodeR_fourier_minus_at_c25_4_N3

private theorem iiP (a b : ℝ) : IntervalIntegrable fP MeasureTheory.volume a b :=
  Seg01Range.nodeR_fourier_plus_at_c25_4_N3_intervalIntegrable a b

private theorem iiM (a b : ℝ) : IntervalIntegrable fM MeasureTheory.volume a b :=
  Seg01Range.nodeR_fourier_minus_at_c25_4_N3_intervalIntegrable a b
/-! ## §2 — Headline PLUS enclosure on `[0, 3/2]` -/

theorem reLambda0_threehalves_lb_ub :
    (2215328211 / 160000000000 : ℝ)
      ≤ (∫ u in (0 : ℝ)..(3/2 : ℝ), nodeR_fourier_plus_at_c25_4_N3 u)
    ∧ (∫ u in (0 : ℝ)..(3/2 : ℝ), nodeR_fourier_plus_at_c25_4_N3 u)
      ≤ (219960753 / 12800000000 : ℝ) := by
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
    have hnum : (2215328211 / 160000000000 : ℝ)
      = (0.03125 : ℝ) * (0.0778566106 : ℝ)
        + (0.03125 : ℝ) * (0.0697826523 : ℝ)
        + (0.03125 : ℝ) * (0.0617301996 : ℝ)
        + (0.03125 : ℝ) * (0.0538622437 : ℝ)
        + (0.03125 : ℝ) * (0.0463162138 : ℝ)
        + (0.03125 : ℝ) * (0.0392035159 : ℝ)
        + (0.03125 : ℝ) * (0.0326098234 : ℝ)
        + (0.03125 : ℝ) * (0.0265960503 : ℝ)
        + (0.03125 : ℝ) * (0.0211999165 : ℝ)
        + (0.03125 : ℝ) * (0.0164380041 : ℝ)
        + (0.03125 : ℝ) * (0.0123081921 : ℝ)
        + (0.03125 : ℝ) * (0.0087923548 : ℝ)
        + (0.03125 : ℝ) * (0.0058592087 : ℝ)
        + (0.03125 : ℝ) * (0.003467197 : ℝ)
        + (0.03125 : ℝ) * (0.0015673105 : ℝ)
        + (0.03125 : ℝ) * (0.0001057555 : ℝ)
        + (0.03125 : ℝ) * (-0.0011577566 : ℝ)
        + (0.03125 : ℝ) * (-0.0020646436 : ℝ)
        + (0.03125 : ℝ) * (-0.0026556532 : ℝ)
        + (0.03125 : ℝ) * (-0.002988178 : ℝ)
        + (0.03125 : ℝ) * (-0.0031155264 : ℝ)
        + (0.03125 : ℝ) * (-0.0030859255 : ℝ)
        + (0.03125 : ℝ) * (-0.0029418781 : ℝ)
        + (0.03125 : ℝ) * (-0.0027198447 : ℝ)
        + (0.03125 : ℝ) * (-0.0024502106 : ℝ)
        + (0.03125 : ℝ) * (-0.0021574933 : ℝ)
        + (0.03125 : ℝ) * (-0.0018607389 : ℝ)
        + (0.03125 : ℝ) * (-0.0015740577 : ℝ)
        + (0.03125 : ℝ) * (-0.0013072494 : ℝ)
        + (0.03125 : ℝ) * (-0.0010664732 : ℝ)
        + (0.03125 : ℝ) * (-0.0008549235 : ℝ)
        + (0.03125 : ℝ) * (-0.0006734784 : ℝ)
        + (0.03125 : ℝ) * (-0.000523014 : ℝ)
        + (0.03125 : ℝ) * (-0.0004014369 : ℝ)
        + (0.03125 : ℝ) * (-0.0003026167 : ℝ)
        + (0.03125 : ℝ) * (-0.0002238995 : ℝ)
        + (0.03125 : ℝ) * (-0.000162471 : ℝ)
        + (0.03125 : ℝ) * (-0.0001155121 : ℝ)
        + (0.03125 : ℝ) * (-0.000080359 : ℝ)
        + (0.03125 : ℝ) * (-0.0000546057 : ℝ)
        + (0.03125 : ℝ) * (-0.0000361591 : ℝ)
        + (0.03125 : ℝ) * (-0.0000232578 : ℝ)
        + (0.03125 : ℝ) * (-0.0000144638 : ℝ)
        + (0.03125 : ℝ) * (-0.0000086365 : ℝ)
        + (0.03125 : ℝ) * (-0.0000048959 : ℝ)
        + (0.03125 : ℝ) * (-0.0000025821 : ℝ)
        + (0.03125 : ℝ) * (-0.0000012141 : ℝ)
        + (0.03125 : ℝ) * (-0.0000004513 : ℝ)
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
    have hnum : (219960753 / 12800000000 : ℝ)
      = (0.03125 : ℝ) * (0.0871153865 : ℝ)
        + (0.03125 : ℝ) * (0.079092328 : ℝ)
        + (0.03125 : ℝ) * (0.0708988749 : ℝ)
        + (0.03125 : ℝ) * (0.0627252709 : ℝ)
        + (0.03125 : ℝ) * (0.0547371623 : ℝ)
        + (0.03125 : ℝ) * (0.0470742963 : ℝ)
        + (0.03125 : ℝ) * (0.0398500362 : ℝ)
        + (0.03125 : ℝ) * (0.0331516406 : ℝ)
        + (0.03125 : ℝ) * (0.0270412371 : ℝ)
        + (0.03125 : ℝ) * (0.0215573982 : ℝ)
        + (0.03125 : ℝ) * (0.0167172179 : ℝ)
        + (0.03125 : ℝ) * (0.0125187753 : ℝ)
        + (0.03125 : ℝ) * (0.0089438679 : ℝ)
        + (0.03125 : ℝ) * (0.0059608975 : ℝ)
        + (0.03125 : ℝ) * (0.0035277975 : ℝ)
        + (0.03125 : ℝ) * (0.0015948967 : ℝ)
        + (0.03125 : ℝ) * (0.0001076302 : ℝ)
        + (0.03125 : ℝ) * (-0.0008289691 : ℝ)
        + (0.03125 : ℝ) * (-0.0014627191 : ℝ)
        + (0.03125 : ℝ) * (-0.0018609545 : ℝ)
        + (0.03125 : ℝ) * (-0.0020704682 : ℝ)
        + (0.03125 : ℝ) * (-0.0021337111 : ℝ)
        + (0.03125 : ℝ) * (-0.0020881954 : ℝ)
        + (0.03125 : ℝ) * (-0.0019661934 : ℝ)
        + (0.03125 : ℝ) * (-0.0017946948 : ℝ)
        + (0.03125 : ℝ) * (-0.0015955798 : ℝ)
        + (0.03125 : ℝ) * (-0.0013859618 : ℝ)
        + (0.03125 : ℝ) * (-0.0011786536 : ℝ)
        + (0.03125 : ℝ) * (-0.000982713 : ℝ)
        + (0.03125 : ℝ) * (-0.0008040258 : ℝ)
        + (0.03125 : ℝ) * (-0.0006458933 : ℝ)
        + (0.03125 : ℝ) * (-0.0005095944 : ℝ)
        + (0.03125 : ℝ) * (-0.0003936584 : ℝ)
        + (0.03125 : ℝ) * (-0.000296719 : ℝ)
        + (0.03125 : ℝ) * (-0.0002195109 : ℝ)
        + (0.03125 : ℝ) * (-0.0001592683 : ℝ)
        + (0.03125 : ℝ) * (-0.0001132223 : ℝ)
        + (0.03125 : ℝ) * (-0.0000787571 : ℝ)
        + (0.03125 : ℝ) * (-0.0000535111 : ℝ)
        + (0.03125 : ℝ) * (-0.0000354302 : ℝ)
        + (0.03125 : ℝ) * (-0.0000227863 : ℝ)
        + (0.03125 : ℝ) * (-0.000014169 : ℝ)
        + (0.03125 : ℝ) * (-0.0000084594 : ℝ)
        + (0.03125 : ℝ) * (-0.0000047948 : ℝ)
        + (0.03125 : ℝ) * (-0.0000025284 : ℝ)
        + (0.03125 : ℝ) * (-0.0000011886 : ℝ)
        + (0.03125 : ℝ) * (-0.0000004416 : ℝ)
        + (0.03125 : ℝ) * (-0.0000000588 : ℝ)
    := by norm_num
    rw [hnum]
    linarith [b00.2, b01.2, b02.2, b03.2, b04.2, b05.2, b06.2, b07.2, b08.2, b09.2, b10.2, b11.2, b12.2, b13.2, b14.2, b15.2, b16.2, b17.2, b18.2, b19.2, b20.2, b21.2, b22.2, b23.2, b24.2, b25.2, b26.2, b27.2, b28.2, b29.2, b30.2, b31.2, b32.2, b33.2, b34.2, b35.2, b36.2, b37.2, b38.2, b39.2, b40.2, b41.2, b42.2, b43.2, b44.2, b45.2, b46.2, b47.2]

/-! ## §3 — Headline MINUS enclosure on `[0, 3/2]` -/

theorem imLambda0_threehalves_lb_ub :
    (6465647 / 160000000000 : ℝ)
      ≤ (∫ u in (0 : ℝ)..(3/2 : ℝ), nodeR_fourier_minus_at_c25_4_N3 u)
    ∧ (∫ u in (0 : ℝ)..(3/2 : ℝ), nodeR_fourier_minus_at_c25_4_N3 u)
      ≤ (150301153 / 80000000000 : ℝ) := by
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
    have hnum : (6465647 / 160000000000 : ℝ)
      = (0.03125 : ℝ) * (-0.0004000214 : ℝ)
        + (0.03125 : ℝ) * (-0.0006344706 : ℝ)
        + (0.03125 : ℝ) * (-0.0007356334 : ℝ)
        + (0.03125 : ℝ) * (-0.0007339309 : ℝ)
        + (0.03125 : ℝ) * (-0.0006571967 : ℝ)
        + (0.03125 : ℝ) * (-0.0005301455 : ℝ)
        + (0.03125 : ℝ) * (-0.0003740325 : ℝ)
        + (0.03125 : ℝ) * (-0.0002064912 : ℝ)
        + (0.03125 : ℝ) * (-0.0000415343 : ℝ)
        + (0.03125 : ℝ) * (0.0001025129 : ℝ)
        + (0.03125 : ℝ) * (0.0002277962 : ℝ)
        + (0.03125 : ℝ) * (0.0003322983 : ℝ)
        + (0.03125 : ℝ) * (0.0004129946 : ℝ)
        + (0.03125 : ℝ) * (0.0004689972 : ℝ)
        + (0.03125 : ℝ) * (0.0005011258 : ℝ)
        + (0.03125 : ℝ) * (0.0005114815 : ℝ)
        + (0.03125 : ℝ) * (0.0005010525 : ℝ)
        + (0.03125 : ℝ) * (0.0004728265 : ℝ)
        + (0.03125 : ℝ) * (0.000433623 : ℝ)
        + (0.03125 : ℝ) * (0.0003872151 : ℝ)
        + (0.03125 : ℝ) * (0.0003370129 : ℝ)
        + (0.03125 : ℝ) * (0.000285941 : ℝ)
        + (0.03125 : ℝ) * (0.0002363705 : ℝ)
        + (0.03125 : ℝ) * (0.0001900992 : ℝ)
        + (0.03125 : ℝ) * (0.0001483708 : ℝ)
        + (0.03125 : ℝ) * (0.0001119247 : ℝ)
        + (0.03125 : ℝ) * (0.0000810646 : ℝ)
        + (0.03125 : ℝ) * (0.0000557403 : ℝ)
        + (0.03125 : ℝ) * (0.0000356324 : ℝ)
        + (0.03125 : ℝ) * (0.0000202346 : ℝ)
        + (0.03125 : ℝ) * (0.0000089282 : ℝ)
        + (0.03125 : ℝ) * (0.0000010467 : ℝ)
        + (0.03125 : ℝ) * (-0.0000144428 : ℝ)
        + (0.03125 : ℝ) * (-0.0000250508 : ℝ)
        + (0.03125 : ℝ) * (-0.0000301002 : ℝ)
        + (0.03125 : ℝ) * (-0.000031252 : ℝ)
        + (0.03125 : ℝ) * (-0.0000298452 : ℝ)
        + (0.03125 : ℝ) * (-0.0000269189 : ℝ)
        + (0.03125 : ℝ) * (-0.0000232451 : ℝ)
        + (0.03125 : ℝ) * (-0.0000193685 : ℝ)
        + (0.03125 : ℝ) * (-0.0000156474 : ℝ)
        + (0.03125 : ℝ) * (-0.0000122947 : ℝ)
        + (0.03125 : ℝ) * (-0.0000094147 : ℝ)
        + (0.03125 : ℝ) * (-0.0000070354 : ℝ)
        + (0.03125 : ℝ) * (-0.0000051348 : ℝ)
        + (0.03125 : ℝ) * (-0.000003662 : ℝ)
        + (0.03125 : ℝ) * (-0.0000025524 : ℝ)
        + (0.03125 : ℝ) * (-0.0000017387 : ℝ)
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
    have hnum : (150301153 / 80000000000 : ℝ)
      = (0.03125 : ℝ) * (0.0004663782 : ℝ)
        + (0.03125 : ℝ) * (0.0009832908 : ℝ)
        + (0.03125 : ℝ) * (0.0015156614 : ℝ)
        + (0.03125 : ℝ) * (0.0020330011 : ℝ)
        + (0.03125 : ℝ) * (0.0025099658 : ℝ)
        + (0.03125 : ℝ) * (0.0029266542 : ℝ)
        + (0.03125 : ℝ) * (0.0032686634 : ℝ)
        + (0.03125 : ℝ) * (0.0035269206 : ℝ)
        + (0.03125 : ℝ) * (0.0036973235 : ℝ)
        + (0.03125 : ℝ) * (0.0037802215 : ℝ)
        + (0.03125 : ℝ) * (0.0037797787 : ℝ)
        + (0.03125 : ℝ) * (0.003703257 : ℝ)
        + (0.03125 : ℝ) * (0.0035602607 : ℝ)
        + (0.03125 : ℝ) * (0.0033619792 : ℝ)
        + (0.03125 : ℝ) * (0.0031204626 : ℝ)
        + (0.03125 : ℝ) * (0.0028479592 : ℝ)
        + (0.03125 : ℝ) * (0.0025665773 : ℝ)
        + (0.03125 : ℝ) * (0.0022874878 : ℝ)
        + (0.03125 : ℝ) * (0.0020050973 : ℝ)
        + (0.03125 : ℝ) * (0.0017280109 : ℝ)
        + (0.03125 : ℝ) * (0.0014634134 : ℝ)
        + (0.03125 : ℝ) * (0.0012168971 : ℝ)
        + (0.03125 : ℝ) * (0.0009924681 : ℝ)
        + (0.03125 : ℝ) * (0.0007926304 : ℝ)
        + (0.03125 : ℝ) * (0.0006185305 : ℝ)
        + (0.03125 : ℝ) * (0.0004701449 : ℝ)
        + (0.03125 : ℝ) * (0.000346494 : ℝ)
        + (0.03125 : ℝ) * (0.000245866 : ℝ)
        + (0.03125 : ℝ) * (0.0001660361 : ℝ)
        + (0.03125 : ℝ) * (0.000104471 : ℝ)
        + (0.03125 : ℝ) * (0.0000585079 : ℝ)
        + (0.03125 : ℝ) * (0.0000255053 : ℝ)
        + (0.03125 : ℝ) * (0.0000029595 : ℝ)
        + (0.03125 : ℝ) * (-0.0000032128 : ℝ)
        + (0.03125 : ℝ) * (-0.0000055043 : ℝ)
        + (0.03125 : ℝ) * (-0.0000065217 : ℝ)
        + (0.03125 : ℝ) * (-0.000006666 : ℝ)
        + (0.03125 : ℝ) * (-0.000006257 : ℝ)
        + (0.03125 : ℝ) * (-0.0000055382 : ℝ)
        + (0.03125 : ℝ) * (-0.0000046858 : ℝ)
        + (0.03125 : ℝ) * (-0.0000038196 : ℝ)
        + (0.03125 : ℝ) * (-0.0000030141 : ℝ)
        + (0.03125 : ℝ) * (-0.0000023097 : ℝ)
        + (0.03125 : ℝ) * (-0.0000017222 : ℝ)
        + (0.03125 : ℝ) * (-0.0000012511 : ℝ)
        + (0.03125 : ℝ) * (-0.0000008863 : ℝ)
        + (0.03125 : ℝ) * (-0.0000006125 : ℝ)
        + (0.03125 : ℝ) * (-0.0000004129 : ℝ)
    := by norm_num
    rw [hnum]
    linarith [b00.2, b01.2, b02.2, b03.2, b04.2, b05.2, b06.2, b07.2, b08.2, b09.2, b10.2, b11.2, b12.2, b13.2, b14.2, b15.2, b16.2, b17.2, b18.2, b19.2, b20.2, b21.2, b22.2, b23.2, b24.2, b25.2, b26.2, b27.2, b28.2, b29.2, b30.2, b31.2, b32.2, b33.2, b34.2, b35.2, b36.2, b37.2, b38.2, b39.2, b40.2, b41.2, b42.2, b43.2, b44.2, b45.2, b46.2, b47.2]

/-! ## §Axiom check -/

#print axioms reLambda0_threehalves_lb_ub
#print axioms imLambda0_threehalves_lb_ub

end Assemble_threehalves
end FourierPanels_c25_4
end PrincipiaTractalis
