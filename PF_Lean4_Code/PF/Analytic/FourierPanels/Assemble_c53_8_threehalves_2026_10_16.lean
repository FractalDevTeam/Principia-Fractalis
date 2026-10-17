/-
# PF.Analytic.FourierPanels.Assemble_c53_8_threehalves_2026_10_16

**M2.5 assembly** at `c = 53/8` — combines the 48 per-panel integral bounds
from `Seg01Range`..`Seg06Range` (u ∈ [0, 3/2], 6 segments × 8 panels of
width 1/32) into two headline [0, 3/2]-integral enclosures.

  reLambda0_threehalves_lb_ub :
    R_lb ≤ ∫ u in 0..(3/2), nodeR_fourier_plus_at_c53_8_N3  u ≤ R_ub

  imLambda0_threehalves_lb_ub :
    I_lb ≤ ∫ u in 0..(3/2), nodeR_fourier_minus_at_c53_8_N3 u ≤ I_ub

Three-axiom bar: every top-level declaration prints
`[propext, Classical.choice, Quot.sound]`.  No sorry, no native_decide,
no `interval` tactic, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-16.
-/
import PF.Analytic.FourierPanels.Seg01Range_c53_8_2026_10_16
import PF.Analytic.FourierPanels.Seg02Range_c53_8_2026_10_16
import PF.Analytic.FourierPanels.Seg03Range_c53_8_2026_10_16
import PF.Analytic.FourierPanels.Seg04Range_c53_8_2026_10_16
import PF.Analytic.FourierPanels.Seg05Range_c53_8_2026_10_16
import PF.Analytic.FourierPanels.Seg06Range_c53_8_2026_10_16

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace PrincipiaTractalis
namespace FourierPanels_c53_8
namespace Assemble_threehalves

open MeasureTheory
open PrincipiaTractalis.FourierPanels_c53_8

/-! ## §1 — Local notation -/

private noncomputable abbrev fP : ℝ → ℝ := nodeR_fourier_plus_at_c53_8_N3
private noncomputable abbrev fM : ℝ → ℝ := nodeR_fourier_minus_at_c53_8_N3

private theorem iiP (a b : ℝ) : IntervalIntegrable fP MeasureTheory.volume a b :=
  Seg01Range.nodeR_fourier_plus_at_c53_8_N3_intervalIntegrable a b

private theorem iiM (a b : ℝ) : IntervalIntegrable fM MeasureTheory.volume a b :=
  Seg01Range.nodeR_fourier_minus_at_c53_8_N3_intervalIntegrable a b

/-! ## §2 — Headline PLUS enclosure on `[0, 3/2]` -/

theorem reLambda0_threehalves_lb_ub :
    (4195623213 / 320000000000 : ℝ)
      ≤ (∫ u in (0 : ℝ)..(3/2 : ℝ), nodeR_fourier_plus_at_c53_8_N3 u)
    ∧ (∫ u in (0 : ℝ)..(3/2 : ℝ), nodeR_fourier_plus_at_c53_8_N3 u)
      ≤ (2643610271 / 160000000000 : ℝ) := by
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
    have hnum : (4195623213 / 320000000000 : ℝ)
      = (0.03125 : ℝ) * (0.0778105823 : ℝ)
        + (0.03125 : ℝ) * (0.0696160822 : ℝ)
        + (0.03125 : ℝ) * (0.0613933603 : ℝ)
        + (0.03125 : ℝ) * (0.0533276615 : ℝ)
        + (0.03125 : ℝ) * (0.0455756693 : ℝ)
        + (0.03125 : ℝ) * (0.0382647529 : ℝ)
        + (0.03125 : ℝ) * (0.0314931356 : ℝ)
        + (0.03125 : ℝ) * (0.0253308995 : ℝ)
        + (0.03125 : ℝ) * (0.0198217178 : ℝ)
        + (0.03125 : ℝ) * (0.0149851886 : ℝ)
        + (0.03125 : ℝ) * (0.0108196338 : ℝ)
        + (0.03125 : ℝ) * (0.0073052193 : ℝ)
        + (0.03125 : ℝ) * (0.0044072573 : ℝ)
        + (0.03125 : ℝ) * (0.0020795523 : ℝ)
        + (0.03125 : ℝ) * (0.0002676685 : ℝ)
        + (0.03125 : ℝ) * (-0.0012871701 : ℝ)
        + (0.03125 : ℝ) * (-0.0024370029 : ℝ)
        + (0.03125 : ℝ) * (-0.003201799 : ℝ)
        + (0.03125 : ℝ) * (-0.0036474786 : ℝ)
        + (0.03125 : ℝ) * (-0.0038365288 : ℝ)
        + (0.03125 : ℝ) * (-0.0038264987 : ℝ)
        + (0.03125 : ℝ) * (-0.0036689332 : ℝ)
        + (0.03125 : ℝ) * (-0.0034087217 : ℝ)
        + (0.03125 : ℝ) * (-0.003083823 : ℝ)
        + (0.03125 : ℝ) * (-0.0027253157 : ℝ)
        + (0.03125 : ℝ) * (-0.0023577174 : ℝ)
        + (0.03125 : ℝ) * (-0.0019995097 : ℝ)
        + (0.03125 : ℝ) * (-0.0016638097 : ℝ)
        + (0.03125 : ℝ) * (-0.001359128 : ℝ)
        + (0.03125 : ℝ) * (-0.0010901622 : ℝ)
        + (0.03125 : ℝ) * (-0.0008605336 : ℝ)
        + (0.03125 : ℝ) * (-0.0006720421 : ℝ)
        + (0.03125 : ℝ) * (-0.0005153941 : ℝ)
        + (0.03125 : ℝ) * (-0.000387689 : ℝ)
        + (0.03125 : ℝ) * (-0.0002858127 : ℝ)
        + (0.03125 : ℝ) * (-0.0002062751 : ℝ)
        + (0.03125 : ℝ) * (-0.0001455176 : ℝ)
        + (0.03125 : ℝ) * (-0.0001001339 : ℝ)
        + (0.03125 : ℝ) * (-0.0000670178 : ℝ)
        + (0.03125 : ℝ) * (-0.0000434463 : ℝ)
        + (0.03125 : ℝ) * (-0.0000271144 : ℝ)
        + (0.03125 : ℝ) * (-0.000016132 : ℝ)
        + (0.03125 : ℝ) * (-0.0000089954 : ℝ)
        + (0.03125 : ℝ) * (-0.0000045432 : ℝ)
        + (0.03125 : ℝ) * (-0.0000019049 : ℝ)
        + (0.03125 : ℝ) * (-0.0000004476 : ℝ)
        + (0.03125 : ℝ) * (0.0000001781 : ℝ)
        + (0.03125 : ℝ) * (0.0000003604 : ℝ)
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
    have hnum : (2643610271 / 160000000000 : ℝ)
      = (0.03125 : ℝ) * (0.0871153865 : ℝ)
        + (0.03125 : ℝ) * (0.0790455691 : ℝ)
        + (0.03125 : ℝ) * (0.0707296404 : ℝ)
        + (0.03125 : ℝ) * (0.0623830018 : ℝ)
        + (0.03125 : ℝ) * (0.0541938965 : ℝ)
        + (0.03125 : ℝ) * (0.0463216309 : ℝ)
        + (0.03125 : ℝ) * (0.0388957917 : ℝ)
        + (0.03125 : ℝ) * (0.0320163989 : ℝ)
        + (0.03125 : ℝ) * (0.0257549092 : ℝ)
        + (0.03125 : ℝ) * (0.0201559597 : ℝ)
        + (0.03125 : ℝ) * (0.0152397251 : ℝ)
        + (0.03125 : ℝ) * (0.011004749 : ℝ)
        + (0.03125 : ℝ) * (0.0074311056 : ℝ)
        + (0.03125 : ℝ) * (0.004483747 : ℝ)
        + (0.03125 : ℝ) * (0.0021158993 : ℝ)
        + (0.03125 : ℝ) * (0.00027238 : ℝ)
        + (0.03125 : ℝ) * (-0.000931152 : ℝ)
        + (0.03125 : ℝ) * (-0.0017449266 : ℝ)
        + (0.03125 : ℝ) * (-0.0022683493 : ℝ)
        + (0.03125 : ℝ) * (-0.0025559782 : ℝ)
        + (0.03125 : ℝ) * (-0.002658279 : ℝ)
        + (0.03125 : ℝ) * (-0.0026206303 : ℝ)
        + (0.03125 : ℝ) * (-0.0024827072 : ℝ)
        + (0.03125 : ℝ) * (-0.0022782066 : ℝ)
        + (0.03125 : ℝ) * (-0.0020348666 : ℝ)
        + (0.03125 : ℝ) * (-0.0017747286 : ℝ)
        + (0.03125 : ℝ) * (-0.0015145846 : ℝ)
        + (0.03125 : ℝ) * (-0.0012665557 : ℝ)
        + (0.03125 : ℝ) * (-0.0010387468 : ℝ)
        + (0.03125 : ℝ) * (-0.0008359338 : ℝ)
        + (0.03125 : ℝ) * (-0.0006591715 : ℝ)
        + (0.03125 : ℝ) * (-0.0005054654 : ℝ)
        + (0.03125 : ℝ) * (-0.0003801768 : ℝ)
        + (0.03125 : ℝ) * (-0.0002802424 : ℝ)
        + (0.03125 : ℝ) * (-0.000202232 : ℝ)
        + (0.03125 : ℝ) * (-0.0001426491 : ℝ)
        + (0.03125 : ℝ) * (-0.0000981489 : ℝ)
        + (0.03125 : ℝ) * (-0.0000656818 : ℝ)
        + (0.03125 : ℝ) * (-0.0000425753 : ℝ)
        + (0.03125 : ℝ) * (-0.0000265678 : ℝ)
        + (0.03125 : ℝ) * (-0.0000158049 : ℝ)
        + (0.03125 : ℝ) * (-0.0000088119 : ℝ)
        + (0.03125 : ℝ) * (-0.0000044499 : ℝ)
        + (0.03125 : ℝ) * (-0.0000018654 : ℝ)
        + (0.03125 : ℝ) * (-0.000000438 : ℝ)
        + (0.03125 : ℝ) * (0.0000004075 : ℝ)
        + (0.03125 : ℝ) * (0.0000008463 : ℝ)
        + (0.03125 : ℝ) * (0.0000009361 : ℝ)
    := by norm_num
    rw [hnum]
    linarith [b00.2, b01.2, b02.2, b03.2, b04.2, b05.2, b06.2, b07.2, b08.2, b09.2, b10.2, b11.2, b12.2, b13.2, b14.2, b15.2, b16.2, b17.2, b18.2, b19.2, b20.2, b21.2, b22.2, b23.2, b24.2, b25.2, b26.2, b27.2, b28.2, b29.2, b30.2, b31.2, b32.2, b33.2, b34.2, b35.2, b36.2, b37.2, b38.2, b39.2, b40.2, b41.2, b42.2, b43.2, b44.2, b45.2, b46.2, b47.2]

/-! ## §3 — Headline MINUS enclosure on `[0, 3/2]` -/

theorem imLambda0_threehalves_lb_ub :
    (6068773 / 320000000000 : ℝ)
      ≤ (∫ u in (0 : ℝ)..(3/2 : ℝ), nodeR_fourier_minus_at_c53_8_N3 u)
    ∧ (∫ u in (0 : ℝ)..(3/2 : ℝ), nodeR_fourier_minus_at_c53_8_N3 u)
      ≤ (15151373 / 8000000000 : ℝ) := by
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
    have hnum : (6068773 / 320000000000 : ℝ)
      = (0.03125 : ℝ) * (-0.0004239393 : ℝ)
        + (0.03125 : ℝ) * (-0.0006720092 : ℝ)
        + (0.03125 : ℝ) * (-0.0007783854 : ℝ)
        + (0.03125 : ℝ) * (-0.0007754984 : ℝ)
        + (0.03125 : ℝ) * (-0.0006931565 : ℝ)
        + (0.03125 : ℝ) * (-0.0005578945 : ℝ)
        + (0.03125 : ℝ) * (-0.0003925449 : ℝ)
        + (0.03125 : ℝ) * (-0.0002160207 : ℝ)
        + (0.03125 : ℝ) * (-0.0000432904 : ℝ)
        + (0.03125 : ℝ) * (0.0001068472 : ℝ)
        + (0.03125 : ℝ) * (0.000236419 : ℝ)
        + (0.03125 : ℝ) * (0.0003432058 : ℝ)
        + (0.03125 : ℝ) * (0.0004242045 : ℝ)
        + (0.03125 : ℝ) * (0.0004787269 : ℝ)
        + (0.03125 : ℝ) * (0.0005079187 : ℝ)
        + (0.03125 : ℝ) * (0.000512489 : ℝ)
        + (0.03125 : ℝ) * (0.0004941044 : ℝ)
        + (0.03125 : ℝ) * (0.0004607802 : ℝ)
        + (0.03125 : ℝ) * (0.0004168417 : ℝ)
        + (0.03125 : ℝ) * (0.0003663543 : ℝ)
        + (0.03125 : ℝ) * (0.0003129312 : ℝ)
        + (0.03125 : ℝ) * (0.0002596099 : ℝ)
        + (0.03125 : ℝ) * (0.0002087917 : ℝ)
        + (0.03125 : ℝ) * (0.000162233 : ℝ)
        + (0.03125 : ℝ) * (0.0001210802 : ℝ)
        + (0.03125 : ℝ) * (0.0000859355 : ℝ)
        + (0.03125 : ℝ) * (0.000056943 : ℝ)
        + (0.03125 : ℝ) * (0.000033885 : ℝ)
        + (0.03125 : ℝ) * (0.0000162799 : ℝ)
        + (0.03125 : ℝ) * (0.0000034745 : ℝ)
        + (0.03125 : ℝ) * (-0.000018733 : ℝ)
        + (0.03125 : ℝ) * (-0.0000380511 : ℝ)
        + (0.03125 : ℝ) * (-0.0000483342 : ℝ)
        + (0.03125 : ℝ) * (-0.0000519989 : ℝ)
        + (0.03125 : ℝ) * (-0.0000510806 : ℝ)
        + (0.03125 : ℝ) * (-0.00004723 : ℝ)
        + (0.03125 : ℝ) * (-0.000041732 : ℝ)
        + (0.03125 : ℝ) * (-0.0000355416 : ℝ)
        + (0.03125 : ℝ) * (-0.0000293285 : ℝ)
        + (0.03125 : ℝ) * (-0.0000235275 : ℝ)
        + (0.03125 : ℝ) * (-0.0000183882 : ℝ)
        + (0.03125 : ℝ) * (-0.0000140214 : ℝ)
        + (0.03125 : ℝ) * (-0.0000104401 : ℝ)
        + (0.03125 : ℝ) * (-0.0000075942 : ℝ)
        + (0.03125 : ℝ) * (-0.0000053976 : ℝ)
        + (0.03125 : ℝ) * (-0.0000037526 : ℝ)
        + (0.03125 : ℝ) * (-0.0000025686 : ℝ)
        + (0.03125 : ℝ) * (-0.0000017189 : ℝ)
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
    have hnum : (15151373 / 8000000000 : ℝ)
      = (0.03125 : ℝ) * (0.0004942637 : ℝ)
        + (0.03125 : ℝ) * (0.0010414673 : ℝ)
        + (0.03125 : ℝ) * (0.0016037455 : ℝ)
        + (0.03125 : ℝ) * (0.002148144 : ℝ)
        + (0.03125 : ℝ) * (0.0026473037 : ℝ)
        + (0.03125 : ℝ) * (0.0030798418 : ℝ)
        + (0.03125 : ℝ) * (0.0034304429 : ℝ)
        + (0.03125 : ℝ) * (0.0036896872 : ℝ)
        + (0.03125 : ℝ) * (0.0038536501 : ℝ)
        + (0.03125 : ℝ) * (0.0039233155 : ℝ)
        + (0.03125 : ℝ) * (0.0039038479 : ℝ)
        + (0.03125 : ℝ) * (0.0038037744 : ℝ)
        + (0.03125 : ℝ) * (0.0036341211 : ℝ)
        + (0.03125 : ℝ) * (0.0034075519 : ℝ)
        + (0.03125 : ℝ) * (0.0031375481 : ℝ)
        + (0.03125 : ℝ) * (0.0028480572 : ℝ)
        + (0.03125 : ℝ) * (0.002557212 : ℝ)
        + (0.03125 : ℝ) * (0.0022557671 : ℝ)
        + (0.03125 : ℝ) * (0.0019540129 : ℝ)
        + (0.03125 : ℝ) * (0.0016611366 : ℝ)
        + (0.03125 : ℝ) * (0.0013845739 : ℝ)
        + (0.03125 : ℝ) * (0.001129942 : ℝ)
        + (0.03125 : ℝ) * (0.0009010759 : ℝ)
        + (0.03125 : ℝ) * (0.0007001493 : ℝ)
        + (0.03125 : ℝ) * (0.0005278616 : ℝ)
        + (0.03125 : ℝ) * (0.0003836687 : ℝ)
        + (0.03125 : ℝ) * (0.0002660375 : ℝ)
        + (0.03125 : ℝ) * (0.0001727063 : ℝ)
        + (0.03125 : ℝ) * (0.000100935 : ℝ)
        + (0.03125 : ℝ) * (0.0000477314 : ℝ)
        + (0.03125 : ℝ) * (0.0000100469 : ℝ)
        + (0.03125 : ℝ) * (-0.0000042488 : ℝ)
        + (0.03125 : ℝ) * (-0.000008555 : ℝ)
        + (0.03125 : ℝ) * (-0.0000107523 : ℝ)
        + (0.03125 : ℝ) * (-0.0000114257 : ℝ)
        + (0.03125 : ℝ) * (-0.0000110676 : ℝ)
        + (0.03125 : ℝ) * (-0.0000100742 : ℝ)
        + (0.03125 : ℝ) * (-0.0000087491 : ℝ)
        + (0.03125 : ℝ) * (-0.0000073122 : ℝ)
        + (0.03125 : ℝ) * (-0.0000059121 : ℝ)
        + (0.03125 : ℝ) * (-0.0000046398 : ℝ)
        + (0.03125 : ℝ) * (-0.0000035421 : ℝ)
        + (0.03125 : ℝ) * (-0.000002634 : ℝ)
        + (0.03125 : ℝ) * (-0.0000019097 : ℝ)
        + (0.03125 : ℝ) * (-0.0000013505 : ℝ)
        + (0.03125 : ℝ) * (-0.0000009316 : ℝ)
        + (0.03125 : ℝ) * (-0.0000006203 : ℝ)
        + (0.03125 : ℝ) * (-0.0000004024 : ℝ)
    := by norm_num
    rw [hnum]
    linarith [b00.2, b01.2, b02.2, b03.2, b04.2, b05.2, b06.2, b07.2, b08.2, b09.2, b10.2, b11.2, b12.2, b13.2, b14.2, b15.2, b16.2, b17.2, b18.2, b19.2, b20.2, b21.2, b22.2, b23.2, b24.2, b25.2, b26.2, b27.2, b28.2, b29.2, b30.2, b31.2, b32.2, b33.2, b34.2, b35.2, b36.2, b37.2, b38.2, b39.2, b40.2, b41.2, b42.2, b43.2, b44.2, b45.2, b46.2, b47.2]

/-! ## §Axiom check -/

#print axioms reLambda0_threehalves_lb_ub
#print axioms imLambda0_threehalves_lb_ub

end Assemble_threehalves
end FourierPanels_c53_8
end PrincipiaTractalis
