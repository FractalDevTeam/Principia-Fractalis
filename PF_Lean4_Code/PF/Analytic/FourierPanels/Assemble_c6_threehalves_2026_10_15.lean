/-
# PF.Analytic.FourierPanels.Assemble_c6_threehalves_2026_10_15

**M2.5 assembly** — combines the 48 per-panel integral bounds from
`Seg01Range`, `Seg02Range`, `Seg03Range`, `Seg04Range`, `Seg05Range`,
`Seg06Range` (u ∈ [0, 3/2], 6 segments × 8 panels of width 1/32) into
two headline [0, 3/2]-integral enclosures:

  reLambda0_threehalves_lb_ub :
    R_lb ≤ ∫ u in 0..(3/2), nodeR_fourier_plus_at_c6_N3  u ≤ R_ub

  imLambda0_threehalves_lb_ub :
    I_lb ≤ ∫ u in 0..(3/2), nodeR_fourier_minus_at_c6_N3 u ≤ I_ub

where (as EXACT rationals, computed from the generator's 10-digit
width·bound products):

  R_lb = 4586915733/320000000000       ≈ 1.4334·10⁻²
  R_ub = 176282313/10000000000         ≈ 1.7628·10⁻²
  I_lb = 8443581/160000000000          ≈ 5.2772·10⁻⁵
  I_ub = 298154561/160000000000        ≈ 1.8635·10⁻³

Composition is purely integration-additivity:

  ∫_0^{3/2} f = Σ_{k=0..47} ∫_{a_k}^{b_k} f    with  a_k = k/32.

We chain `intervalIntegral.integral_add_adjacent_intervals` 47 times.

Three-axiom bar: every top-level declaration prints
`[propext, Classical.choice, Quot.sound]`.  No sorry, no native_decide,
no `interval` tactic, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-15.
-/
import PF.Analytic.FourierPanels.Seg01Range_c6_2026_10_15
import PF.Analytic.FourierPanels.Seg02Range_c6_2026_10_15
import PF.Analytic.FourierPanels.Seg03Range_c6_2026_10_15
import PF.Analytic.FourierPanels.Seg04Range_c6_2026_10_15
import PF.Analytic.FourierPanels.Seg05Range_c6_2026_10_15
import PF.Analytic.FourierPanels.Seg06Range_c6_2026_10_15

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace PrincipiaTractalis
namespace FourierPanels_c6
namespace Assemble_threehalves

open MeasureTheory
open PrincipiaTractalis.FourierPanels_c6

/-! ## §1 — Local notation -/

private noncomputable abbrev fP : ℝ → ℝ := nodeR_fourier_plus_at_c6_N3
private noncomputable abbrev fM : ℝ → ℝ := nodeR_fourier_minus_at_c6_N3

private theorem iiP (a b : ℝ) : IntervalIntegrable fP MeasureTheory.volume a b :=
  Seg01Range.nodeR_fourier_plus_at_c6_N3_intervalIntegrable a b

private theorem iiM (a b : ℝ) : IntervalIntegrable fM MeasureTheory.volume a b :=
  Seg01Range.nodeR_fourier_minus_at_c6_N3_intervalIntegrable a b

/-! ## §2 — Headline PLUS enclosure on `[0, 3/2]` -/

theorem reLambda0_threehalves_lb_ub :
    (4586915733 / 320000000000 : ℝ)
      ≤ (∫ u in (0 : ℝ)..(3/2 : ℝ), nodeR_fourier_plus_at_c6_N3 u)
    ∧ (∫ u in (0 : ℝ)..(3/2 : ℝ), nodeR_fourier_plus_at_c6_N3 u)
      ≤ (176282313 / 10000000000 : ℝ) := by
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
    have hnum : (4586915733 / 320000000000 : ℝ)
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
        + (0.03125 : ℝ) * (0.0009017179 : ℝ)
        + (0.03125 : ℝ) * (-0.0002977603 : ℝ)
        + (0.03125 : ℝ) * (-0.0012930006 : ℝ)
        + (0.03125 : ℝ) * (-0.0019753932 : ℝ)
        + (0.03125 : ℝ) * (-0.0023990957 : ℝ)
        + (0.03125 : ℝ) * (-0.0026146771 : ℝ)
        + (0.03125 : ℝ) * (-0.0026681712 : ℝ)
        + (0.03125 : ℝ) * (-0.0026004466 : ℝ)
        + (0.03125 : ℝ) * (-0.0024468717 : ℝ)
        + (0.03125 : ℝ) * (-0.002237239 : ℝ)
        + (0.03125 : ℝ) * (-0.001995911 : ℝ)
        + (0.03125 : ℝ) * (-0.0017421433 : ℝ)
        + (0.03125 : ℝ) * (-0.0014905415 : ℝ)
        + (0.03125 : ℝ) * (-0.0012516072 : ℝ)
        + (0.03125 : ℝ) * (-0.0010323332 : ℝ)
        + (0.03125 : ℝ) * (-0.0008368125 : ℝ)
        + (0.03125 : ℝ) * (-0.0006668303 : ℝ)
        + (0.03125 : ℝ) * (-0.0005224155 : ℝ)
        + (0.03125 : ℝ) * (-0.0004027596 : ℝ)
        + (0.03125 : ℝ) * (-0.0003071908 : ℝ)
        + (0.03125 : ℝ) * (-0.0002304655 : ℝ)
        + (0.03125 : ℝ) * (-0.0001698055 : ℝ)
        + (0.03125 : ℝ) * (-0.0001227941 : ℝ)
        + (0.03125 : ℝ) * (-0.000087082 : ℝ)
        + (0.03125 : ℝ) * (-0.000060498 : ℝ)
        + (0.03125 : ℝ) * (-0.0000411167 : ℝ)
        + (0.03125 : ℝ) * (-0.0000272885 : ℝ)
        + (0.03125 : ℝ) * (-0.0000176436 : ℝ)
        + (0.03125 : ℝ) * (-0.000011077 : ℝ)
        + (0.03125 : ℝ) * (-0.0000067216 : ℝ)
        + (0.03125 : ℝ) * (-0.0000039147 : ℝ)
        + (0.03125 : ℝ) * (-0.0000021639 : ℝ)
        + (0.03125 : ℝ) * (-0.0000011126 : ℝ)
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
    have hnum : (176282313 / 10000000000 : ℝ)
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
        + (0.03125 : ℝ) * (0.0024703615 : ℝ)
        + (0.03125 : ℝ) * (0.0009176996 : ℝ)
        + (0.03125 : ℝ) * (-0.0002132002 : ℝ)
        + (0.03125 : ℝ) * (-0.0009160402 : ℝ)
        + (0.03125 : ℝ) * (-0.0013842608 : ℝ)
        + (0.03125 : ℝ) * (-0.0016623009 : ℝ)
        + (0.03125 : ℝ) * (-0.0017906975 : ℝ)
        + (0.03125 : ℝ) * (-0.0018055078 : ℝ)
        + (0.03125 : ℝ) * (-0.0017379988 : ℝ)
        + (0.03125 : ℝ) * (-0.001614573 : ℝ)
        + (0.03125 : ℝ) * (-0.0014568925 : ℝ)
        + (0.03125 : ℝ) * (-0.0012821622 : ℝ)
        + (0.03125 : ℝ) * (-0.0011035312 : ℝ)
        + (0.03125 : ℝ) * (-0.0009305723 : ℝ)
        + (0.03125 : ℝ) * (-0.0007698029 : ℝ)
        + (0.03125 : ℝ) * (-0.0006252169 : ℝ)
        + (0.03125 : ℝ) * (-0.000498799 : ℝ)
        + (0.03125 : ℝ) * (-0.0003910028 : ℝ)
        + (0.03125 : ℝ) * (-0.0003011766 : ℝ)
        + (0.03125 : ℝ) * (-0.0002259483 : ℝ)
        + (0.03125 : ℝ) * (-0.0001664582 : ℝ)
        + (0.03125 : ℝ) * (-0.00012036 : ℝ)
        + (0.03125 : ℝ) * (-0.0000853461 : ℝ)
        + (0.03125 : ℝ) * (-0.0000592854 : ℝ)
        + (0.03125 : ℝ) * (-0.000040288 : ℝ)
        + (0.03125 : ℝ) * (-0.0000267354 : ℝ)
        + (0.03125 : ℝ) * (-0.000017284 : ℝ)
        + (0.03125 : ℝ) * (-0.00001085 : ℝ)
        + (0.03125 : ℝ) * (-0.0000065829 : ℝ)
        + (0.03125 : ℝ) * (-0.0000038334 : ℝ)
        + (0.03125 : ℝ) * (-0.0000021186 : ℝ)
        + (0.03125 : ℝ) * (-0.000001089 : ℝ)
        + (0.03125 : ℝ) * (-0.0000004991 : ℝ)
    := by norm_num
    rw [hnum]
    linarith [b00.2, b01.2, b02.2, b03.2, b04.2, b05.2, b06.2, b07.2, b08.2, b09.2, b10.2, b11.2, b12.2, b13.2, b14.2, b15.2, b16.2, b17.2, b18.2, b19.2, b20.2, b21.2, b22.2, b23.2, b24.2, b25.2, b26.2, b27.2, b28.2, b29.2, b30.2, b31.2, b32.2, b33.2, b34.2, b35.2, b36.2, b37.2, b38.2, b39.2, b40.2, b41.2, b42.2, b43.2, b44.2, b45.2, b46.2, b47.2]

/-! ## §3 — Headline MINUS enclosure on `[0, 3/2]` -/

theorem imLambda0_threehalves_lb_ub :
    (8443581 / 160000000000 : ℝ)
      ≤ (∫ u in (0 : ℝ)..(3/2 : ℝ), nodeR_fourier_minus_at_c6_N3 u)
    ∧ (∫ u in (0 : ℝ)..(3/2 : ℝ), nodeR_fourier_minus_at_c6_N3 u)
      ≤ (298154561 / 160000000000 : ℝ) := by
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
    have hnum : (8443581 / 160000000000 : ℝ)
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
        + (0.03125 : ℝ) * (0.0005074183 : ℝ)
        + (0.03125 : ℝ) * (0.0005017995 : ℝ)
        + (0.03125 : ℝ) * (0.000477944 : ℝ)
        + (0.03125 : ℝ) * (0.000441838 : ℝ)
        + (0.03125 : ℝ) * (0.0003981861 : ℝ)
        + (0.03125 : ℝ) * (0.0003502556 : ℝ)
        + (0.03125 : ℝ) * (0.0003008829 : ℝ)
        + (0.03125 : ℝ) * (0.0002524028 : ℝ)
        + (0.03125 : ℝ) * (0.0002066226 : ℝ)
        + (0.03125 : ℝ) * (0.0001648325 : ℝ)
        + (0.03125 : ℝ) * (0.0001278453 : ℝ)
        + (0.03125 : ℝ) * (0.0000960561 : ℝ)
        + (0.03125 : ℝ) * (0.0000695136 : ℝ)
        + (0.03125 : ℝ) * (0.0000479973 : ℝ)
        + (0.03125 : ℝ) * (0.0000310928 : ℝ)
        + (0.03125 : ℝ) * (0.0000182619 : ℝ)
        + (0.03125 : ℝ) * (0.0000089039 : ℝ)
        + (0.03125 : ℝ) * (0.0000024055 : ℝ)
        + (0.03125 : ℝ) * (-0.000006467 : ℝ)
        + (0.03125 : ℝ) * (-0.0000153555 : ℝ)
        + (0.03125 : ℝ) * (-0.0000197837 : ℝ)
        + (0.03125 : ℝ) * (-0.000021107 : ℝ)
        + (0.03125 : ℝ) * (-0.0000204028 : ℝ)
        + (0.03125 : ℝ) * (-0.0000184958 : ℝ)
        + (0.03125 : ℝ) * (-0.0000159909 : ℝ)
        + (0.03125 : ℝ) * (-0.000013309 : ℝ)
        + (0.03125 : ℝ) * (-0.0000107237 : ℝ)
        + (0.03125 : ℝ) * (-0.0000083953 : ℝ)
        + (0.03125 : ℝ) * (-0.0000064008 : ℝ)
        + (0.03125 : ℝ) * (-0.0000047602 : ℝ)
        + (0.03125 : ℝ) * (-0.0000034565 : ℝ)
        + (0.03125 : ℝ) * (-0.0000024521 : ℝ)
        + (0.03125 : ℝ) * (-0.0000017001 : ℝ)
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
    have hnum : (298154561 / 160000000000 : ℝ)
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
        + (0.03125 : ℝ) * (0.0028409228 : ℝ)
        + (0.03125 : ℝ) * (0.0025665773 : ℝ)
        + (0.03125 : ℝ) * (0.0022960463 : ℝ)
        + (0.03125 : ℝ) * (0.0020267989 : ℝ)
        + (0.03125 : ℝ) * (0.001760748 : ℝ)
        + (0.03125 : ℝ) * (0.0015048764 : ℝ)
        + (0.03125 : ℝ) * (0.0012647141 : ℝ)
        + (0.03125 : ℝ) * (0.0010443295 : ℝ)
        + (0.03125 : ℝ) * (0.0008463922 : ℝ)
        + (0.03125 : ℝ) * (0.0006722932 : ℝ)
        + (0.03125 : ℝ) * (0.000522307 : ℝ)
        + (0.03125 : ℝ) * (0.0003957806 : ℝ)
        + (0.03125 : ℝ) * (0.0002913345 : ℝ)
        + (0.03125 : ℝ) * (0.0002070631 : ℝ)
        + (0.03125 : ℝ) * (0.0001407234 : ℝ)
        + (0.03125 : ℝ) * (0.0000899039 : ℝ)
        + (0.03125 : ℝ) * (0.0000521683 : ℝ)
        + (0.03125 : ℝ) * (0.0000251703 : ℝ)
        + (0.03125 : ℝ) * (0.0000067394 : ℝ)
        + (0.03125 : ℝ) * (-0.0000014208 : ℝ)
        + (0.03125 : ℝ) * (-0.0000033269 : ℝ)
        + (0.03125 : ℝ) * (-0.0000042198 : ℝ)
        + (0.03125 : ℝ) * (-0.000004425 : ℝ)
        + (0.03125 : ℝ) * (-0.0000041975 : ℝ)
        + (0.03125 : ℝ) * (-0.0000037284 : ℝ)
        + (0.03125 : ℝ) * (-0.0000031534 : ℝ)
        + (0.03125 : ℝ) * (-0.0000025636 : ℝ)
        + (0.03125 : ℝ) * (-0.0000020145 : ℝ)
        + (0.03125 : ℝ) * (-0.0000015357 : ℝ)
        + (0.03125 : ℝ) * (-0.0000011383 : ℝ)
        + (0.03125 : ℝ) * (-0.0000008216 : ℝ)
        + (0.03125 : ℝ) * (-0.0000005781 : ℝ)
        + (0.03125 : ℝ) * (-0.0000003967 : ℝ)
    := by norm_num
    rw [hnum]
    linarith [b00.2, b01.2, b02.2, b03.2, b04.2, b05.2, b06.2, b07.2, b08.2, b09.2, b10.2, b11.2, b12.2, b13.2, b14.2, b15.2, b16.2, b17.2, b18.2, b19.2, b20.2, b21.2, b22.2, b23.2, b24.2, b25.2, b26.2, b27.2, b28.2, b29.2, b30.2, b31.2, b32.2, b33.2, b34.2, b35.2, b36.2, b37.2, b38.2, b39.2, b40.2, b41.2, b42.2, b43.2, b44.2, b45.2, b46.2, b47.2]

/-! ## §Axiom check -/

#print axioms reLambda0_threehalves_lb_ub
#print axioms imLambda0_threehalves_lb_ub

end Assemble_threehalves
end FourierPanels_c6
end PrincipiaTractalis

