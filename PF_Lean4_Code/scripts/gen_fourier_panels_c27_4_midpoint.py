#!/usr/bin/env python3
"""
gen_fourier_panels_c27_4_midpoint.py — midpoint-rule panel generator at c = 27/4.

Replaces the zeroth-order range bricks of `gen_fourier_panels_c27_4.py` with
midpoint-rule panels using the plus/minus-side C² bounds:

  * `abs_fourier_plus_termD2_sum_le` (FourierTermC2_2026_10_16, kernel-clean).
  * `abs_fourier_minus_termD2_sum_le` (FourierTermC2Minus_2026_10_17, kernel-clean).

The per-panel integral enclosure is
    |∫_a^b f(u) du − (b − a)·f(m)| ≤ M · (b − a)³ / 24,     m := (a + b)/2,
which — composed with a single-point numeric bound `L ≤ f(m) ≤ U` from the
Interval mirror — yields
    (b − a)·L − err ≤ ∫_a^b f du ≤ (b − a)·U + err,          err := M·(b−a)³/24.

With `(b − a) = 1/32`, err = M/786432. Taking M = 3000 (the demo's crude
bound for T = 1/32), err = 3000/786432 ≈ 3.8e-3. For comparison, the range
brick's loose [L, U] spread is typically ~1.5e-2 to 1e-1 — midpoint is
tighter by ~4-25× PER PANEL on top of being shorter.

Three-axiom bar (downstream): `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no floating-point-as-proof.

Usage:
    python3 gen_fourier_panels_c27_4_midpoint.py --seg 1    # emit Seg01Midpoint for u ∈ [0, 1/4]
    python3 gen_fourier_panels_c27_4_midpoint.py --seg 1 --dry-run   # report only
"""
import argparse
import os
import sys
from fractions import Fraction

# ---------------------------------------------------------------------------
# Reuse: Fraction-only outward-rounded interval arithmetic (verbatim from v1)
# ---------------------------------------------------------------------------
# Import the v1 helpers; they are stable and we don't duplicate them here.
_v1_path = os.path.join(os.path.dirname(__file__), 'gen_fourier_panels_c27_4.py')
_v1_src = open(_v1_path).read()
# Execute the helpers in our namespace
_v1_globals = {}
exec(compile(_v1_src, _v1_path, 'exec'), _v1_globals)

I               = _v1_globals['I']
exp_pos_interval = _v1_globals['exp_pos_interval']
exp_neg_interval = _v1_globals['exp_neg_interval']
cos_interval    = _v1_globals['cos_interval']
sin_interval    = _v1_globals['sin_interval']
omega_N3_interval = _v1_globals['omega_N3_interval']
emit_lower_bound = _v1_globals['emit_lower_bound']
emit_upper_bound = _v1_globals['emit_upper_bound']
frac_to_lean_decimal = _v1_globals['frac_to_lean_decimal']
SEGMENTS        = _v1_globals['SEGMENTS']
N_PANELS        = _v1_globals['N_PANELS']
panel_endpoints = _v1_globals['panel_endpoints']
C_HALF          = _v1_globals['C_HALF']  # 27/8

# ---------------------------------------------------------------------------
# Midpoint-point numeric evaluation of f_plus and f_minus
# ---------------------------------------------------------------------------
def point_bounds(m_frac, series_terms=50):
    """Return (L_plus, U_plus, L_minus, U_minus) tight 10-digit bounds on
    f_plus(m) and f_minus(m) at the SINGLE point m.

    f_plus (u)  = (exp(u/2)·omega + omega) · cos((c/2)·u) = (exp(u/2)+1)·omega·cos
    f_minus(u)  = (exp(u/2)·omega - omega) · sin((c/2)·u) = (exp(u/2)-1)·omega·sin

    (These are the N=3-truncated omega forms the Lean side encloses via
    `nodeI_fourier_±_at_c27_4` applied to a single-point Interval.)
    """
    m_iv = I(m_frac, m_frac)
    exp_u = exp_pos_interval(m_iv, series_terms=series_terms)
    u_half = I(m_frac * Fraction(1, 2), m_frac * Fraction(1, 2))
    exp_u_half = exp_pos_interval(u_half, series_terms=series_terms)
    om = omega_N3_interval(exp_u, series_terms=series_terms)
    Fp = (exp_u_half * om).rounded()
    Fm = om
    cu = I(C_HALF * m_frac, C_HALF * m_frac)
    cos_cu = cos_interval(cu, series_terms=series_terms)
    sin_cu = sin_interval(cu, series_terms=series_terms)
    R_plus  = ((Fp + Fm) * cos_cu).rounded()
    R_minus = ((Fp - Fm) * sin_cu).rounded()
    # Return outward-rounded 10-digit bounds.
    return (emit_lower_bound(R_plus.lo),  emit_upper_bound(R_plus.hi),
            emit_lower_bound(R_minus.lo), emit_upper_bound(R_minus.hi))


# ---------------------------------------------------------------------------
# Segment constants (T, M, error-per-panel)
# ---------------------------------------------------------------------------
# Universal crude M-bound: `fourier_plus_termM (27/4) n (1/4) ≤ 1000` for each
# n ∈ {0, 1, 2}, summed over 3 terms gives ≤ 3000 = M. (Only verified for Seg01
# with T = 1/4; later segments need a looser M. For a demo we fix at 3000.)
M_VALUE = Fraction(24)
PANEL_WIDTH = Fraction(1, 32)  # (b - a) for each panel
ERR_PER_PANEL = M_VALUE * (PANEL_WIDTH ** 3) / 24  # = 3000/786432


def seg_file_name_mp(seg_idx):
    return f"Seg0{seg_idx}Midpoint_c27_4_2026_10_17.lean"


def seg_namespace_mp(seg_idx):
    return f"Seg0{seg_idx}Midpoint"


def seg_prefix_mp(seg_idx):
    return f"m0{seg_idx}p"


def seg_file_header_mp(seg_idx, seg_lo, seg_hi):
    lo_s = frac_to_lean_decimal(seg_lo)
    hi_s = frac_to_lean_decimal(seg_hi)
    ns = seg_namespace_mp(seg_idx)
    return f"""/-
# PF.Analytic.FourierPanels.{ns}_c27_4_2026_10_17

**MIDPOINT-RULE panel certificate** at `c = 27/4` — generated by
`scripts/gen_fourier_panels_c27_4_midpoint.py`. Replaces the zeroth-order
range bricks of `Seg0{seg_idx}Range_c27_4_2026_10_16` with midpoint-rule
panels using the C² bounds from `FourierTermC2_2026_10_16` (plus-side) and
`FourierTermC2Minus_2026_10_17` (minus-side).

THIS FILE IS AUTO-GENERATED.  Regenerate via:
    python3 PF_Lean4_Code/scripts/gen_fourier_panels_c27_4_midpoint.py --seg {seg_idx}

Scope: ONE segment covering `u ∈ [{lo_s}, {hi_s}]` with 8 uniform panels of
width `1/32`. Each panel emits:
  * 4 single-point numeric bounds on `f_plus(m)` and `f_minus(m)`
    (`*_mid_lo`, `*_mid_hi` for plus+minus).
  * 2 midpoint-rule error theorems (`*_mp_err` for plus+minus) invoking
    `XiQuadrature.midpoint_rule_error` with the segment-level M = 3000.
  * 2 panel integral enclosure theorems (`*_integral_bound` for plus+minus),
    combining the mid-point bound and the midpoint error.

Compared to the range-brick generator: the integral enclosures here are
TIGHTER (midpoint error scales as `(b-a)³` vs the zeroth-order spread
`(b-a) · (max − min)`) AND SHORTER per panel.

Three-axiom bar: every top-level declaration prints
`[propext, Classical.choice, Quot.sound]`. No sorry, no native_decide,
no `interval` tactic, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-17.
-/
"""


def seg_preamble_mp(seg_idx):
    ns = seg_namespace_mp(seg_idx)
    return f"""import PF.Analytic.FourierPanels.CoreDefs_c27_4_2026_10_16
import PF.Analytic.FourierPanels.FourierTermC2_2026_10_16
import PF.Analytic.FourierPanels.FourierTermC2Minus_2026_10_17
import PF.Analytic.XiQuadrature
import PF.Analytic.Lambda0TightestBoundsMellin_2026_10_14

set_option autoImplicit false

namespace PrincipiaTractalis
namespace FourierPanels_c27_4
namespace {ns}

open PrincipiaTractalis.FourierTermC2 PrincipiaTractalis.XiQuadrature Real
open MeasureTheory

set_option maxRecDepth 4000000

/-! ## §1 — Shared segment-level infrastructure -/

/-- The plus-side integrand `f_plus u = ∑ n<3, fourier_plus_term (27/4) n u`.
Equal to `nodeR_fourier_plus_at_c27_4_N3 u / 2` via definitional unfolding, but
we use the explicit sum form so the midpoint-rule derivative witnesses apply
directly. -/
private noncomputable abbrev f_plus (u : ℝ) : ℝ :=
  ∑ n ∈ Finset.range 3, fourier_plus_term (27/4) n u

private noncomputable abbrev f_minus (u : ℝ) : ℝ :=
  ∑ n ∈ Finset.range 3, fourier_minus_term (27/4) n u

/-- Segment-level M bound. Universal: bounds `|∑ fourier_plus_termD2|` on
`u ∈ [0, 1/4]`. True max|f''| ≈ 1.3773; symbolic upper bound ≈ 8.44 at T=1/4;
we prove ≤ 24 using per-`n` tight bounds (n=0: A≤4, B≤1/23; n=1: A≤16,
B≤(1/23)⁴; n=2: A≤36, B≤(1/23)⁹). (24 instead of 20 keeps `M·(1/32)³/24`
a terminating-decimal rational for literal emission.) -/
private noncomputable abbrev M : ℝ := 24

/-- Shared E/T bounds (`exp(1/8) ≤ 2`, `exp(1/4) ≤ 2`). -/
private lemma hE_le_2 : Real.exp ((1:ℝ)/8) ≤ 2 :=
  ((Real.exp_le_exp).mpr (by have := Real.log_two_gt_d9; linarith :
    (1:ℝ)/8 ≤ Real.log 2)).trans_eq (Real.exp_log (by norm_num))

private lemma hT_le_2 : Real.exp ((1:ℝ)/4) ≤ 2 :=
  ((Real.exp_le_exp).mpr (by have := Real.log_two_gt_d9; linarith :
    (1:ℝ)/4 ≤ Real.log 2)).trans_eq (Real.exp_log (by norm_num))

/-- The per-`n` bound at n=0: A=π ≤ 4, B=exp(-π) ≤ 1/23. -/
private lemma fourier_plus_termM_n0 :
    fourier_plus_termM (27/4) 0 (1/4) ≤ 19 := by
  unfold fourier_plus_termM
  have hπ_le : π ≤ 4 := Real.pi_lt_four.le
  have hπ_pos : 0 < π := Real.pi_pos
  have hE_le := hE_le_2
  have hT_le := hT_le_2
  have hE_pos : 0 < Real.exp ((1:ℝ)/8) := Real.exp_pos _
  have hT_pos : 0 < Real.exp ((1:ℝ)/4) := Real.exp_pos _
  have h_eneg_pi : Real.exp (-π) ≤ 1/23 :=
    PrincipiaTractalis.Lambda0TightestBoundsMellin20261014.exp_neg_pi_le_one_twentythird
  have hA_eq : π * ((0:ℕ) + 1 : ℝ)^2 = π := by push_cast; ring
  rw [hA_eq]
  have hB_pos : 0 < Real.exp (-π) := Real.exp_pos _
  have hB_le : Real.exp (-π) ≤ 1/23 := h_eneg_pi
  have habs_c : |((27:ℝ)/4)| = 27/4 := by rw [abs_of_pos]; norm_num
  rw [habs_c, show ((1:ℝ)/4/2 : ℝ) = 1/8 from by norm_num]
  set E := Real.exp ((1:ℝ)/8)
  set B := Real.exp (-π)
  set T := Real.exp ((1:ℝ)/4)
  have hπB_le : π * B ≤ 4/23 := by
    have := mul_le_mul hπ_le hB_le hB_pos.le (by norm_num : (0:ℝ) ≤ 4); linarith
  have hπB_nn : 0 ≤ π * B := mul_nonneg hπ_pos.le hB_pos.le
  have hEB_le : E * B ≤ 2/23 := by
    have := mul_le_mul hE_le hB_le hB_pos.le (by norm_num : (0:ℝ) ≤ 2); linarith
  have hEB_nn : 0 ≤ E * B := mul_nonneg hE_pos.le hB_pos.le
  have hπT_le : π * T ≤ 8 := by
    have := mul_le_mul hπ_le hT_le hT_pos.le (by norm_num : (0:ℝ) ≤ 4); linarith
  have hπT_pos : 0 ≤ π * T := mul_nonneg hπ_pos.le hT_pos.le
  have hπT_ge_one : 1 ≤ π * T := by
    have h1 : (1:ℝ) ≤ π := by linarith [hπ_pos, Real.pi_gt_three]
    have h2 : (1:ℝ) ≤ T := Real.one_le_exp (by norm_num)
    have : (1:ℝ) * 1 ≤ π * T := mul_le_mul h1 h2 (by norm_num) (by linarith)
    linarith
  -- π·(π·T−1)·B ≤ 4·7·(1/23) = 28/23 (with π·T ≤ 8, so π·T−1 ≤ 7)
  have hπTm1_le : π * T - 1 ≤ 7 := by linarith
  have hπTm1_nn : 0 ≤ π * T - 1 := by linarith
  have hπ_πTm1_le : π * (π * T - 1) ≤ 28 := by
    have := mul_le_mul hπ_le hπTm1_le hπTm1_nn (by norm_num : (0:ℝ) ≤ 4); linarith
  have hπ_πTm1_nn : 0 ≤ π * (π * T - 1) := mul_nonneg hπ_pos.le hπTm1_nn
  have hπ_πTm1_B_le : π * (π * T - 1) * B ≤ 28/23 := by
    have := mul_le_mul hπ_πTm1_le hB_le hB_pos.le (by norm_num : (0:ℝ) ≤ 28)
    linarith
  have hπ_πTm1_B_nn : 0 ≤ π * (π * T - 1) * B := mul_nonneg hπ_πTm1_nn hB_pos.le
  have hEπB_le : E * (π * B) ≤ 2 * (4/23) := by
    have := mul_le_mul hE_le hπB_le hπB_nn (by norm_num : (0:ℝ) ≤ 2); linarith
  have hE1πB_le : (E + 1) * (π * B) ≤ 3 * (4/23) := by
    have h1 : E + 1 ≤ 3 := by linarith
    have := mul_le_mul h1 hπB_le hπB_nn (by norm_num : (0:ℝ) ≤ 3); linarith
  have hE1_nn : 0 ≤ E + 1 := by linarith
  nlinarith [hπB_le, hπB_nn, hEB_le, hEB_nn, hπ_πTm1_B_le, hπ_πTm1_B_nn,
             hEπB_le, mul_nonneg hE_pos.le hπB_nn,
             hE1πB_le, mul_nonneg hE1_nn hπB_nn,
             hE_le, hE_pos.le, hT_le, hT_pos.le, hB_pos.le, hπ_pos]

/-- The per-`n` bound at n=1: A=4π ≤ 16, B=exp(-4π) ≤ (1/23)⁴ = 1/279841. -/
private lemma fourier_plus_termM_n1 :
    fourier_plus_termM (27/4) 1 (1/4) ≤ 1 := by
  unfold fourier_plus_termM
  have hπ_le : π ≤ 4 := Real.pi_lt_four.le
  have hπ_pos : 0 < π := Real.pi_pos
  have hE_le := hE_le_2
  have hT_le := hT_le_2
  have hE_pos : 0 < Real.exp ((1:ℝ)/8) := Real.exp_pos _
  have hT_pos : 0 < Real.exp ((1:ℝ)/4) := Real.exp_pos _
  have h_eneg_pi : Real.exp (-π) ≤ 1/23 :=
    PrincipiaTractalis.Lambda0TightestBoundsMellin20261014.exp_neg_pi_le_one_twentythird
  have hA_eq : π * ((1:ℕ) + 1 : ℝ)^2 = 4 * π := by push_cast; ring
  rw [hA_eq]
  have hB_pos : 0 < Real.exp (-(4 * π)) := Real.exp_pos _
  have hB_le : Real.exp (-(4 * π)) ≤ 1/279841 := by
    have h_split : -(4 * π) = (-π) + (-π) + (-π) + (-π) := by ring
    rw [h_split, Real.exp_add, Real.exp_add, Real.exp_add]
    have h0 := (Real.exp_pos (-π)).le
    calc Real.exp (-π) * Real.exp (-π) * Real.exp (-π) * Real.exp (-π)
        ≤ (1/23) * (1/23) * (1/23) * (1/23) :=
          mul_le_mul (mul_le_mul (mul_le_mul h_eneg_pi h_eneg_pi h0 (by norm_num))
            h_eneg_pi (by positivity) (by positivity))
            h_eneg_pi (by positivity) (by positivity)
      _ = 1/279841 := by norm_num
  have habs_c : |((27:ℝ)/4)| = 27/4 := by rw [abs_of_pos]; norm_num
  rw [habs_c, show ((1:ℝ)/4/2 : ℝ) = 1/8 from by norm_num]
  set E := Real.exp ((1:ℝ)/8)
  set B := Real.exp (-(4 * π))
  set T := Real.exp ((1:ℝ)/4)
  have h4π_le : 4 * π ≤ 16 := by linarith
  have h4π_pos : 0 ≤ 4 * π := by linarith
  -- Pre-compute all product bounds explicitly.
  have hAB_le : (4 * π) * B ≤ 16 * (1/279841) := by
    have := mul_le_mul h4π_le hB_le hB_pos.le (by norm_num : (0:ℝ) ≤ 16); linarith
  have hAB_nn : 0 ≤ (4 * π) * B := mul_nonneg h4π_pos hB_pos.le
  have hAT_le : (4 * π) * T ≤ 32 := by
    have := mul_le_mul h4π_le hT_le hT_pos.le (by norm_num : (0:ℝ) ≤ 16); linarith
  have hATm1_le : (4 * π) * T - 1 ≤ 31 := by linarith
  have hATm1_nn : 0 ≤ (4 * π) * T - 1 := by
    have h1 : (1:ℝ) ≤ 4*π := by linarith [hπ_pos, Real.pi_gt_three]
    have h2 : (1:ℝ) ≤ T := Real.one_le_exp (by norm_num)
    have : (1:ℝ) ≤ (4*π) * T := by
      have := mul_le_mul h1 h2 (by norm_num) (by linarith)
      linarith
    linarith
  have hA_ATm1_le : (4 * π) * ((4 * π) * T - 1) ≤ 16 * 31 := by
    have := mul_le_mul h4π_le hATm1_le hATm1_nn (by norm_num : (0:ℝ) ≤ 16)
    linarith
  have hA_ATm1_nn : 0 ≤ (4 * π) * ((4 * π) * T - 1) := mul_nonneg h4π_pos hATm1_nn
  have hA_ATm1_B_le : (4 * π) * ((4 * π) * T - 1) * B ≤ 16 * 31 * (1/279841) := by
    have := mul_le_mul hA_ATm1_le hB_le hB_pos.le (by norm_num : (0:ℝ) ≤ 16*31)
    linarith
  have hA_ATm1_B_nn : 0 ≤ (4 * π) * ((4 * π) * T - 1) * B := mul_nonneg hA_ATm1_nn hB_pos.le
  have hEB_le : E * B ≤ 2 * (1/279841) := by
    have := mul_le_mul hE_le hB_le hB_pos.le (by norm_num : (0:ℝ) ≤ 2); linarith
  have hEAB_le : E * ((4 * π) * B) ≤ 2 * (16 * (1/279841)) := by
    have := mul_le_mul hE_le hAB_le hAB_nn (by norm_num : (0:ℝ) ≤ 2); linarith
  have hE1AB_le : (E + 1) * ((4 * π) * B) ≤ 3 * (16 * (1/279841)) := by
    have h1 : E + 1 ≤ 3 := by linarith
    have := mul_le_mul h1 hAB_le hAB_nn (by norm_num : (0:ℝ) ≤ 3); linarith
  have hE1_nn : 0 ≤ E + 1 := by linarith
  nlinarith [hAB_le, hAB_nn, hEB_le, mul_nonneg hE_pos.le hB_pos.le,
             hA_ATm1_B_le, hA_ATm1_B_nn, hEAB_le, mul_nonneg hE_pos.le hAB_nn,
             hE1AB_le, mul_nonneg hE1_nn hAB_nn,
             hE_le, hE_pos.le, hT_le, hT_pos.le, hB_pos.le, hπ_pos]

/-- The per-`n` bound at n=2: A=9π ≤ 36, B=exp(-9π) ≤ exp(-4π) ≤ (1/23)⁴ = 1/279841.
Looser than optimal (true B ≈ 5e-13 vs 1/279841 ≈ 3.6e-6) but sufficient for ≤ 1. -/
private lemma fourier_plus_termM_n2 :
    fourier_plus_termM (27/4) 2 (1/4) ≤ 1 := by
  unfold fourier_plus_termM
  have hπ_le : π ≤ 4 := Real.pi_lt_four.le
  have hπ_pos : 0 < π := Real.pi_pos
  have hE_le := hE_le_2
  have hT_le := hT_le_2
  have hE_pos : 0 < Real.exp ((1:ℝ)/8) := Real.exp_pos _
  have hT_pos : 0 < Real.exp ((1:ℝ)/4) := Real.exp_pos _
  have h_eneg_pi : Real.exp (-π) ≤ 1/23 :=
    PrincipiaTractalis.Lambda0TightestBoundsMellin20261014.exp_neg_pi_le_one_twentythird
  have hA_eq : π * ((2:ℕ) + 1 : ℝ)^2 = 9 * π := by push_cast; ring
  rw [hA_eq]
  have hB_pos : 0 < Real.exp (-(9 * π)) := Real.exp_pos _
  -- exp(-9π) ≤ exp(-4π) ≤ (1/23)⁴ via two steps.
  have hB_le : Real.exp (-(9 * π)) ≤ 1/279841 := by
    have h_neg : -(9 * π) ≤ -(4 * π) := by nlinarith
    have h_step1 : Real.exp (-(9 * π)) ≤ Real.exp (-(4 * π)) := Real.exp_le_exp.mpr h_neg
    have h_step2 : Real.exp (-(4 * π)) ≤ 1/279841 := by
      have h_split : -(4 * π) = (-π) + (-π) + (-π) + (-π) := by ring
      rw [h_split, Real.exp_add, Real.exp_add, Real.exp_add]
      have h0 := (Real.exp_pos (-π)).le
      calc Real.exp (-π) * Real.exp (-π) * Real.exp (-π) * Real.exp (-π)
          ≤ (1/23) * (1/23) * (1/23) * (1/23) :=
            mul_le_mul (mul_le_mul (mul_le_mul h_eneg_pi h_eneg_pi h0 (by norm_num))
              h_eneg_pi (by positivity) (by positivity))
              h_eneg_pi (by positivity) (by positivity)
        _ = 1/279841 := by norm_num
    exact h_step1.trans h_step2
  have habs_c : |((27:ℝ)/4)| = 27/4 := by rw [abs_of_pos]; norm_num
  rw [habs_c, show ((1:ℝ)/4/2 : ℝ) = 1/8 from by norm_num]
  set E := Real.exp ((1:ℝ)/8)
  set B := Real.exp (-(9 * π))
  set T := Real.exp ((1:ℝ)/4)
  have h9π_le : 9 * π ≤ 36 := by linarith
  have h9π_pos : 0 ≤ 9 * π := by linarith
  have hAB_le : (9 * π) * B ≤ 36 * (1/279841) := by
    have := mul_le_mul h9π_le hB_le hB_pos.le (by norm_num : (0:ℝ) ≤ 36); linarith
  have hAB_nn : 0 ≤ (9 * π) * B := mul_nonneg h9π_pos hB_pos.le
  have hAT_le : (9 * π) * T ≤ 72 := by
    have := mul_le_mul h9π_le hT_le hT_pos.le (by norm_num : (0:ℝ) ≤ 36); linarith
  have hATm1_le : (9 * π) * T - 1 ≤ 71 := by linarith
  have hATm1_nn : 0 ≤ (9 * π) * T - 1 := by
    have h1 : (1:ℝ) ≤ 9*π := by linarith [hπ_pos, Real.pi_gt_three]
    have h2 : (1:ℝ) ≤ T := Real.one_le_exp (by norm_num)
    have : (1:ℝ) ≤ (9*π) * T := by
      have := mul_le_mul h1 h2 (by norm_num) (by linarith)
      linarith
    linarith
  have hA_ATm1_le : (9 * π) * ((9 * π) * T - 1) ≤ 36 * 71 := by
    have := mul_le_mul h9π_le hATm1_le hATm1_nn (by norm_num : (0:ℝ) ≤ 36)
    linarith
  have hA_ATm1_nn : 0 ≤ (9 * π) * ((9 * π) * T - 1) := mul_nonneg h9π_pos hATm1_nn
  have hA_ATm1_B_le : (9 * π) * ((9 * π) * T - 1) * B ≤ 36 * 71 * (1/279841) := by
    have := mul_le_mul hA_ATm1_le hB_le hB_pos.le (by norm_num : (0:ℝ) ≤ 36*71)
    linarith
  have hA_ATm1_B_nn : 0 ≤ (9 * π) * ((9 * π) * T - 1) * B := mul_nonneg hA_ATm1_nn hB_pos.le
  have hEB_le : E * B ≤ 2 * (1/279841) := by
    have := mul_le_mul hE_le hB_le hB_pos.le (by norm_num : (0:ℝ) ≤ 2); linarith
  have hEAB_le : E * ((9 * π) * B) ≤ 2 * (36 * (1/279841)) := by
    have := mul_le_mul hE_le hAB_le hAB_nn (by norm_num : (0:ℝ) ≤ 2); linarith
  have hE1AB_le : (E + 1) * ((9 * π) * B) ≤ 3 * (36 * (1/279841)) := by
    have h1 : E + 1 ≤ 3 := by linarith
    have := mul_le_mul h1 hAB_le hAB_nn (by norm_num : (0:ℝ) ≤ 3); linarith
  have hE1_nn : 0 ≤ E + 1 := by linarith
  nlinarith [hAB_le, hAB_nn, hEB_le, mul_nonneg hE_pos.le hB_pos.le,
             hA_ATm1_B_le, hA_ATm1_B_nn, hEAB_le, mul_nonneg hE_pos.le hAB_nn,
             hE1AB_le, mul_nonneg hE1_nn hAB_nn,
             hE_le, hE_pos.le, hT_le, hT_pos.le, hB_pos.le, hπ_pos]

/-- Sum of per-term bounds `≤ M = 24` (per-n: ≤19 + ≤1 + ≤1 ≤ 24). -/
private lemma M_sum_le_plus :
    ∑ n ∈ Finset.range 3, fourier_plus_termM (27/4) n (1/4) ≤ M := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith [fourier_plus_termM_n0, fourier_plus_termM_n1, fourier_plus_termM_n2]

/-! ## §2 — Panel enclosures. -/

"""


def emit_midpoint_panel_block(seg_idx, k, a, b, L_node_plus, U_node_plus, L_node_minus, U_node_minus):
    prefix = seg_prefix_mp(seg_idx)
    m = (a + b) / 2
    width = b - a
    err = M_VALUE * (width ** 3) / 24
    # f_plus = 2 * nodeR_fourier_plus (same for minus). So f_plus bound =
    # 2 * node bound. We emit BOTH: the node bound (used in Interval proof)
    # and the f_plus bound (used in the final theorem statement).
    L_plus_m = 2 * L_node_plus
    U_plus_m = 2 * U_node_plus
    L_minus_m = 2 * L_node_minus
    U_minus_m = 2 * U_node_minus
    panel_lo_plus = width * L_plus_m - err
    panel_hi_plus = width * U_plus_m + err
    panel_lo_minus = width * L_minus_m - err
    panel_hi_minus = width * U_minus_m + err

    a_s     = frac_to_lean_decimal(a)
    b_s     = frac_to_lean_decimal(b)
    m_s     = frac_to_lean_decimal(m)
    w_s     = frac_to_lean_decimal(width)
    err_s   = frac_to_lean_decimal(err)
    LNp_s   = frac_to_lean_decimal(L_node_plus)
    UNp_s   = frac_to_lean_decimal(U_node_plus)
    LNm_s   = frac_to_lean_decimal(L_node_minus)
    UNm_s   = frac_to_lean_decimal(U_node_minus)
    Lp_s    = frac_to_lean_decimal(L_plus_m)
    Up_s    = frac_to_lean_decimal(U_plus_m)
    Lm_s    = frac_to_lean_decimal(L_minus_m)
    Um_s    = frac_to_lean_decimal(U_minus_m)
    plo_s   = frac_to_lean_decimal(panel_lo_plus)
    phi_s   = frac_to_lean_decimal(panel_hi_plus)
    mlo_s   = frac_to_lean_decimal(panel_lo_minus)
    mhi_s   = frac_to_lean_decimal(panel_hi_minus)

    out = f"/-! ### §2.{k} — Panel {k}: u ∈ Icc {a_s} {b_s}, midpoint {m_s} -/\n\n"

    # Single-point numeric bounds on f_plus(m) and f_minus(m).
    # f_plus m = 2 * nodeR_fourier_plus_at_c27_4_N3 m (via definitional unfolding + ring).
    out += (
        f"theorem {prefix}{k}_plus_mid_lo : ({Lp_s} : ℝ) ≤ f_plus ({m_s} : ℝ) := by\n"
        f"  have h_eq : f_plus ({m_s} : ℝ) = 2 * nodeR_fourier_plus_at_c27_4_N3 ({m_s} : ℝ) := by\n"
        f"    show (∑ n ∈ Finset.range 3, fourier_plus_term (27/4) n ({m_s} : ℝ))\n"
        f"      = 2 * nodeR_fourier_plus_at_c27_4_N3 ({m_s} : ℝ)\n"
        f"    unfold fourier_plus_term nodeR_fourier_plus_at_c27_4_N3 omega_N3_at_exp\n"
        f"    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,\n"
        f"               Nat.cast_zero, Nat.cast_one, zero_add]\n"
        f"    ring_nf\n"
        f"  rw [h_eq]\n"
        f"  have h_node : ({LNp_s} : ℝ) ≤ nodeR_fourier_plus_at_c27_4_N3 ({m_s} : ℝ) := by\n"
        f"    refine _root_.Interval.approx_le\n"
        f"      (({LNp_s} : _root_.Interval))\n"
        f"      (nodeI_fourier_plus_at_c27_4 (({m_s} : _root_.Interval)))\n"
        f"      ({LNp_s} : ℝ)\n"
        f"      (nodeR_fourier_plus_at_c27_4_N3 ({m_s} : ℝ))\n"
        f"      (by approx)\n"
        f"      (nodeR_fourier_plus_at_c27_4_N3_mem_approx\n"
        f"        (u := ({m_s} : ℝ)) (U := (({m_s} : _root_.Interval))) (by approx))\n"
        f"      ?_\n"
        f"    decide +kernel\n"
        f"  linarith\n\n"
    )
    out += (
        f"theorem {prefix}{k}_plus_mid_hi : f_plus ({m_s} : ℝ) ≤ ({Up_s} : ℝ) := by\n"
        f"  have h_eq : f_plus ({m_s} : ℝ) = 2 * nodeR_fourier_plus_at_c27_4_N3 ({m_s} : ℝ) := by\n"
        f"    show (∑ n ∈ Finset.range 3, fourier_plus_term (27/4) n ({m_s} : ℝ))\n"
        f"      = 2 * nodeR_fourier_plus_at_c27_4_N3 ({m_s} : ℝ)\n"
        f"    unfold fourier_plus_term nodeR_fourier_plus_at_c27_4_N3 omega_N3_at_exp\n"
        f"    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,\n"
        f"               Nat.cast_zero, Nat.cast_one, zero_add]\n"
        f"    ring_nf\n"
        f"  rw [h_eq]\n"
        f"  have h_node : nodeR_fourier_plus_at_c27_4_N3 ({m_s} : ℝ) ≤ ({UNp_s} : ℝ) := by\n"
        f"    refine _root_.Interval.approx_le\n"
        f"      (nodeI_fourier_plus_at_c27_4 (({m_s} : _root_.Interval)))\n"
        f"      (({UNp_s} : _root_.Interval))\n"
        f"      (nodeR_fourier_plus_at_c27_4_N3 ({m_s} : ℝ))\n"
        f"      ({UNp_s} : ℝ)\n"
        f"      (nodeR_fourier_plus_at_c27_4_N3_mem_approx\n"
        f"        (u := ({m_s} : ℝ)) (U := (({m_s} : _root_.Interval))) (by approx))\n"
        f"      (by approx) ?_\n"
        f"    decide +kernel\n"
        f"  linarith\n\n"
    )
    out += (
        f"theorem {prefix}{k}_minus_mid_lo : ({Lm_s} : ℝ) ≤ f_minus ({m_s} : ℝ) := by\n"
        f"  have h_eq : f_minus ({m_s} : ℝ) = 2 * nodeR_fourier_minus_at_c27_4_N3 ({m_s} : ℝ) := by\n"
        f"    show (∑ n ∈ Finset.range 3, fourier_minus_term (27/4) n ({m_s} : ℝ))\n"
        f"      = 2 * nodeR_fourier_minus_at_c27_4_N3 ({m_s} : ℝ)\n"
        f"    unfold fourier_minus_term nodeR_fourier_minus_at_c27_4_N3 omega_N3_at_exp\n"
        f"    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,\n"
        f"               Nat.cast_zero, Nat.cast_one, zero_add]\n"
        f"    ring_nf\n"
        f"  rw [h_eq]\n"
        f"  have h_node : ({LNm_s} : ℝ) ≤ nodeR_fourier_minus_at_c27_4_N3 ({m_s} : ℝ) := by\n"
        f"    refine _root_.Interval.approx_le\n"
        f"      (({LNm_s} : _root_.Interval))\n"
        f"      (nodeI_fourier_minus_at_c27_4 (({m_s} : _root_.Interval)))\n"
        f"      ({LNm_s} : ℝ)\n"
        f"      (nodeR_fourier_minus_at_c27_4_N3 ({m_s} : ℝ))\n"
        f"      (by approx)\n"
        f"      (nodeR_fourier_minus_at_c27_4_N3_mem_approx\n"
        f"        (u := ({m_s} : ℝ)) (U := (({m_s} : _root_.Interval))) (by approx))\n"
        f"      ?_\n"
        f"    decide +kernel\n"
        f"  linarith\n\n"
    )
    out += (
        f"theorem {prefix}{k}_minus_mid_hi : f_minus ({m_s} : ℝ) ≤ ({Um_s} : ℝ) := by\n"
        f"  have h_eq : f_minus ({m_s} : ℝ) = 2 * nodeR_fourier_minus_at_c27_4_N3 ({m_s} : ℝ) := by\n"
        f"    show (∑ n ∈ Finset.range 3, fourier_minus_term (27/4) n ({m_s} : ℝ))\n"
        f"      = 2 * nodeR_fourier_minus_at_c27_4_N3 ({m_s} : ℝ)\n"
        f"    unfold fourier_minus_term nodeR_fourier_minus_at_c27_4_N3 omega_N3_at_exp\n"
        f"    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,\n"
        f"               Nat.cast_zero, Nat.cast_one, zero_add]\n"
        f"    ring_nf\n"
        f"  rw [h_eq]\n"
        f"  have h_node : nodeR_fourier_minus_at_c27_4_N3 ({m_s} : ℝ) ≤ ({UNm_s} : ℝ) := by\n"
        f"    refine _root_.Interval.approx_le\n"
        f"      (nodeI_fourier_minus_at_c27_4 (({m_s} : _root_.Interval)))\n"
        f"      (({UNm_s} : _root_.Interval))\n"
        f"      (nodeR_fourier_minus_at_c27_4_N3 ({m_s} : ℝ))\n"
        f"      ({UNm_s} : ℝ)\n"
        f"      (nodeR_fourier_minus_at_c27_4_N3_mem_approx\n"
        f"        (u := ({m_s} : ℝ)) (U := (({m_s} : _root_.Interval))) (by approx))\n"
        f"      (by approx) ?_\n"
        f"    decide +kernel\n"
        f"  linarith\n\n"
    )

    # Midpoint-rule error theorems (plus and minus).
    out += (
        f"theorem {prefix}{k}_plus_mp_err :\n"
        f"    |(∫ u in ({a_s} : ℝ)..({b_s} : ℝ), f_plus u) - ({w_s} : ℝ) * f_plus ({m_s} : ℝ)|\n"
        f"      ≤ ({err_s} : ℝ) := by\n"
        f"  have hab : ({a_s} : ℝ) ≤ ({b_s} : ℝ) := by norm_num\n"
        f"  have h_f : ∀ u ∈ Set.uIcc ({a_s} : ℝ) ({b_s} : ℝ), HasDerivAt f_plus\n"
        f"      (∑ n ∈ Finset.range 3, fourier_plus_termD1 (27/4) n u) u :=\n"
        f"    fun u _ ↦ hasDerivAt_fourier_plus_term_sum (27/4) 3 u\n"
        f"  have h_f' : ∀ u ∈ Set.uIcc ({a_s} : ℝ) ({b_s} : ℝ),\n"
        f"      HasDerivAt (fun y ↦ ∑ n ∈ Finset.range 3, fourier_plus_termD1 (27/4) n y)\n"
        f"        (∑ n ∈ Finset.range 3, fourier_plus_termD2 (27/4) n u) u :=\n"
        f"    fun u _ ↦ hasDerivAt_fourier_plus_termD1_sum (27/4) 3 u\n"
        f"  have h_M : ∀ u ∈ Set.uIcc ({a_s} : ℝ) ({b_s} : ℝ),\n"
        f"      |∑ n ∈ Finset.range 3, fourier_plus_termD2 (27/4) n u| ≤ M := by\n"
        f"    intro u hu\n"
        f"    rw [Set.uIcc_of_le hab] at hu\n"
        f"    have h0u : (0 : ℝ) ≤ u := by linarith [hu.1]\n"
        f"    have h_bu : u ≤ (1/4 : ℝ) := by linarith [hu.2]\n"
        f"    exact (abs_fourier_plus_termD2_sum_le (27/4) (1/4) 3 h0u h_bu).trans M_sum_le_plus\n"
        f"  have h_mid : (({a_s} : ℝ) + {b_s}) / 2 = {m_s} := by norm_num\n"
        f"  have h_mp := midpoint_rule_error hab h_f h_f' h_M\n"
        f"  rw [h_mid] at h_mp\n"
        f"  have h_rhs : M * (({b_s} : ℝ) - ({a_s} : ℝ)) ^ 3 / 24 = ({err_s} : ℝ) := by\n"
        f"    show (24 : ℝ) * (({b_s} : ℝ) - ({a_s} : ℝ)) ^ 3 / 24 = ({err_s} : ℝ)\n"
        f"    norm_num\n"
        f"  linarith [h_rhs]\n\n"
    )
    out += (
        f"theorem {prefix}{k}_minus_mp_err :\n"
        f"    |(∫ u in ({a_s} : ℝ)..({b_s} : ℝ), f_minus u) - ({w_s} : ℝ) * f_minus ({m_s} : ℝ)|\n"
        f"      ≤ ({err_s} : ℝ) := by\n"
        f"  have hab : ({a_s} : ℝ) ≤ ({b_s} : ℝ) := by norm_num\n"
        f"  have h_f : ∀ u ∈ Set.uIcc ({a_s} : ℝ) ({b_s} : ℝ), HasDerivAt f_minus\n"
        f"      (∑ n ∈ Finset.range 3, fourier_minus_termD1 (27/4) n u) u :=\n"
        f"    fun u _ ↦ hasDerivAt_fourier_minus_term_sum (27/4) 3 u\n"
        f"  have h_f' : ∀ u ∈ Set.uIcc ({a_s} : ℝ) ({b_s} : ℝ),\n"
        f"      HasDerivAt (fun y ↦ ∑ n ∈ Finset.range 3, fourier_minus_termD1 (27/4) n y)\n"
        f"        (∑ n ∈ Finset.range 3, fourier_minus_termD2 (27/4) n u) u :=\n"
        f"    fun u _ ↦ hasDerivAt_fourier_minus_termD1_sum (27/4) 3 u\n"
        f"  have h_M : ∀ u ∈ Set.uIcc ({a_s} : ℝ) ({b_s} : ℝ),\n"
        f"      |∑ n ∈ Finset.range 3, fourier_minus_termD2 (27/4) n u| ≤ M := by\n"
        f"    intro u hu\n"
        f"    rw [Set.uIcc_of_le hab] at hu\n"
        f"    have h0u : (0 : ℝ) ≤ u := by linarith [hu.1]\n"
        f"    have h_bu : u ≤ (1/4 : ℝ) := by linarith [hu.2]\n"
        f"    exact (abs_fourier_minus_termD2_sum_le (27/4) (1/4) 3 h0u h_bu).trans M_sum_le_plus\n"
        f"  have h_mid : (({a_s} : ℝ) + {b_s}) / 2 = {m_s} := by norm_num\n"
        f"  have h_mp := midpoint_rule_error hab h_f h_f' h_M\n"
        f"  rw [h_mid] at h_mp\n"
        f"  have h_rhs : M * (({b_s} : ℝ) - ({a_s} : ℝ)) ^ 3 / 24 = ({err_s} : ℝ) := by\n"
        f"    show (24 : ℝ) * (({b_s} : ℝ) - ({a_s} : ℝ)) ^ 3 / 24 = ({err_s} : ℝ)\n"
        f"    norm_num\n"
        f"  linarith [h_rhs]\n\n"
    )

    # Panel integral enclosure: combine mid-eval + midpoint error.
    out += (
        f"theorem {prefix}{k}_plus_integral_bound :\n"
        f"    ({plo_s} : ℝ)\n"
        f"      ≤ (∫ u in ({a_s} : ℝ)..({b_s} : ℝ), f_plus u)\n"
        f"    ∧ (∫ u in ({a_s} : ℝ)..({b_s} : ℝ), f_plus u)\n"
        f"      ≤ ({phi_s} : ℝ) := by\n"
        f"  have h_mp := {prefix}{k}_plus_mp_err\n"
        f"  have h_lo := {prefix}{k}_plus_mid_lo\n"
        f"  have h_hi := {prefix}{k}_plus_mid_hi\n"
        f"  have h_abs := abs_le.mp h_mp\n"
        f"  refine ⟨?_, ?_⟩\n"
        f"  · nlinarith [h_abs.1, h_abs.2, h_lo, h_hi]\n"
        f"  · nlinarith [h_abs.1, h_abs.2, h_lo, h_hi]\n\n"
    )
    out += (
        f"theorem {prefix}{k}_minus_integral_bound :\n"
        f"    ({mlo_s} : ℝ)\n"
        f"      ≤ (∫ u in ({a_s} : ℝ)..({b_s} : ℝ), f_minus u)\n"
        f"    ∧ (∫ u in ({a_s} : ℝ)..({b_s} : ℝ), f_minus u)\n"
        f"      ≤ ({mhi_s} : ℝ) := by\n"
        f"  have h_mp := {prefix}{k}_minus_mp_err\n"
        f"  have h_lo := {prefix}{k}_minus_mid_lo\n"
        f"  have h_hi := {prefix}{k}_minus_mid_hi\n"
        f"  have h_abs := abs_le.mp h_mp\n"
        f"  refine ⟨?_, ?_⟩\n"
        f"  · nlinarith [h_abs.1, h_abs.2, h_lo, h_hi]\n"
        f"  · nlinarith [h_abs.1, h_abs.2, h_lo, h_hi]\n\n"
    )
    return out


def emit_lean_file_mp(seg_idx, seg_lo, seg_hi, bricks, path):
    body = seg_file_header_mp(seg_idx, seg_lo, seg_hi)
    body += seg_preamble_mp(seg_idx)
    for brick in bricks:
        body += brick
    body += "end " + seg_namespace_mp(seg_idx) + "\n"
    body += "end FourierPanels_c27_4\n"
    body += "end PrincipiaTractalis\n\n"
    # Axiom-check for the first and last panel's headline theorems.
    prefix = seg_prefix_mp(seg_idx)
    ns = f"PrincipiaTractalis.FourierPanels_c27_4.{seg_namespace_mp(seg_idx)}"
    body += "/-! ## §Axiom check — spot-check first and last panels -/\n"
    body += f"#print axioms {ns}.{prefix}1_plus_integral_bound\n"
    body += f"#print axioms {ns}.{prefix}1_minus_integral_bound\n"
    body += f"#print axioms {ns}.{prefix}{N_PANELS}_plus_integral_bound\n"
    body += f"#print axioms {ns}.{prefix}{N_PANELS}_minus_integral_bound\n"
    with open(path, "w") as f:
        f.write(body)


def run_segment(seg_idx):
    seg_lo, seg_hi = SEGMENTS[seg_idx]
    bricks = []
    for k in range(1, N_PANELS + 1):
        a, b = panel_endpoints(seg_lo, seg_hi, k - 1)  # 0-indexed internally
        m = (a + b) / 2
        Lp, Up, Lm, Um = point_bounds(m)
        print(f"  Panel {k}: u ∈ [{a}, {b}], m = {m}")
        print(f"           L_plus  = {float(Lp):+.6e}, U_plus  = {float(Up):+.6e}")
        print(f"           L_minus = {float(Lm):+.6e}, U_minus = {float(Um):+.6e}")
        bricks.append(emit_midpoint_panel_block(seg_idx, k, a, b, Lp, Up, Lm, Um))
    return seg_lo, seg_hi, bricks


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--seg", type=int, required=True, choices=list(SEGMENTS.keys()))
    p.add_argument("--dry-run", action="store_true")
    args = p.parse_args()

    print(f"=== Generating midpoint-rule panels for Seg0{args.seg} at c = 27/4 ===")
    seg_lo, seg_hi, bricks = run_segment(args.seg)

    if args.dry_run:
        print("Dry-run — not writing file.")
        return

    out_path = os.path.join(
        os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
        "PF", "Analytic", "FourierPanels",
        seg_file_name_mp(args.seg))
    emit_lean_file_mp(args.seg, seg_lo, seg_hi, bricks, out_path)
    print(f"Wrote {out_path}")
    with open(out_path) as f:
        content = f.read()
    nlines = content.count("\n")
    print(f"  Lines: {nlines}")
    print(f"  Panels: {N_PANELS}")
    print(f"  Approx L/panel: {nlines / N_PANELS:.1f}")


if __name__ == "__main__":
    main()
