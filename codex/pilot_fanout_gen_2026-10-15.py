#!/usr/bin/env python3
"""Fan-out generator for 4 Cauchy–Schwarz pointwise-form pilots at c past 4.05.
   Writes one Lean module per pilot into PF_Lean4_Code/PF/Analytic/PilotBoxes/.
   All parameters verified passing Gate 1 (squared-form) + Gate 2 (L=1) before emit.
"""
from fractions import Fraction as F
from pathlib import Path

B    = F(50, 1727)   # uniform ||Λ₀|| bound
ROOT = Path("/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE/PF_Lean4_Code/PF/Analytic/PilotBoxes")

# Pilot parameters: c, r, Mc_lb_num, Mc_lb_den, name_suffix
# Each verified: c²(c²+1)·B² ≤ (1-2·Mc_lb)²  AND  L·r = 1·r < Mc_lb  AND  (1+2|t_max|)·B + (t_max²+|t_max|)·B ≤ 2 at t_max = c+r
pilots = [
    # c, r, Mc_lb,  name_tag,                  namespace_tag,                           box_text
    (F(83,20), F(1, 50), F(1,  5),  "c83_20_r1_50",    "c83_20_r1_50",   "[413/100, 417/100] (= [4.13, 4.17])"),
    (F( 9, 2), F(1, 50), F(1,  8),  "c9_2_r1_50",      "c9_2_r1_50",     "[224/50, 226/50]  (= [4.48, 4.52])"),
    (F(21, 4), F(1, 50), F(1, 16),  "c21_4_r1_50",     "c21_4_r1_50",    "[524/100, 526/100] (= [5.24, 5.26])"),
    (F(23, 4), F(1,200), F(1,100),  "c23_4_r1_200",    "c23_4_r1_200",   "[1149/200, 1151/200] (= [5.745, 5.755])"),
]

def rr(f):
    """Render Fraction as Lean rational, e.g. 83/20."""
    return f"{f.numerator}/{f.denominator}"

def rr_box(lo, hi):
    """Render Icc endpoints as Lean rationals."""
    return rr(lo), rr(hi)

def verify_gates(c, r, Mc_lb):
    """Prove the two gate inequalities hold as rationals."""
    # Gate 1 squared: c²(c²+1)·B² ≤ (1-2·Mc_lb)²
    g1_lhs = c*c*(c*c + 1) * B * B
    g1_rhs = (1 - 2*Mc_lb)**2
    assert g1_lhs <= g1_rhs, f"Gate 1 FAIL at c={c}: {g1_lhs} > {g1_rhs}"
    # Gate 2 strict: L·r < Mc_lb with L=1
    L = F(1)
    assert L*r < Mc_lb, f"Gate 2 FAIL at c={c}: {L*r} >= {Mc_lb}"
    # L=1 justification: (1+2|t_max|)·B + (t_max²+|t_max|)·B ≤ 2
    t_max = c + r
    sum_val = (1 + 2*t_max) * B + (t_max*t_max + t_max) * B
    assert sum_val <= 2, f"L=1 derivation FAIL at c={c}: sum = {sum_val}"
    return g1_lhs, g1_rhs, L*r

def box_bounds(c, r):
    """Return Lean rationals for Icc lower and upper, and |t|_max."""
    lo = c - r
    hi = c + r
    t_max = hi  # since c, r > 0
    return lo, hi, t_max

TEMPLATE = r"""/-
# PF.Analytic.PilotBoxes.R1_{TAG}_poc_pointwise_2026_10_15

**Cauchy–Schwarz pointwise-form pilot at c = {C_FRAC}.**

Follows the recipe of the c = 11/2 proof-of-concept at `d47577f1`: the
aggregate Cauchy–Schwarz form

  (c²·Re Λ₀ + c·Im Λ₀)² ≤ c²(c²+1)·(Re² + Im²) ≤ c²(c²+1)·B²

replaces the pilot-1..13 component-wise triangle (which fails here because
`(c² + c)·B > 1` once `c > 1/((√5-1)/(2·B))` ≈ 3.69). Combined with
uniform `‖Λ₀‖ ≤ 50/1727` plus the exact algebra
`Re ξ(1+it) = (1 − t²·Re Λ₀ − t·Im Λ₀)/2`.

Parameters:
* `c = {C_FRAC}`, `r = {R_FRAC}`, box = `{BOX_TEXT}`.
* `Mc_lb = {MC_FRAC}`, `L = 1`, `L · r = {LR_FRAC} < {MC_FRAC}` ✓.
* Gate 1 squared: `c²(c²+1)·B² = {G1_LHS}` ≤ `(1 − 2·Mc_lb)² = {G1_RHS}`.
* L=1 at |t| ≤ {TMAX_FRAC}: `(1+2|t|)·B + (t²+|t|)·B ≤ 2` ✓.

No sorry, native_decide, axiom, Prop := True. autoImplicit off. Additive.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-15.
-/

import PF.Analytic.CenteredFormBridge_2026_10_13
import PF.Analytic.Lambda0UltraTightBoundsMellin_2026_10_14
import PF.Analytic.EdgeReDerivBound_2026_10_14

set_option autoImplicit false

namespace PrincipiaTractalis
namespace PilotR1Box_{NSTAG}_poc_pointwise_20261015

open Complex Set
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.RiemannXiThetaBoxEnclosure
open PrincipiaTractalis.R1Neighborhood20261009
open PrincipiaTractalis.EdgeSignNeighborhoods20261013
open PrincipiaTractalis.CenteredFormBridge20261013
open PrincipiaTractalis.Lambda0UltraTightBoundsMellin20261014
open PrincipiaTractalis.EdgeReDerivBound20261014

noncomputable section

/-! ## §1 — Gate 1 via Cauchy–Schwarz -/

private lemma norm_sq_decomp (z : ℂ) : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
  linarith [Complex.sq_norm_sub_sq_re z]

theorem pilot_r1_hvalue_lb_at_{NSTAG} :
    ({MC_FRAC} : ℝ) ≤ (riemannXiEntire (⟨1, {C_FRAC}⟩ : ℂ)).re := by
  rw [re_xi_at_s]
  set re := (completedRiemannZeta₀ (⟨1, {C_FRAC}⟩ : ℂ)).re with hre
  set im := (completedRiemannZeta₀ (⟨1, {C_FRAC}⟩ : ℂ)).im with him
  have hΛ : ‖completedRiemannZeta₀ (⟨1, {C_FRAC}⟩ : ℂ)‖ ≤ 50 / 1727 :=
    lambda0_abs_le_fifty_over_1727 ({C_FRAC} : ℝ)
  have hNormSq : re ^ 2 + im ^ 2 ≤ (50 / 1727 : ℝ) ^ 2 := by
    have h1 : re ^ 2 + im ^ 2 = ‖completedRiemannZeta₀ (⟨1, {C_FRAC}⟩ : ℂ)‖ ^ 2 :=
      norm_sq_decomp _
    rw [h1]
    exact pow_le_pow_left₀ (norm_nonneg _) hΛ 2
  -- Cauchy–Schwarz polynomial identity:
  --   (c²·re + c·im)² + (c·re − c²·im)² = (c² + c⁴)·(re² + im²)
  have hCS :
      (({C_SQ_FRAC} : ℝ) * re + ({C_FRAC}) * im) ^ 2
        ≤ ({C_QUAD_PLUS_SQ_FRAC}) * (re ^ 2 + im ^ 2) := by
    nlinarith [sq_nonneg (({C_FRAC} : ℝ) * re - ({C_SQ_FRAC}) * im),
               sq_nonneg re, sq_nonneg im]
  have hQ_sq_bd :
      (({C_SQ_FRAC} : ℝ) * re + ({C_FRAC}) * im) ^ 2 ≤ ({ONE_MINUS_2MC_FRAC} : ℝ) ^ 2 := by
    have hArith :
        ({C_QUAD_PLUS_SQ_FRAC} : ℝ) * (50 / 1727) ^ 2 ≤ ({ONE_MINUS_2MC_FRAC} : ℝ) ^ 2 := by
      norm_num
    have hChain :
        ({C_QUAD_PLUS_SQ_FRAC} : ℝ) * (re ^ 2 + im ^ 2)
          ≤ ({C_QUAD_PLUS_SQ_FRAC}) * (50 / 1727) ^ 2 :=
      mul_le_mul_of_nonneg_left hNormSq (by norm_num : (0 : ℝ) ≤ {C_QUAD_PLUS_SQ_FRAC})
    linarith
  have hQ_bd :
      ({C_SQ_FRAC} : ℝ) * re + ({C_FRAC}) * im ≤ {ONE_MINUS_2MC_FRAC} := by
    nlinarith [hQ_sq_bd,
               sq_nonneg (({C_SQ_FRAC} : ℝ) * re + ({C_FRAC}) * im - {ONE_MINUS_2MC_FRAC}),
               sq_nonneg (({C_SQ_FRAC} : ℝ) * re + ({C_FRAC}) * im + {ONE_MINUS_2MC_FRAC})]
  linarith

/-! ## §2 — Gate 2: `|deriv edgeRe t| ≤ 1` on `|t| ≤ {TMAX_FRAC}` -/

private lemma gate2_num_bound_{NSTAG} {t : ℝ} (ht : |t| ≤ {TMAX_FRAC}) :
    (1 + 2 * |t|) * (50 / 1727) + (t ^ 2 + |t|) * (50 / 1727) ≤ 2 := by
  have h_abs_nn : (0 : ℝ) ≤ |t| := abs_nonneg t
  have h_t_sq_bd : t ^ 2 ≤ ({TMAX_FRAC}) ^ 2 := by nlinarith [abs_le.mp ht]
  nlinarith [h_t_sq_bd, h_abs_nn, ht]

theorem norm_deriv_riemannXiEntire_le_one_at_{NSTAG} {t : ℝ}
    (ht : |t| ≤ {TMAX_FRAC}) :
    ‖deriv riemannXiEntire (⟨1, t⟩ : ℂ)‖ ≤ 1 := by
  rw [deriv_riemannXiEntire_at]
  have h_Λ := lambda0_abs_le_fifty_over_1727 t
  have h_Λ' := lambda0_prime_abs_le_fifty_over_1727 t
  have h_2s := norm_two_s_minus_one_le t
  have h_ss := norm_s_mul_s_minus_one_le t
  have h_abs_nn : (0 : ℝ) ≤ |t| := abs_nonneg t
  have h_t_sq_nn : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
  rw [norm_div]
  have h2_norm : ‖(2 : ℂ)‖ = 2 := by
    show ‖((2 : ℕ) : ℂ)‖ = 2
    rw [Complex.norm_natCast]; norm_num
  rw [h2_norm]
  have h_num_bound :
      ‖(2 * (⟨1, t⟩ : ℂ) - 1) * completedRiemannZeta₀ (⟨1, t⟩ : ℂ)
          + (⟨1, t⟩ : ℂ) * ((⟨1, t⟩ : ℂ) - 1)
              * deriv completedRiemannZeta₀ (⟨1, t⟩ : ℂ)‖ ≤ 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h_mul1 :
        ‖2 * (⟨1, t⟩ : ℂ) - 1‖ * ‖completedRiemannZeta₀ (⟨1, t⟩ : ℂ)‖
          ≤ (1 + 2 * |t|) * (50 / 1727) := by
      apply mul_le_mul h_2s h_Λ (norm_nonneg _)
      linarith
    have h_mul2 :
        ‖(⟨1, t⟩ : ℂ) * ((⟨1, t⟩ : ℂ) - 1)‖
          * ‖deriv completedRiemannZeta₀ (⟨1, t⟩ : ℂ)‖
          ≤ (t ^ 2 + |t|) * (50 / 1727) := by
      apply mul_le_mul h_ss h_Λ' (norm_nonneg _)
      linarith
    have h_sum := gate2_num_bound_{NSTAG} ht
    linarith
  linarith

theorem abs_deriv_edgeRe_le_one_at_{NSTAG} {t : ℝ}
    (ht : |t| ≤ {TMAX_FRAC}) :
    |deriv edgeRe t| ≤ 1 := by
  rw [deriv_edgeRe_eq]
  have h_re_le :
      |(deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I).re|
        ≤ ‖deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I‖ :=
    abs_re_le_norm _
  rw [norm_mul, Complex.norm_I, mul_one] at h_re_le
  have h := norm_deriv_riemannXiEntire_le_one_at_{NSTAG} ht
  linarith

theorem pilot_r1_hbound_{NSTAG} :
    ∀ x ∈ Set.Icc ({LO_FRAC} : ℝ) ({HI_FRAC}), |deriv edgeRe x| ≤ 1 := by
  intro x hx
  rw [Set.mem_Icc] at hx
  have hx_abs : |x| ≤ {TMAX_FRAC} := by
    rw [abs_le]
    refine ⟨by linarith, hx.2⟩
  exact abs_deriv_edgeRe_le_one_at_{NSTAG} hx_abs

/-! ## §3 — The pilot box, closed end-to-end -/

/-- **Pilot** at `c = {C_FRAC}` on `{BOX_TEXT}`. Zero hypotheses, kernel-clean. -/
theorem pilot_r1_box_{NSTAG}_poc_closed :
    ∀ t ∈ Icc ({LO_FRAC} : ℝ) ({HI_FRAC}),
      0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re := by
  have h_icc_rewrite : Icc ({LO_FRAC} : ℝ) ({HI_FRAC})
      = Icc (({C_FRAC} : ℝ) - {R_FRAC}) (({C_FRAC} : ℝ) + {R_FRAC}) := by
    congr 1 <;> norm_num
  rw [h_icc_rewrite]
  refine R1_box_centered_of_lb
    (c := {C_FRAC}) (r := {R_FRAC}) (L := 1) (Mc_lb := {MC_FRAC})
    (by norm_num : (0 : ℝ) ≤ {R_FRAC})
    pilot_r1_hvalue_lb_at_{NSTAG}
    ?_
    (by norm_num : (1 : ℝ) * ({R_FRAC}) < {MC_FRAC})
  intro x hx
  have hx' : x ∈ Icc ({LO_FRAC} : ℝ) ({HI_FRAC}) := by
    rw [h_icc_rewrite]; exact hx
  exact pilot_r1_hbound_{NSTAG} x hx'

end

/-! ## §Axiom check -/

#print axioms norm_sq_decomp
#print axioms pilot_r1_hvalue_lb_at_{NSTAG}
#print axioms gate2_num_bound_{NSTAG}
#print axioms norm_deriv_riemannXiEntire_le_one_at_{NSTAG}
#print axioms abs_deriv_edgeRe_le_one_at_{NSTAG}
#print axioms pilot_r1_hbound_{NSTAG}
#print axioms pilot_r1_box_{NSTAG}_poc_closed

end PilotR1Box_{NSTAG}_poc_pointwise_20261015
end PrincipiaTractalis
"""

for c, r, Mc_lb, tag, nstag, box_text in pilots:
    lo, hi, t_max = box_bounds(c, r)
    g1_lhs, g1_rhs, lr = verify_gates(c, r, Mc_lb)
    c_sq        = c * c
    c_quad_plus = c_sq + c*c*c*c
    one_minus_2mc = 1 - 2*Mc_lb

    subs = {
        "C_FRAC":                 rr(c),
        "C_SQ_FRAC":              rr(c_sq),
        "C_QUAD_PLUS_SQ_FRAC":    rr(c_quad_plus),
        "R_FRAC":                 rr(r),
        "MC_FRAC":                rr(Mc_lb),
        "ONE_MINUS_2MC_FRAC":     rr(one_minus_2mc),
        "LR_FRAC":                rr(lr),
        "G1_LHS":                 rr(g1_lhs),
        "G1_RHS":                 rr(g1_rhs),
        "LO_FRAC":                rr(lo),
        "HI_FRAC":                rr(hi),
        "TMAX_FRAC":              rr(t_max),
        "TAG":                    tag,
        "NSTAG":                  nstag,
        "BOX_TEXT":               box_text,
    }

    content = TEMPLATE
    for k, v in subs.items():
        content = content.replace("{" + k + "}", str(v))

    out_path = ROOT / f"R1_{tag}_poc_pointwise_2026_10_15.lean"
    out_path.write_text(content)
    print(f"Wrote: {out_path}  ({len(content)} chars)  Mc={Mc_lb}  Lr={lr}  margin={Mc_lb - lr}")

print("\nAll parameters verified. Build with:")
print("  cd PF_Lean4_Code && lake build \\")
for c, r, Mc_lb, tag, nstag, box_text in pilots:
    print(f"    PF.Analytic.PilotBoxes.R1_{tag}_poc_pointwise_2026_10_15 \\")
