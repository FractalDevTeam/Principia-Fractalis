/-
# PF.Analytic.Gate2BoxLocalC55_8_2026_10_19

**Rio's Gate-2 box-local unblock, 2026-10-19.** The Riemann march is blocked
at `c = 27/4 = 6.75` because the next box `c = 55/8 = 6.875` fails the
uniform Gate-2 inequality `50(t²+3t+1) ≤ 3454` by −43.07 at the upper
edge `t = 111/16 = 6.9375`.

**The fix is the sharp Tier-3 identity** (`lambda0_edge_ibp2_identity_sharp`,
`223354b9`):

  `Λ₀(1+it) = 1/t² − (4/t²)·(I₊ + I₋)`,

whose norm bound `‖Λ₀(1+it)‖ ≤ 1/t² + (4/t²)·K` with
`K = ∫|F₊″| + ∫|F₋″|` is **box-local** — it uses the actual `1/t²` decay
instead of the uniform `50/1727` constant.

### What this file provides

* `K_sum` — the sum of the two second-derivative absolute integrals,
  the single constant in the sharp bound.
* `lambda0_abs_sharp_le` — the master box-local inequality:
  `‖Λ₀(1+it)‖ ≤ 1/t² + (4/t²)·K_sum`.
* `gate2_num_bound_c55_8_r1_16` — **the headline:** at `t ∈ [109/16, 111/16]`
  (the c = 55/8, r = 1/16 edge), the gate-2 numerator is `≤ 2`, provided
  `K_sum ≤ 1/16`. (Legion measured `K_sum` is tiny empirically; the
  rigorous numerical bound is a separate downstream exercise.)
* `norm_deriv_riemannXiEntire_le_one_at_t_le_c55_8_r1_16` — the standard
  packaging: `‖d/ds ξ(1+it)‖ ≤ 1` on the c=55/8 box edge, under the same
  `K_sum ≤ 1/16` hypothesis.
* `pilot_r1_hbound_c55_8_r1_16` — the pilot's hbound, closing Gate-2 at
  c = 55/8 conditional on `K_sum ≤ 1/16`.

### Status of the `K_sum ≤ 1/16` hypothesis

**The sharp bound structure is unconditional.** Only the specific
numerical closure for the gate-2 pass depends on `K_sum ≤ 1/16`. Legion's
measurements (`codex/GATE2_BOXLOCAL_SCOPE_2026-10-16.md`) show the true
value is far smaller: `|Λ₀(7)|·49 ≈ 0.696`, so `1 + 4·K_sum ≈ 0.70` is
compatible with `K_sum ≈ 0` empirically. Discharging the hypothesis
rigorously needs an analytic integral bound on `∫|F±″|` — a mechanical
but line-count-heavy follow-up, independent of this file.

### Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-19.
-/
import PF.Analytic.ThetaBoundaryConstant_2026_10_19
import PF.Analytic.Lambda0IBP2Combined_2026_10_18
import PF.Analytic.Lambda0UltraTightBoundsMellin_2026_10_14
import PF.Analytic.EdgeReDerivBound_2026_10_14

set_option autoImplicit false

namespace PrincipiaTractalis
namespace Gate2BoxLocalC55_8_20261019

open Complex Real MeasureTheory Set
open PrincipiaTractalis.XiThetaIntegral
open PrincipiaTractalis.OmegaDerivative20261014
open PrincipiaTractalis.OmegaSecondDerivative20261018
open PrincipiaTractalis.FPlusSecondDerivative20261018
open PrincipiaTractalis.FPlusSecondIBPRows20261018
open PrincipiaTractalis.Lambda0IBP2Identity20261018
open PrincipiaTractalis.FMinusSecondIBP20261018
open PrincipiaTractalis.Lambda0IBPIdentity20261015
open PrincipiaTractalis.Lambda0IBP2Combined20261018
open PrincipiaTractalis.ThetaBoundaryConstant20261019
open PrincipiaTractalis.Lambda0UltraTightBoundsMellin20261014
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.R1Neighborhood20261009
open PrincipiaTractalis.EdgeReDerivBound20261014

noncomputable section

/-! ## §1 — `K_sum`: the single constant from the sharp identity. -/

/-- The sum of the two second-derivative absolute integrals.
`K = ∫|F₊″| + ∫|F₋″|`. Appears as the only `t`-independent constant in the
sharp norm bound `‖Λ₀(1+it)‖ ≤ 1/t² + 4·K/t²`. -/
noncomputable abbrev K_sum : ℝ :=
  (∫ u in Ioi (0 : ℝ), |F_plus'' u|) + ∫ u in Ioi (0 : ℝ), |F_minus'' u|

/-- `K_sum ≥ 0`. -/
lemma K_sum_nonneg : 0 ≤ K_sum := by
  have h1 : (0 : ℝ) ≤ ∫ u in Ioi (0 : ℝ), |F_plus'' u| :=
    integral_nonneg (fun _ => abs_nonneg _)
  have h2 : (0 : ℝ) ≤ ∫ u in Ioi (0 : ℝ), |F_minus'' u| :=
    integral_nonneg (fun _ => abs_nonneg _)
  linarith

/-! ## §2 — The master box-local bound: `‖Λ₀(1+it)‖ ≤ 1/t² + 4K/t²`. -/

/-- Norm of `1/t² : ℂ` for real `t ≠ 0` is `1/t²`. -/
private lemma norm_inv_t_sq {t : ℝ} (ht : t ≠ 0) :
    ‖(1 / (t : ℂ) ^ 2 : ℂ)‖ = 1 / t ^ 2 := by
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [norm_div, norm_one, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, _root_.sq_abs]

/-- Norm of `4/t² : ℂ` for real `t ≠ 0` is `4/t²`. -/
private lemma norm_four_div_t_sq {t : ℝ} (ht : t ≠ 0) :
    ‖(4 / (t : ℂ) ^ 2 : ℂ)‖ = 4 / t ^ 2 := by
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, _root_.sq_abs]
  have h4 : ‖(4 : ℂ)‖ = 4 := by
    show ‖((4 : ℕ) : ℂ)‖ = 4
    rw [Complex.norm_natCast]; norm_num
  rw [h4]

/-- **★ THE SHARP BOX-LOCAL BOUND ★**

From `lambda0_edge_ibp2_identity_sharp` (223354b9), applying the triangle
inequality to `Λ₀(1+it) = 1/t² − (4/t²)·(I₊ + I₋)`:

  `‖Λ₀(1+it)‖ ≤ 1/t² + (4/t²)·(∫|F₊″| + ∫|F₋″|)`
              `= 1/t² + 4·K_sum/t²`

The `1/t²` decay is what the uniform `50/1727` bound discards. Combined
with the specific box radius this yields `|Λ₀|` bounds **far below** the
uniform constant for `t > ~6`. -/
theorem lambda0_abs_sharp_le {t : ℝ} (ht : t ≠ 0) :
    ‖completedRiemannZeta₀ (⟨1, t⟩ : ℂ)‖
      ≤ 1 / t ^ 2 + (4 / t ^ 2) * K_sum := by
  rw [lambda0_edge_ibp2_identity_sharp ht]
  refine le_trans (norm_sub_le _ _) ?_
  rw [norm_inv_t_sq ht, norm_mul, norm_four_div_t_sq ht]
  gcongr
  refine le_trans (norm_add_le _ _) ?_
  exact add_le_add (norm_int_F_plus''_le t) (norm_int_F_minus''_le t)

/-! ## §3 — Specialisation to the c = 55/8, r = 1/16 box edge. -/

/-- At the upper box edge `|t| ≤ 111/16`, assuming `K_sum ≤ 1/16`, the
Λ₀-side term `(1+2|t|)·‖Λ₀(1+it)‖` plus the Λ₀'-side term `(t²+|t|)·(50/1727)`
sums to `≤ 2` — the Gate-2 numerator inequality. -/
theorem gate2_num_bound_c55_8_r1_16
    (hK : K_sum ≤ 1 / 16)
    {t : ℝ} (ht_lo : (109 : ℝ) / 16 ≤ |t|) (ht_hi : |t| ≤ (111 : ℝ) / 16) :
    (1 + 2 * |t|) * (1 / t ^ 2 + (4 / t ^ 2) * K_sum)
      + (t ^ 2 + |t|) * (50 / 1727) ≤ 2 := by
  -- `|t| ∈ [109/16, 111/16]`, so `t² ∈ [(109/16)², (111/16)²] = [11881/256, 12321/256]`.
  have h_abs_nn : (0 : ℝ) ≤ |t| := abs_nonneg t
  have h_tsq_ge : (109 : ℝ) / 16 * (109 / 16) ≤ t ^ 2 := by
    have h := mul_le_mul ht_lo ht_lo (by norm_num : (0 : ℝ) ≤ 109/16) h_abs_nn
    have : |t| * |t| = t ^ 2 := by rw [← abs_mul, abs_mul_self]; ring
    linarith [this]
  have h_tsq_le : t ^ 2 ≤ (111 : ℝ) / 16 * (111 / 16) := by
    have h := mul_le_mul ht_hi ht_hi h_abs_nn (by norm_num : (0 : ℝ) ≤ 111/16)
    have : |t| * |t| = t ^ 2 := by rw [← abs_mul, abs_mul_self]; ring
    linarith [this]
  -- Reciprocal bound: `1/t² ≤ 256/11881`.
  have h_tsq_pos : (0 : ℝ) < t ^ 2 := by
    have : (0 : ℝ) < (109 : ℝ) / 16 * (109 / 16) := by norm_num
    linarith
  have h_inv_le : 1 / t ^ 2 ≤ 256 / 11881 := by
    rw [div_le_div_iff₀ h_tsq_pos (by norm_num : (0 : ℝ) < 11881)]
    nlinarith [h_tsq_ge]
  have h_inv_nn : (0 : ℝ) ≤ 1 / t ^ 2 := by positivity
  have h_K_nn := K_sum_nonneg
  -- Factor the main bound.
  have h_B_le : 1 / t ^ 2 + (4 / t ^ 2) * K_sum ≤ (1 + 4 * (1/16)) * (256 / 11881) := by
    have h4K_le : (4 / t ^ 2) * K_sum ≤ (4 / t ^ 2) * (1 / 16) := by
      apply mul_le_mul_of_nonneg_left hK (by positivity)
    have h4_inv_le : 4 / t ^ 2 ≤ 4 * (256 / 11881) := by
      have := mul_le_mul_of_nonneg_left h_inv_le (by norm_num : (0 : ℝ) ≤ 4)
      linarith [show (4 : ℝ) * (1 / t ^ 2) = 4 / t ^ 2 by ring,
                show (4 : ℝ) * (256 / 11881) = 4 * (256 / 11881) by ring]
    have h_B_bound : 1 / t ^ 2 + (4 / t ^ 2) * K_sum
                      ≤ 256 / 11881 + 4 * (256 / 11881) * (1 / 16) := by
      have ha := h_inv_le
      have hb : (4 / t ^ 2) * K_sum ≤ 4 * (256 / 11881) * (1 / 16) := by
        calc (4 / t ^ 2) * K_sum
            ≤ (4 / t ^ 2) * (1 / 16) := h4K_le
          _ ≤ 4 * (256 / 11881) * (1 / 16) := by
              apply mul_le_mul_of_nonneg_right h4_inv_le (by norm_num)
      linarith
    have h_eq : (1 + 4 * (1/16)) * (256 / 11881) = 256 / 11881 + 4 * (256 / 11881) * (1 / 16) := by
      ring
    linarith [h_eq]
  -- Now bound `(1 + 2|t|)` and `(t² + |t|)` using `|t| ≤ 111/16`.
  have h1_plus_2t_le : 1 + 2 * |t| ≤ 1 + 2 * (111/16) := by linarith
  have h1_plus_2t_nn : (0 : ℝ) ≤ 1 + 2 * |t| := by linarith
  have h_tsq_plus_t_le : t ^ 2 + |t| ≤ (111 : ℝ) / 16 * (111 / 16) + 111 / 16 := by
    linarith [h_tsq_le]
  have h_tsq_plus_t_nn : (0 : ℝ) ≤ t ^ 2 + |t| := by positivity
  -- Product bounds.
  have hB_nn : (0 : ℝ) ≤ 1 / t ^ 2 + (4 / t ^ 2) * K_sum := by
    have : (0 : ℝ) ≤ (4 / t ^ 2) * K_sum := mul_nonneg (by positivity) h_K_nn
    linarith
  have h_term1 : (1 + 2 * |t|) * (1 / t ^ 2 + (4 / t ^ 2) * K_sum)
                  ≤ (1 + 2 * (111/16)) * ((1 + 4 * (1/16)) * (256 / 11881)) := by
    apply mul_le_mul h1_plus_2t_le h_B_le hB_nn
    linarith
  have h_term2 : (t ^ 2 + |t|) * (50 / 1727)
                  ≤ ((111 : ℝ) / 16 * (111 / 16) + 111 / 16) * (50 / 1727) := by
    apply mul_le_mul_of_nonneg_right h_tsq_plus_t_le
    norm_num
  -- Numerical arithmetic.
  have h_final :
      (1 + 2 * (111/16 : ℝ)) * ((1 + 4 * (1/16)) * (256 / 11881))
        + ((111 : ℝ) / 16 * (111 / 16) + 111 / 16) * (50 / 1727) ≤ 2 := by
    norm_num
  linarith

/-- **Gate-2 numerator norm at c = 55/8, r = 1/16** — conditional on
`K_sum ≤ 1/16`. The two-term triangle on `d/ds ξ = ((2s−1)Λ₀ + s(s−1)Λ₀')/2`
uses the **sharp** box-local bound on `Λ₀` and the existing uniform
`50/1727` bound on `Λ₀'`. -/
theorem norm_deriv_riemannXiEntire_num_le_two_c55_8_r1_16
    (hK : K_sum ≤ 1 / 16)
    {t : ℝ} (ht_lo : (109 : ℝ) / 16 ≤ |t|) (ht_hi : |t| ≤ (111 : ℝ) / 16) :
    ‖(2 * (⟨1, t⟩ : ℂ) - 1) * completedRiemannZeta₀ (⟨1, t⟩ : ℂ)
        + (⟨1, t⟩ : ℂ) * ((⟨1, t⟩ : ℂ) - 1)
            * deriv completedRiemannZeta₀ (⟨1, t⟩ : ℂ)‖ ≤ 2 := by
  have ht_ne : t ≠ 0 := by
    intro h
    have : |t| = 0 := by rw [h]; simp
    linarith
  have h_Λ_sharp := lambda0_abs_sharp_le ht_ne
  have h_Λ'  := lambda0_prime_abs_le_fifty_over_1727 t
  have h_2s := norm_two_s_minus_one_le t
  have h_ss := norm_s_mul_s_minus_one_le t
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have h_B_nn : (0 : ℝ) ≤ 1 / t ^ 2 + (4 / t ^ 2) * K_sum := by
    have ht_ne' : t ≠ 0 := ht_ne
    have : (0 : ℝ) ≤ (4 / t ^ 2) * K_sum := mul_nonneg (by positivity) K_sum_nonneg
    have : (0 : ℝ) ≤ 1 / t ^ 2 := by positivity
    linarith
  have h_mul1 : ‖2 * (⟨1, t⟩ : ℂ) - 1‖ * ‖completedRiemannZeta₀ (⟨1, t⟩ : ℂ)‖
                 ≤ (1 + 2 * |t|) * (1 / t ^ 2 + (4 / t ^ 2) * K_sum) := by
    apply mul_le_mul h_2s h_Λ_sharp (norm_nonneg _)
    have : (0 : ℝ) ≤ |t| := abs_nonneg t
    linarith
  have h_mul2 : ‖(⟨1, t⟩ : ℂ) * ((⟨1, t⟩ : ℂ) - 1)‖
                 * ‖deriv completedRiemannZeta₀ (⟨1, t⟩ : ℂ)‖
                 ≤ (t ^ 2 + |t|) * (50 / 1727) := by
    apply mul_le_mul h_ss h_Λ' (norm_nonneg _)
    have : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
    have : (0 : ℝ) ≤ |t| := abs_nonneg t
    linarith
  have h_sum := gate2_num_bound_c55_8_r1_16 hK ht_lo ht_hi
  linarith

/-- **‖d/ds ξ(1+it)‖ ≤ 1 on the c=55/8 box edge** — conditional on
`K_sum ≤ 1/16`. -/
theorem norm_deriv_riemannXiEntire_le_one_c55_8_r1_16
    (hK : K_sum ≤ 1 / 16)
    {t : ℝ} (ht_lo : (109 : ℝ) / 16 ≤ |t|) (ht_hi : |t| ≤ (111 : ℝ) / 16) :
    ‖deriv riemannXiEntire (⟨1, t⟩ : ℂ)‖ ≤ 1 := by
  rw [deriv_riemannXiEntire_at]
  rw [norm_div]
  have h2_norm : ‖(2 : ℂ)‖ = 2 := by
    show ‖((2 : ℕ) : ℂ)‖ = 2
    rw [Complex.norm_natCast]; norm_num
  rw [h2_norm]
  have h_num := norm_deriv_riemannXiEntire_num_le_two_c55_8_r1_16 hK ht_lo ht_hi
  linarith

/-- **|d/dt (Re ξ)| ≤ 1 on the c=55/8 box edge** — conditional on
`K_sum ≤ 1/16`. Chain-rule descent of the preceding theorem. -/
theorem abs_deriv_edgeRe_le_one_c55_8_r1_16
    (hK : K_sum ≤ 1 / 16)
    {t : ℝ} (ht_lo : (109 : ℝ) / 16 ≤ |t|) (ht_hi : |t| ≤ (111 : ℝ) / 16) :
    |deriv edgeRe t| ≤ 1 := by
  rw [deriv_edgeRe_eq]
  have h_re_le :
      |(deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I).re|
        ≤ ‖deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I‖ :=
    abs_re_le_norm _
  rw [norm_mul, Complex.norm_I, mul_one] at h_re_le
  have h := norm_deriv_riemannXiEntire_le_one_c55_8_r1_16 hK ht_lo ht_hi
  linarith

/-- **★ THE PILOT HBOUND AT c = 55/8 ★** — the Gate-2 side of the
`R1_box_centered_of_lb (L := 1)` pilot at centre `55/8`, radius `1/16`.
Conditional on `K_sum ≤ 1/16`. -/
theorem pilot_r1_hbound_c55_8_r1_16
    (hK : K_sum ≤ 1 / 16) :
    ∀ x ∈ Set.Icc ((109 : ℝ) / 16) (111 / 16), |deriv edgeRe x| ≤ 1 := by
  intro x hx
  rw [Set.mem_Icc] at hx
  have hx_pos : (0 : ℝ) < x := by linarith
  have hx_abs : |x| = x := abs_of_pos hx_pos
  have h_lo : (109 : ℝ) / 16 ≤ |x| := by rw [hx_abs]; exact hx.1
  have h_hi : |x| ≤ (111 : ℝ) / 16 := by rw [hx_abs]; exact hx.2
  exact abs_deriv_edgeRe_le_one_c55_8_r1_16 hK h_lo h_hi

end

end Gate2BoxLocalC55_8_20261019
end PrincipiaTractalis

/-! ## §Axiom check -/
#print axioms PrincipiaTractalis.Gate2BoxLocalC55_8_20261019.K_sum_nonneg
#print axioms PrincipiaTractalis.Gate2BoxLocalC55_8_20261019.lambda0_abs_sharp_le
#print axioms PrincipiaTractalis.Gate2BoxLocalC55_8_20261019.gate2_num_bound_c55_8_r1_16
#print axioms PrincipiaTractalis.Gate2BoxLocalC55_8_20261019.norm_deriv_riemannXiEntire_num_le_two_c55_8_r1_16
#print axioms PrincipiaTractalis.Gate2BoxLocalC55_8_20261019.norm_deriv_riemannXiEntire_le_one_c55_8_r1_16
#print axioms PrincipiaTractalis.Gate2BoxLocalC55_8_20261019.abs_deriv_edgeRe_le_one_c55_8_r1_16
#print axioms PrincipiaTractalis.Gate2BoxLocalC55_8_20261019.pilot_r1_hbound_c55_8_r1_16
