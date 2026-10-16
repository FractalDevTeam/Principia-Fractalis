/-
# PF.Analytic.PilotBoxes.R1_c6_r_pointwise_SCAFFOLD_2026_10_15

**Gate-1 pilot SCAFFOLD at c = 6, r = 1/16.** Design-ahead for the pointwise
panel pack at `c = 6`. The Gate-2 side (`|deriv edgeRe t| ≤ 1` on
`|t| ≤ 97/16`) is proved unconditionally via the same chain as the earlier
POC pilots (`(1 + 2|t|) · B + (t² + |t|) · B ≤ 2` with `B = 50/1727`).

The Gate-1 side is left as a CONDITIONAL theorem parameterised by rational
`(R_lb, R_ub, I_lb, I_ub)` enclosures of
`(Re Λ₀(1 + 6i), Im Λ₀(1 + 6i))` and a numerical gate hypothesis
`36 · R_ub + 6 · I_ub ≤ 3/4`. Once Agent M's Assembly module lands with
unconditional witnesses `R_lb ≤ Re Λ₀(1+6i) ≤ R_ub`,
`I_lb ≤ Im Λ₀(1+6i) ≤ I_ub`, this scaffold is instantiated to an
unconditional pilot `R1_box [95/16, 97/16]`.

### Explicit parameters

* `c = 6`, `r = 1/16`, box `= [95/16, 97/16] (= [5.9375, 6.0625])`.
* `Mc_lb = 1/8`, `L = 1`, strict margin: `L · r = 1/16 < 1/8 = Mc_lb` ✓.
* Gate-1 arithmetic (from `re_xi_at_s` at σ=1, t=6):
    `Re ξ(1+6i) = (1 - 36 · Re Λ₀ - 6 · Im Λ₀) / 2`.
  Target `Re ξ(1+6i) ≥ 1/8` ⟺ `1 - 36 · Re Λ₀ - 6 · Im Λ₀ ≥ 1/4`
  ⟺ `36 · Re Λ₀ + 6 · Im Λ₀ ≤ 3/4` — the input numeric hypothesis.
* Gate-2 cross-multiplied inequality at `|t| ≤ 97/16`:
    `(1 + 2|t|) · 50 + (t² + |t|) · 50 ≤ 2 · 1727`, closed by `nlinarith`.
  Numerically at `|t| = 97/16`: `1 + 3·(97/16) + (97/16)² ≈ 55.94 ≤ 69.08`. ✓

### What this file is / is NOT

* **IS:** a design-ahead scaffold with the Gate-2 side fully kernel-clean and
  the Gate-1 side wrapped as a conditional producer-slot. The final composition
  via `R1_box_centered_of_lb` is mechanical.
* **IS NOT:** an unconditional pilot. The Λ₀-enclosure hypotheses must be
  discharged by the (yet-to-land) Assembly module.
* **IS NOT:** a claim about the open Riemann Hypothesis. `rh_below_15_conditional`
  is RH on one finite rectangle, classically known since Riemann and Gram.

### No sorry, native_decide, axiom, Prop := True. autoImplicit off. Additive.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-15.
-/

import PF.Analytic.CenteredFormBridge_2026_10_13
import PF.Analytic.Lambda0UltraTightBoundsMellin_2026_10_14
import PF.Analytic.EdgeReDerivBound_2026_10_14

set_option autoImplicit false

namespace PrincipiaTractalis
namespace PilotR1Box_c6_r_pointwise_SCAFFOLD_20261015

open Complex Set
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.RiemannXiThetaBoxEnclosure
open PrincipiaTractalis.R1Neighborhood20261009
open PrincipiaTractalis.EdgeSignNeighborhoods20261013
open PrincipiaTractalis.CenteredFormBridge20261013
open PrincipiaTractalis.Lambda0UltraTightBoundsMellin20261014
open PrincipiaTractalis.EdgeReDerivBound20261014

noncomputable section

/-! ## §1 — Gate 1 (conditional): `1/8 ≤ Re ξ(1 + 6i)` from Λ₀ enclosure slots

Pointwise form: assuming yet-to-be-assembled Λ₀ enclosure bounds, the Gate-1
inequality drops out from `re_xi_at_s` and `linarith`.

SLOTS to be filled by Agent M's Assembly module:
  - SLOT 1 (`hR_ub`): `Re Λ₀(1+6i) ≤ R_ub`
  - SLOT 2 (`hI_ub`): `Im Λ₀(1+6i) ≤ I_ub`
  - SLOT 3 (`hR_lb`, `hI_lb`): lower-bound companions (not load-bearing for
    Gate-1 positivity; included for signature uniformity and for later Im-side /
    R3 reuse of the same enclosure pack).
  - Numerical gate: `36 · R_ub + 6 · I_ub ≤ 3/4`.
-/

/-- **Gate 1 for the c = 6 pilot (CONDITIONAL).** Given rational enclosure
bounds on `(Re, Im) Λ₀(1+6i)` and the numeric gate inequality
`36 · R_ub + 6 · I_ub ≤ 3/4`, concludes `1/8 ≤ Re ξ(1 + 6i)`.

Instantiation plan: once Agent M's Assembly supplies unconditional
`Re Λ₀(1+6i) ≤ R_ub` and `Im Λ₀(1+6i) ≤ I_ub`, apply this theorem with those
hypotheses and discharge the arithmetic gate by `norm_num` on the exact
rationals. -/
theorem pilot_r1_hvalue_lb_at_c6_scaffold
    (R_lb R_ub I_lb I_ub : ℝ)
    (hR_lb : R_lb ≤ (completedRiemannZeta₀ (⟨1, 6⟩ : ℂ)).re)
    (hR_ub : (completedRiemannZeta₀ (⟨1, 6⟩ : ℂ)).re ≤ R_ub)
    (hI_lb : I_lb ≤ (completedRiemannZeta₀ (⟨1, 6⟩ : ℂ)).im)
    (hI_ub : (completedRiemannZeta₀ (⟨1, 6⟩ : ℂ)).im ≤ I_ub)
    (h_gate : 36 * R_ub + 6 * I_ub ≤ 3/4) :
    (1 / 8 : ℝ) ≤ (riemannXiEntire (⟨1, 6⟩ : ℂ)).re := by
  rw [re_xi_at_s]
  -- After `rw`: 1/8 ≤ (1 + (1·0 - 6²) · Re Λ₀ - 6·(2·1 - 1) · Im Λ₀) / 2
  --         =  (1 - 36 · Re Λ₀ - 6 · Im Λ₀) / 2
  -- Target reduces to: 36 · Re Λ₀ + 6 · Im Λ₀ ≤ 3/4.
  set re := (completedRiemannZeta₀ (⟨1, 6⟩ : ℂ)).re with hre_def
  set im := (completedRiemannZeta₀ (⟨1, 6⟩ : ℂ)).im with him_def
  -- re ≤ R_ub, im ≤ I_ub are the load-bearing inequalities.
  have h_re_up : re ≤ R_ub := hR_ub
  have h_im_up : im ≤ I_ub := hI_ub
  -- 36 · re + 6 · im ≤ 36 · R_ub + 6 · I_ub ≤ 3/4
  have h_combo : 36 * re + 6 * im ≤ 3/4 := by
    have h36 : 36 * re ≤ 36 * R_ub :=
      mul_le_mul_of_nonneg_left h_re_up (by norm_num : (0 : ℝ) ≤ 36)
    have h6  : 6 * im ≤ 6 * I_ub :=
      mul_le_mul_of_nonneg_left h_im_up (by norm_num : (0 : ℝ) ≤ 6)
    linarith
  -- Rewrite the goal's affine expression into `-(36·re + 6·im)` form.
  have hNum :
      (1 * (1 - 1) - (6 : ℝ) ^ 2) * re - 6 * (2 * 1 - 1) * im
        = -(36 * re + 6 * im) := by ring
  linarith

/-! ## §2 — Gate 2 (unconditional): `|deriv edgeRe t| ≤ 1` on `|t| ≤ 97/16`

Same chain as pilots 1–13 and the c=11/2 / c=23/4 POCs:
  `(1 + 2|t|) · (50/1727) + (t² + |t|) · (50/1727) ≤ 2` at `|t| ≤ 97/16`.
-/

/-- Numerator-norm bound used by `‖deriv ξ(1+it)‖ ≤ 1` at `|t| ≤ 97/16`. -/
private lemma gate2_num_bound_c6_r1_16 {t : ℝ} (ht : |t| ≤ 97/16) :
    (1 + 2 * |t|) * (50 / 1727) + (t ^ 2 + |t|) * (50 / 1727) ≤ 2 := by
  have h_abs_nn : (0 : ℝ) ≤ |t| := abs_nonneg t
  have h_t_sq_bd : t ^ 2 ≤ (97/16) ^ 2 := by nlinarith [abs_le.mp ht]
  nlinarith [h_t_sq_bd, h_abs_nn, ht]

/-- **Gate 2 numerator norm.** For `|t| ≤ 97/16`,
`‖(2s - 1) · Λ₀ + s(s - 1) · Λ₀'‖ ≤ 2`, hence `‖deriv ξ‖ = ‖·‖/2 ≤ 1`. -/
theorem norm_deriv_riemannXiEntire_le_one_at_t_le_c6_r {t : ℝ}
    (ht : |t| ≤ (6 + 1/16 : ℝ)) :
    ‖deriv riemannXiEntire (⟨1, t⟩ : ℂ)‖ ≤ 1 := by
  have ht' : |t| ≤ 97/16 := by
    have : (6 + 1/16 : ℝ) = 97/16 := by norm_num
    rw [this] at ht; exact ht
  rw [deriv_riemannXiEntire_at]
  have h_Λ  := lambda0_abs_le_fifty_over_1727 t
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
    have h_sum := gate2_num_bound_c6_r1_16 ht'
    linarith
  linarith

/-- Chain-rule descent: `|deriv edgeRe t| ≤ ‖deriv ξ(1+it)‖ ≤ 1`. -/
theorem abs_deriv_edgeRe_le_one_at_t_le_c6_r {t : ℝ}
    (ht : |t| ≤ (6 + 1/16 : ℝ)) :
    |deriv edgeRe t| ≤ 1 := by
  rw [deriv_edgeRe_eq]
  have h_re_le :
      |(deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I).re|
        ≤ ‖deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I‖ :=
    abs_re_le_norm _
  rw [norm_mul, Complex.norm_I, mul_one] at h_re_le
  have h := norm_deriv_riemannXiEntire_le_one_at_t_le_c6_r ht
  linarith

/-- Specialisation of Gate 2 to the box `[95/16, 97/16]`. -/
theorem pilot_r1_hbound_c6_r1_16 :
    ∀ x ∈ Set.Icc ((95 : ℝ) / 16) (97 / 16), |deriv edgeRe x| ≤ 1 := by
  intro x hx
  rw [Set.mem_Icc] at hx
  have hx_abs : |x| ≤ (6 + 1/16 : ℝ) := by
    have heq : (6 + 1/16 : ℝ) = 97/16 := by norm_num
    rw [heq, abs_le]
    refine ⟨by linarith, hx.2⟩
  exact abs_deriv_edgeRe_le_one_at_t_le_c6_r hx_abs

/-! ## §3 — SCAFFOLD composition: conditional pilot box -/

/-- **SCAFFOLD** final c=6 pilot (CONDITIONAL). Zero hypotheses on
`riemannXiEntire` once the Λ₀ enclosure bounds are plugged in via the
yet-to-land Assembly module.

Instantiation: supply unconditional `hR_lb, hR_ub, hI_lb, hI_ub` from the
Assembly module plus `h_gate : 36 · R_ub + 6 · I_ub ≤ 3/4` by `norm_num`.
Produces: `R1_box [95/16, 97/16]`. -/
theorem pilot_r1_box_c6_r1_16_pointwise_closed
    (R_lb R_ub I_lb I_ub : ℝ)
    (hR_lb : R_lb ≤ (completedRiemannZeta₀ (⟨1, 6⟩ : ℂ)).re)
    (hR_ub : (completedRiemannZeta₀ (⟨1, 6⟩ : ℂ)).re ≤ R_ub)
    (hI_lb : I_lb ≤ (completedRiemannZeta₀ (⟨1, 6⟩ : ℂ)).im)
    (hI_ub : (completedRiemannZeta₀ (⟨1, 6⟩ : ℂ)).im ≤ I_ub)
    (h_gate : 36 * R_ub + 6 * I_ub ≤ 3/4) :
    ∀ t ∈ Icc ((95/16 : ℝ)) (97/16),
      0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re := by
  have h_icc_rewrite : Icc ((95/16 : ℝ)) (97/16)
      = Icc ((6 : ℝ) - 1/16) ((6 : ℝ) + 1/16) := by
    congr 1 <;> norm_num
  rw [h_icc_rewrite]
  refine R1_box_centered_of_lb
    (c := 6) (r := 1/16) (L := 1) (Mc_lb := 1/8)
    (by norm_num : (0 : ℝ) ≤ 1/16)
    (pilot_r1_hvalue_lb_at_c6_scaffold R_lb R_ub I_lb I_ub
      hR_lb hR_ub hI_lb hI_ub h_gate)
    ?_
    (by norm_num : (1 : ℝ) * (1/16) < 1/8)
  intro x hx
  have hx' : x ∈ Icc ((95/16 : ℝ)) (97/16) := by
    rw [h_icc_rewrite]; exact hx
  exact pilot_r1_hbound_c6_r1_16 x hx'

end

/-! ## §Axiom check -/

#print axioms pilot_r1_hvalue_lb_at_c6_scaffold
#print axioms gate2_num_bound_c6_r1_16
#print axioms norm_deriv_riemannXiEntire_le_one_at_t_le_c6_r
#print axioms abs_deriv_edgeRe_le_one_at_t_le_c6_r
#print axioms pilot_r1_hbound_c6_r1_16
#print axioms pilot_r1_box_c6_r1_16_pointwise_closed

end PilotR1Box_c6_r_pointwise_SCAFFOLD_20261015
end PrincipiaTractalis
