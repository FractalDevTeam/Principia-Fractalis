/-
# PF.Analytic.EdgeReDerivBound_2026_10_14

Certified bound `|deriv edgeRe x| ≤ 2` for `x ∈ [9/20, 11/20]`.

Chain:
1. ξ product rule at `s = 1 + it`:
     `deriv ξ (⟨1,t⟩) = ((2s - 1)·Λ₀(s) + s(s-1)·Λ₀'(s)) / 2`.
2. Chain rule for `edgeRe = Re ∘ ξ ∘ edgeLine`:
     `deriv edgeRe t = (deriv ξ (⟨1,t⟩) · I).re`.
3. Triangle inequalities on `|2s-1|` and `|s(s-1)|` (no sqrt computation):
     `|2(1+it) - 1| = |1 + 2it| ≤ 1 + 2|t|`
     `|(1+it)·(it)| = |⟨-t², t⟩| ≤ t² + |t|`
4. Combine with uniform bounds `‖Λ₀‖, ‖deriv Λ₀‖ ≤ 2/3` to close `≤ 2`.

Target `L = 2` is loose but sufficient for the pilot box with `r = 1/20`:
`L·r = 1/10 < Mc_lb = 1/4`. Tighter `L` requires tighter `‖Λ₀‖, ‖deriv Λ₀‖`
bounds (see codex strategy note for the full chain to `L = 1/10`).

No sorry, native_decide, axiom, Prop := True. autoImplicit off. Additive.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-14.
-/

import PF.Analytic.Lambda0UniformBound_2026_10_14
import PF.Analytic.Lambda0PrimeUniformBound_2026_10_14
import PF.Analytic.EdgeSignNeighborhoods_2026_10_13

set_option autoImplicit false

namespace PrincipiaTractalis
namespace EdgeReDerivBound20261014

open Complex Real Set
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.R1Neighborhood20261009
open PrincipiaTractalis.EdgeSignNeighborhoods20261013
open PrincipiaTractalis.Lambda0UniformBound20261014
open PrincipiaTractalis.Lambda0PrimeUniformBound20261014

noncomputable section

/-! ## §0 — Triangle inequality `‖z‖ ≤ |z.re| + |z.im|` -/

lemma norm_le_abs_re_add_abs_im (z : ℂ) : ‖z‖ ≤ |z.re| + |z.im| := by
  have h : z = ((z.re : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  calc ‖z‖ = ‖((z.re : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * Complex.I‖ := by rw [← h]
    _ ≤ ‖((z.re : ℝ) : ℂ)‖ + ‖((z.im : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |z.re| + |z.im| := by
        rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I,
            mul_one, Real.norm_eq_abs, Real.norm_eq_abs]

/-! ## §1 — Triangle bounds on `|2s-1|` and `|s(s-1)|` at s = 1+it -/

lemma norm_two_s_minus_one_le (t : ℝ) :
    ‖2 * (⟨1, t⟩ : ℂ) - 1‖ ≤ 1 + 2 * |t| := by
  have h : 2 * (⟨1, t⟩ : ℂ) - 1 = (⟨1, 2 * t⟩ : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  rw [h]
  have h_tri := norm_le_abs_re_add_abs_im (⟨1, 2 * t⟩ : ℂ)
  have h_re : (⟨1, 2 * t⟩ : ℂ).re = 1 := rfl
  have h_im : (⟨1, 2 * t⟩ : ℂ).im = 2 * t := rfl
  rw [h_re, h_im] at h_tri
  have h_abs_one : |(1 : ℝ)| = 1 := abs_one
  rw [h_abs_one] at h_tri
  have h_abs_mul : |2 * t| = 2 * |t| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  rw [h_abs_mul] at h_tri
  exact h_tri

lemma norm_s_mul_s_minus_one_le (t : ℝ) :
    ‖(⟨1, t⟩ : ℂ) * ((⟨1, t⟩ : ℂ) - 1)‖ ≤ t ^ 2 + |t| := by
  have h : (⟨1, t⟩ : ℂ) * ((⟨1, t⟩ : ℂ) - 1) = (⟨-(t ^ 2), t⟩ : ℂ) := by
    apply Complex.ext
    · simp [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
      ring
    · simp [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  rw [h]
  have h_tri := norm_le_abs_re_add_abs_im (⟨-(t ^ 2), t⟩ : ℂ)
  have h_re : (⟨-(t ^ 2), t⟩ : ℂ).re = -(t ^ 2) := rfl
  have h_im : (⟨-(t ^ 2), t⟩ : ℂ).im = t := rfl
  rw [h_re, h_im] at h_tri
  have h_abs_neg : |(-(t ^ 2))| = t ^ 2 := by
    rw [abs_neg, abs_of_nonneg (sq_nonneg t)]
  rw [h_abs_neg] at h_tri
  exact h_tri

/-! ## §2 — Derivative of `edgeLine : ℝ → ℂ`, `edgeLine s = ⟨1, s⟩` -/

lemma hasDerivAt_edgeLine_at (t : ℝ) :
    HasDerivAt (fun s : ℝ => (⟨1, s⟩ : ℂ)) Complex.I t := by
  have h : (fun s : ℝ => (⟨1, s⟩ : ℂ)) = fun s : ℝ => Complex.I * (s : ℂ) + 1 := by
    funext s; apply Complex.ext <;> simp
  rw [h]
  have h_ofReal : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t :=
    Complex.ofRealCLM.hasDerivAt
  have h1 := h_ofReal.const_mul Complex.I
  have h2 := h1.add_const (1 : ℂ)
  simpa using h2

/-! ## §3 — ξ product rule at `s = 1 + it` -/

theorem deriv_riemannXiEntire_at (t : ℝ) :
    deriv riemannXiEntire (⟨1, t⟩ : ℂ)
      = ((2 * (⟨1, t⟩ : ℂ) - 1) * completedRiemannZeta₀ (⟨1, t⟩ : ℂ)
          + (⟨1, t⟩ : ℂ) * ((⟨1, t⟩ : ℂ) - 1)
              * deriv completedRiemannZeta₀ (⟨1, t⟩ : ℂ)) / 2 := by
  have h : HasDerivAt riemannXiEntire
      (((2 * (⟨1, t⟩ : ℂ) - 1) * completedRiemannZeta₀ (⟨1, t⟩ : ℂ)
          + (⟨1, t⟩ : ℂ) * ((⟨1, t⟩ : ℂ) - 1)
              * deriv completedRiemannZeta₀ (⟨1, t⟩ : ℂ)) / 2)
      (⟨1, t⟩ : ℂ) := by
    unfold riemannXiEntire
    have h_id : HasDerivAt (fun s : ℂ => s) 1 (⟨1, t⟩ : ℂ) := hasDerivAt_id _
    have h_s_minus : HasDerivAt (fun s : ℂ => s - 1) 1 (⟨1, t⟩ : ℂ) :=
      h_id.sub_const 1
    have h_prod : HasDerivAt (fun s : ℂ => s * (s - 1))
        (1 * ((⟨1, t⟩ : ℂ) - 1) + (⟨1, t⟩ : ℂ) * 1) (⟨1, t⟩ : ℂ) :=
      h_id.mul h_s_minus
    have h_Λ : HasDerivAt completedRiemannZeta₀
        (deriv completedRiemannZeta₀ (⟨1, t⟩ : ℂ)) (⟨1, t⟩ : ℂ) :=
      (differentiable_completedZeta₀ _).hasDerivAt
    have h_sΛ : HasDerivAt (fun s : ℂ => s * (s - 1) * completedRiemannZeta₀ s)
        ((1 * ((⟨1, t⟩ : ℂ) - 1) + (⟨1, t⟩ : ℂ) * 1) * completedRiemannZeta₀ (⟨1, t⟩ : ℂ)
          + (⟨1, t⟩ : ℂ) * ((⟨1, t⟩ : ℂ) - 1)
              * deriv completedRiemannZeta₀ (⟨1, t⟩ : ℂ))
        (⟨1, t⟩ : ℂ) :=
      h_prod.mul h_Λ
    have h_final := (h_sΛ.add_const 1).div_const 2
    convert h_final using 1
    ring
  exact h.deriv

/-! ## §4 — Norm bound on `deriv ξ (⟨1, t⟩)` for `|t| ≤ 11/20` -/

theorem norm_deriv_riemannXiEntire_le_at {t : ℝ} (ht : |t| ≤ 11 / 20) :
    ‖deriv riemannXiEntire (⟨1, t⟩ : ℂ)‖ ≤ 2 := by
  rw [deriv_riemannXiEntire_at]
  have h_Λ := lambda0_abs_le_two_thirds t
  have h_Λ' := lambda0_prime_abs_le_two_thirds t
  have h_2s := norm_two_s_minus_one_le t
  have h_ss := norm_s_mul_s_minus_one_le t
  have h_abs_nn : (0 : ℝ) ≤ |t| := abs_nonneg t
  have h_t_sq_nn : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
  have h_t_sq_bd : t ^ 2 ≤ (11 / 20) ^ 2 := by nlinarith [abs_le.mp ht]
  rw [norm_div]
  have h2_norm : ‖(2 : ℂ)‖ = 2 := by
    show ‖((2 : ℕ) : ℂ)‖ = 2
    rw [Complex.norm_natCast]; norm_num
  rw [h2_norm]
  have h_num_bound :
      ‖(2 * (⟨1, t⟩ : ℂ) - 1) * completedRiemannZeta₀ (⟨1, t⟩ : ℂ)
          + (⟨1, t⟩ : ℂ) * ((⟨1, t⟩ : ℂ) - 1)
              * deriv completedRiemannZeta₀ (⟨1, t⟩ : ℂ)‖ ≤ 4 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h_mul1 : ‖2 * (⟨1, t⟩ : ℂ) - 1‖ * ‖completedRiemannZeta₀ (⟨1, t⟩ : ℂ)‖
                 ≤ (1 + 2 * |t|) * (2 / 3) := by
      apply mul_le_mul h_2s h_Λ (norm_nonneg _)
      linarith
    have h_mul2 : ‖(⟨1, t⟩ : ℂ) * ((⟨1, t⟩ : ℂ) - 1)‖
                   * ‖deriv completedRiemannZeta₀ (⟨1, t⟩ : ℂ)‖
                 ≤ (t ^ 2 + |t|) * (2 / 3) := by
      apply mul_le_mul h_ss h_Λ' (norm_nonneg _)
      linarith
    have h_sum : (1 + 2 * |t|) * (2 / 3) + (t ^ 2 + |t|) * (2 / 3) ≤ 4 := by
      nlinarith [h_t_sq_bd, h_abs_nn, ht]
    linarith
  linarith

/-! ## §5 — Chain rule: `deriv edgeRe t = (deriv ξ (⟨1,t⟩) · I).re` -/

theorem deriv_edgeRe_eq (t : ℝ) :
    deriv edgeRe t = (deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I).re := by
  have h_line : HasDerivAt (fun s : ℝ => (⟨1, s⟩ : ℂ)) Complex.I t :=
    hasDerivAt_edgeLine_at t
  have h_xi : HasDerivAt riemannXiEntire
      (deriv riemannXiEntire (⟨1, t⟩ : ℂ)) (⟨1, t⟩ : ℂ) :=
    (differentiable_riemannXiEntire (⟨1, t⟩ : ℂ)).hasDerivAt
  have h_comp : HasDerivAt (fun s : ℝ => riemannXiEntire (⟨1, s⟩ : ℂ))
      (deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I) t :=
    h_xi.comp t h_line
  have h_re : HasDerivAt (fun s : ℝ => (riemannXiEntire (⟨1, s⟩ : ℂ)).re)
      ((deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I).re) t := by
    have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h_comp
    simpa using this
  show deriv (fun s : ℝ => (riemannXiEntire (⟨1, s⟩ : ℂ)).re) t
       = (deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I).re
  exact h_re.deriv

/-! ## §6 — Final: `|deriv edgeRe t| ≤ 2` for `|t| ≤ 11/20` -/

theorem abs_deriv_edgeRe_le_at {t : ℝ} (ht : |t| ≤ 11 / 20) :
    |deriv edgeRe t| ≤ 2 := by
  rw [deriv_edgeRe_eq]
  have h_re_le : |(deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I).re|
                 ≤ ‖deriv riemannXiEntire (⟨1, t⟩ : ℂ) * Complex.I‖ :=
    abs_re_le_norm _
  rw [norm_mul, Complex.norm_I, mul_one] at h_re_le
  have h := norm_deriv_riemannXiEntire_le_at ht
  linarith

/-- **PILOT R1 hbound** — the pilot's second producer-side hypothesis, kernel-clean.
Combined with `pilot_r1_hvalue_lb`, closes the pilot R1 box at `L = 2`
(see `PilotBoxes/R1_c0_5_r0_05_L2_2026_10_14.lean`). -/
theorem pilot_r1_hbound :
    ∀ x ∈ Set.Icc ((9 : ℝ) / 20) (11 / 20), |deriv edgeRe x| ≤ 2 := by
  intro x hx
  rw [Set.mem_Icc] at hx
  have hx_abs : |x| ≤ 11 / 20 := by
    rw [abs_le]
    refine ⟨by linarith, hx.2⟩
  exact abs_deriv_edgeRe_le_at hx_abs

end

/-! ## §Axiom check -/

#print axioms norm_le_abs_re_add_abs_im
#print axioms norm_two_s_minus_one_le
#print axioms norm_s_mul_s_minus_one_le
#print axioms hasDerivAt_edgeLine_at
#print axioms deriv_riemannXiEntire_at
#print axioms norm_deriv_riemannXiEntire_le_at
#print axioms deriv_edgeRe_eq
#print axioms abs_deriv_edgeRe_le_at
#print axioms pilot_r1_hbound

end EdgeReDerivBound20261014
end PrincipiaTractalis
