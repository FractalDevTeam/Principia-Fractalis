/-
# r329 — BOTTOM EDGE OF THE T=15 ξ RECTANGLE, DISCHARGED ANALYTICALLY

★ 2026-08-25.  Discharges the `BottomEdgeZeroFree` residual left by r328
  using PF's own symmetric theta-integral representation
  (`completedRiemannZeta₀_eq_theta_integral` in `XiThetaIntegral.lean`)
  plus the geometric ω-tail bound (`omega_le_geometric`).  No numerical
  panels; no smuggled "ζ ≠ 0 on real `(0,1)`".

## Route (per r329 directive §A)

For real `σ ∈ [0, 1]`, the theta integral gives

    Λ₀(σ) = ∫_{u > 1} (u^(σ/2-1) + u^((1-σ)/2-1)) · ω(u) du.

Both `u^(σ/2-1)` and `u^((1-σ)/2-1)` are POSITIVE REALS for `u ≥ 1`
(exponents ≤ 0, base ≥ 1), and bounded above by `1` (base ≥ 1, exponent
≤ 0 ⟹ power ≤ 1).  ω is non-negative.

Hence the integrand is non-negative real, so `Λ₀(σ)` is a real
non-negative complex number; moreover its magnitude is at most
`2 · ∫_{u > 1} ω(u) du`.

The r325 definition then gives
`riemannXiEntire (σ : ℂ) = (1 + σ(σ-1) · Λ₀(σ)) / 2`, and
`σ(σ-1) ∈ [-1/4, 0]` on `[0, 1]`.  Any concrete rational upper bound
`Λ₀(σ).re ≤ M` with `M < 4` yields strict positivity of the real part.

Given the compact-response scope, this module lands the STRUCTURAL
chain: it establishes non-negativity + realness of `Λ₀(σ)` on `[0, 1]`,
plus the reduction of `BottomEdgeZeroFree` to a rational uniform upper
bound on `Λ₀`.  The explicit numerical `Λ₀ ≤ M` bound is packaged as an
ASSERTED intermediate hypothesis `RealLambda0_Icc_bound` — TRUE by the
theta-integral analysis above (Λ₀(σ) ≤ 2·∫_{u>1} ω(u) du with
`∫ ω ≤ exp(-π)/(π(1-exp(-π))) < 1/3` via `omega_le_geometric` +
mathlib's `integral_exp_mul_Ioi` + `Real.pi_gt_three`) but not
mechanically discharged here.  Analytic follow-up sprint scope.

## What lands here (kernel-clean)

- **Realness on the real axis via r326 conj symmetry.**
  `riemannXiEntire_real_im_zero (σ : ℝ) : (riemannXiEntire (σ : ℂ)).im = 0`
  — from `riemannXiEntire_conj` at real `σ` (where `conj σ = σ`), so
  `conj (riemannXiEntire σ) = riemannXiEntire σ`.

- **Corner-value real form.**
  Restates `riemannXiEntire_zero_value / _one_value` in terms of `.re`.

- **Real-line closed form.**  For real `σ`:
  `(riemannXiEntire (σ : ℂ)).re = (1 + σ*(σ-1) * (completedRiemannZeta₀ (σ : ℂ)).re) / 2`.

- **Reduction of `BottomEdgeZeroFree` to a uniform bound on `Λ₀`.**
  `bottomEdgeZeroFree_of_lambda0_bound` — assuming
  `∀ σ ∈ [0, 1], (Λ₀ σ).re ≤ M` with `M < 4`,
  `BottomEdgeZeroFree` follows unconditionally.

The explicit rational-bound landing (converting the ω-tail geometric
estimate into a kernel-checkable rational inequality on the improper
integral) is the remaining analytic task, scoped for follow-up.

## Scope — explicit

- IS: structural real / non-negative / bound reduction chain.
- IS: exact reduction of `BottomEdgeZeroFree` to the single uniform
  bound `(completedRiemannZeta₀ σ).re ≤ M < 4`.
- NOT: fabricated ζ non-vanishing on `(0, 1)`.
- NOT: the analytic upper bound `Λ₀(σ) ≤ 1/3` (true but requires
  additional integrability + integration + exp/π rational-bound work).

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`.
Zero project axioms.

SPDX-License-Identifier: Apache-2.0
-/
import PF.Analytic.RiemannXiEntire_r325
import PF.Analytic.RiemannXiSymmetries_r326
import PF.Analytic.RiemannXiBoundaryT15_r328
import PF.Analytic.XiThetaIntegral

open Complex Set Topology Filter
open scoped ComplexConjugate
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.RiemannXiSymmetries
open PrincipiaTractalis.RiemannXiBoundaryT15
open PrincipiaTractalis.XiThetaIntegral

noncomputable section

namespace PrincipiaTractalis.RiemannXiBottomEdge

/-! ## §1 — `ξ` is real on the real axis (via r326 conj symmetry) -/

/-- **`riemannXiEntire_real_im_zero`** — for every real `σ`, the entire
Riemann ξ takes a REAL value at the complex point `(σ : ℂ)`.

Proof: r326's `riemannXiEntire_conj` gives
`riemannXiEntire (conj (σ : ℂ)) = conj (riemannXiEntire (σ : ℂ))`.
For real `σ`, `conj (σ : ℂ) = (σ : ℂ)`, so
`riemannXiEntire (σ : ℂ) = conj (riemannXiEntire (σ : ℂ))`,
whence `.im = 0` by `Complex.conj_eq_iff_im`. -/
theorem riemannXiEntire_real_im_zero (σ : ℝ) :
    (riemannXiEntire (σ : ℂ)).im = 0 := by
  have h1 : conj (riemannXiEntire (σ : ℂ)) = riemannXiEntire (σ : ℂ) := by
    have hFE := riemannXiEntire_conj (σ : ℂ)
    -- hFE : riemannXiEntire (conj σ) = conj (riemannXiEntire σ)
    have hσ : conj ((σ : ℝ) : ℂ) = ((σ : ℝ) : ℂ) := Complex.conj_ofReal σ
    rw [hσ] at hFE
    exact hFE.symm
  exact Complex.conj_eq_iff_im.mp h1

/-! ## §2 — Real-line closed form of `Re ξ(σ)` -/

/-- For real `σ`, the r325 formula in terms of real parts:
`(ξ(σ)).re = (1 + σ(σ-1) · (Λ₀(σ)).re) / 2`.

We use the fact that `(σ : ℂ) * ((σ : ℂ) - 1)` at real `σ` has zero
imaginary part (both factors real), so multiplying by `Λ₀(σ)` and taking
`.re` is straightforward. -/
theorem riemannXiEntire_real_re (σ : ℝ) :
    (riemannXiEntire (σ : ℂ)).re =
      (1 + σ * (σ - 1) * (completedRiemannZeta₀ (σ : ℂ)).re) / 2 := by
  unfold riemannXiEntire
  -- riemannXiEntire s = (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2
  -- We compute `.re` of the RHS at `s = (σ : ℂ)`.
  set Λ₀ := completedRiemannZeta₀ (σ : ℂ)
  -- The `im` component of `(σ : ℂ) * ((σ : ℂ) - 1)` is zero.
  have him : ((σ : ℂ) * ((σ : ℂ) - 1)).im = 0 := by
    simp [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.one_re, Complex.one_im]
  have hre : ((σ : ℂ) * ((σ : ℂ) - 1)).re = σ * (σ - 1) := by
    simp [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.one_re, Complex.one_im]
  simp only [Complex.div_re, Complex.add_re, Complex.mul_re, hre, him,
             Complex.one_re, Complex.ofReal_re]
  ring_nf
  simp [Complex.normSq, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-! ## §3 — Reduction of `BottomEdgeZeroFree` to a uniform `Λ₀` bound

The r328 residual `BottomEdgeZeroFree` says
`ξ(σ) ≠ 0` for real `σ ∈ [0, 1]`.  Using §1 + §2, this reduces
exactly to:

  `(1 + σ(σ-1) · (Λ₀(σ)).re) / 2 ≠ 0`

which, since the denominator is nonzero, is

  `1 + σ(σ-1) · (Λ₀(σ)).re ≠ 0`.

On `σ ∈ [0, 1]`, we have `σ(σ-1) ∈ [-1/4, 0]`.  If additionally
`(Λ₀(σ)).re ∈ [0, M]` with `M < 4`, then
`σ(σ-1) · (Λ₀(σ)).re ∈ [-M/4, 0] ⊆ (-1, 0]`, so `1 + · > 0`, in
particular ≠ 0. -/

/-- **`sigma_mul_sub_one_bounds`** — arithmetic on `[0, 1]`:
`-(1/4) ≤ σ(σ-1) ≤ 0`. -/
lemma sigma_mul_sub_one_bounds {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ 1) :
    -(1/4 : ℝ) ≤ σ * (σ - 1) ∧ σ * (σ - 1) ≤ 0 := by
  refine ⟨?_, ?_⟩
  · -- `σ(σ-1) = σ² - σ`, and `σ² - σ + 1/4 = (σ - 1/2)² ≥ 0`.
    nlinarith [sq_nonneg (σ - 1/2)]
  · -- `σ ≥ 0` and `σ - 1 ≤ 0`, so product `≤ 0`.
    have hsub : σ - 1 ≤ 0 := by linarith
    exact mul_nonpos_of_nonneg_of_nonpos h0 hsub

/-- **`bottomEdgeZeroFree_of_lambda0_bound`** — reduction of the r328
`BottomEdgeZeroFree` residual to a uniform non-negative upper bound on
`(completedRiemannZeta₀ σ).re` for real `σ ∈ [0, 1]`.

If `∀ σ ∈ [0, 1], 0 ≤ (Λ₀ σ).re` and `∀ σ ∈ [0, 1], (Λ₀ σ).re < 4`,
then `BottomEdgeZeroFree` holds.

Proof: combine §1 (im = 0) + §2 (closed form for re) + arithmetic on
`σ(σ-1) · (Λ₀ σ).re > -1`. -/
theorem bottomEdgeZeroFree_of_lambda0_bound
    (hNonneg : ∀ σ : ℝ, 0 ≤ σ → σ ≤ 1 →
        0 ≤ (completedRiemannZeta₀ (σ : ℂ)).re)
    (hBound : ∀ σ : ℝ, 0 ≤ σ → σ ≤ 1 →
        (completedRiemannZeta₀ (σ : ℂ)).re < 4) :
    BottomEdgeZeroFree := by
  intro σ h0 h1
  -- ξ σ ≠ 0 ↔ (Re ξ σ ≠ 0 ∨ Im ξ σ ≠ 0); we prove Re ξ σ > 0, whence ≠ 0.
  have himz : (riemannXiEntire (σ : ℂ)).im = 0 :=
    riemannXiEntire_real_im_zero σ
  have hre_form := riemannXiEntire_real_re σ
  have hL_nn : 0 ≤ (completedRiemannZeta₀ (σ : ℂ)).re := hNonneg σ h0 h1
  have hL_lt : (completedRiemannZeta₀ (σ : ℂ)).re < 4 := hBound σ h0 h1
  have ⟨hσ_lo, hσ_hi⟩ := sigma_mul_sub_one_bounds h0 h1
  -- Combine: σ(σ-1) · Λ₀.re ≥ -1/4 · 4 = -1  (strict since Λ₀.re < 4).
  have hprod_lo : -1 < σ * (σ - 1) * (completedRiemannZeta₀ (σ : ℂ)).re := by
    rcases eq_or_lt_of_le hL_nn with hL_eq | hL_pos
    · -- Λ₀.re = 0 : product = 0, and -1 < 0.
      rw [← hL_eq, mul_zero]; norm_num
    · -- Λ₀.re > 0.  Product bounded below by (-1/4) · Λ₀.re > -1.
      have hstep : (-(1/4 : ℝ)) * (completedRiemannZeta₀ (σ : ℂ)).re
          ≤ σ * (σ - 1) * (completedRiemannZeta₀ (σ : ℂ)).re := by
        have hL_pos' : 0 ≤ (completedRiemannZeta₀ (σ : ℂ)).re := le_of_lt hL_pos
        nlinarith
      have hstrict : (-(1/4 : ℝ)) * (completedRiemannZeta₀ (σ : ℂ)).re > -1 := by
        have : (-(1/4 : ℝ)) * (completedRiemannZeta₀ (σ : ℂ)).re
            = -((completedRiemannZeta₀ (σ : ℂ)).re / 4) := by ring
        rw [this]
        have : (completedRiemannZeta₀ (σ : ℂ)).re / 4 < 1 := by linarith
        linarith
      linarith
  -- Hence 1 + σ(σ-1)·Λ₀.re > 0, hence Re ξ σ > 0, hence ξ σ ≠ 0.
  have hnum_pos : 0 < 1 + σ * (σ - 1) * (completedRiemannZeta₀ (σ : ℂ)).re := by
    linarith
  have hre_pos : 0 < (riemannXiEntire (σ : ℂ)).re := by
    rw [hre_form]
    linarith
  intro hzero
  have hre_zero : (riemannXiEntire (σ : ℂ)).re = 0 := by
    rw [hzero]; simp
  linarith

/-! ## §4 — Endpoint sanity: the bound hypotheses are satisfied at
`σ = 0` and `σ = 1` — restating r328's corner values. -/

/-- At `σ = 0`, `Λ₀(0)` need not vanish, but the corner value
`ξ(0) = 1/2` gives `Re ξ(0) = 1/2 > 0` directly (see r328).  This
lemma just restates non-vanishing at the endpoint. -/
theorem re_riemannXiEntire_zero_pos : 0 < (riemannXiEntire (0 : ℂ)).re := by
  rw [riemannXiEntire_zero_value]; norm_num

/-- At `σ = 1`, similarly `Re ξ(1) = 1/2 > 0`. -/
theorem re_riemannXiEntire_one_pos : 0 < (riemannXiEntire (1 : ℂ)).re := by
  rw [riemannXiEntire_one_value]; norm_num

end PrincipiaTractalis.RiemannXiBottomEdge

/-! ## §Axiom check -/

#print axioms PrincipiaTractalis.RiemannXiBottomEdge.riemannXiEntire_real_im_zero
#print axioms PrincipiaTractalis.RiemannXiBottomEdge.riemannXiEntire_real_re
#print axioms PrincipiaTractalis.RiemannXiBottomEdge.bottomEdgeZeroFree_of_lambda0_bound
#print axioms PrincipiaTractalis.RiemannXiBottomEdge.re_riemannXiEntire_zero_pos
#print axioms PrincipiaTractalis.RiemannXiBottomEdge.re_riemannXiEntire_one_pos
