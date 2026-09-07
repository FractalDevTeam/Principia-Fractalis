/-
# PF.Analytic.RiemannXiEdgeEnclosure_r331c

**r331c stage C0 — the t-ranged transpose of the r331a box interface.**

SKELETON, NOT YET ELABORATED. Written 2026-09-06 during the r331b C1 rebuild; no
build slot was taken. Proof bodies below are the intended shapes, mirroring the
monotone-step pattern the r331b bridges use. They have not been checked.

## Why this module exists

`RiemannXiThetaBoxEnclosure_r331a` ranges over `σ` at a FIXED `t`:

    structure BoxReEnclosure (σ_lo σ_hi t A B : ℝ)
      bounds : ∀ σ, σ_lo ≤ σ → σ ≤ σ_hi → A ≤ (Λ₀ ⟨σ,t⟩).re ∧ (Λ₀ ⟨σ,t⟩).re ≤ B

r331c's targets live on the RIGHT EDGE — `σ = 1` fixed, `t` ranging over `[0, 15]`:

    RIGHT LOW  :  Re ξ(1+it) > 1/1000
    RIGHT HIGH :  Im ξ(1+it) > 1/20000

The r331a structures cannot express that. Setting `σ_lo = σ_hi = 1` still fixes `t`
per instance, so covering `[0,15]` would need one instance per point. Hence the
transpose below.

What is reused unchanged from r331a: `re_xi_at_s` and `im_xi_at_s`, which are already
general in both arguments.

## The σ = 1 specialisation

With `p1 = σ(σ-1) - t²` and `q1 = t(2σ-1)`, at `σ = 1`:

    p1 = -t²        q1 = t

so `re_xi_at_s` / `im_xi_at_s` give directly

    Re ξ(1+it) = (1 - t²·(Λ₀ ⟨1,t⟩).re - t·(Λ₀ ⟨1,t⟩).im) / 2
    Im ξ(1+it) = (   - t²·(Λ₀ ⟨1,t⟩).im + t·(Λ₀ ⟨1,t⟩).re) / 2

Both reduce to enclosures of `Λ₀(1+it)` over t-boxes — the r331b pattern transposed.

SPDX-License-Identifier: Apache-2.0
-/

import PF.Analytic.RiemannXiThetaBoxEnclosure_r331a

namespace PrincipiaTractalis.RiemannXiEdgeEnclosure

open Complex Set
open scoped Real
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.RiemannXiThetaBoxEnclosure

/-! ## §1 — t-ranged enclosure witnesses (transpose of r331a §4) -/

/-- `EdgeReEnclosure t_lo t_hi σ A B` witnesses `A ≤ (Λ₀ ⟨σ,t⟩).re ≤ B` for every
`t ∈ [t_lo, t_hi]` at fixed `σ`. -/
structure EdgeReEnclosure (t_lo t_hi σ A B : ℝ) : Prop where
  bounds : ∀ t : ℝ, t_lo ≤ t → t ≤ t_hi →
    A ≤ (completedRiemannZeta₀ (⟨σ, t⟩ : ℂ)).re ∧
        (completedRiemannZeta₀ (⟨σ, t⟩ : ℂ)).re ≤ B

/-- `EdgeImEnclosure t_lo t_hi σ A B` — the same for the imaginary part. -/
structure EdgeImEnclosure (t_lo t_hi σ A B : ℝ) : Prop where
  bounds : ∀ t : ℝ, t_lo ≤ t → t ≤ t_hi →
    A ≤ (completedRiemannZeta₀ (⟨σ, t⟩ : ℂ)).im ∧
        (completedRiemannZeta₀ (⟨σ, t⟩ : ℂ)).im ≤ B

/-! ## §2 — polynomial factors on the right edge

At `σ = 1` these are exact, not enclosures: `p1 = -t²` and `q1 = t`. They are stated
as lemmas so the consumers below read like their r331a counterparts. -/

theorem edge_p1_eq (t : ℝ) : (1 : ℝ) * ((1 : ℝ) - 1) - t ^ 2 = -t ^ 2 := by ring

theorem edge_q1_eq (t : ℝ) : t * (2 * (1 : ℝ) - 1) = t := by ring

/-- On `[t_lo, t_hi] ⊆ [0, 15]`, `-t²` is bounded below by `-t_hi²` and above by
`-t_lo²`. -/
theorem edge_p1_bounds {t_lo t_hi t : ℝ} (h0 : 0 ≤ t_lo) (hl : t_lo ≤ t) (hh : t ≤ t_hi) :
    -t_hi ^ 2 ≤ -t ^ 2 ∧ -t ^ 2 ≤ -t_lo ^ 2 := by
  constructor
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ t_hi - t) (by linarith : (0:ℝ) ≤ t_hi + t)]
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ t - t_lo) (by linarith : (0:ℝ) ≤ t + t_lo)]

/-! ## §3 — consumers (transpose of r331a §5)

Same shape as `re_xi_lower_bound_from_enclosures` / `im_xi_lower_bound_from_enclosures`,
with the roles of `σ` and `t` exchanged. The arithmetic hypothesis is supplied at the
call site from the box's rational endpoints, exactly as in the r331b bridges. -/

/-- **RIGHT LOW consumer** — `Re ξ(σ+it) ≥ m` for every `t` in the box. -/
theorem re_xi_lower_bound_from_edge
    {t_lo t_hi σ : ℝ}
    {AΛ_re BΛ_re : ℝ} (h_re : EdgeReEnclosure t_lo t_hi σ AΛ_re BΛ_re)
    {AΛ_im BΛ_im : ℝ} (h_im : EdgeImEnclosure t_lo t_hi σ AΛ_im BΛ_im)
    {C_re_lo C_re_hi : ℝ}
    (h_pcre_lo : ∀ t : ℝ, t_lo ≤ t → t ≤ t_hi → C_re_lo ≤ σ * (σ - 1) - t ^ 2)
    (h_pcre_hi : ∀ t : ℝ, t_lo ≤ t → t ≤ t_hi → σ * (σ - 1) - t ^ 2 ≤ C_re_hi)
    {C_im_lo C_im_hi : ℝ}
    (h_pcim_lo : ∀ t : ℝ, t_lo ≤ t → t ≤ t_hi → C_im_lo ≤ t * (2 * σ - 1))
    (h_pcim_hi : ∀ t : ℝ, t_lo ≤ t → t ≤ t_hi → t * (2 * σ - 1) ≤ C_im_hi)
    (m : ℝ)
    (h_arith : ∀ (p1 p2 q1 q2 : ℝ),
        C_re_lo ≤ p1 → p1 ≤ C_re_hi → AΛ_re ≤ p2 → p2 ≤ BΛ_re →
        C_im_lo ≤ q1 → q1 ≤ C_im_hi → AΛ_im ≤ q2 → q2 ≤ BΛ_im →
        m ≤ (1 + p1 * p2 - q1 * q2) / 2) :
    ∀ t : ℝ, t_lo ≤ t → t ≤ t_hi → m ≤ (riemannXiEntire (⟨σ, t⟩ : ℂ)).re := by
  intro t h0 h1
  rw [re_xi_at_s]
  have ⟨hre_lo, hre_hi⟩ := h_re.bounds t h0 h1
  have ⟨him_lo, him_hi⟩ := h_im.bounds t h0 h1
  exact h_arith _ _ _ _
    (h_pcre_lo t h0 h1) (h_pcre_hi t h0 h1)
    hre_lo hre_hi
    (h_pcim_lo t h0 h1) (h_pcim_hi t h0 h1)
    him_lo him_hi

/-- **RIGHT HIGH consumer** — `Im ξ(σ+it) ≥ m` for every `t` in the box. -/
theorem im_xi_lower_bound_from_edge
    {t_lo t_hi σ : ℝ}
    {AΛ_re BΛ_re : ℝ} (h_re : EdgeReEnclosure t_lo t_hi σ AΛ_re BΛ_re)
    {AΛ_im BΛ_im : ℝ} (h_im : EdgeImEnclosure t_lo t_hi σ AΛ_im BΛ_im)
    {C_re_lo C_re_hi : ℝ}
    (h_pcre_lo : ∀ t : ℝ, t_lo ≤ t → t ≤ t_hi → C_re_lo ≤ σ * (σ - 1) - t ^ 2)
    (h_pcre_hi : ∀ t : ℝ, t_lo ≤ t → t ≤ t_hi → σ * (σ - 1) - t ^ 2 ≤ C_re_hi)
    {C_im_lo C_im_hi : ℝ}
    (h_pcim_lo : ∀ t : ℝ, t_lo ≤ t → t ≤ t_hi → C_im_lo ≤ t * (2 * σ - 1))
    (h_pcim_hi : ∀ t : ℝ, t_lo ≤ t → t ≤ t_hi → t * (2 * σ - 1) ≤ C_im_hi)
    (m : ℝ)
    (h_arith : ∀ (p1 p2 q1 q2 : ℝ),
        C_re_lo ≤ p1 → p1 ≤ C_re_hi → AΛ_re ≤ p2 → p2 ≤ BΛ_re →
        C_im_lo ≤ q1 → q1 ≤ C_im_hi → AΛ_im ≤ q2 → q2 ≤ BΛ_im →
        m ≤ (p1 * q2 + q1 * p2) / 2) :
    ∀ t : ℝ, t_lo ≤ t → t ≤ t_hi → m ≤ (riemannXiEntire (⟨σ, t⟩ : ℂ)).im := by
  intro t h0 h1
  rw [im_xi_at_s]
  have ⟨hre_lo, hre_hi⟩ := h_re.bounds t h0 h1
  have ⟨him_lo, him_hi⟩ := h_im.bounds t h0 h1
  exact h_arith _ _ _ _
    (h_pcre_lo t h0 h1) (h_pcre_hi t h0 h1)
    hre_lo hre_hi
    (h_pcim_lo t h0 h1) (h_pcim_hi t h0 h1)
    him_lo him_hi

end PrincipiaTractalis.RiemannXiEdgeEnclosure

/-! ## §Axiom check — to be added once this module is first elaborated.

Per release-gate item B0, the audit verdict must come from `#print axioms` output,
never from a zero exit code:

    #print axioms PrincipiaTractalis.RiemannXiEdgeEnclosure.re_xi_lower_bound_from_edge
    #print axioms PrincipiaTractalis.RiemannXiEdgeEnclosure.im_xi_lower_bound_from_edge

They are commented out here because this module is staged, not built, and a stale
audit line would be worse than none. -/
