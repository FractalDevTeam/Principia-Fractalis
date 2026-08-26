/-
# r331a — SHARED CERTIFIED THETA-ENCLOSURE CORE FOR T=15 BOUNDARY BOXES

★ 2026-08-26.  Stage 1 of the four-stage r331 chain.  Provides the
shared analytic + certificate infrastructure that Stages 2-4 consume:

  (§1) Real / imaginary decomposition of `s(s-1)` at `s = ⟨σ, t⟩`.

  (§2) Closed real forms
       `Re ξ(σ+it) = (1 + (σ(σ-1) - t²)·Re Λ₀ - t(2σ-1)·Im Λ₀) / 2`
       `Im ξ(σ+it) = ((σ(σ-1) - t²)·Im Λ₀ + t(2σ-1)·Re Λ₀) / 2`
       from the r325 definition `ξ(s) = (s(s-1)·Λ₀(s) + 1) / 2`.

  (§3) σ-endpoint monotone enclosures of the theta-integral exponents
       `u^(σ/2 - 1)` and `u^((1-σ)/2 - 1)` on `u ≥ 1`, `σ ∈ [σ_lo, σ_hi]`,
       via `Real.rpow_le_rpow_of_exponent_le` — the r331 directive's
       critical simplification (no interval-valued exponents needed).

  (§4) `BoxReEnclosure` / `BoxImEnclosure` propositional structures
       packaging the certified rational enclosures of
       `Re Λ₀(σ+it)` / `Im Λ₀(σ+it)` over a rational σ-box at fixed `t`.

  (§5) Generic CERTIFICATE CONSUMER lemmas — three variants
       (`re_xi_upper_bound_from_enclosures`,
       `re_xi_lower_bound_from_enclosures`,
       `im_xi_lower_bound_from_enclosures`) — which given
       `BoxRe/ImEnclosure` + polynomial-factor enclosures produce a
       rational interval containing `Re ξ` / `Im ξ` throughout the box.

The consumers are the sole load-bearing endpoints downstream: r331b
(TOP: closes `Re ξ(σ+15i) < -1/10000` for σ ∈ [1/2, 1] via 8 σ-box
`BoxRe/ImEnclosure` instances) and r331c (RIGHT LOW: closes
`Re ξ(1+it) > 1/1000`; RIGHT HIGH: closes `Im ξ(1+it) > 1/20000`).

The actual `BoxRe/ImEnclosure` producers — truncated theta series
with `omega_partial_error` bound + `Ioi T` tail bound + interval
arithmetic — live in Stages 2-3 alongside the σ-box splits and
committed generator/panel data.  Building them here (without a
consuming certificate) would violate the r331 "no scaffolding-only
commits" directive.  Building them in r331b/c keeps every producer
directly proof-consumed.

No `sorry`, no `native_decide`, no `axiom`.  Zero project axioms.

SPDX-License-Identifier: Apache-2.0
-/
import PF.Analytic.RiemannXiEntire_r325
import PF.Analytic.RiemannXiSymmetries_r326
import PF.Analytic.RiemannXiBottomEdgeUnconditional_r329b
import PF.Analytic.XiThetaIntegral
import PF.Analytic.XiQuadrature

open Complex Set Topology Filter MeasureTheory
open scoped ComplexConjugate Real
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.RiemannXiSymmetries
open PrincipiaTractalis.RiemannXiBottomEdgeUnconditional
open PrincipiaTractalis.XiThetaIntegral
open PrincipiaTractalis.XiQuadrature

noncomputable section

namespace PrincipiaTractalis.RiemannXiThetaBoxEnclosure

/-! ## §1 — `s(s-1)` real / imag at `s = ⟨σ, t⟩` -/

/-- `Re(s(s-1)) = σ(σ-1) - t²` at `s = ⟨σ, t⟩`. -/
lemma re_s_mul_s_sub_one (σ t : ℝ) :
    ((⟨σ, t⟩ : ℂ) * ((⟨σ, t⟩ : ℂ) - 1)).re = σ * (σ - 1) - t ^ 2 := by
  simp [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  ring

/-- `Im(s(s-1)) = t(2σ-1)` at `s = ⟨σ, t⟩`. -/
lemma im_s_mul_s_sub_one (σ t : ℝ) :
    ((⟨σ, t⟩ : ℂ) * ((⟨σ, t⟩ : ℂ) - 1)).im = t * (2 * σ - 1) := by
  simp [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  ring

/-! ## §2 — Re/Im ξ closed forms at `s = ⟨σ, t⟩` -/

/-- Real part of `s(s-1)·Λ₀(s)` at `s = ⟨σ, t⟩`, expanded. -/
lemma re_s_mul_s_sub_one_mul_Λ (σ t : ℝ) :
    (((⟨σ, t⟩ : ℂ) * ((⟨σ, t⟩ : ℂ) - 1)) * completedRiemannZeta₀ (⟨σ, t⟩ : ℂ)).re
      = (σ * (σ - 1) - t ^ 2) * (completedRiemannZeta₀ (⟨σ, t⟩ : ℂ)).re
          - t * (2 * σ - 1) * (completedRiemannZeta₀ (⟨σ, t⟩ : ℂ)).im := by
  rw [Complex.mul_re, re_s_mul_s_sub_one σ t, im_s_mul_s_sub_one σ t]

/-- Imaginary part of `s(s-1)·Λ₀(s)` at `s = ⟨σ, t⟩`, expanded. -/
lemma im_s_mul_s_sub_one_mul_Λ (σ t : ℝ) :
    (((⟨σ, t⟩ : ℂ) * ((⟨σ, t⟩ : ℂ) - 1)) * completedRiemannZeta₀ (⟨σ, t⟩ : ℂ)).im
      = (σ * (σ - 1) - t ^ 2) * (completedRiemannZeta₀ (⟨σ, t⟩ : ℂ)).im
          + t * (2 * σ - 1) * (completedRiemannZeta₀ (⟨σ, t⟩ : ℂ)).re := by
  rw [Complex.mul_im, re_s_mul_s_sub_one σ t, im_s_mul_s_sub_one σ t]

/-- **`re_xi_at_s`** — closed real form for `Re ξ(σ+it)`. -/
theorem re_xi_at_s (σ t : ℝ) :
    (riemannXiEntire (⟨σ, t⟩ : ℂ)).re
      = (1 + (σ * (σ - 1) - t ^ 2) * (completedRiemannZeta₀ (⟨σ, t⟩ : ℂ)).re
           - t * (2 * σ - 1) * (completedRiemannZeta₀ (⟨σ, t⟩ : ℂ)).im) / 2 := by
  unfold riemannXiEntire
  set N : ℂ :=
    (⟨σ, t⟩ : ℂ) * ((⟨σ, t⟩ : ℂ) - 1) * completedRiemannZeta₀ (⟨σ, t⟩ : ℂ) + 1
  show (N / 2).re = _
  have h2ne : ((2 : ℝ) : ℂ) ≠ 0 := by norm_num
  have hN_re : N.re
      = (σ * (σ - 1) - t ^ 2) * (completedRiemannZeta₀ (⟨σ, t⟩ : ℂ)).re
          - t * (2 * σ - 1) * (completedRiemannZeta₀ (⟨σ, t⟩ : ℂ)).im + 1 := by
    show ((⟨σ, t⟩ : ℂ) * ((⟨σ, t⟩ : ℂ) - 1) *
              completedRiemannZeta₀ (⟨σ, t⟩ : ℂ) + 1).re = _
    rw [Complex.add_re, Complex.one_re, re_s_mul_s_sub_one_mul_Λ]
  rw [show ((2 : ℂ) : ℂ) = ((2 : ℝ) : ℂ) from by norm_num]
  rw [Complex.div_ofReal_re, hN_re]
  ring

/-- **`im_xi_at_s`** — closed real form for `Im ξ(σ+it)`. -/
theorem im_xi_at_s (σ t : ℝ) :
    (riemannXiEntire (⟨σ, t⟩ : ℂ)).im
      = ((σ * (σ - 1) - t ^ 2) * (completedRiemannZeta₀ (⟨σ, t⟩ : ℂ)).im
           + t * (2 * σ - 1) * (completedRiemannZeta₀ (⟨σ, t⟩ : ℂ)).re) / 2 := by
  unfold riemannXiEntire
  set N : ℂ :=
    (⟨σ, t⟩ : ℂ) * ((⟨σ, t⟩ : ℂ) - 1) * completedRiemannZeta₀ (⟨σ, t⟩ : ℂ) + 1
  show (N / 2).im = _
  have hN_im : N.im
      = (σ * (σ - 1) - t ^ 2) * (completedRiemannZeta₀ (⟨σ, t⟩ : ℂ)).im
          + t * (2 * σ - 1) * (completedRiemannZeta₀ (⟨σ, t⟩ : ℂ)).re := by
    show ((⟨σ, t⟩ : ℂ) * ((⟨σ, t⟩ : ℂ) - 1) *
              completedRiemannZeta₀ (⟨σ, t⟩ : ℂ) + 1).im = _
    rw [Complex.add_im, Complex.one_im, im_s_mul_s_sub_one_mul_Λ]
    ring
  rw [show ((2 : ℂ) : ℂ) = ((2 : ℝ) : ℂ) from by norm_num]
  rw [Complex.div_ofReal_im, hN_im]

/-! ## §3 — σ-endpoint monotone enclosure of `u^(...)` on `u ≥ 1` -/

lemma rpow_lo_bound_of_le {u σ : ℝ} (hu : 1 ≤ u) {σ_lo : ℝ} (hσ : σ_lo ≤ σ) :
    u ^ (σ_lo / 2 - 1) ≤ u ^ (σ / 2 - 1) :=
  Real.rpow_le_rpow_of_exponent_le hu (by linarith)

lemma rpow_hi_bound_of_le {u σ : ℝ} (hu : 1 ≤ u) {σ_hi : ℝ} (hσ : σ ≤ σ_hi) :
    u ^ (σ / 2 - 1) ≤ u ^ (σ_hi / 2 - 1) :=
  Real.rpow_le_rpow_of_exponent_le hu (by linarith)

lemma rpow_conj_lo_bound_of_le {u σ : ℝ} (hu : 1 ≤ u) {σ_hi : ℝ} (hσ : σ ≤ σ_hi) :
    u ^ ((1 - σ_hi) / 2 - 1) ≤ u ^ ((1 - σ) / 2 - 1) :=
  Real.rpow_le_rpow_of_exponent_le hu (by linarith)

lemma rpow_conj_hi_bound_of_le {u σ : ℝ} (hu : 1 ≤ u) {σ_lo : ℝ} (hσ : σ_lo ≤ σ) :
    u ^ ((1 - σ) / 2 - 1) ≤ u ^ ((1 - σ_lo) / 2 - 1) :=
  Real.rpow_le_rpow_of_exponent_le hu (by linarith)

/-! ## §4 — Enclosure-witness structures -/

/-- A `BoxReEnclosure σ_lo σ_hi t A B` witnesses a certified rational
enclosure `A ≤ (completedRiemannZeta₀ ⟨σ, t⟩).re ≤ B` for every
`σ ∈ [σ_lo, σ_hi]` at the given fixed `t`.  The producer (r331b, r331c)
must supply this via truncated theta + interval-arithmetic. -/
structure BoxReEnclosure (σ_lo σ_hi t A B : ℝ) : Prop where
  bounds : ∀ σ : ℝ, σ_lo ≤ σ → σ ≤ σ_hi →
    A ≤ (completedRiemannZeta₀ (⟨σ, t⟩ : ℂ)).re ∧
        (completedRiemannZeta₀ (⟨σ, t⟩ : ℂ)).re ≤ B

/-- A `BoxImEnclosure σ_lo σ_hi t A B` witnesses a certified rational
enclosure `A ≤ (completedRiemannZeta₀ ⟨σ, t⟩).im ≤ B` for every
`σ ∈ [σ_lo, σ_hi]` at fixed `t`. -/
structure BoxImEnclosure (σ_lo σ_hi t A B : ℝ) : Prop where
  bounds : ∀ σ : ℝ, σ_lo ≤ σ → σ ≤ σ_hi →
    A ≤ (completedRiemannZeta₀ (⟨σ, t⟩ : ℂ)).im ∧
        (completedRiemannZeta₀ (⟨σ, t⟩ : ℂ)).im ≤ B

/-! ## §5 — Generic certificate consumers

Three consumers.  Each takes:
  * `BoxReEnclosure` and `BoxImEnclosure` at fixed `t` over a rational σ-box;
  * elementary polynomial-factor enclosures on `σ(σ-1) - t²` and `t(2σ-1)`;
  * a purely arithmetic "combine" hypothesis that packages the linear /
    bilinear rational computation into the target bound.

The arithmetic hypothesis is delivered concretely at the call site
(usually via `by intros; nlinarith` or `by intros; linarith`) using the
specific rational endpoints of each box. -/

/-- **`re_xi_upper_bound_from_enclosures`** — SHARED consumer for the
TOP-edge sign statement `Re ξ(σ+15i) ≤ M` (and by strengthening ≤ to <
outside, `< -1/10000`).  Also usable for right-edge upper-bound work. -/
theorem re_xi_upper_bound_from_enclosures
    {σ_lo σ_hi t : ℝ}
    {AΛ_re BΛ_re : ℝ} (h_re : BoxReEnclosure σ_lo σ_hi t AΛ_re BΛ_re)
    {AΛ_im BΛ_im : ℝ} (h_im : BoxImEnclosure σ_lo σ_hi t AΛ_im BΛ_im)
    {C_re_lo C_re_hi : ℝ}
    (h_pcre_lo : ∀ σ : ℝ, σ_lo ≤ σ → σ ≤ σ_hi → C_re_lo ≤ σ * (σ - 1) - t ^ 2)
    (h_pcre_hi : ∀ σ : ℝ, σ_lo ≤ σ → σ ≤ σ_hi → σ * (σ - 1) - t ^ 2 ≤ C_re_hi)
    {C_im_lo C_im_hi : ℝ}
    (h_pcim_lo : ∀ σ : ℝ, σ_lo ≤ σ → σ ≤ σ_hi → C_im_lo ≤ t * (2 * σ - 1))
    (h_pcim_hi : ∀ σ : ℝ, σ_lo ≤ σ → σ ≤ σ_hi → t * (2 * σ - 1) ≤ C_im_hi)
    (M : ℝ)
    (h_arith : ∀ (p1 p2 q1 q2 : ℝ),
        C_re_lo ≤ p1 → p1 ≤ C_re_hi → AΛ_re ≤ p2 → p2 ≤ BΛ_re →
        C_im_lo ≤ q1 → q1 ≤ C_im_hi → AΛ_im ≤ q2 → q2 ≤ BΛ_im →
        (1 + p1 * p2 - q1 * q2) / 2 ≤ M) :
    ∀ σ : ℝ, σ_lo ≤ σ → σ ≤ σ_hi → (riemannXiEntire (⟨σ, t⟩ : ℂ)).re ≤ M := by
  intro σ h0 h1
  rw [re_xi_at_s]
  have ⟨hre_lo, hre_hi⟩ := h_re.bounds σ h0 h1
  have ⟨him_lo, him_hi⟩ := h_im.bounds σ h0 h1
  exact h_arith _ _ _ _
    (h_pcre_lo σ h0 h1) (h_pcre_hi σ h0 h1)
    hre_lo hre_hi
    (h_pcim_lo σ h0 h1) (h_pcim_hi σ h0 h1)
    him_lo him_hi

/-- **`re_xi_lower_bound_from_enclosures`** — symmetric consumer for
RIGHT-LOW `Re ξ(1+it) ≥ m` (and `> 1/1000` by strict tightening). -/
theorem re_xi_lower_bound_from_enclosures
    {σ_lo σ_hi t : ℝ}
    {AΛ_re BΛ_re : ℝ} (h_re : BoxReEnclosure σ_lo σ_hi t AΛ_re BΛ_re)
    {AΛ_im BΛ_im : ℝ} (h_im : BoxImEnclosure σ_lo σ_hi t AΛ_im BΛ_im)
    {C_re_lo C_re_hi : ℝ}
    (h_pcre_lo : ∀ σ : ℝ, σ_lo ≤ σ → σ ≤ σ_hi → C_re_lo ≤ σ * (σ - 1) - t ^ 2)
    (h_pcre_hi : ∀ σ : ℝ, σ_lo ≤ σ → σ ≤ σ_hi → σ * (σ - 1) - t ^ 2 ≤ C_re_hi)
    {C_im_lo C_im_hi : ℝ}
    (h_pcim_lo : ∀ σ : ℝ, σ_lo ≤ σ → σ ≤ σ_hi → C_im_lo ≤ t * (2 * σ - 1))
    (h_pcim_hi : ∀ σ : ℝ, σ_lo ≤ σ → σ ≤ σ_hi → t * (2 * σ - 1) ≤ C_im_hi)
    (m : ℝ)
    (h_arith : ∀ (p1 p2 q1 q2 : ℝ),
        C_re_lo ≤ p1 → p1 ≤ C_re_hi → AΛ_re ≤ p2 → p2 ≤ BΛ_re →
        C_im_lo ≤ q1 → q1 ≤ C_im_hi → AΛ_im ≤ q2 → q2 ≤ BΛ_im →
        m ≤ (1 + p1 * p2 - q1 * q2) / 2) :
    ∀ σ : ℝ, σ_lo ≤ σ → σ ≤ σ_hi → m ≤ (riemannXiEntire (⟨σ, t⟩ : ℂ)).re := by
  intro σ h0 h1
  rw [re_xi_at_s]
  have ⟨hre_lo, hre_hi⟩ := h_re.bounds σ h0 h1
  have ⟨him_lo, him_hi⟩ := h_im.bounds σ h0 h1
  exact h_arith _ _ _ _
    (h_pcre_lo σ h0 h1) (h_pcre_hi σ h0 h1)
    hre_lo hre_hi
    (h_pcim_lo σ h0 h1) (h_pcim_hi σ h0 h1)
    him_lo him_hi

/-- **`im_xi_lower_bound_from_enclosures`** — consumer for RIGHT-HIGH
`Im ξ(1+it) ≥ m` (and `> 1/20000`). -/
theorem im_xi_lower_bound_from_enclosures
    {σ_lo σ_hi t : ℝ}
    {AΛ_re BΛ_re : ℝ} (h_re : BoxReEnclosure σ_lo σ_hi t AΛ_re BΛ_re)
    {AΛ_im BΛ_im : ℝ} (h_im : BoxImEnclosure σ_lo σ_hi t AΛ_im BΛ_im)
    {C_re_lo C_re_hi : ℝ}
    (h_pcre_lo : ∀ σ : ℝ, σ_lo ≤ σ → σ ≤ σ_hi → C_re_lo ≤ σ * (σ - 1) - t ^ 2)
    (h_pcre_hi : ∀ σ : ℝ, σ_lo ≤ σ → σ ≤ σ_hi → σ * (σ - 1) - t ^ 2 ≤ C_re_hi)
    {C_im_lo C_im_hi : ℝ}
    (h_pcim_lo : ∀ σ : ℝ, σ_lo ≤ σ → σ ≤ σ_hi → C_im_lo ≤ t * (2 * σ - 1))
    (h_pcim_hi : ∀ σ : ℝ, σ_lo ≤ σ → σ ≤ σ_hi → t * (2 * σ - 1) ≤ C_im_hi)
    (m : ℝ)
    (h_arith : ∀ (p1 p2 q1 q2 : ℝ),
        C_re_lo ≤ p1 → p1 ≤ C_re_hi → AΛ_re ≤ p2 → p2 ≤ BΛ_re →
        C_im_lo ≤ q1 → q1 ≤ C_im_hi → AΛ_im ≤ q2 → q2 ≤ BΛ_im →
        m ≤ (p1 * q2 + q1 * p2) / 2) :
    ∀ σ : ℝ, σ_lo ≤ σ → σ ≤ σ_hi → m ≤ (riemannXiEntire (⟨σ, t⟩ : ℂ)).im := by
  intro σ h0 h1
  rw [im_xi_at_s]
  have ⟨hre_lo, hre_hi⟩ := h_re.bounds σ h0 h1
  have ⟨him_lo, him_hi⟩ := h_im.bounds σ h0 h1
  exact h_arith _ _ _ _
    (h_pcre_lo σ h0 h1) (h_pcre_hi σ h0 h1)
    hre_lo hre_hi
    (h_pcim_lo σ h0 h1) (h_pcim_hi σ h0 h1)
    him_lo him_hi

end PrincipiaTractalis.RiemannXiThetaBoxEnclosure

/-! ## §Axiom check -/

#print axioms PrincipiaTractalis.RiemannXiThetaBoxEnclosure.re_s_mul_s_sub_one
#print axioms PrincipiaTractalis.RiemannXiThetaBoxEnclosure.im_s_mul_s_sub_one
#print axioms PrincipiaTractalis.RiemannXiThetaBoxEnclosure.re_xi_at_s
#print axioms PrincipiaTractalis.RiemannXiThetaBoxEnclosure.im_xi_at_s
#print axioms PrincipiaTractalis.RiemannXiThetaBoxEnclosure.rpow_lo_bound_of_le
#print axioms PrincipiaTractalis.RiemannXiThetaBoxEnclosure.rpow_hi_bound_of_le
#print axioms PrincipiaTractalis.RiemannXiThetaBoxEnclosure.rpow_conj_lo_bound_of_le
#print axioms PrincipiaTractalis.RiemannXiThetaBoxEnclosure.rpow_conj_hi_bound_of_le
#print axioms PrincipiaTractalis.RiemannXiThetaBoxEnclosure.re_xi_upper_bound_from_enclosures
#print axioms PrincipiaTractalis.RiemannXiThetaBoxEnclosure.re_xi_lower_bound_from_enclosures
#print axioms PrincipiaTractalis.RiemannXiThetaBoxEnclosure.im_xi_lower_bound_from_enclosures
