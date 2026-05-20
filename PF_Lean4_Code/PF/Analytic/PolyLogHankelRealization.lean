/-
# PolyLog Hankel Realization — Partial Discharge

This file attacks the **load-bearing gap** of the Principia Fractalis
framework: `PolyLogHankelRealization` from `PF/Analytic/PolyLogSheaf.lean`.

The full target is to construct a function `f : ℂ → ℂ` satisfying
`IsPolyLogSheafSection s f` on `U_slit := (BranchCut ∪ {0})ᶜ` for
`0 < Re s < 1`, with `f` representable as the Hankel contour integral

  `f(z) = (Γ(1-s) / 2πi) · ∮_H (-t)^(s-1) / (e^t/z - 1) dt`.

## What this file delivers (PROVEN — no sorry, no axioms)

1. **`polyLog_hasDerivAt`** — derivative of the polyLog series for all
   `s` with `0 ≤ Re s` and `z` in the open unit disk. This is a
   strict generalization of the existing `polyLog_succ_hasDerivAt`
   (which only handles `Re(s+1) ≥ 1`); the new bound uses the summable
   majorant `Σ (n+1) r^n = 1/(1-r)^2`.

2. **`polyLog_differentiableOn_ball`** — `DifferentiableOn ℂ (polyLog s)
   (Metric.ball 0 1)` for `0 ≤ Re s`.

3. **`polyLog_analyticOnNhd_ball`** — `AnalyticOnNhd ℂ (polyLog s)
   (Metric.ball 0 1)` for `0 ≤ Re s`, via `DifferentiableOn.analyticOnNhd`.

4. **`ball_diff_zero_subset_U_slit`** — `(Metric.ball 0 1) \ {0} ⊆ U_slit`,
   the topological inclusion needed to restrict the analytic section.

5. **`polyLog_analyticOnNhd_U_slit_inter_ball`** — `polyLog s` is
   analytic on `U_slit ∩ Metric.ball 0 1`.

6. **`polyLog_Hankel`** — the canonical realization: defined as
   `polyLog s z`. On the open unit disk this IS the Hankel integral
   value (modulo the open `polyLog_eq_hankel_integral` identity); on
   the disk it satisfies all three section conditions.

7. **`isPolyLogSheafSection_on_ball`** — the partial section predicate:
   the restriction of the section axioms to `U_slit ∩ ball 0 1`.

8. **`polyLog_Hankel_isPolyLogSheafSection_on_ball`** — `polyLog_Hankel`
   satisfies the partial section predicate.

9. **`polyLogHankelRealization_from_extension`** — the full
   `PolyLogHankelRealization` reduces to an **extension hypothesis**:
   if `polyLog s` extends analytically to all of `U_slit` (preserving
   values on the disk), then `PolyLogHankelRealization s` holds.

## The residual blocker (NOT proven here)

The full `IsPolyLogSheafSection s f` on **all of U_slit** requires
constructing an analytic extension of `polyLog s` from `U_slit ∩ ball 0 1`
to all of `U_slit`. This is precisely the analytic-continuation
content of the Hankel identity:

  Build `f` via the Hankel contour integral, show it converges to
  an analytic function on `U_slit`, and show it agrees with the
  tsum on the disk.

The 17-module Hankel chain (`HankelContour`, `HankelCauchyCapstone`,
`HankelIntegrability`, ..., `HankelUpperEdgeDCTUnified`,
`HankelLowerEdgeDCTUnified`, `HankelSmallLoopBoundProof`,
`GammaHankel`) provides the building blocks: edge-integral DCT
convergence, small-loop bound vanishing, branch-jump trig identity,
Euler reflection. The composite Γ-reciprocal Hankel formula is
proven for the **constant** integrand `(-t)^(s-1) e^(-t)`. The
polylog Hankel formula uses a **z-dependent** integrand
`(-t)^(s-1) / (e^t/z - 1)` — bridging requires:

  (i) Geometric expansion `1/(e^t/z - 1) = Σ z^n e^(-nt)` on a
      neighborhood of the contour (convergent for `|z|e^(-Re t) < 1`).
  (ii) Termwise integration via DCT (justified by the existing
       per-term dominating-function infrastructure).
  (iii) Per-term reduction `∮_H (-t)^(s-1) e^(-nt) dt = n^(-s) · 2πi/Γ(1-s)`
        via substitution `u := n·t` (rescaling the Hankel contour).
  (iv) Summation: `Σ z^n n^(-s) = polyLog s z`.

The **specific lemma** that closes the gap:

```
theorem polyLog_eq_hankel_integral
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    {z : ℂ} (hz_slit : z ∈ U_slit) (hz_ball : ‖z‖ < 1) :
    polyLog s z = (Complex.Gamma (1 - s) / (2 * (Real.pi : ℂ) * I)) *
      hankelPolylogContourIntegral s z
```

where `hankelPolylogContourIntegral` is the closed-contour integral
of `hankelPolylogIntegrand s z` along a parameterized Hankel path.

**Mathlib infrastructure needed**:
- Closed-contour integral with piecewise parameterization (the
  edge + circle assembly is partial in `HankelContour.lean`).
- Cauchy's theorem on annular domains for the contour deformation
  (mathlib has `Complex.circleIntegral_eq_zero` on disks; needs
  annular generalization).
- Termwise integration of a sum-of-functions under DCT bounds (mathlib
  has `MeasureTheory.tsum_integral_of_summable` for the `μ`-integral
  version; needs adaptation to contour integrals).

These are the multi-month deliverables. This file mechanizes the
**analytic-on-the-disk** content (which IS the canonical realization
on the largest open where the tsum converges) and isolates the
extension as the SOLE remaining obstruction.

Stage L5 — PolyLog Hankel partial realization (2026-05-20).
-/

import PF.Analytic.PolyLogSheaf
import PF.Analytic.HankelCauchyCapstone
import PF.Analytic.PolyLogHankelIdentity
import Mathlib.Analysis.Analytic.Constructions

namespace PrincipiaTractalis.Analytic.Sheaf

open Complex Filter Topology Set
open PrincipiaTractalis.Analytic

/-! ## Stage 1: General `polyLog` derivative on the open unit disk

The existing `polyLog_succ_hasDerivAt` (PF.Analytic.Polylog) proves
the derivative of `polyLog (s+1)` for `0 ≤ Re s`, giving analyticity
of `polyLog s'` for `Re s' ≥ 1`. The Hankel-realization target needs
`0 < Re s < 1`, requiring a fresh proof with a different summable
majorant.

The summand `g_n(y) := y^(n+1)/(n+1)^s` has derivative
`g'_n(y) := (n+1) · y^n / (n+1)^s`. Its norm on `‖y‖ ≤ r` is bounded
by `(n+1) · r^n / (n+1)^(Re s) ≤ (n+1) · r^n` (since `(n+1)^(Re s) ≥ 1`
for `Re s ≥ 0`). The majorant `Σ (n+1) r^n = 1/(1-r)^2` is summable
for `r < 1`. -/

/-- **Derivative of `polyLog s` on the open unit disk** for `0 ≤ Re s`:

      `HasDerivAt (polyLog s) (Σ' n, (n+1)·z^n/(n+1)^s) z`

    for `‖z‖ < 1`. Direct application of
    `hasDerivAt_tsum_of_isPreconnected` with the majorant
    `u_n := (n+1) · r^n` where `r := (‖z‖+1)/2 < 1`. -/
theorem polyLog_hasDerivAt {s : ℂ} (hs : 0 ≤ s.re) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (polyLog s)
      (∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * z ^ n / ((n + 1 : ℕ) : ℂ) ^ s) z := by
  set r := (‖z‖ + 1) / 2 with hr_def
  have hz_lt_r : ‖z‖ < r := by show ‖z‖ < (‖z‖ + 1) / 2; linarith
  have hr_lt_one : r < 1 := by show (‖z‖ + 1) / 2 < 1; linarith
  have hr_nn : (0 : ℝ) ≤ r := by linarith [norm_nonneg z]
  have hr_pos : 0 < r := by linarith [norm_nonneg z]
  -- The summable majorant u_n := (n+1) · r^n
  let g : ℕ → ℂ → ℂ := fun n y => y ^ (n + 1) / ((n + 1 : ℕ) : ℂ) ^ s
  let g' : ℕ → ℂ → ℂ :=
    fun n y => ((n + 1 : ℕ) : ℂ) * y ^ n / ((n + 1 : ℕ) : ℂ) ^ s
  let u : ℕ → ℝ := fun n => (n + 1 : ℝ) * r ^ n
  have hu_geom := summable_pow_mul_geometric_of_norm_lt_one 1 (r := r)
                  (by rwa [Real.norm_eq_abs, abs_of_nonneg hr_nn])
  have hu_sum : Summable u := by
    have h0 := summable_geometric_of_lt_one hr_nn hr_lt_one
    have hsum : Summable (fun n : ℕ => (n : ℝ) * r ^ n + r ^ n) := by
      refine (hu_geom.congr ?_).add h0
      intro n; ring
    refine hsum.congr ?_
    intro n; show (n : ℝ) * r ^ n + r ^ n = (n + 1 : ℝ) * r ^ n; ring
  -- The open ball
  let t : Set ℂ := Metric.ball 0 r
  have ht_open : IsOpen t := Metric.isOpen_ball
  have hz_in_t : z ∈ t := by simp [t, Metric.mem_ball, hz_lt_r]
  have h0_in_t : (0 : ℂ) ∈ t := by simp [t, Metric.mem_ball]; exact hr_pos
  have hg_deriv : ∀ (n : ℕ) (y : ℂ), y ∈ t → HasDerivAt (g n) (g' n y) y := by
    intro n y _hy
    have h_pow : HasDerivAt (fun w : ℂ => w ^ (n + 1))
        ((((n + 1 : ℕ)) : ℂ) * y ^ n) y := by
      have h := hasDerivAt_pow (n + 1) y
      simp only [Nat.add_sub_cancel] at h
      exact h
    exact h_pow.div_const _
  have hg_bound : ∀ (n : ℕ) (y : ℂ), y ∈ t → ‖g' n y‖ ≤ u n := by
    intro n y hy
    simp only [t, Metric.mem_ball, dist_zero_right] at hy
    have h_y_le : ‖y‖ ≤ r := le_of_lt hy
    show ‖((n + 1 : ℕ) : ℂ) * y ^ n / ((n + 1 : ℕ) : ℂ) ^ s‖ ≤
         (n + 1 : ℝ) * r ^ n
    rw [norm_div, norm_mul, norm_pow]
    have h_pos : (0 : ℝ) < (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
    have h_norm_n1 : ‖((n + 1 : ℕ) : ℂ)‖ = (n + 1 : ℕ) := by
      rw [show (((n + 1 : ℕ) : ℂ)) = ((((n + 1 : ℕ) : ℝ)) : ℂ) from by norm_cast]
      rw [Complex.norm_real]
      exact abs_of_pos h_pos
    have h_denom : ‖((n + 1 : ℕ) : ℂ) ^ s‖ = (n + 1 : ℕ) ^ s.re := by
      rw [show (((n + 1 : ℕ) : ℂ)) = ((((n + 1 : ℕ) : ℝ)) : ℂ) from by norm_cast]
      exact Complex.norm_cpow_eq_rpow_re_of_pos h_pos s
    rw [h_norm_n1, h_denom]
    have h_denom_ge : (1 : ℝ) ≤ (n + 1 : ℕ) ^ s.re := by
      have h_base : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
      exact Real.one_le_rpow h_base hs
    have h_y_pow_le : ‖y‖ ^ n ≤ r ^ n := pow_le_pow_left₀ (norm_nonneg _) h_y_le n
    have h_n1_nn : (0 : ℝ) ≤ (n + 1 : ℕ) := by positivity
    have h_n1_y_nn : (0 : ℝ) ≤ (n + 1 : ℕ) * ‖y‖ ^ n := by positivity
    show (↑(n + 1) : ℝ) * ‖y‖ ^ n / (↑(n + 1) : ℝ) ^ s.re ≤ (↑n + 1) * r ^ n
    calc (↑(n + 1) : ℝ) * ‖y‖ ^ n / (↑(n + 1) : ℝ) ^ s.re
        ≤ (↑(n + 1) : ℝ) * ‖y‖ ^ n / 1 := by
          apply div_le_div_of_nonneg_left h_n1_y_nn (by norm_num) h_denom_ge
      _ = (↑(n + 1) : ℝ) * ‖y‖ ^ n := by rw [div_one]
      _ ≤ (↑(n + 1) : ℝ) * r ^ n := by
          apply mul_le_mul_of_nonneg_left h_y_pow_le h_n1_nn
      _ = (↑n + 1) * r ^ n := by push_cast; ring
  have hg0 : Summable (fun n => g n 0) := by
    have h_eq : ∀ n, g n (0 : ℂ) = 0 := by
      intro n; simp only [g]; rw [zero_pow (Nat.succ_ne_zero n), zero_div]
    simp_rw [h_eq]; exact summable_zero
  have h_preconn : IsPreconnected t := (convex_ball 0 r).isPreconnected
  exact hasDerivAt_tsum_of_isPreconnected (u := u)
    hu_sum ht_open h_preconn hg_deriv hg_bound h0_in_t hg0 hz_in_t

/-- **Differentiability of `polyLog s` on the open unit disk** for `0 ≤ Re s`. -/
theorem polyLog_differentiableOn_ball {s : ℂ} (hs : 0 ≤ s.re) :
    DifferentiableOn ℂ (polyLog s) (Metric.ball (0 : ℂ) 1) := by
  intro z hz
  have hz_norm : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
  exact (polyLog_hasDerivAt hs hz_norm).differentiableAt.differentiableWithinAt

/-- **Analyticity of `polyLog s` on the open unit ball** for `0 ≤ Re s`,
    via `DifferentiableOn.analyticOnNhd`. The open unit ball is open
    in ℂ, and `polyLog s` is differentiable there (Stage 1). -/
theorem polyLog_analyticOnNhd_ball {s : ℂ} (hs : 0 ≤ s.re) :
    AnalyticOnNhd ℂ (polyLog s) (Metric.ball (0 : ℂ) 1) :=
  (polyLog_differentiableOn_ball hs).analyticOnNhd Metric.isOpen_ball

/-! ## Stage 2: Topological inclusion `(ball 0 1) \ {0} ⊆ U_slit` -/

/-- **The open unit ball with origin removed is a subset of `U_slit`**.

    A point `z` with `‖z‖ < 1, z ≠ 0` lies in `U_slit = (BranchCut ∪ {0})ᶜ`:
    * `z ≠ 0` by hypothesis.
    * `z ∉ BranchCut`: if `z.im = 0` and `1 ≤ z.re`, then
      `1 ≤ z.re ≤ ‖z‖ < 1` is contradictory. -/
theorem ball_diff_zero_subset_U_slit :
    (Metric.ball (0 : ℂ) 1) \ {0} ⊆ U_slit := by
  intro z ⟨hz_ball, hz_ne⟩
  unfold U_slit BranchCut
  simp only [mem_compl_iff, mem_union, mem_setOf_eq, mem_singleton_iff,
             not_or, not_and, not_le] at *
  refine ⟨?_, hz_ne⟩
  intro _him
  -- Show ¬(1 ≤ z.re), i.e., z.re < 1
  simp only [Metric.mem_ball, dist_zero_right] at hz_ball
  have h_re_le : z.re ≤ ‖z‖ := Complex.re_le_norm z
  linarith

/-- **The open unit ball with origin removed is open** (since it's
    the open ball minus the singleton {0}). -/
theorem ball_diff_zero_isOpen :
    IsOpen ((Metric.ball (0 : ℂ) 1) \ {0}) :=
  Metric.isOpen_ball.sdiff isClosed_singleton

/-- **`U_slit ∩ ball 0 1 = ball 0 1 \ {0}`**: the intersection
    of the slit plane with the open unit ball equals the punctured
    open unit ball. -/
theorem U_slit_inter_ball_eq :
    U_slit ∩ Metric.ball (0 : ℂ) 1 = (Metric.ball (0 : ℂ) 1) \ {0} := by
  ext z
  simp only [mem_inter_iff, mem_diff, mem_singleton_iff]
  constructor
  · rintro ⟨hz_slit, hz_ball⟩
    refine ⟨hz_ball, ?_⟩
    intro h_zero
    apply hz_slit
    right; exact h_zero
  · rintro ⟨hz_ball, hz_ne⟩
    refine ⟨?_, hz_ball⟩
    exact ball_diff_zero_subset_U_slit ⟨hz_ball, hz_ne⟩

/-! ## Stage 3: Analyticity of `polyLog s` on `U_slit ∩ ball 0 1` -/

/-- **Analyticity of `polyLog s` on the slit-plane intersection with
    the open unit ball**: a direct consequence of analyticity on the
    open ball, restricted to the subset `(ball 0 1) \ {0}` = `U_slit ∩ ball 0 1`. -/
theorem polyLog_analyticOnNhd_U_slit_inter_ball {s : ℂ} (hs : 0 ≤ s.re) :
    AnalyticOnNhd ℂ (polyLog s) (U_slit ∩ Metric.ball (0 : ℂ) 1) := by
  intro z hz
  apply polyLog_analyticOnNhd_ball hs
  exact hz.2

/-! ## Stage 4: The Hankel realization function (canonical) -/

/-- **The Hankel realization of `polyLog s`**: defined as the existing
    `polyLog s z` (the formal tsum). On `|z| < 1` this is the
    analytic-on-the-disc value; the polylog Hankel identity says
    this equals the Hankel contour integral on the disk. Outside
    the disk, the tsum returns 0 by Lean's convention; the genuine
    Hankel-integral extension to all of `U_slit` is the analytic
    continuation (the load-bearing open construction).

    For the present partial realization, `polyLog_Hankel` is the
    canonical section on `U_slit ∩ ball 0 1`. -/
noncomputable def polyLog_Hankel (s : ℂ) (z : ℂ) : ℂ := polyLog s z

/-! ## Stage 5: Partial section predicate and proof

The full `IsPolyLogSheafSection s f` requires analyticity on ALL of
`U_slit`. Without the analytic-extension theorem (load-bearing open
conjecture), we cannot satisfy condition (1) on the global `U_slit`.

We define the **partial section predicate** restricted to
`U_slit ∩ ball 0 1` (the largest open subset where the tsum is
proven analytic), and discharge it for `polyLog_Hankel`. -/

/-- **The partial polylog sheaf section predicate**: restriction of
    `IsPolyLogSheafSection` to `U_slit ∩ ball 0 1`. -/
def IsPolyLogSheafSectionOnBall (s : ℂ) (f : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ f (U_slit ∩ Metric.ball (0 : ℂ) 1) ∧
  (∀ z ∈ U_slit ∩ Metric.ball (0 : ℂ) 1, f z = polyLog s z)

/-- **The Hankel realization satisfies the partial section predicate**
    on `U_slit ∩ ball 0 1` for `0 ≤ Re s`. Both conditions are
    immediate: analyticity from Stage 3, value-agreement by definition. -/
theorem polyLog_Hankel_isPolyLogSheafSectionOnBall
    {s : ℂ} (hs : 0 ≤ s.re) :
    IsPolyLogSheafSectionOnBall s (polyLog_Hankel s) := by
  refine ⟨?_, ?_⟩
  · -- AnalyticOnNhd on U_slit ∩ ball 0 1
    exact polyLog_analyticOnNhd_U_slit_inter_ball hs
  · -- Agreement with polyLog (true by definition of polyLog_Hankel)
    intro z _hz
    rfl

/-! ## Stage 6: The conditional full realization

The full `PolyLogHankelRealization s` follows from the **extension
hypothesis** that `polyLog s` admits an analytic continuation from
`U_slit ∩ ball 0 1` to all of `U_slit`. This extension is precisely
the analytic-continuation content of the Hankel integral.

We package this as a conditional theorem: GIVEN an analytic extension
`f` on `U_slit` agreeing with `polyLog s` on the disk, the
`PolyLogHankelRealization s` Prop holds. -/

/-- **The extension hypothesis**: there exists an analytic function on
    `U_slit` agreeing with `polyLog s` on `U_slit ∩ ball 0 1`.

    This is the **load-bearing open conjecture**: the analytic
    continuation of `polyLog s` from the disk to the full slit plane
    via the Hankel integral construction. -/
def PolyLogAnalyticExtensionExists (s : ℂ) : Prop :=
  ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f U_slit ∧
    (∀ z ∈ U_slit ∩ Metric.ball (0 : ℂ) 1, f z = polyLog s z)

/-- **Conditional polyLog Hankel realization**: GIVEN the extension
    hypothesis (load-bearing open conjecture), `PolyLogHankelRealization s`
    holds.

    Direct construction: take the extension `f`, verify the three
    section conditions:
    (1) `f` is analytic on `U_slit` — by hypothesis.
    (2) `f z = polyLog s z` for `z ∈ U_slit, ‖z‖ < 1` — by the
        extension's agreement property (the disc subset of U_slit is
        exactly `U_slit ∩ ball 0 1`).
    (3) `True` — trivial.

    This reduces the entire `PolyLogHankelRealization` to the extension
    construction. -/
theorem polyLogHankelRealization_from_extension
    {s : ℂ} (hext : PolyLogAnalyticExtensionExists s) :
    PolyLogHankelRealization s := by
  obtain ⟨f, hf_an, hf_agree⟩ := hext
  refine ⟨f, ?_, ?_, ?_⟩
  · exact hf_an
  · intro z hz_slit hz_ball
    apply hf_agree
    exact ⟨hz_slit, by simpa [Metric.mem_ball, dist_zero_right] using hz_ball⟩
  · trivial

/-! ## Stage 7: A SUFFICIENT condition via the disc-domain section

If we accept the polylog's domain as just the unit disc (the
"polylog tsum is the polylog" view), the partial section is in
fact the **complete** mathematical content available without analytic
continuation. The framework's manuscript-bridging step
(evaluation at `z_book` with `‖z_book‖ = 1` exactly) is precisely
where the extension is required — `z_book` lies on the boundary,
NOT in the open ball, so the tsum doesn't apply.

We state a **disc-only section existence** theorem to make the
partial content fully discharge-able. -/

/-- **Disc-only section existence**: `PolyLogHankelRealization` restricted
    to the disc is unconditionally established. Concretely: there exists
    a function `f` (namely `polyLog s`) satisfying the partial section
    predicate `IsPolyLogSheafSectionOnBall s f`. -/
theorem polyLogSheafSection_on_ball_exists {s : ℂ} (hs : 0 ≤ s.re) :
    ∃ f : ℂ → ℂ, IsPolyLogSheafSectionOnBall s f :=
  ⟨polyLog_Hankel s, polyLog_Hankel_isPolyLogSheafSectionOnBall hs⟩

/-! ## Roadmap and status

**Discharged (this file, axiom-free)**:
* `polyLog_hasDerivAt` — derivative of polyLog s on |z| < 1 for any Re s ≥ 0
* `polyLog_differentiableOn_ball` — DifferentiableOn on the open unit ball
* `polyLog_analyticOnNhd_ball` — AnalyticOnNhd on the open unit ball
* `ball_diff_zero_subset_U_slit` — topological inclusion
* `U_slit_inter_ball_eq` — set identity
* `polyLog_analyticOnNhd_U_slit_inter_ball` — restricted analyticity
* `polyLog_Hankel` — definition (canonical disk realization)
* `IsPolyLogSheafSectionOnBall` — partial section predicate
* `polyLog_Hankel_isPolyLogSheafSectionOnBall` — partial section proven
* `polyLogHankelRealization_from_extension` — conditional full realization
* `polyLogSheafSection_on_ball_exists` — unconditional partial existence

**Residual blocker** (the load-bearing open theorem):
* `PolyLogAnalyticExtensionExists s` — existence of an analytic
  extension from `U_slit ∩ ball 0 1` to all of `U_slit`. This is
  the analytic-continuation theorem realized via the Hankel integral.

**Mathlib infrastructure that would close the gap**:
1. `Complex.analyticContinuation` (or similar) for analytic
   continuation along a path. Mathlib has limited support for this
   beyond the immediate `AnalyticOnNhd` framework.
2. A formal `Complex.hankelContour` and `Complex.integralAlongHankelContour`
   primitive. Mathlib has `CircleIntegral` and `intervalIntegral` but
   does not have the closed-contour assembly with branch-cut handling.
3. The Erdélyi-Magnus-Oberhettinger-Tricomi closed-form
   `polyLog_eq_hankel_integral` (multi-page classical proof, not in
   mathlib).

**The key sub-lemma that would unlock the realization**:

```
theorem polyLog_hankel_extension
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    ∃ f : ℂ → ℂ,
      AnalyticOnNhd ℂ f U_slit ∧
      ∀ z, ‖z‖ < 1 → z ≠ 0 → f z = polyLog s z
```

Proven via:
1. Define `f z := (Γ(1-s) / 2πi) · ∮_H hankelPolylogIntegrand s z dt`
   along a parameterized Hankel contour.
2. Use parameter-dependent analyticity (differentiate under the integral
   sign via `intervalIntegral.differentiableUnderIntegral` and its
   analytic generalization).
3. Use the existing tsum-vs-Hankel identity for `z` in the disk.

This file's contribution: the analytic-on-the-disk piece is fully
mechanized, with no axioms and no sorries. The remaining work is
the contour-integral construction (analytic-extension piece), which
this file isolates as the single residual gap.

Stage L5 — PolyLog Hankel partial realization complete (2026-05-20).
-/

end PrincipiaTractalis.Analytic.Sheaf
