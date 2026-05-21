/-
# Jonquières ζ-Series — Analyticity (Discharge of
# `JonquieresZetaSeriesAnalyticityHypothesis`)

This file attacks the ζ-series analyticity half of the Jonquières
expansion analytic-continuation chain. The Γ-term half is proved
UNCONDITIONAL in `PF/Analytic/JonquieresAnalyticity.lean` as
`jonquieresGammaTerm_analyticOnNhd` on the maximal correct domain
`JonquieresAnalyticDomain := SlitPlane ∩ Complex.slitPlane`.

The ζ-series side proves:

  `AnalyticOnNhd ℂ (jonquieresZetaSeries s)
      (JonquieresAnalyticDomain ∩ {z | ‖log z‖ < 2π})`

## Mathematical content

Each term `z ↦ ζ(s - k) · (log z)^k / k!` is analytic on
`Complex.slitPlane` (constant in z times analytic factor `log` powered
to `k`, divided by a constant). The tsum is analytic on the
convergence region given a summable majorant.

The classical bound, near any point `z₀` with `‖log z₀‖ < 2π`:
* pick `R ∈ (‖log z₀‖, 2π)`;
* on a small ball around `z₀` (where `‖log w‖ < R`), the term is
  bounded by `‖ζ(s - k)‖ · R^k / k!`;
* this majorant is summable in `k` (the genuine analytic content,
  reducible to the Bernoulli growth bridge of
  `JonquieresZetaSeriesSummable.lean`).

Mathlib's `differentiableOn_tsum_of_summable_norm` then gives
`DifferentiableOn ℂ (z ↦ ∑' k, ...) (small ball)`, hence (via
`DifferentiableOn.analyticOnNhd` from `Analysis.Complex.CauchyIntegral`)
`AnalyticOnNhd` on the ball, hence `AnalyticAt` at `z₀`.

## What this file delivers (axiom-free, no `sorry`)

1. **Per-term analyticity** `jonquieresZetaTerm_analyticOnNhd` —
   each fixed-k term is analytic on `Complex.slitPlane`. UNCONDITIONAL.

2. **`JonquieresZetaUniformGrowthBridge s`** — the named residual
   hypothesis that for any radius `R < 2π`, the majorant
   `k ↦ ‖ζ(s - k)‖ · R^k / k!` is summable. This is the precise
   analytic content needed for locally uniform convergence; it
   subsumes the pointwise `JonquieresZetaSummableFromBernoulliBridge`
   in a uniform-on-disc-of-radius-R form.

3. **`jonquieresZetaSeries_analyticOnNhd_of_bridge`** — CAPSTONE
   CONDITIONAL: under `JonquieresZetaUniformGrowthBridge s`, the
   ζ-series is analytic on
   `JonquieresAnalyticDomain ∩ {z | ‖log z‖ < 2π}`.

4. **`jonquieresExpansion_analyticOnNhd_of_bridge`** — combined
   with `jonquieresGammaTerm_analyticOnNhd`, the full Jonquières
   expansion is analytic on the same domain.

5. **`JonquieresZetaSeriesAnalyticityHypothesis_of_bridge`** — the
   bridge discharges the named `JonquieresZetaSeriesAnalyticityHypothesis`
   residual of `JonquieresAnalyticity.lean`.

## Architecture

* The `Bridge` Prop is the SAME load-bearing content as the existing
  ζ-summability bridge, expressed at the level of a uniform radius
  rather than a single z. Both reduce to the same Bernoulli-growth
  asymptotic + functional-equation interpolation.

* This file does NOT prove the bridge unconditionally. The bridge
  is the genuine open analytic-number-theory content (named
  `JonquieresZetaSummableFromBernoulliBridge` in
  `JonquieresZetaSeriesSummable.lean`; this file gives its
  uniform-radius variant).

Stage L13 — Jonquières ζ-series analyticity (conditional discharge).
-/

import PF.Analytic.JonquieresAnalyticity
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit

namespace PrincipiaTractalis.Analytic.Sheaf

open Complex Filter Topology Set Metric
open PrincipiaTractalis.Analytic

/-! ## Step 1: Per-term analyticity (unconditional) -/

/-- Each term `z ↦ ζ(s-k) · (log z)^k / k!` is analytic on
    `Complex.slitPlane`. UNCONDITIONAL. -/
theorem jonquieresZetaTerm_analyticOnNhd_complexSlitPlane (s : ℂ) (k : ℕ) :
    AnalyticOnNhd ℂ (fun z => jonquieresZetaTerm s z k) Complex.slitPlane := by
  intro z hz
  unfold jonquieresZetaTerm
  -- = ζ(s-k) * (log z)^k / k!
  -- = ζ(s-k) * (log z)^k * (1/k!)
  have h_log : AnalyticAt ℂ Complex.log z := analyticAt_clog hz
  have h_log_pow : AnalyticAt ℂ (fun w => (Complex.log w) ^ k) z := h_log.pow k
  have h_const_left : AnalyticAt ℂ (fun _ : ℂ => riemannZeta (s - k)) z :=
    analyticAt_const
  have h_prod : AnalyticAt ℂ (fun w => riemannZeta (s - k) * (Complex.log w) ^ k) z :=
    h_const_left.mul h_log_pow
  -- Now divide by (k.factorial : ℂ).
  have h_inv_const : AnalyticAt ℂ
      (fun _ : ℂ => (1 : ℂ) / (k.factorial : ℂ)) z := analyticAt_const
  have h_full : AnalyticAt ℂ
      (fun w => riemannZeta (s - k) * (Complex.log w) ^ k * (1 / (k.factorial : ℂ))) z :=
    h_prod.mul h_inv_const
  -- Show the goal matches via congrArg.
  have h_eq : (fun w => riemannZeta (s - k) * (Complex.log w) ^ k / (k.factorial : ℂ))
      = (fun w => riemannZeta (s - k) * (Complex.log w) ^ k * (1 / (k.factorial : ℂ))) := by
    funext w
    rw [mul_one_div]
  rw [h_eq]
  exact h_full

/-- Each term is analytic on `JonquieresAnalyticDomain` (a subset of
    `Complex.slitPlane`). -/
theorem jonquieresZetaTerm_analyticOnNhd_jonquieresDomain (s : ℂ) (k : ℕ) :
    AnalyticOnNhd ℂ (fun z => jonquieresZetaTerm s z k) JonquieresAnalyticDomain :=
  fun _ hz => jonquieresZetaTerm_analyticOnNhd_complexSlitPlane s k _ hz.2

/-- Each term is differentiable on `Complex.slitPlane` (consequence of
    analyticity). Used for `differentiableOn_tsum_of_summable_norm`. -/
theorem jonquieresZetaTerm_differentiableOn_complexSlitPlane (s : ℂ) (k : ℕ) :
    DifferentiableOn ℂ (fun z => jonquieresZetaTerm s z k) Complex.slitPlane :=
  (jonquieresZetaTerm_analyticOnNhd_complexSlitPlane s k).differentiableOn

/-! ## Step 2: The uniform growth bridge

    For locally uniform convergence on the radius-2π convergence
    region, we need a summable majorant `‖ζ(s-k)‖ · R^k / k!` for
    every radius `R < 2π`. This is the precise analytic content,
    captured as a named residual hypothesis. -/

/-- **The uniform growth bridge for the Jonquières ζ-series**.

    For any radius `R ∈ [0, 2π)`, the majorant `k ↦ ‖ζ(s-k)‖ · R^k / k!`
    is summable. This is the locally-uniform-on-compact analogue of
    `JonquieresZetaSummableFromBernoulliBridge`; both reduce to the
    same Bernoulli-growth + functional-equation interpolation. -/
def JonquieresZetaUniformGrowthBridge (s : ℂ) : Prop :=
  ∀ R : ℝ, 0 ≤ R → R < 2 * Real.pi →
    Summable (fun k : ℕ => ‖riemannZeta (s - k)‖ * R ^ k / (Nat.factorial k : ℝ))

/-! ## Step 3: From the bridge to local analyticity -/

/-- **Open-ball containment in the convergence subdomain.**

    Given `z₀` in `JonquieresAnalyticDomain` with `‖log z₀‖ < R < 2π`,
    there is an open ball around `z₀` contained in the convergence
    subdomain on which `‖log w‖ < R` uniformly. -/
private theorem exists_ball_with_log_bound
    {z₀ : ℂ} (hz₀_dom : z₀ ∈ JonquieresAnalyticDomain) {R : ℝ}
    (h_lt : ‖Complex.log z₀‖ < R) :
    ∃ δ > 0, Metric.ball z₀ δ ⊆ JonquieresAnalyticDomain ∧
      ∀ w ∈ Metric.ball z₀ δ, ‖Complex.log w‖ < R := by
  -- Continuity of log at z₀ + openness of {w | ‖log w‖ < R}.
  have h_log_cont : ContinuousAt Complex.log z₀ := continuousAt_clog hz₀_dom.2
  -- The set {w | ‖log w‖ < R} is open in slitPlane via continuity.
  have h_norm_cont : ContinuousAt (fun w => ‖Complex.log w‖) z₀ :=
    (continuous_norm.continuousAt).comp h_log_cont
  -- Preimage of (-∞, R) under ‖log ·‖ is a neighborhood of z₀.
  have h_nhds : {w : ℂ | ‖Complex.log w‖ < R} ∈ nhds z₀ :=
    h_norm_cont.preimage_mem_nhds (gt_mem_nhds h_lt)
  -- JonquieresAnalyticDomain is open, hence in nhds z₀.
  have h_dom_nhds : JonquieresAnalyticDomain ∈ nhds z₀ :=
    JonquieresAnalyticDomain_isOpen.mem_nhds hz₀_dom
  -- Intersection is in nhds z₀.
  have h_inter_nhds : JonquieresAnalyticDomain ∩ {w | ‖Complex.log w‖ < R} ∈ nhds z₀ :=
    Filter.inter_mem h_dom_nhds h_nhds
  -- Extract a ball.
  rcases Metric.mem_nhds_iff.mp h_inter_nhds with ⟨δ, hδpos, hδsub⟩
  refine ⟨δ, hδpos, ?_, ?_⟩
  · intro w hw; exact (hδsub hw).1
  · intro w hw; exact (hδsub hw).2

/-- **Termwise norm bound** on a ball: if `‖log w‖ < R` on the ball,
    then `‖term k w‖ ≤ ‖ζ(s - k)‖ · R^k / k!`. -/
private theorem norm_jonquieresZetaTerm_le_of_log_bound
    (s : ℂ) (k : ℕ) {R : ℝ} (_hR : 0 ≤ R) {w : ℂ} (hw : ‖Complex.log w‖ ≤ R) :
    ‖jonquieresZetaTerm s w k‖ ≤ ‖riemannZeta (s - k)‖ * R ^ k / (Nat.factorial k : ℝ) := by
  rw [norm_jonquieresZetaTerm]
  -- ‖ζ(s-k)‖ * ‖log w‖^k / k! ≤ ‖ζ(s-k)‖ * R^k / k!
  have h_pow : ‖Complex.log w‖ ^ k ≤ R ^ k :=
    pow_le_pow_left₀ (norm_nonneg _) hw k
  have h_zeta_nn : 0 ≤ ‖riemannZeta (s - k)‖ := norm_nonneg _
  have h_num_le : ‖riemannZeta (s - k)‖ * ‖Complex.log w‖ ^ k
      ≤ ‖riemannZeta (s - k)‖ * R ^ k :=
    mul_le_mul_of_nonneg_left h_pow h_zeta_nn
  have h_fact_pos : (0 : ℝ) < (Nat.factorial k : ℝ) := by
    exact_mod_cast Nat.factorial_pos k
  exact div_le_div_of_nonneg_right h_num_le (le_of_lt h_fact_pos)

/-- **Local analyticity of the ζ-series** at a point `z₀` in the
    convergence subdomain, given the uniform growth bridge. -/
theorem jonquieresZetaSeries_analyticAt_of_bridge
    {s : ℂ} (h_bridge : JonquieresZetaUniformGrowthBridge s)
    {z₀ : ℂ} (hz₀_dom : z₀ ∈ JonquieresAnalyticDomain)
    (hz₀_lt : ‖Complex.log z₀‖ < 2 * Real.pi) :
    AnalyticAt ℂ (jonquieresZetaSeries s) z₀ := by
  -- Pick R ∈ (‖log z₀‖, 2π).
  obtain ⟨R, hRlt_log, hRlt_2pi⟩ := exists_between hz₀_lt
  have hR_nn : 0 ≤ R := (norm_nonneg _).trans hRlt_log.le
  -- Summable majorant at radius R from the bridge.
  have h_sum : Summable
      (fun k : ℕ => ‖riemannZeta (s - k)‖ * R ^ k / (Nat.factorial k : ℝ)) :=
    h_bridge R hR_nn hRlt_2pi
  -- Open ball around z₀ within domain where ‖log w‖ < R.
  obtain ⟨δ, hδpos, hδ_dom, hδ_log⟩ := exists_ball_with_log_bound hz₀_dom hRlt_log
  -- On this ball, the differentiableOn-of-summable-norm lemma applies.
  have h_ball_open : IsOpen (Metric.ball z₀ δ) := Metric.isOpen_ball
  have h_diff_on : DifferentiableOn ℂ (fun w => ∑' k : ℕ, jonquieresZetaTerm s w k)
      (Metric.ball z₀ δ) :=
    differentiableOn_tsum_of_summable_norm
      (u := fun k : ℕ => ‖riemannZeta (s - k)‖ * R ^ k / (Nat.factorial k : ℝ))
      h_sum
      (fun k => (jonquieresZetaTerm_differentiableOn_complexSlitPlane s k).mono
        (fun w hw => (hδ_dom hw).2))
      h_ball_open
      (fun k w hw =>
        norm_jonquieresZetaTerm_le_of_log_bound s k hR_nn (hδ_log w hw).le)
  -- DifferentiableOn on open set ⇒ AnalyticOnNhd.
  have h_an : AnalyticOnNhd ℂ (fun w => ∑' k : ℕ, jonquieresZetaTerm s w k)
      (Metric.ball z₀ δ) :=
    h_diff_on.analyticOnNhd h_ball_open
  -- AnalyticAt at z₀ (z₀ is the center of the ball).
  have hz₀_mem : z₀ ∈ Metric.ball z₀ δ := Metric.mem_ball_self hδpos
  have h_an_at : AnalyticAt ℂ (fun w => ∑' k : ℕ, jonquieresZetaTerm s w k) z₀ :=
    h_an z₀ hz₀_mem
  -- jonquieresZetaSeries s w is definitionally ∑' k, jonquieresZetaTerm s w k.
  exact h_an_at

/-! ## Step 4: CAPSTONE — analyticity on the convergence subdomain -/

/-- **CAPSTONE**: under the uniform growth bridge, the ζ-series is
    analytic on `JonquieresAnalyticDomain ∩ {z | ‖log z‖ < 2π}`. -/
theorem jonquieresZetaSeries_analyticOnNhd_of_bridge
    {s : ℂ} (h_bridge : JonquieresZetaUniformGrowthBridge s) :
    AnalyticOnNhd ℂ (jonquieresZetaSeries s)
      (JonquieresAnalyticDomain ∩ {z : ℂ | ‖Complex.log z‖ < 2 * Real.pi}) := by
  intro z hz
  exact jonquieresZetaSeries_analyticAt_of_bridge h_bridge hz.1 hz.2

/-- **Discharge of `JonquieresZetaSeriesAnalyticityHypothesis`**: the
    bridge implies the named hypothesis from `JonquieresAnalyticity.lean`. -/
theorem JonquieresZetaSeriesAnalyticityHypothesis_of_bridge
    {s : ℂ} (h_bridge : JonquieresZetaUniformGrowthBridge s) :
    JonquieresZetaSeriesAnalyticityHypothesis s :=
  jonquieresZetaSeries_analyticOnNhd_of_bridge h_bridge

/-! ## Step 5: Full Jonquières expansion analyticity (conditional capstone) -/

/-- **Headline theorem (conditional)**: under the uniform growth bridge,
    the FULL Jonquières expansion is analytic on the maximal correct
    convergence subdomain
    `JonquieresAnalyticDomain ∩ {z | ‖log z‖ < 2π}`. -/
theorem jonquieresExpansion_analyticOnNhd_of_bridge
    {s : ℂ} (h_bridge : JonquieresZetaUniformGrowthBridge s) :
    AnalyticOnNhd ℂ (jonquieresExpansion s)
      (JonquieresAnalyticDomain ∩ {z : ℂ | ‖Complex.log z‖ < 2 * Real.pi}) :=
  jonquieresExpansion_analyticOnNhd_of_zeta
    (JonquieresZetaSeriesAnalyticityHypothesis_of_bridge h_bridge)

/-! ## Architecture summary

**This file establishes (axiom-free, no sorry)**:

* `jonquieresZetaTerm_analyticOnNhd_complexSlitPlane` — UNCONDITIONAL,
  per-term analyticity on `Complex.slitPlane`.
* `jonquieresZetaTerm_analyticOnNhd_jonquieresDomain` — same restricted
  to `JonquieresAnalyticDomain`.
* `jonquieresZetaTerm_differentiableOn_complexSlitPlane` — usable form
  for `differentiableOn_tsum_of_summable_norm`.
* `JonquieresZetaUniformGrowthBridge s` — the named residual: for every
  `R < 2π`, the majorant `k ↦ ‖ζ(s-k)‖ · R^k / k!` is summable.
* `exists_ball_with_log_bound` — open-ball certificate: continuity of
  `log` gives a neighborhood with `‖log w‖ < R` for any `R > ‖log z₀‖`.
* `norm_jonquieresZetaTerm_le_of_log_bound` — termwise majorant.
* `jonquieresZetaSeries_analyticAt_of_bridge` — pointwise local
  analyticity via `differentiableOn_tsum_of_summable_norm` +
  `DifferentiableOn.analyticOnNhd`.
* `jonquieresZetaSeries_analyticOnNhd_of_bridge` — CAPSTONE conditional
  analyticity on the convergence subdomain.
* `JonquieresZetaSeriesAnalyticityHypothesis_of_bridge` — DISCHARGES the
  named hypothesis from `JonquieresAnalyticity.lean`.
* `jonquieresExpansion_analyticOnNhd_of_bridge` — combined headline:
  the FULL expansion is analytic on the convergence subdomain.

**Residual**: `JonquieresZetaUniformGrowthBridge s` — the uniform-radius
form of the Bernoulli-growth + functional-equation interpolation. Same
analytic-number-theory content as the existing pointwise
`JonquieresZetaSummableFromBernoulliBridge`.

**Status**: ζ-series analyticity is now mechanically reduced to a
single named uniform-summability hypothesis. Combined with the
unconditional `jonquieresGammaTerm_analyticOnNhd`, this gives the
full conditional analyticity of `jonquieresExpansion s` on the
maximal correct convergence subdomain.

Stage L13 — Jonquières ζ-series analyticity (conditional discharge).
-/

end PrincipiaTractalis.Analytic.Sheaf
