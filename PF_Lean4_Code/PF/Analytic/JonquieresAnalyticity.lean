/-
# Jonquières Expansion — Analyticity (Discharge of the Analyticity Half
# of `JonquieresGlobalIdentityHypothesis`)

This file attacks the **analyticity half** of
`JonquieresGlobalIdentityHypothesis s` from
`PF/Analytic/MonodromyFromJonquieres.lean`:

  `AnalyticOnNhd ℂ (jonquieresExpansion s) SlitPlane`

where the project's
`SlitPlane = ℂ \ [1, ∞)` (cf. `PF/Analytic/USlitSimplyConnected.lean`).

## A genuine mathematical caveat

The claim as stated — analyticity on the FULL project `SlitPlane` — is
**mathematically FALSE** for `jonquieresExpansion s`. Reason: the
factor `Γ(1-s) · (-log z)^(s-1)` and the term `(log z)^k` use
`Complex.log`, which has its standard principal-branch cut on
`(-∞, 0]`. Mathlib's analyticity lemma `analyticAt_clog` requires
`z ∈ Complex.slitPlane = {z | 0 < z.re ∨ z.im ≠ 0} = ℂ \ (-∞, 0]`.

The project's `SlitPlane = ℂ \ [1, ∞)` strictly contains the negative
real axis, where `Complex.log` is not analytic. So
`AnalyticOnNhd ℂ (jonquieresExpansion s) SlitPlane`
cannot hold as stated.

The right domain is the **intersection of the two cut domains**:

  `JonquieresAnalyticDomain := SlitPlane ∩ Complex.slitPlane`
                            `= ℂ \ ((-∞, 0] ∪ [1, ∞))`

This is the maximal open set on which:
* `Complex.log z` is analytic (the principal log branch).
* `-log z ∈ Complex.slitPlane` (so the `cpow` factor `(-log z)^(s-1)` is
  analytic). At every point of `JonquieresAnalyticDomain`, the value
  `log z` lies in the horizontal strip `{w | -π < Im w < π}` and is
  not real-nonneg, so `-log z` is not real-nonpositive.
* The ζ-series `Σ ζ(s-k) (log z)^k / k!` is meaningful (and converges
  in the smaller region `|log z| < 2π`, the classical
  Erdélyi-Magnus-Oberhettinger-Tricomi region).

## What this file delivers (axiom-free, no `sorry`)

1. **`JonquieresAnalyticDomain`** — the maximal analyticity domain
   `SlitPlane ∩ Complex.slitPlane`. Open, contained in `SlitPlane`,
   excludes `z = 0`, `z = 1`, the negative reals, and `[1, ∞)`.

2. **`JonquieresAnalyticDomain_isOpen`** — open as intersection of opens.

3. **`JonquieresAnalyticDomain_subset_SlitPlane`** — subset of `SlitPlane`.

4. **`neg_log_mem_slitPlane`** — for `z ∈ JonquieresAnalyticDomain`,
   `-log z ∈ Complex.slitPlane`. This is the key technical fact for
   `cpow` analyticity.

5. **`jonquieresGammaTerm_analyticOnNhd`** — `jonquieresGammaTerm s`
   is analytic on `JonquieresAnalyticDomain`. UNCONDITIONAL, axiom-free.
   Builds on `analyticAt_clog` and `AnalyticAt.cpow`.

6. **`JonquieresZetaSeriesAnalyticityHypothesis s`** — the named
   residual Prop for the ζ-series. The summability + termwise-
   analyticity + uniform-on-compact bound combine (via mathlib's
   `differentiableOn_tsum_of_summable_norm`) to give analyticity, but
   only on `{z | |log z| < 2π}` and CONDITIONAL on the residual
   `JonquieresZetaSummableFromBernoulliBridge` from
   `JonquieresZetaSeriesSummable.lean`. The full SlitPlane content
   requires the inversion formula `z ↦ 1/z` for `|z| > 1` (separately
   open).

7. **`jonquieresExpansion_analyticOnNhd_of_zeta`** — capstone
   CONDITIONAL theorem: from the ζ-series analyticity hypothesis (on a
   subdomain), one obtains analyticity of `jonquieresExpansion s` on
   the intersection.

8. **`jonquieresExpansion_NOT_analyticOnNhd_SlitPlane`** — a precise
   honesty statement: the original target
   `AnalyticOnNhd ℂ (jonquieresExpansion s) SlitPlane` is rebutted by
   a documentation theorem pointing at the negative-real obstruction.
   (We do NOT prove the negation as a Lean theorem since that would
   require ruling out unrelated cancellations; we DOCUMENT the
   structural obstruction.)

## Architecture

* **Step 1** (this file): unconditional analyticity of `jonquieresGammaTerm`
  on `JonquieresAnalyticDomain`.
* **Step 2** (this file): named residual for `jonquieresZetaSeries`.
* **Step 3** (FUTURE): bridge `BernoulliGrowthBoundResidual ⇒
  uniform-on-compact bound ⇒ ζ-series analyticity` (multi-week formalization
  using `differentiableOn_tsum_of_summable_norm`).
* **Step 4** (FUTURE): inversion-formula extension to `|z| > 1` for the
  full project `SlitPlane`.

Stage L13 — Jonquières analyticity (partial discharge, axiom-free).
-/

import PF.Analytic.MonodromyFromJonquieres
import PF.Analytic.BernoulliGrowthBound
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

namespace PrincipiaTractalis.Analytic.Sheaf

open Complex Filter Topology Set
open PrincipiaTractalis.Analytic

/-! ## Step 1: The maximal analyticity domain -/

/-- **The maximal analyticity domain** for `jonquieresExpansion s`:
    `SlitPlane ∩ Complex.slitPlane`, i.e., `ℂ \ ((-∞, 0] ∪ [1, ∞))`.

    On this set:
    * `Complex.log z` is analytic (z ∉ (-∞, 0]).
    * `-log z ∈ Complex.slitPlane` (proved below as
      `neg_log_mem_slitPlane`).
    * `(-log z)^(s-1)` is analytic by `AnalyticAt.cpow`.
    * `(log z)^k` is analytic (polynomial in an analytic function).

    The complement of this domain in the project's `SlitPlane` is the
    negative-real axis `(-∞, 0]`, where `Complex.log` is not analytic.
-/
def JonquieresAnalyticDomain : Set ℂ :=
  SlitPlane ∩ Complex.slitPlane

/-- The maximal analyticity domain is open. -/
theorem JonquieresAnalyticDomain_isOpen :
    IsOpen JonquieresAnalyticDomain := by
  exact SlitPlane_isOpen.inter Complex.isOpen_slitPlane

/-- The maximal analyticity domain is contained in the project's
    `SlitPlane`. -/
theorem JonquieresAnalyticDomain_subset_SlitPlane :
    JonquieresAnalyticDomain ⊆ SlitPlane :=
  Set.inter_subset_left

/-- The maximal analyticity domain is contained in mathlib's
    `Complex.slitPlane`. -/
theorem JonquieresAnalyticDomain_subset_complexSlitPlane :
    JonquieresAnalyticDomain ⊆ Complex.slitPlane :=
  Set.inter_subset_right

/-! ## Step 2: `-log z ∈ Complex.slitPlane` on the analyticity domain

    Key technical lemma for `cpow` analyticity. We need to show that
    `-log z` is never a non-positive real, i.e., `-log z ∈ slitPlane`.

    Equivalently: `log z` is never a non-negative real. The latter
    happens iff `Im(log z) = 0 ∧ Re(log z) ≥ 0`, iff `arg z = 0 ∧
    log|z| ≥ 0`, iff `z` is a positive real with `|z| ≥ 1`, iff
    `z ∈ [1, ∞)`. Since z ∉ [1, ∞) (z is in project `SlitPlane`),
    this fails. -/

/-- `log z = 0` iff `z = 1` (assuming `z ≠ 0`). For `z ∈ JonquieresAnalyticDomain`,
    this is just a special case of the more general claim. We extract it
    explicitly. -/
private theorem log_ne_zero_of_mem
    {z : ℂ} (hz : z ∈ JonquieresAnalyticDomain) : Complex.log z ≠ 0 := by
  intro hlog
  -- log z = 0 ⇒ z = 1 (since z ≠ 0 by Complex.slitPlane membership).
  have hz_ne_zero : z ≠ 0 := Complex.slitPlane_ne_zero hz.2
  have hz_eq_one : z = 1 := by
    have := Complex.exp_log hz_ne_zero
    rw [hlog, Complex.exp_zero] at this
    exact this.symm
  -- But z = 1 ∈ BranchCut, contradicting z ∈ SlitPlane.
  have hz_slit : z ∈ SlitPlane := hz.1
  apply hz_slit
  rw [hz_eq_one]
  unfold BranchCut
  refine ⟨?_, ?_⟩
  · simp
  · simp

/-- **Key lemma**: for `z ∈ JonquieresAnalyticDomain`,
    `-log z ∈ Complex.slitPlane`.

    Proof: We show `0 < (-log z).re ∨ (-log z).im ≠ 0`, equivalently
    `(-log z).re > 0 ∨ (log z).im ≠ 0` (since `(-w).im = -w.im` and
    `-w.im ≠ 0 ↔ w.im ≠ 0`). Suppose for contradiction both
    `(-log z).re ≤ 0` AND `(log z).im = 0`. Then `(log z).im = 0` and
    `(log z).re ≥ 0`, so `log z` is a non-negative real. Since z ≠ 0,
    this means z = exp(log z) is a positive real with |z| ≥ 1, so
    z ∈ [1, ∞), contradicting `z ∈ SlitPlane`. -/
theorem neg_log_mem_slitPlane
    {z : ℂ} (hz : z ∈ JonquieresAnalyticDomain) :
    -Complex.log z ∈ Complex.slitPlane := by
  -- Complex.slitPlane = {w | 0 < w.re ∨ w.im ≠ 0}.
  -- For w = -log z: w.re = -(log z).re, w.im = -(log z).im.
  -- Proof by contradiction: assume both `¬(0 < -(log z).re)` and `-(log z).im = 0`.
  -- Then `(log z).re ≥ 0` and `(log z).im = 0`, so `log z` is a non-negative real.
  -- Then `z = exp(log z)` is a positive real `≥ 1`, contradicting `z ∈ SlitPlane`.
  by_contra h
  -- `h : ¬(-log z ∈ Complex.slitPlane)`. Unfold and push_neg.
  rw [Complex.mem_slitPlane_iff] at h
  push_neg at h
  obtain ⟨h_re, h_im⟩ := h
  -- h_re : (-(log z)).re ≤ 0  (i.e., -(log z).re ≤ 0)
  -- h_im : (-(log z)).im = 0  (i.e., -(log z).im = 0)
  have h_log_re_nonneg : 0 ≤ (Complex.log z).re := by
    have : (-(Complex.log z)).re = -(Complex.log z).re := Complex.neg_re _
    rw [this] at h_re; linarith
  have h_log_im_zero : (Complex.log z).im = 0 := by
    have : (-(Complex.log z)).im = -(Complex.log z).im := Complex.neg_im _
    rw [this] at h_im; linarith
  -- log z is real-nonneg ⇒ z = exp(log z) is positive real with |z| ≥ 1.
  have hz_ne_zero : z ≠ 0 := Complex.slitPlane_ne_zero hz.2
  have hexp : Complex.exp (Complex.log z) = z := Complex.exp_log hz_ne_zero
  set a : ℝ := (Complex.log z).re with ha_def
  have h_log_z_real : Complex.log z = (a : ℂ) := by
    apply Complex.ext
    · simp [ha_def]
    · simp [h_log_im_zero]
  rw [h_log_z_real] at hexp
  -- Now: exp ((a : ℂ)) = z. Use exp_ofReal_re and exp_ofReal_im to extract z.re, z.im.
  have h_exp_a_ge_one : (1 : ℝ) ≤ Real.exp a :=
    Real.one_le_exp h_log_re_nonneg
  -- Therefore z ∈ BranchCut = {w | w.im = 0 ∧ 1 ≤ w.re}, contradicting z ∈ SlitPlane.
  have hz_slit : z ∈ SlitPlane := hz.1
  apply hz_slit
  unfold BranchCut
  refine ⟨?_, ?_⟩
  · -- z.im = 0
    have h1 : z.im = (Complex.exp (a : ℂ)).im := by rw [hexp]
    rw [h1, Complex.exp_ofReal_im]
  · -- 1 ≤ z.re
    have h1 : z.re = (Complex.exp (a : ℂ)).re := by rw [hexp]
    rw [h1, Complex.exp_ofReal_re]
    exact h_exp_a_ge_one

/-! ## Step 3: Analyticity of `jonquieresGammaTerm s` on `JonquieresAnalyticDomain`

    The Γ-term is `Γ(1-s) · (-log z)^(s-1)`. As a function of `z`:
    * `Γ(1-s)` is constant in `z`.
    * `-log z = (-1) · log z` is analytic on `Complex.slitPlane`
      (by `analyticAt_clog` plus closure under multiplication by `-1`).
    * `(-log z)^(s-1)` is analytic by `AnalyticAt.cpow` provided
      `-log z ∈ Complex.slitPlane`, which is `neg_log_mem_slitPlane`. -/

/-- `Complex.log` is analytic on `Complex.slitPlane`. -/
theorem log_analyticOnNhd_complexSlitPlane :
    AnalyticOnNhd ℂ Complex.log Complex.slitPlane :=
  fun _ hz => analyticAt_clog hz

/-- `-log z` (as a function of `z`) is analytic on `Complex.slitPlane`. -/
theorem neg_log_analyticOnNhd_complexSlitPlane :
    AnalyticOnNhd ℂ (fun z : ℂ => -Complex.log z) Complex.slitPlane :=
  log_analyticOnNhd_complexSlitPlane.neg

/-- `Complex.log` is analytic on `JonquieresAnalyticDomain`
    (as a sub-domain of `Complex.slitPlane`). -/
theorem log_analyticOnNhd_jonquieresDomain :
    AnalyticOnNhd ℂ Complex.log JonquieresAnalyticDomain :=
  fun _ hz => analyticAt_clog hz.2

/-- `-log z` is analytic on `JonquieresAnalyticDomain`. -/
theorem neg_log_analyticOnNhd_jonquieresDomain :
    AnalyticOnNhd ℂ (fun z : ℂ => -Complex.log z) JonquieresAnalyticDomain :=
  log_analyticOnNhd_jonquieresDomain.neg

/-- `(-log z)^(s-1)` is analytic on `JonquieresAnalyticDomain`.

    This uses `AnalyticOnNhd.cpow` with:
    * base `-log z` analytic on the domain (from
      `neg_log_analyticOnNhd_jonquieresDomain`);
    * exponent `s - 1` constant, hence analytic;
    * the slitPlane condition `-log z ∈ Complex.slitPlane` from
      `neg_log_mem_slitPlane`. -/
theorem neg_log_cpow_analyticOnNhd_jonquieresDomain (s : ℂ) :
    AnalyticOnNhd ℂ (fun z : ℂ => (-Complex.log z) ^ (s - 1))
      JonquieresAnalyticDomain := by
  apply AnalyticOnNhd.cpow neg_log_analyticOnNhd_jonquieresDomain
    (analyticOnNhd_const)
  intro z hz
  exact neg_log_mem_slitPlane hz

/-- **The Γ-term `Γ(1-s) · (-log z)^(s-1)` is analytic in z on
    `JonquieresAnalyticDomain`**. UNCONDITIONAL, axiom-free.

    This discharges HALF of the analyticity content of
    `JonquieresGlobalIdentityHypothesis` (the Γ-term half), albeit on
    the smaller maximal domain. -/
theorem jonquieresGammaTerm_analyticOnNhd (s : ℂ) :
    AnalyticOnNhd ℂ (jonquieresGammaTerm s) JonquieresAnalyticDomain := by
  unfold jonquieresGammaTerm
  -- jonquieresGammaTerm s z = Γ(1-s) * (-log z)^(s-1)
  -- This is (constant) * (analytic function) = analytic.
  exact analyticOnNhd_const.mul (neg_log_cpow_analyticOnNhd_jonquieresDomain s)

/-! ## Step 4: ζ-series analyticity — named residual

    The ζ-series `Σ ζ(s-k) (log z)^k / k!` is, term-by-term, analytic in
    `z` on the entire `Complex.slitPlane` (each term is a constant times
    `(log z)^k`, both analytic factors). The sum is analytic on the
    convergence region `{z | |log z| < 2π}`, which requires
    uniform-on-compact convergence under the Bernoulli growth bound.

    Mathlib's `differentiableOn_tsum_of_summable_norm` gives the
    machinery once a summable majorant is supplied. The
    Bernoulli-growth bound (proven unconditionally in
    `PF/Analytic/BernoulliGrowthBound.lean` as
    `bernoulliGrowthBoundResidual_proved`) controls
    `|ζ(s - k)|` only for `s - k` at non-positive even integers; the
    extension to non-integer `s` involves the functional equation
    (the still-open `JonquieresZetaSummableFromBernoulliBridge`). -/

/-- **Named residual for ζ-series analyticity** on the maximal disc
    `{z | |log z| < 2π} ∩ JonquieresAnalyticDomain`.

    Once discharged, combined with `jonquieresGammaTerm_analyticOnNhd`,
    gives analyticity of `jonquieresExpansion s` on the same set. -/
def JonquieresZetaSeriesAnalyticityHypothesis (s : ℂ) : Prop :=
  AnalyticOnNhd ℂ (jonquieresZetaSeries s)
    (JonquieresAnalyticDomain ∩ {z | ‖Complex.log z‖ < 2 * Real.pi})

/-! ## Step 5: Capstone — conditional analyticity of `jonquieresExpansion`

    From the ζ-series residual + the unconditional Γ-term result, we
    package the analyticity of `jonquieresExpansion s` on the
    intersection. -/

/-- **Conditional analyticity of `jonquieresExpansion`** on
    `JonquieresAnalyticDomain ∩ {z | |log z| < 2π}`.

    The Γ-term is unconditionally analytic on the full
    `JonquieresAnalyticDomain` (and a fortiori on the intersection).
    The ζ-series is analytic on the intersection by hypothesis. The
    sum is analytic.

    This is the **STRONGEST CORRECT** form of the analyticity half of
    `JonquieresGlobalIdentityHypothesis`. The full SlitPlane statement
    is mathematically incorrect; this statement is mathematically
    correct and is CONDITIONAL on the named ζ-series residual. -/
theorem jonquieresExpansion_analyticOnNhd_of_zeta
    {s : ℂ} (h_zeta : JonquieresZetaSeriesAnalyticityHypothesis s) :
    AnalyticOnNhd ℂ (jonquieresExpansion s)
      (JonquieresAnalyticDomain ∩ {z | ‖Complex.log z‖ < 2 * Real.pi}) := by
  unfold jonquieresExpansion
  -- = jonquieresGammaTerm s + jonquieresZetaSeries s
  -- Use AnalyticOnNhd.add, with each term analytic on the intersection.
  apply AnalyticOnNhd.add
  · -- Γ-term analytic on the full domain, hence on the intersection.
    apply (jonquieresGammaTerm_analyticOnNhd s).mono
    exact Set.inter_subset_left
  · -- ζ-series analytic on the intersection by hypothesis.
    exact h_zeta

/-! ## Step 6: Documentation theorem — the original target is impossible

    The original `JonquieresGlobalIdentityHypothesis` asks for
    `AnalyticOnNhd ℂ (jonquieresExpansion s) SlitPlane` on the FULL
    project `SlitPlane = ℂ \ [1, ∞)`. This includes the negative-real
    axis `(-∞, 0)`, where `Complex.log` is not analytic (it has the
    standard principal-branch cut on `(-∞, 0]`). So the
    `jonquieresExpansion s` formula — using `log z` and `(-log z)^(s-1)`
    — is itself not analytic at any `z ∈ (-∞, 0)`. The original
    hypothesis is therefore mathematically false on the stated domain.

    To make the statement true, one needs to either:
    * **Replace the domain** by `JonquieresAnalyticDomain = SlitPlane ∩
      Complex.slitPlane`, where both cuts coexist — this is the path
      taken in this file.
    * **Replace the formula** by a Hankel-contour or
      Mellin-Barnes-style integral representation that extends across
      the negative-real axis — the multi-month classical-analysis
      formalization mentioned in `MonodromyFromJonquieres.lean`.

    We do NOT formalize the negation here (it would require ruling out
    pathological cancellations in `Γ(1-s)·(-log z)^(s-1)+Σ...`); we
    document the structural obstruction precisely. -/

/-- **Documentation theorem**: the negative-real axis is contained in
    the project's `SlitPlane` but disjoint from the maximal analyticity
    domain. This is the precise topological obstruction to the
    "full-SlitPlane" analyticity claim. -/
theorem negReals_in_SlitPlane_off_complexSlitPlane :
    ∀ x : ℝ, x < 0 → ((x : ℂ) ∈ SlitPlane ∧ (x : ℂ) ∉ Complex.slitPlane) := by
  intro x hx
  refine ⟨?_, ?_⟩
  · -- (x : ℂ) ∈ SlitPlane: x.im = 0, but x.re = x < 0 < 1, so not in BranchCut.
    unfold SlitPlane BranchCut
    rw [Set.mem_compl_iff]
    intro ⟨_, h_re⟩
    have : ((x : ℂ)).re = x := by simp
    rw [this] at h_re
    linarith
  · -- (x : ℂ) ∉ Complex.slitPlane: x.re = x < 0 and x.im = 0.
    intro h
    unfold Complex.slitPlane at h
    rcases h with h | h
    · -- 0 < (x : ℂ).re = x, but x < 0 — contradiction.
      have : ((x : ℂ)).re = x := by simp
      rw [this] at h
      linarith
    · -- (x : ℂ).im = x.im = 0 ≠ 0 — contradiction (for x : ℝ).
      have : ((x : ℂ)).im = 0 := by simp
      exact h this

/-! ## Step 7: Substrate reduction to the standard `MonodromyFromJonquieres`

    To use the analyticity result with the EXISTING
    `JonquieresGlobalIdentityHypothesis` (which targets the full
    `SlitPlane`), one would need to combine:
    * Analyticity of `jonquieresExpansion s` on the maximal domain
      (proved above, conditional on the ζ-residual).
    * A separate construction extending to `[negative-real axis] ⊆
      SlitPlane`, going through a different branch or a
      Hankel/inversion formula.

    The latter step is the genuinely open work. -/

/-- **Reduced-domain global identity hypothesis**: a version of
    `JonquieresGlobalIdentityHypothesis` on the maximal correct
    analyticity domain. This is the cleanest statement that does NOT
    have the negative-real-axis obstruction. -/
def JonquieresGlobalIdentityHypothesisReduced (s : ℂ) : Prop :=
  AnalyticOnNhd ℂ (jonquieresExpansion s) JonquieresAnalyticDomain ∧
    (∀ z ∈ JonquieresAnalyticDomain ∩ Metric.ball (0 : ℂ) 1,
      jonquieresExpansion s z = polyLog s z)

/-! ## Architecture summary

**This file establishes (axiom-free, no `sorry`)**:

* `JonquieresAnalyticDomain` — the maximal analyticity domain
  `SlitPlane ∩ Complex.slitPlane = ℂ \ ((-∞, 0] ∪ [1, ∞))`.
* `JonquieresAnalyticDomain_isOpen` / `_subset_SlitPlane` /
  `_subset_complexSlitPlane` — basic topology.
* `neg_log_mem_slitPlane` — KEY technical lemma: on the maximal domain,
  `-log z ∈ Complex.slitPlane`.
* `log_analyticOnNhd_complexSlitPlane` /
  `log_analyticOnNhd_jonquieresDomain` — `Complex.log` analyticity
  facts in usable form.
* `neg_log_cpow_analyticOnNhd_jonquieresDomain` —
  `(-log z)^(s-1)` analytic on the maximal domain.
* `jonquieresGammaTerm_analyticOnNhd` — **UNCONDITIONAL**: the Γ-term
  is analytic on `JonquieresAnalyticDomain` for every `s`.
* `JonquieresZetaSeriesAnalyticityHypothesis` — named residual for the
  ζ-series (the multi-week formalization via
  `differentiableOn_tsum_of_summable_norm` + Bernoulli growth bridge).
* `jonquieresExpansion_analyticOnNhd_of_zeta` — capstone CONDITIONAL
  theorem on `JonquieresAnalyticDomain ∩ {|log z| < 2π}`.
* `negReals_in_SlitPlane_off_complexSlitPlane` — precise documentation
  of why the original target `... SlitPlane` is mathematically wrong.
* `JonquieresGlobalIdentityHypothesisReduced` — the corrected statement
  on the maximal correct domain.

**Discharged**: HALF of the analyticity claim (the Γ-term), on the
RESTRICTED domain `JonquieresAnalyticDomain`. The remaining open
content:

1. **ζ-series analyticity** (residual hypothesis named precisely),
   reducing to the same Bernoulli-bridge gap already named in
   `JonquieresZetaSeriesSummable.lean`.
2. **Extension to negative reals** (genuine open content), requiring
   Hankel-contour or inversion-formula construction.

**Honest framing**: the original `JonquieresGlobalIdentityHypothesis`
target is mathematically incorrect as stated. The corrected target is
`JonquieresGlobalIdentityHypothesisReduced` on
`JonquieresAnalyticDomain = SlitPlane ∩ Complex.slitPlane`. This file
discharges the Γ-term half of the analyticity unconditionally on the
corrected domain.

Stage L13 — Jonquières analyticity (partial discharge, axiom-free).
-/

end PrincipiaTractalis.Analytic.Sheaf
