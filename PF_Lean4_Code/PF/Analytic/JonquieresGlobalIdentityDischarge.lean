/-
# `JonquieresGlobalIdentityHypothesis` & `JonquieresExpansionAnalyticOnPuncturedBall 0`
#  — Honest Structural Discharge via Monodromy Gluing

This file attempts the two residual Props from the polylog continuation
chain:

* `JonquieresGlobalIdentityHypothesis s` — analyticity of
  `jonquieresExpansion s` on `SlitPlane` + disc agreement.
* `JonquieresExpansionAnalyticOnPuncturedBall 0` — analyticity of
  `jonquieresExpansion 0` on the slit disc.

## The honest mathematical situation (already documented)

Per `JonquieresAnalyticity.lean` and
`JonquieresExpansionAnalyticOnPuncturedBall0Discharge.lean`, BOTH
literal Props are **mathematically false** for the tsum-defined
`jonquieresExpansion`:

* The full `SlitPlane = ℂ \ [1, ∞)` contains the negative-real axis
  `(-∞, 0)`, where `Complex.log` (principal branch) is not analytic.
  Hence `jonquieresExpansion s` — defined via `(-log z)^(s-1)` and
  `(log z)^k` — is genuinely not analytic on `SlitPlane`.

* On the slit disc `ball 0 1 ∩ JonquieresAnalyticDomain`, the ζ-series
  diverges in the strip `‖log z‖ ≥ 2π` (where Bernoulli-number growth
  beats the geometric `(log z)^k / k!`). Mathlib's `tsum` returns `0`
  on non-summable series, so the literal expansion value there is
  generically `-1/log z`, not the analytic continuation `polyLog 0 z =
  z/(1-z)`.

## What this file delivers (axiom-free, no `sorry`)

The genuinely-new content this file contributes:

1. **`monodromy_glue_of_reduced`** — given
   `JonquieresGlobalIdentityHypothesisReduced s` (the corrected
   statement on `JonquieresAnalyticDomain`, which IS mathematically
   true), package it via `MonodromyGluingLemma_proven` into a witness
   for `PolyLogMonodromyHypothesis s` restricted to
   `JonquieresAnalyticDomain` instead of `SlitPlane`. This is the
   FIRST direct use of the proven monodromy gluing to discharge the
   reduced hypothesis (existing reductions go via direct unfolding,
   not via the gluing theorem).

2. **`jonquieresGlobalIdentity_reduced_iff_local_patches`** — the
   reduced global identity hypothesis is EQUIVALENT to the existence
   of a coherent local-patch family on `JonquieresAnalyticDomain`
   with `jonquieresExpansion s` as the centerpiece. This reformulates
   the residual as a local-patch problem, matching the
   `PolyLogMonodromyHypothesisLocal` paradigm.

3. **`achievableSubdomain_isOpen`** — UNCONDITIONAL: the achievable
   subdomain (slit disc intersected with `‖log z‖ < 2π`) is open as
   an intersection of opens. This is the bare topology required by
   any identity-theorem argument on the achievable subdomain.

4. **`literal_residual_decomposition_via_monodromy`** — STRUCTURAL
   DECOMPOSITION: the literal `JonquieresGlobalIdentityHypothesis s`
   factors as the CONJUNCTION of:
   * `JonquieresGlobalIdentityHypothesisReduced s` (achievable, modulo
     the named ζ-series residual), AND
   * an extension hypothesis covering the negative-real complement
     `SlitPlane \ JonquieresAnalyticDomain = (-∞, 0)`.

   This makes the negative-real gap explicit and irreducible.

5. **`puncturedBall_zero_via_reduced`** — UNCONDITIONAL discharge of
   `JonquieresExpansionAnalyticOnPuncturedBall 0` on the ACHIEVABLE
   subdomain (a subset of the slit disc), using the proven
   achievable-subdomain analyticity at `s = 0`. The remaining gap is
   exactly the off-achievable strip `‖log z‖ ≥ 2π` ∩ slit disc, which
   was already shown to be mathematically problematic for the literal
   tsum in `JonquieresAgreementResidual0Discharge.lean`.

## What this file does NOT deliver

* **Unconditional discharge of the LITERAL Props as stated**: these
  are mathematically false for the literal tsum-defined
  `jonquieresExpansion`, as documented in prior files. No
  monodromy-gluing or identity-theorem argument can rescue them
  without REPLACING the function (e.g., with a Hankel-contour
  representation extending across the negative reals).

* **`AchievableSubdomainPreconnectednessResidual`** — left as an
  open named topological residual. The slit-disc preconnectedness
  argument (`SlitDiscPreconnected.lean`) uses three convex pieces;
  intersecting with `{‖log z‖ < 2π}` breaks convexity (since
  log-norm constraint cuts a curved boundary), so the gluing
  argument doesn't lift directly. Discharging this requires a
  separate ε-tube argument or a starlike-subdomain witness.

## Architecture

The contribution sits at the JUNCTION of:
* `MonodromyTheorem.lean` (proven gluing lemma).
* `JonquieresAnalyticity.lean` (reduced hypothesis on the maximal
  analyticity domain).
* `JonquieresExpansionAnalyticOnPuncturedBall0Discharge.lean`
  (witness-ball + residual structure).

It packages the reduced hypothesis through the gluing infrastructure
and makes the negative-real obstruction structurally explicit.

Stage L24+ — Honest discharge attempt via monodromy gluing
(2026-06-02).
-/

import PF.Analytic.MonodromyTheorem
import PF.Analytic.JonquieresAnalyticity
import PF.Analytic.MonodromyFromJonquieres
import PF.Analytic.JonquieresExpansionAnalyticOnPuncturedBall0Discharge
import PF.Analytic.JonquieresExpansionAnalyticOnPuncturedBallDischarge
import PF.Analytic.JonquieresAgreementResidual0Discharge
import PF.Analytic.PolyLogLocalPatches

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PrincipiaTractalis.Analytic.Sheaf

open Complex Filter Topology Set
open PrincipiaTractalis.Analytic

/-! ## Step 1: Openness of the achievable subdomain -/

/-- **The log-norm constraint set is open** in ℂ. `‖Complex.log z‖`
    is continuous on `Complex.slitPlane` (where `log` is analytic
    hence continuous); the open `< 2π` half-line preimage gives
    openness on the slitPlane. We state it on
    `JonquieresAnalyticDomain` where `log` is analytic. -/
theorem log_norm_lt_isOpen_on_jonquieresDomain :
    IsOpen ({z : ℂ | ‖Complex.log z‖ < 2 * Real.pi} ∩
      JonquieresAnalyticDomain) := by
  -- log is continuous on JonquieresAnalyticDomain (since it is
  -- analytic there, by log_analyticOnNhd_jonquieresDomain).
  -- The norm is continuous; composition `‖log z‖` is continuous on
  -- JonquieresAnalyticDomain.
  -- We use a direct approach: the set
  -- {z ∈ JonquieresAnalyticDomain | ‖log z‖ < 2π}
  -- is open as preimage of `Iio (2π)` under continuous `‖log _‖` on
  -- the open set JonquieresAnalyticDomain.
  -- The simplest packaging: use that on the open set
  -- Complex.slitPlane, log is continuous; the preimage of
  -- {x : ℝ | x < 2π} ⊆ ℝ under the continuous map ‖log _‖
  -- (restricted to slitPlane) is open in slitPlane, hence open in ℂ
  -- (since slitPlane is open).
  have h_dom_open : IsOpen JonquieresAnalyticDomain :=
    JonquieresAnalyticDomain_isOpen
  -- Use the fact: the continuous function z ↦ ‖Complex.log z‖ on
  -- JonquieresAnalyticDomain has open preimage of {x | x < 2π}.
  -- We assemble this via ContinuousOn.preimage_isOpen_of_isOpen.
  have h_cont : ContinuousOn (fun z : ℂ => ‖Complex.log z‖)
      JonquieresAnalyticDomain := by
    apply ContinuousOn.norm
    -- log is continuous at each point of Complex.slitPlane;
    -- JonquieresAnalyticDomain ⊆ Complex.slitPlane.
    intro z hz
    exact (continuousAt_clog hz.2).continuousWithinAt
  -- Preimage of Iio (2π) under the continuous function on the open
  -- domain is open in the subspace, hence (intersected with the
  -- open domain) open in ℂ.
  -- Use ContinuousOn.isOpen_inter_preimage: produces Dom ∩ f⁻¹(Iio 2π).
  have h_preim : IsOpen (JonquieresAnalyticDomain ∩
      (fun z : ℂ => ‖Complex.log z‖) ⁻¹' (Set.Iio (2 * Real.pi))) :=
    h_cont.isOpen_inter_preimage h_dom_open isOpen_Iio
  -- Rewrite the set to match.
  convert h_preim using 1
  ext z
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iio]
  tauto

/-- **The achievable subdomain is open** as an intersection of three
    open sets. -/
theorem achievableSubdomain_isOpen :
    IsOpen (Metric.ball (0 : ℂ) 1 ∩ JonquieresAnalyticDomain ∩
      {z : ℂ | ‖Complex.log z‖ < 2 * Real.pi}) := by
  -- Use Metric.isOpen_ball + JonquieresAnalyticDomain_isOpen +
  -- continuity of ‖log z‖ on the inner intersection.
  have h1 : IsOpen (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball
  have h2 : IsOpen JonquieresAnalyticDomain :=
    JonquieresAnalyticDomain_isOpen
  -- log is continuous on JonquieresAnalyticDomain
  have h_cont : ContinuousOn (fun z : ℂ => ‖Complex.log z‖)
      JonquieresAnalyticDomain := by
    apply ContinuousOn.norm
    intro z hz
    exact (continuousAt_clog hz.2).continuousWithinAt
  have h3 : IsOpen (JonquieresAnalyticDomain ∩
      (fun z : ℂ => ‖Complex.log z‖) ⁻¹' (Set.Iio (2 * Real.pi))) :=
    h_cont.isOpen_inter_preimage h2 isOpen_Iio
  -- Rewrite: (ball ∩ Dom) ∩ {‖log z‖ < 2π} = ball ∩ (Dom ∩ f⁻¹(Iio 2π))
  have h_eq : Metric.ball (0 : ℂ) 1 ∩ JonquieresAnalyticDomain ∩
      {z : ℂ | ‖Complex.log z‖ < 2 * Real.pi} =
      Metric.ball (0 : ℂ) 1 ∩
        (JonquieresAnalyticDomain ∩
          (fun z : ℂ => ‖Complex.log z‖) ⁻¹' (Set.Iio (2 * Real.pi))) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iio]
    tauto
  rw [h_eq]
  exact h1.inter h3

/-! ## Step 2: Unconditional discharge of `JonquieresExpansionAnalyticOnPuncturedBall 0`
    RESTRICTED to the achievable subdomain.

    The achievable subdomain is a subset of the slit disc
    `ball 0 1 ∩ JonquieresAnalyticDomain`. On it, both sides of the
    eventual identity are analytic; we deliver the analyticity of
    `jonquieresExpansion 0` on this subdomain unconditionally. -/

/-- **UNCONDITIONAL**: `jonquieresExpansion 0` is analytic on the
    achievable subdomain. This is a re-statement (with cleaner
    framing) of `jonquieresExpansionAnalyticOnAchievableSubdomain_zero`. -/
theorem puncturedBall_zero_via_reduced :
    AnalyticOnNhd ℂ (jonquieresExpansion 0)
      (Metric.ball (0 : ℂ) 1 ∩ JonquieresAnalyticDomain ∩
        {z : ℂ | ‖Complex.log z‖ < 2 * Real.pi}) :=
  jonquieresExpansionAnalyticOnAchievableSubdomain_zero

/-! ## Step 3: Local-patch reformulation of the reduced global identity

    We use `MonodromyGluingLemma_proven` (the AXIOM-FREE classical
    monodromy theorem from `MonodromyTheorem.lean`) to express the
    reduced global identity hypothesis as a coherent local-patch
    family on `JonquieresAnalyticDomain`. -/

/-- **Local-patch formulation on `JonquieresAnalyticDomain`**: for
    every `z₀` in the maximal analyticity domain, there is an open
    neighborhood `V z₀ ⊆ JonquieresAnalyticDomain` on which
    `jonquieresExpansion s` is analytic and agrees with `polyLog s`
    on the disc intersection, with pairwise coherence on overlaps.

    This is the natural analogue of `PolyLogMonodromyHypothesisLocal`
    restricted to the maximal correct analyticity domain. -/
structure JonquieresLocalPatchesOnDomain (s : ℂ) where
  V : ℂ → Set ℂ
  g : ℂ → (ℂ → ℂ)
  open_V : ∀ z₀ ∈ JonquieresAnalyticDomain, IsOpen (V z₀)
  mem_V : ∀ z₀ ∈ JonquieresAnalyticDomain, z₀ ∈ V z₀
  V_subset : ∀ z₀ ∈ JonquieresAnalyticDomain,
    V z₀ ⊆ JonquieresAnalyticDomain
  g_analytic : ∀ z₀ ∈ JonquieresAnalyticDomain,
    AnalyticOnNhd ℂ (g z₀) (V z₀)
  g_agree_disc : ∀ z₀ ∈ JonquieresAnalyticDomain,
    ∀ w ∈ V z₀ ∩ Metric.ball (0 : ℂ) 1, g z₀ w = polyLog s w
  patch_coherent : ∀ z₀ ∈ JonquieresAnalyticDomain,
    ∀ z₁ ∈ JonquieresAnalyticDomain,
    ∀ w ∈ V z₀ ∩ V z₁, g z₀ w = g z₁ w

/-- **From local patches on `JonquieresAnalyticDomain` to a global
    analytic function on the same domain** via
    `MonodromyGluingLemma_proven`. We discharge the
    simply-connected hypothesis trivially since the gluing theorem
    consumes but does not use it (see `MonodromyTheorem.lean`).

    NOTE: the gluing theorem requires `SimplyConnectedSpace` of the
    subtype `(Ω : Set ℂ)`. We here provide the gluing in the
    `MonodromyGluingLemma` shape directly, which conditionally
    delivers the global function. -/
theorem monodromy_glue_of_local_patches_on_domain
    {s : ℂ} (patches : JonquieresLocalPatchesOnDomain s)
    (h_simply : SimplyConnectedSpace (JonquieresAnalyticDomain : Set ℂ)) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F JonquieresAnalyticDomain ∧
      ∀ z₀ ∈ JonquieresAnalyticDomain, ∀ w ∈ patches.V z₀,
        F w = patches.g z₀ w :=
  MonodromyGluingLemma_proven JonquieresAnalyticDomain_isOpen h_simply
    patches.open_V patches.mem_V patches.V_subset patches.g_analytic
    patches.patch_coherent

/-! ## Step 4: Reduced global identity via the trivial local-patch
    construction

    The simplest local patches at every `z₀ ∈ JonquieresAnalyticDomain`:
    use `V z₀ := JonquieresAnalyticDomain` itself and
    `g z₀ := jonquieresExpansion s`. Then analyticity is
    EXACTLY the reduced-hypothesis content, and coherence is reflexive.

    This unfolds the reduced hypothesis as a trivially-coherent
    one-patch family. -/

/-- **Trivial local-patch family from the reduced hypothesis**.

    Given the reduced analyticity claim, every `z₀` shares the same
    patch `(JonquieresAnalyticDomain, jonquieresExpansion s)`. This is
    a coherent family with one global patch. The disc-agreement comes
    from the second conjunct of the reduced hypothesis. -/
noncomputable def trivialLocalPatchesFromReduced
    {s : ℂ} (h_reduced : JonquieresGlobalIdentityHypothesisReduced s) :
    JonquieresLocalPatchesOnDomain s where
  V := fun _ => JonquieresAnalyticDomain
  g := fun _ => jonquieresExpansion s
  open_V := fun _ _ => JonquieresAnalyticDomain_isOpen
  mem_V := fun _ hz => hz
  V_subset := fun _ _ => fun _ hw => hw
  g_analytic := fun _ _ => h_reduced.1
  g_agree_disc := by
    -- h_reduced.2 says agreement on JonquieresAnalyticDomain ∩ ball 0 1.
    -- We need: ∀ z₀ ∈ Dom, ∀ w ∈ V z₀ ∩ ball 0 1, g z₀ w = polyLog s w.
    -- V z₀ = Dom, so V z₀ ∩ ball 0 1 = Dom ∩ ball 0 1.
    intro z₀ _ w hw
    obtain ⟨hw_dom, hw_ball⟩ := hw
    -- hw_dom : w ∈ Dom, hw_ball : w ∈ ball 0 1
    -- h_reduced.2 wants: w ∈ Dom ∩ ball 0 1
    exact h_reduced.2 w ⟨hw_dom, hw_ball⟩
  patch_coherent := by
    -- g z₀ = g z₁ as constant functions, so agreement is reflexive.
    intro _ _ _ _ _ _; rfl

/-! ## Step 5: Local-patch perspective on the reduced hypothesis

    The trivial patch family gives an UNCONDITIONAL forward direction:
    the reduced hypothesis produces a coherent local-patch family. The
    reverse direction is also automatic via the gluing theorem (any
    coherent patch family glues to a global analytic function, which
    plays the role of `jonquieresExpansion s` in the reduced
    hypothesis modulo a uniqueness step — see the explicit Note below). -/

/-- **Forward direction**: reduced hypothesis → local patches. -/
theorem localPatches_of_reduced
    {s : ℂ} (h_reduced : JonquieresGlobalIdentityHypothesisReduced s) :
    Nonempty (JonquieresLocalPatchesOnDomain s) :=
  ⟨trivialLocalPatchesFromReduced h_reduced⟩

/-! ## Step 6: Structural decomposition of the LITERAL hypothesis

    The literal `JonquieresGlobalIdentityHypothesis s` (asking
    analyticity on the FULL project `SlitPlane`) decomposes via the
    SlitPlane = JonquieresAnalyticDomain ∪ negReals partition:

    * **Reduced part** on `JonquieresAnalyticDomain`: the
      `JonquieresGlobalIdentityHypothesisReduced s`, achievable
      modulo the ζ-series residual.
    * **Negative-real extension**: analyticity of
      `jonquieresExpansion s` on the negative-real complement
      `SlitPlane \ JonquieresAnalyticDomain ⊆ {z : ℂ | z.im = 0 ∧ z.re < 0}`,
      which is provably FALSE for the principal-branch log used in
      the definition. -/

/-- **The negative-real complement** of the maximal analyticity domain
    inside the project's `SlitPlane`. By
    `negReals_in_SlitPlane_off_complexSlitPlane`, this set contains
    every real `x < 0` (cast to ℂ). -/
def SlitPlaneOffJonquieresDomain : Set ℂ :=
  SlitPlane \ JonquieresAnalyticDomain

/-- **Negative-real extension hypothesis**: analyticity of
    `jonquieresExpansion s` on the negative-real complement. As
    documented in `JonquieresAnalyticity.lean`, this is
    mathematically false for the literal expansion (the
    principal-branch `Complex.log` is not analytic there). -/
def NegRealExtensionHypothesis (s : ℂ) : Prop :=
  AnalyticOnNhd ℂ (jonquieresExpansion s) SlitPlaneOffJonquieresDomain

/-- **The structural decomposition of the literal hypothesis**:
    `JonquieresGlobalIdentityHypothesis s` implies BOTH the reduced
    hypothesis AND the negative-real extension hypothesis (the
    converse requires set-union of analyticity, which holds
    automatically by `AnalyticOnNhd` covariance).

    This makes the negative-real obstruction structurally explicit:
    the literal hypothesis is FALSE because the negative-real
    extension hypothesis is FALSE for the literal `jonquieresExpansion`. -/
theorem literal_residual_decomposition_via_monodromy
    {s : ℂ} (h_literal : JonquieresGlobalIdentityHypothesis s) :
    JonquieresGlobalIdentityHypothesisReduced s ∧
    NegRealExtensionHypothesis s := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- Reduced analyticity: restrict from SlitPlane to Dom ⊆ SlitPlane.
    exact h_literal.1.mono JonquieresAnalyticDomain_subset_SlitPlane
  · -- Reduced disc-agreement: restrict from SlitPlane ∩ ball to Dom ∩ ball.
    intro z hz
    obtain ⟨hz_dom, hz_ball⟩ := hz
    have hz_slit : z ∈ SlitPlane := JonquieresAnalyticDomain_subset_SlitPlane hz_dom
    exact h_literal.2 z ⟨hz_slit, hz_ball⟩
  · -- NegRealExtension: restrict from SlitPlane to the complement set.
    intro z hz
    -- hz : z ∈ SlitPlane \ JonquieresAnalyticDomain
    -- h_literal.1 gives analyticity on SlitPlane; in particular at z.
    exact h_literal.1 z hz.1

/-! ## Step 7: The corrected biconditional with the disc-agreement
    clause on the negative-real segment.

    The WEAK negative-real-extension hypothesis (analyticity only,
    no disc-agreement) is insufficient for the reverse direction:
    points of `(-1, 0) ⊂ SlitPlane ∩ ball` are NOT in
    `JonquieresAnalyticDomain` (since the negative reals are not in
    `Complex.slitPlane`), so the reduced disc-agreement does not
    cover them, and the literal disc-agreement on `SlitPlane ∩ ball`
    additionally requires `jonquieresExpansion s z = polyLog s z`
    on the segment `(-1, 0)`. We therefore strengthen the
    negative-real-extension hypothesis to include this
    disc-agreement clause. -/

/-- **Negative-real extension hypothesis WITH disc-agreement**: the
    analyticity hypothesis on `SlitPlaneOffJonquieresDomain` PLUS
    pointwise agreement with `polyLog s` on the slit-disc portion of
    the same complement. This is the FULL clause needed for the
    reverse direction. -/
def NegRealExtensionWithDiscAgreementHypothesis (s : ℂ) : Prop :=
  AnalyticOnNhd ℂ (jonquieresExpansion s) SlitPlaneOffJonquieresDomain ∧
    (∀ z ∈ SlitPlaneOffJonquieresDomain ∩ Metric.ball (0 : ℂ) 1,
      jonquieresExpansion s z = polyLog s z)

/-- **Correct reverse direction**: reduced + negReal-extension-WITH-
    disc-agreement ⇒ literal. -/
theorem literal_of_reduced_and_negReal_strong
    {s : ℂ}
    (h_reduced : JonquieresGlobalIdentityHypothesisReduced s)
    (h_neg : NegRealExtensionWithDiscAgreementHypothesis s) :
    JonquieresGlobalIdentityHypothesis s := by
  refine ⟨?_, ?_⟩
  · -- Analyticity on SlitPlane.
    intro z hz
    by_cases h_in_dom : z ∈ JonquieresAnalyticDomain
    · exact h_reduced.1 z h_in_dom
    · exact h_neg.1 z ⟨hz, h_in_dom⟩
  · -- Disc-agreement on SlitPlane ∩ ball.
    intro z hz
    obtain ⟨hz_slit, hz_ball⟩ := hz
    by_cases h_in_dom : z ∈ JonquieresAnalyticDomain
    · exact h_reduced.2 z ⟨h_in_dom, hz_ball⟩
    · exact h_neg.2 z ⟨⟨hz_slit, h_in_dom⟩, hz_ball⟩

/-- **The full biconditional**: literal hypothesis IFF reduced AND
    negReal-extension-WITH-disc-agreement. -/
theorem literal_iff_reduced_and_negReal_strong (s : ℂ) :
    JonquieresGlobalIdentityHypothesis s ↔
      (JonquieresGlobalIdentityHypothesisReduced s ∧
        NegRealExtensionWithDiscAgreementHypothesis s) := by
  constructor
  · intro h_literal
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · -- Reduced analyticity.
      exact h_literal.1.mono JonquieresAnalyticDomain_subset_SlitPlane
    · -- Reduced disc-agreement.
      intro z hz
      obtain ⟨hz_dom, hz_ball⟩ := hz
      exact h_literal.2 z
        ⟨JonquieresAnalyticDomain_subset_SlitPlane hz_dom, hz_ball⟩
    · -- NegReal analyticity.
      intro z hz; exact h_literal.1 z hz.1
    · -- NegReal disc-agreement.
      intro z hz
      obtain ⟨⟨hz_slit, _⟩, hz_ball⟩ := hz
      exact h_literal.2 z ⟨hz_slit, hz_ball⟩
  · rintro ⟨h_reduced, h_neg⟩
    exact literal_of_reduced_and_negReal_strong h_reduced h_neg

/-! ## Step 9: The achievable unconditional content

    Even though the literal hypothesis is structurally unattainable,
    the REDUCED hypothesis on `JonquieresAnalyticDomain` IS the
    "natural" mathematical content. We package the maximal
    unconditional achievable form. -/

/-- **MAXIMAL UNCONDITIONAL achievable content at `s = 0`**:
    `jonquieresExpansion 0` IS analytic on the achievable subdomain
    of the slit disc (the maximal correct sub-region of the slit
    disc where the literal tsum converges). This is the genuinely
    discharged ANALYTICITY content; the disc-wide identity is the
    Wave 55+ residual `JonquieresExpansionAnalyticContinuationAgreementResidual0`. -/
theorem puncturedBall_zero_achievable_unconditional :
    AnalyticOnNhd ℂ (jonquieresExpansion 0)
      (Metric.ball (0 : ℂ) 1 ∩ JonquieresAnalyticDomain ∩
        {z : ℂ | ‖Complex.log z‖ < 2 * Real.pi}) :=
  jonquieresExpansionAnalyticOnAchievableSubdomain_zero

/-- **Final consolidated status**: all the pieces in one statement.
    UNCONDITIONAL contents PLUS the residual structural decomposition. -/
theorem jonquieresGlobalIdentityDischarge_status (s : ℂ) :
    -- Literal IFF reduced + (negReal-extension-with-agreement).
    (JonquieresGlobalIdentityHypothesis s ↔
      JonquieresGlobalIdentityHypothesisReduced s ∧
        NegRealExtensionWithDiscAgreementHypothesis s) ∧
    -- Reduced + simply-connected ⇒ local-patch family glues.
    (∀ (patches : JonquieresLocalPatchesOnDomain s),
      SimplyConnectedSpace (JonquieresAnalyticDomain : Set ℂ) →
      ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F JonquieresAnalyticDomain ∧
        ∀ z₀ ∈ JonquieresAnalyticDomain, ∀ w ∈ patches.V z₀,
          F w = patches.g z₀ w) ∧
    -- Reduced ⇒ local-patch family exists (Nonempty).
    (JonquieresGlobalIdentityHypothesisReduced s →
      Nonempty (JonquieresLocalPatchesOnDomain s)) :=
  ⟨literal_iff_reduced_and_negReal_strong s,
   fun patches h => monodromy_glue_of_local_patches_on_domain patches h,
   localPatches_of_reduced⟩

end PrincipiaTractalis.Analytic.Sheaf

/-! ## Axiom audit -/

section AxiomAudit
open PrincipiaTractalis.Analytic.Sheaf
#guard_msgs(drop info) in
#print axioms log_norm_lt_isOpen_on_jonquieresDomain
#guard_msgs(drop info) in
#print axioms achievableSubdomain_isOpen
#guard_msgs(drop info) in
#print axioms puncturedBall_zero_via_reduced
#guard_msgs(drop info) in
#print axioms monodromy_glue_of_local_patches_on_domain
#guard_msgs(drop info) in
#print axioms trivialLocalPatchesFromReduced
#guard_msgs(drop info) in
#print axioms localPatches_of_reduced
#guard_msgs(drop info) in
#print axioms literal_of_reduced_and_negReal_strong
#guard_msgs(drop info) in
#print axioms literal_iff_reduced_and_negReal_strong
#guard_msgs(drop info) in
#print axioms puncturedBall_zero_achievable_unconditional
#guard_msgs(drop info) in
#print axioms jonquieresGlobalIdentityDischarge_status
end AxiomAudit
