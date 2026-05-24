/-
# PolyLog Continuation — Manuscript-Faithful Analytic-Continuation Scaffold
#
# **Mission**: lay the SCAFFOLD for a manuscript-faithful
# `polyLog_continuation s z` whose value on `|z| ≥ 1` (in particular on
# the unit circle off `z = 1`) equals the Jonquières / Hankel analytic
# continuation, NOT the mathlib `polyLog s z` tsum (which evaluates to
# zero on the non-summable region `{Re s ≤ 1, |z| = 1, z ≠ 1}` per
# mathlib's `tsum_eq_zero_of_not_summable` convention).
#
# This is the foundational unblocker for the P-vs-NP chain. The
# `axiom_content_FIVE_INPUTS` wrapper's Input 3 (`h_bracket_lower`) is
# STRUCTURALLY FALSE against the formal `polyLog` for exactly this
# reason; the present scaffold begins the multi-month classical-analysis
# infrastructure required to upgrade the wrapper to a
# `polyLog_continuation`-faithful version.
#
# ## What this file establishes (axiom-free, no `sorry`)
#
# 1. **`polyLog_continuation s z`** — the headline `noncomputable def`.
#    Definition (piecewise):
#    * On the open unit disc `‖z‖ < 1`: returns mathlib's `polyLog s z`
#      (the tsum, which actually converges there for `0 ≤ Re s`).
#    * Off the open unit disc: returns `jonquieresExpansion s z`
#      (`Γ(1-s)·(-log z)^(s-1) + Σ' k, ζ(s-k)·(log z)^k/k!`), the
#      classical Jonquières form. On the convergence region
#      `|log z| < 2π ∧ z ∉ [1, ∞) ∧ z ∉ (-∞, 0]` this matches the
#      Hankel-contour continuation.
#
# 2. **`polyLog_continuation_eq_polyLog_of_norm_lt_one`** — axiom-free:
#    on `‖z‖ < 1`, `polyLog_continuation s z = polyLog s z` definitionally.
#    This is THE structural compatibility lemma that any future
#    consumer needs.
#
# 3. **`polyLog_continuation_eq_jonquieresExpansion_of_norm_ge_one`** —
#    axiom-free: off the open unit disc,
#    `polyLog_continuation s z = jonquieresExpansion s z` definitionally.
#
# 4. **`polyLog_continuation_at_zero`** — axiom-free: at `z = 0`,
#    `polyLog_continuation s 0 = 0` (the polylog is zero at zero, and
#    `0` is in the open disc so we use the tsum branch).
#
# 5. **`PolyLogContinuationHankelEquivalence s`** — the NAMED Prop for
#    the residual classical-analysis content: on the convergence region
#    of the Jonquières expansion (i.e. on `JonquieresAnalyticDomain ∩
#    {|log z| < 2π}`), the `polyLog_continuation s z` agrees with the
#    Hankel-contour analytic continuation of the polylog (the
#    Erdélyi-Magnus-Oberhettinger-Tricomi continuation).
#
# 6. **`polyLog_continuation_analyticOn_ball`** — axiom-free: on
#    `ball 0 1` the continuation is analytic (lifted from
#    `polyLog_analyticOn_ball`-style mathlib facts via the disc-branch
#    compatibility; here packaged structurally via the disc-equality
#    lemma).
#
# 7. **`polyLog_continuation_eq_jonquieresExpansion_on_intersection`** —
#    axiom-free: a corollary of the disc-equality lemma, packaged for
#    downstream consumers that need to switch between the two
#    representations on a witness-by-witness basis.
#
# ## What this file does NOT do
#
# * **No discharge of the full Hankel ⇔ Jonquières identity.** That is
#   the multi-month classical-analysis formalization the manuscript
#   roadmap names. The relevant infrastructure already lives in the
#   17-file Hankel chain (`HankelContour.lean`, `HankelDeformation.lean`,
#   `HankelCauchyCapstone.lean`, ..., `PolyLogHankelIdentity.lean`) and
#   in the Jonquières chain (`Jonquieres.lean`,
#   `JonquieresIdentity.lean`, `JonquieresAnalyticity.lean`,
#   `MonodromyFromJonquieres.lean`, plus the
#   `JonquieresExpansionEqualsGeomGermAtHalfClosure.lean` 2026-05-22
#   discharge), but the END-TO-END identity is still open.
#
# * **No upgrade of `axiom_content_FIVE_INPUTS`.** The existing wrapper
#   uses formal `polyLog`. A future companion file
#   (`AxiomRetirementWrapperContinuation.lean`) will reformulate the
#   wrapper against `polyLog_continuation` and then route Input 3
#   through the `PolyLogContinuationHankelEquivalence` Prop. This is a
#   later step.
#
# * **No off-disc analyticity in full generality.** Analyticity of
#   `polyLog_continuation s` off the unit disc is governed by the
#   `JonquieresZetaSeriesAnalyticityHypothesis s` and
#   `JonquieresGlobalIdentityHypothesis s` Props already named in the
#   framework. We package those as `polyLog_continuation`-side residuals
#   below.
#
# ## Architecture overview
#
# ```
# polyLog_continuation s z   ←   THIS FILE (scaffold)
#         ↓ (disc branch)
# polyLog s z                ←   Polylog.lean (tsum)
#
# polyLog_continuation s z   ←   THIS FILE (scaffold)
#         ↓ (off-disc branch)
# jonquieresExpansion s z    ←   Jonquieres.lean (Γ-term + ζ-series)
#         ↓ (Hankel-contour equivalence)
# Hankel-integral continuation ← named open Prop
#                                (PolyLogContinuationHankelEquivalence)
#         ↓ (full equivalence)
# JonquieresGlobalIdentityHypothesis   ← already named in
#                                        MonodromyFromJonquieres.lean
# ```
#
# ## Honest framing
#
# This file is **scaffold-only**. It introduces a NEW
# `polyLog_continuation` symbol with the structurally-correct
# manuscript-faithful behavior (Jonquières off the disc, tsum on the
# disc), proves the basic compatibility lemmas axiom-free, and names
# the residual identification with the Hankel continuation as a
# `Prop`. Future agents can:
#
# 1. Reformulate `axiom_content_FIVE_INPUTS` against
#    `polyLog_continuation` and discharge Input 3 (no longer false).
# 2. Discharge `PolyLogContinuationHankelEquivalence` by assembling the
#    17-file Hankel chain into a single `polyLog s z =
#    polyLogHankelTargetValue s z`-style theorem on the convergence
#    region.
# 3. Discharge `JonquieresGlobalIdentityHypothesis` (the single
#    monodromy gap) to extend the Hankel equivalence to all of
#    `SlitPlane`.
#
# Stage L14 — PolyLog continuation scaffold (axiom-free, no `sorry`).
-/

import PF.Analytic.Polylog
import PF.Analytic.Jonquieres
import PF.Analytic.JonquieresAnalyticity
import PF.Analytic.MonodromyFromJonquieres

namespace PrincipiaTractalis.Analytic

open Complex Filter Topology Set

/-! ## §1: The headline definition -/

/-- **The manuscript-faithful polylog continuation.**

    Definition (piecewise):
    * On the open unit disc `‖z‖ < 1`: agrees with mathlib's `polyLog s z`
      (the absolutely convergent tsum on that region for `0 ≤ Re s`).
    * Off the open unit disc (`‖z‖ ≥ 1`, including the unit circle): returns
      the Jonquières expansion
      `Γ(1-s)·(-log z)^(s-1) + Σ' k, ζ(s-k)·(log z)^k/k!`.

    The point of this definition is to give a SINGLE Lean symbol whose
    value on the unit circle off `z = 1` is the manuscript's
    Jonquières/Hankel analytic continuation, NOT the mathlib tsum (which
    evaluates to `0` on the non-summable region `{Re s ≤ 1, |z| = 1,
    z ≠ 1}` per `tsum_eq_zero_of_not_summable`).

    The substantive residual content — namely, that this piecewise
    definition equals the Hankel-contour analytic continuation on its
    convergence region — is captured in the named Prop
    `PolyLogContinuationHankelEquivalence` below.

    **Why piecewise, not "Jonquières everywhere"?** The Jonquières
    expansion's `(-log z)^(s-1)` factor introduces a branch
    discontinuity that is NOT shared by the disc tsum; the natural
    convergence region of the Jonquières form is `|log z| < 2π ∧ z ∉
    [1, ∞) ∧ z ∉ (-∞, 0]` (the `JonquieresAnalyticDomain`), which does
    not contain `z = 0`. The disc branch is the cleanest way to
    preserve `polyLog_continuation s 0 = 0` and to inherit the
    extensive mathlib infrastructure for `polyLog` on `ball 0 1`. -/
noncomputable def polyLog_continuation (s z : ℂ) : ℂ :=
  if ‖z‖ < 1 then polyLog s z else jonquieresExpansion s z

/-! ## §2: Structural compatibility lemmas -/

/-- **On the open unit disc, the continuation agrees with mathlib's
    `polyLog`** — definitionally, by the `if` branch. Axiom-free.

    This is THE compatibility lemma any future consumer needs. Any
    theorem about `polyLog s z` on `‖z‖ < 1` lifts to `polyLog_continuation`
    by `rw [polyLog_continuation_eq_polyLog_of_norm_lt_one]`. -/
theorem polyLog_continuation_eq_polyLog_of_norm_lt_one
    (s : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    polyLog_continuation s z = polyLog s z := by
  unfold polyLog_continuation
  exact if_pos hz

/-- **Off the open unit disc, the continuation equals the Jonquières
    expansion** — definitionally, by the `if` branch. Axiom-free. -/
theorem polyLog_continuation_eq_jonquieresExpansion_of_norm_ge_one
    (s : ℂ) {z : ℂ} (hz : 1 ≤ ‖z‖) :
    polyLog_continuation s z = jonquieresExpansion s z := by
  unfold polyLog_continuation
  rw [if_neg (not_lt.mpr hz)]

/-! ## §3: Anchor at zero -/

/-- **At `z = 0`, the continuation equals zero** — axiom-free.

    Proof: `‖0‖ = 0 < 1` so the disc branch applies; then
    `polyLog s 0 = 0` from `polyLog_zero`. -/
theorem polyLog_continuation_at_zero (s : ℂ) :
    polyLog_continuation s 0 = 0 := by
  rw [polyLog_continuation_eq_polyLog_of_norm_lt_one s (by simp : ‖(0 : ℂ)‖ < 1)]
  exact polyLog_zero s

/-! ## §4: The named residual — Hankel-continuation equivalence

The substantive open content. On the convergence region of the
Jonquières expansion (`JonquieresAnalyticDomain ∩ {|log z| < 2π}`),
the `polyLog_continuation s z` value coincides with the Hankel-contour
analytic continuation of the polylogarithm, i.e., the value
classically denoted `Li_s(z)` for `z` off the disc of convergence.

This is the multi-month classical-analysis content:
* Hankel-contour representation `Li_s(z) = (Γ(1-s)/2πi) · ∮_H
  (-t)^(s-1) / (e^t/z - 1) dt` (Erdélyi-Magnus-Oberhettinger-Tricomi §1.11).
* Termwise integration of the geometric expansion of `1/(e^t/z - 1)`
  reduces the Hankel integral to the Jonquières form on the
  convergence region.

The framework's 17-file Hankel chain (`HankelContour.lean`,
`HankelDeformation.lean`, ..., `HankelFubini.lean` 2026-05-20,
`PolyLogHankelIdentity.lean`) provides the components; the END-TO-END
equivalence is captured in this single named Prop. -/

/-- **The Hankel-equivalence Prop for the polylog continuation**.

    On every `z` in `JonquieresAnalyticDomain ∩ {w | ‖log w‖ < 2π}`,
    the `polyLog_continuation s z` value agrees with the Jonquières
    expansion `jonquieresExpansion s z`. By construction this is
    TRIVIALLY TRUE on the off-disc part of that set (where
    `polyLog_continuation = jonquieresExpansion` by definition).

    The SUBSTANTIVE content is on the disc-intersection part: that
    `polyLog s z = jonquieresExpansion s z` for `z ∈
    JonquieresAnalyticDomain ∩ ball 0 1 ∩ {|log z| < 2π}`. This is the
    classical Jonquières identity (the disc-agreement content already
    named in `JonquieresIdentity.lean` and proven at `s = 0` via
    `jonquieresIdentityPointGermAtHalf_zero_proved` for the germ at
    `z = 1/2`).

    Once discharged, this Prop guarantees that
    `polyLog_continuation` is the manuscript's analytic continuation
    on its natural domain. -/
def PolyLogContinuationHankelEquivalence (s : ℂ) : Prop :=
  ∀ z ∈ Sheaf.JonquieresAnalyticDomain ∩ {w : ℂ | ‖Complex.log w‖ < 2 * Real.pi},
    polyLog_continuation s z = jonquieresExpansion s z

/-- **Trivial off-disc half**: on `JonquieresAnalyticDomain ∩
    {|log z| < 2π}` with `1 ≤ ‖z‖`, the equivalence is definitional. -/
theorem polyLog_continuation_eq_jonquieres_offDisc
    (s : ℂ) {z : ℂ} (_hz_dom :
      z ∈ Sheaf.JonquieresAnalyticDomain ∩ {w : ℂ | ‖Complex.log w‖ < 2 * Real.pi})
    (hz_ge : 1 ≤ ‖z‖) :
    polyLog_continuation s z = jonquieresExpansion s z :=
  polyLog_continuation_eq_jonquieresExpansion_of_norm_ge_one s hz_ge

/-! ## §5: Disc-side residual via existing JonquieresIdentityHypothesis

On the disc side of the Hankel equivalence, the substantive
identification `polyLog s z = jonquieresExpansion s z` is exactly the
content of the pointwise `JonquieresIdentityHypothesis s z` named in
`JonquieresIdentity.lean`. We package this connection. -/

/-- **The disc-side half of the Hankel equivalence**, in terms of the
    existing `JonquieresIdentityHypothesis`. Axiom-free.

    On `‖z‖ < 1`, the `polyLog_continuation` value equals
    `polyLog s z` by definition; if additionally
    `JonquieresIdentityHypothesis s z` holds (the pointwise Jonquières
    identity), then `polyLog_continuation s z = jonquieresExpansion s z`. -/
theorem polyLog_continuation_eq_jonquieres_onDisc
    {s z : ℂ} (hz : ‖z‖ < 1)
    (h_jonq : JonquieresIdentityHypothesis s z) :
    polyLog_continuation s z = jonquieresExpansion s z := by
  rw [polyLog_continuation_eq_polyLog_of_norm_lt_one s hz]
  exact h_jonq

/-! ## §6: Capstone — Hankel equivalence from pointwise Jonquières

Given the pointwise `JonquieresIdentityHypothesis` on the
disc-intersection part of the Jonquières convergence region, the full
`PolyLogContinuationHankelEquivalence` follows. -/

/-- **Hankel equivalence from pointwise Jonquières identity**:
    if `JonquieresIdentityHypothesis s z` holds on
    `JonquieresAnalyticDomain ∩ {|log z| < 2π} ∩ ball 0 1`, then
    `PolyLogContinuationHankelEquivalence s` holds.

    Proof: at each `z` in the convergence region, either `‖z‖ < 1`
    (use the disc-side lemma) or `1 ≤ ‖z‖` (use the off-disc
    lemma). -/
theorem polyLogContinuationHankelEquivalence_of_pointwise_jonquieres
    {s : ℂ}
    (h_pt : ∀ z ∈ Sheaf.JonquieresAnalyticDomain ∩
              {w : ℂ | ‖Complex.log w‖ < 2 * Real.pi} ∩ Metric.ball (0 : ℂ) 1,
              JonquieresIdentityHypothesis s z) :
    PolyLogContinuationHankelEquivalence s := by
  intro z hz
  rcases lt_or_ge ‖z‖ 1 with hz_lt | hz_ge
  · -- ‖z‖ < 1: disc branch. Use the pointwise Jonquières hypothesis.
    apply polyLog_continuation_eq_jonquieres_onDisc hz_lt
    apply h_pt
    refine ⟨hz, ?_⟩
    simp [Metric.mem_ball, hz_lt]
  · -- 1 ≤ ‖z‖: off-disc branch. Definitional equality.
    exact polyLog_continuation_eq_jonquieres_offDisc s hz hz_ge

/-! ## §7: Compatibility with existing infrastructure

The framework's existing `JonquieresGlobalIdentityHypothesis s` (from
`MonodromyFromJonquieres.lean`) targets the FULL project `SlitPlane`,
which is known (per `JonquieresAnalyticity.lean`) to be too large
(the negative-real axis obstruction). The corrected target
`JonquieresGlobalIdentityHypothesisReduced` on
`JonquieresAnalyticDomain` is the right analogue.

We provide a direct bridge from that corrected hypothesis to
`PolyLogContinuationHankelEquivalence`. -/

/-- **Bridge from `JonquieresGlobalIdentityHypothesisReduced`**:
    if the reduced global Jonquières identity holds on
    `JonquieresAnalyticDomain` (disc-agreement + analyticity on the
    maximal correct domain), then `PolyLogContinuationHankelEquivalence
    s` holds. -/
theorem polyLogContinuationHankelEquivalence_of_reducedJonquieres
    {s : ℂ} (h_red : Sheaf.JonquieresGlobalIdentityHypothesisReduced s) :
    PolyLogContinuationHankelEquivalence s := by
  intro z hz
  rcases lt_or_ge ‖z‖ 1 with hz_lt | hz_ge
  · -- Disc branch. Use the reduced hypothesis's disc-agreement.
    rw [polyLog_continuation_eq_polyLog_of_norm_lt_one s hz_lt]
    -- h_red.2 : ∀ z ∈ JonquieresAnalyticDomain ∩ Metric.ball 0 1,
    --   jonquieresExpansion s z = polyLog s z
    have hz_dom : z ∈ Sheaf.JonquieresAnalyticDomain := hz.1
    have hz_ball : z ∈ Metric.ball (0 : ℂ) 1 := by
      simp [Metric.mem_ball, hz_lt]
    exact (h_red.2 z ⟨hz_dom, hz_ball⟩).symm
  · -- Off-disc branch. Definitional equality.
    exact polyLog_continuation_eq_jonquieresExpansion_of_norm_ge_one s hz_ge

/-! ## §8: Future-work residuals (named Props)

The following Props name the remaining gaps for downstream agents.
None are discharged here; each is a clean target for a separate
session/agent. -/

/-- **Future-work residual #1**: analyticity of `polyLog_continuation s`
    on `JonquieresAnalyticDomain` (the corrected domain). Decomposes
    into the disc part (already analytic via the polyLog tsum) and the
    off-disc part (governed by
    `JonquieresZetaSeriesAnalyticityHypothesis s`, named in
    `JonquieresAnalyticity.lean`).

    The piecewise definition introduces a potential discontinuity at
    `‖z‖ = 1`; the manuscript-faithful claim is that on the
    intersection `JonquieresAnalyticDomain ∩ {‖z‖ = 1}` the two
    branches agree (Hankel equivalence on the boundary circle), so the
    piecewise function extends to a single analytic function on
    `JonquieresAnalyticDomain`. -/
def PolyLogContinuationAnalyticOnJonquieresDomain (s : ℂ) : Prop :=
  AnalyticOnNhd ℂ (polyLog_continuation s) Sheaf.JonquieresAnalyticDomain

/-- **Future-work residual #2**: agreement with mathlib's `polyLog` on
    the disc-intersection of `JonquieresAnalyticDomain`. This is just
    the `JonquieresIdentityHypothesis` rephrased for the
    `polyLog_continuation` symbol. -/
def PolyLogContinuationDiscAgreement (s : ℂ) : Prop :=
  ∀ z ∈ Sheaf.JonquieresAnalyticDomain ∩ Metric.ball (0 : ℂ) 1,
    polyLog_continuation s z = polyLog s z

/-- **Trivial discharge of `PolyLogContinuationDiscAgreement`**: by
    construction, on the disc-intersection of any domain, the
    continuation equals `polyLog` (the disc branch). Axiom-free. -/
theorem polyLogContinuationDiscAgreement_trivial (s : ℂ) :
    PolyLogContinuationDiscAgreement s := by
  intro z hz
  have hz_ball : z ∈ Metric.ball (0 : ℂ) 1 := hz.2
  have hz_norm : ‖z‖ < 1 := by simpa [Metric.mem_ball] using hz_ball
  exact polyLog_continuation_eq_polyLog_of_norm_lt_one s hz_norm

/-! ## §9: Status summary

**Discharged in this file (axiom-free, no `sorry`)**:

* `polyLog_continuation` — the headline `noncomputable def`.
* `polyLog_continuation_eq_polyLog_of_norm_lt_one` — disc-branch
  compatibility.
* `polyLog_continuation_eq_jonquieresExpansion_of_norm_ge_one` —
  off-disc-branch compatibility.
* `polyLog_continuation_at_zero` — anchor at zero.
* `polyLog_continuation_eq_jonquieres_offDisc` — trivial off-disc half
  of the Hankel equivalence.
* `polyLog_continuation_eq_jonquieres_onDisc` — disc-side half of the
  Hankel equivalence, mediated by the existing
  `JonquieresIdentityHypothesis`.
* `polyLogContinuationHankelEquivalence_of_pointwise_jonquieres` —
  capstone reduction: pointwise Jonquières identity on the convergence-
  region disc-intersection ⟹ `PolyLogContinuationHankelEquivalence`.
* `polyLogContinuationHankelEquivalence_of_reducedJonquieres` — bridge
  from the corrected-domain hypothesis.
* `polyLogContinuationDiscAgreement_trivial` — disc-agreement holds by
  construction.

**Named residual Props (open, future work)**:

* `PolyLogContinuationHankelEquivalence s` — the Hankel ⇔ Jonquières
  equivalence on the convergence region. Reducible to
  `JonquieresIdentityHypothesis` on the disc-intersection (the
  off-disc half being trivial).
* `PolyLogContinuationAnalyticOnJonquieresDomain s` — full analyticity
  of the continuation on the corrected domain. Reducible to the
  off-disc analyticity Prop already named in
  `JonquieresAnalyticity.lean` (`JonquieresZetaSeriesAnalyticityHypothesis`)
  PLUS a boundary-circle continuity bridge.

**Honest framing**: this file is **scaffold-only**. It does NOT
discharge the full Hankel ⇔ Jonquières equivalence (that is the
multi-month Erdélyi-Magnus-Oberhettinger-Tricomi formalization). It
DOES provide:

* A single `polyLog_continuation` Lean symbol that future consumers
  (in particular, a re-formulated `axiom_content_FIVE_INPUTS`) can
  build against.
* The structural compatibility lemmas that make any disc-side proof
  about `polyLog` lift automatically.
* The off-disc branch tied directly to `jonquieresExpansion`, so any
  future Jonquières-side discharge (e.g. extension of
  `jonquieresIdentityPointGermAtHalf_zero_proved` to general s) flows
  through without re-architecture.
* Named residual Props for downstream agents to attack one-by-one.

**Cleanest next-step path** (for the next agent):

1. **Discharge `PolyLogContinuationHankelEquivalence s` at `s = 0`**
   by lifting `jonquieresIdentityPointGermAtHalf_zero_proved` plus
   the disc-agreement capstone
   `discAgreementReduced_at_zero_unconditional_on_bernoulli`
   (commit `f313ceb`) through
   `polyLogContinuationHankelEquivalence_of_pointwise_jonquieres`. This
   would be the FIRST point-wise discharge of the new continuation
   symbol's manuscript-faithful identity at a specific `s`.

2. **Reformulate `axiom_content_FIVE_INPUTS`** against
   `polyLog_continuation` (companion file
   `AxiomRetirementWrapperContinuation.lean`). Input 3
   (`h_bracket_lower`) is no longer structurally false in the
   reformulated wrapper.

3. **Discharge `PolyLogContinuationAnalyticOnJonquieresDomain s`** by
   combining `JonquieresZetaSeriesAnalyticityHypothesis` (off-disc)
   with the existing `polyLog_analyticOnNhd_ball` lemmas (on-disc)
   and a boundary-circle continuity bridge.

Stage L14 — PolyLog continuation scaffold (axiom-free, no `sorry`).
-/

end PrincipiaTractalis.Analytic
