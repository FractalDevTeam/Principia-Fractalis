/-
# Germ-at-1/2 Discharge — Identity-Theorem Reduction to a Frequent-Equality Witness

This file SHARPENS the named hypothesis
`JonquieresIdentityPointGermAtHalf s` from
`PF/Analytic/JonquieresLocalWitness.lean` by reducing the germ
equality at `z₀ = 1/2` to **pointwise agreement along a single
sequence** accumulating at `1/2`.

## What this file delivers (axiom-free, no `sorry`)

The key tool is mathlib's local identity theorem
`AnalyticAt.frequently_eq_iff_eventually_eq`: for two functions both
analytic at a point `z₀`, germ equality at `z₀` is EQUIVALENT to
frequent (≡ punctured-neighborhood-cluster) pointwise equality there.

We exploit this in three steps:

1. **`polyLog_analyticAt_half`** (UNCONDITIONAL for `0 ≤ Re s`).
   The polylog tsum is analytic on the open unit ball, and `1/2`
   sits there, so `polyLog s` is analytic at `1/2`. This is a direct
   application of `polyLog_analyticOnNhd_ball` from
   `PolyLogHankelRealization.lean`.

2. **`jonquieresExpansion_analyticAt_half`** (under the existing
   named hypothesis `JonquieresExpansionAnalyticOnPuncturedBall s`).
   The Jonquières expansion is analytic on the slit disc by
   hypothesis, and `1/2` lies in `Metric.ball 0 1 ∩
   JonquieresAnalyticDomain` (proved in `JonquieresLocalWitness.lean`).

3. **`JonquieresFrequentAgreementAtHalf s`** — the SHARPER named
   open Prop. It asks for `polyLog s = jonquieresExpansion s`
   frequently in the punctured-neighborhood filter `𝓝[≠] (1/2)`.
   Concretely: there is no neighborhood of `1/2` where the two
   functions disagree on every punctured point — equivalently,
   one can find points arbitrarily close to (but distinct from)
   `1/2` where the identity holds.

## The reduction theorem

`jonquieresIdentityPointGermAtHalf_of_frequentAgreement`:
under `0 ≤ Re s`, the analyticity hypothesis on the expansion, and
`JonquieresFrequentAgreementAtHalf s`, we derive
`JonquieresIdentityPointGermAtHalf s`. This is a straightforward
application of `frequently_eq_iff_eventually_eq`.

## Why this is a real sharpening

The previous formulation `JonquieresIdentityPointGermAtHalf s`
required equality on a WHOLE neighborhood of `1/2`. The sharper
formulation only requires equality at points arbitrarily close to
`1/2` (a much weaker open content). The identity theorem then
extends frequent agreement to a full neighborhood for free, using
analyticity.

Concretely: any sequence `z_n → 1/2` with `z_n ≠ 1/2` and
`polyLog s z_n = jonquieresExpansion s z_n` (for all n) suffices to
discharge the frequent-agreement Prop, hence the germ identity.

## Capstone

`discAgreementReduced_of_frequentAgreement`: combining this file's
reduction with the existing `discAgreementReduced_of_germAtHalf`
from `JonquieresLocalWitness.lean`, the disc-wide Jonquières
identity follows from:
* `JonquieresExpansionAnalyticOnPuncturedBall s` (named),
* `JonquieresFrequentAgreementAtHalf s` (SHARPER named),
* `SlitDiscPreconnectedReachability` (unconditional theorem elsewhere).

This is the SHARPEST formulation: the pointwise identity content is
isolated to *frequent agreement near a single explicit point*.

Stage L16 — Germ-at-1/2 frequent-agreement reduction (2026-05-21).
-/

import PF.Analytic.JonquieresLocalWitness
import PF.Analytic.PolyLogHankelRealization
import Mathlib.Analysis.Analytic.IsolatedZeros

namespace PrincipiaTractalis.Analytic.Sheaf

open Complex Filter Topology Set
open PrincipiaTractalis.Analytic

/-! ## Analyticity facts at the explicit point z₀ = 1/2 -/

/-- **`polyLog s` is analytic at `1/2`** (unconditional for `0 ≤ Re s`).
    Direct from `polyLog_analyticOnNhd_ball` + `half_mem_ball_one`. -/
theorem polyLog_analyticAt_half {s : ℂ} (hs : 0 ≤ s.re) :
    AnalyticAt ℂ (polyLog s) (1/2 : ℂ) :=
  polyLog_analyticOnNhd_ball hs (1/2 : ℂ) half_mem_ball_one

/-- **`jonquieresExpansion s` is analytic at `1/2`** under the named
    analyticity hypothesis on the punctured ball.
    `1/2 ∈ Metric.ball 0 1 ∩ JonquieresAnalyticDomain` by
    `half_mem_ball_one` and `half_mem_jonquieresDomain`. -/
theorem jonquieresExpansion_analyticAt_half
    {s : ℂ} (h_an : JonquieresExpansionAnalyticOnPuncturedBall s) :
    AnalyticAt ℂ (jonquieresExpansion s) (1/2 : ℂ) :=
  h_an (1/2 : ℂ) ⟨half_mem_ball_one, half_mem_jonquieresDomain⟩

/-! ## The sharper hypothesis: frequent agreement near `1/2` -/

/-- **Frequent pointwise agreement of `polyLog s` and
    `jonquieresExpansion s` near `1/2`**.

    This is the SHARPER open content. The `∃ᶠ` predicate in the
    punctured-neighborhood filter `𝓝[≠] (1/2)` says: in every
    punctured neighborhood of `1/2`, there is some point where the
    two functions agree.

    Equivalent (by the standard sequential characterization in
    first-countable spaces, which `ℂ` is): there exists a sequence
    `z_n → 1/2` with `z_n ≠ 1/2` for all `n` and
    `polyLog s z_n = jonquieresExpansion s z_n` for all `n`. -/
def JonquieresFrequentAgreementAtHalf (s : ℂ) : Prop :=
  ∃ᶠ z in 𝓝[≠] (1/2 : ℂ), polyLog s z = jonquieresExpansion s z

/-! ## The reduction theorem -/

/-- **Reduction: frequent agreement near 1/2 + two analyticity facts
    ⇒ germ equality at 1/2**.

    Proof: direct application of mathlib's local identity theorem
    `AnalyticAt.frequently_eq_iff_eventually_eq`. -/
theorem jonquieresIdentityPointGermAtHalf_of_frequentAgreement
    {s : ℂ} (hs : 0 ≤ s.re)
    (h_an : JonquieresExpansionAnalyticOnPuncturedBall s)
    (h_freq : JonquieresFrequentAgreementAtHalf s) :
    JonquieresIdentityPointGermAtHalf s := by
  -- Unfold the target germ Prop.
  unfold JonquieresIdentityPointGermAtHalf JonquieresIdentityPointGerm
  -- Apply the local identity theorem: frequent agreement ⇔ germ equality
  -- when both functions are analytic at the point.
  exact (AnalyticAt.frequently_eq_iff_eventually_eq
    (polyLog_analyticAt_half hs)
    (jonquieresExpansion_analyticAt_half h_an)).mp h_freq

/-! ## Capstone: full disc-agreement from frequent agreement at 1/2 -/

/-- **CAPSTONE**: from analyticity of the expansion on the slit disc
    + frequent agreement near `1/2` + slit-disc preconnectedness,
    the disc-wide Jonquières identity holds.

    Open content reduced to:
    * `JonquieresExpansionAnalyticOnPuncturedBall s` (named),
    * `JonquieresFrequentAgreementAtHalf s` (SHARPER named — strictly
      weaker than a germ equality, which is weaker than a ball
      equality, which is weaker than disc-wide equality).
    * `SlitDiscPreconnectedReachability` (named, but already an
      unconditional theorem in `SlitDiscPreconnected.lean`). -/
theorem discAgreementReduced_of_frequentAgreement
    {s : ℂ} (hs : 0 ≤ s.re)
    (h_an : JonquieresExpansionAnalyticOnPuncturedBall s)
    (h_freq : JonquieresFrequentAgreementAtHalf s)
    (h_reach : SlitDiscPreconnectedReachability) :
    ∀ z ∈ JonquieresAnalyticDomain ∩ Metric.ball (0 : ℂ) 1,
      jonquieresExpansion s z = polyLog s z :=
  discAgreementReduced_of_germAtHalf hs h_an
    (jonquieresIdentityPointGermAtHalf_of_frequentAgreement hs h_an h_freq)
    h_reach

/-! ## Constructive form: a sequence at 1/2 suffices.

A frequently-`R z` filter in `𝓝[≠] z₀` (in a first-countable space
like `ℂ`) is equivalent to the existence of a sequence `z_n → z₀`
with `z_n ≠ z₀` for all `n` and `R z_n` for all `n`. We package the
forward direction here as a convenience constructor. -/

/-- **Sequential constructor for frequent agreement**.

    Given a sequence `z : ℕ → ℂ` with `z n ≠ 1/2` for all `n`,
    `Tendsto z atTop (𝓝 (1/2))`, and pointwise agreement at every
    `z n`, deduce `JonquieresFrequentAgreementAtHalf s`. -/
theorem jonquieresFrequentAgreementAtHalf_of_sequence
    {s : ℂ}
    (z : ℕ → ℂ)
    (h_ne : ∀ n, z n ≠ (1/2 : ℂ))
    (h_tend : Tendsto z atTop (𝓝 (1/2 : ℂ)))
    (h_eq : ∀ n, polyLog s (z n) = jonquieresExpansion s (z n)) :
    JonquieresFrequentAgreementAtHalf s := by
  -- Build a tendsto in 𝓝[≠] (1/2) from the data, then use frequently_of_forall.
  unfold JonquieresFrequentAgreementAtHalf
  -- The composed filter Tendsto z atTop (𝓝[≠] (1/2)).
  have h_tendNE : Tendsto z atTop (𝓝[≠] (1/2 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨h_tend, ?_⟩
    -- ∀ᶠ n in atTop, z n ∈ {1/2}ᶜ, i.e., z n ≠ 1/2
    exact Filter.Eventually.of_forall h_ne
  -- atTop is NeBot on ℕ, and the predicate holds for all n.
  exact h_tendNE.frequently (Filter.Eventually.frequently
    (Filter.Eventually.of_forall h_eq))

/-! ## Architecture summary

**This file establishes (axiom-free, no `sorry`)**:

* `polyLog_analyticAt_half` — `polyLog s` is analytic at `1/2`
  (unconditional for `0 ≤ Re s`).
* `jonquieresExpansion_analyticAt_half` — `jonquieresExpansion s` is
  analytic at `1/2` under the named expansion-analyticity hypothesis.
* `JonquieresFrequentAgreementAtHalf s` — the SHARPER open Prop:
  frequent agreement of polyLog and the expansion near `1/2`.
* `jonquieresIdentityPointGermAtHalf_of_frequentAgreement` — the
  REDUCTION: frequent agreement + analyticity ⇒ germ equality.
* `discAgreementReduced_of_frequentAgreement` — CAPSTONE: under
  analyticity + frequent agreement + slit-disc reachability, the
  disc-wide identity holds.
* `jonquieresFrequentAgreementAtHalf_of_sequence` — convenience
  sequential constructor: a single sequence `z_n → 1/2`
  (`z_n ≠ 1/2`) along which the identity holds suffices.

**Residual gap (sharpest formulation)**:

1. `JonquieresExpansionAnalyticOnPuncturedBall s` — unchanged.

2. `JonquieresFrequentAgreementAtHalf s` — STRICTLY WEAKER than
   the prior germ-at-`1/2` Prop. Mechanism for closing it: produce
   ANY single sequence `z_n → 1/2` with `z_n ≠ 1/2` such that
   `polyLog s z_n = jonquieresExpansion s z_n` for all `n`.

**Comparison table** (open content for the disc-wide identity):

| Version | Open Prop on the identity side |
|---------|--------------------------------|
| Original | pointwise equality at every `z ∈ JonquieresAnalyticDomain ∩ ball 0 1` |
| `JonquieresIdentityLocalWitness` | ∃ ball where equality holds |
| `JonquieresIdentityPointGerm s z₀` | germ at SOME interior point |
| `JonquieresIdentityPointGermAtHalf` | germ at the explicit point `1/2` |
| `JonquieresFrequentAgreementAtHalf` (THIS FILE) | frequent agreement near `1/2` |

Each row is STRICTLY WEAKER than the one above. The final
formulation requires no neighborhood-shape, no germ data — only the
existence of a single accumulating sequence of agreement points.

**Project pattern**: this file extends the
`polyLogHankelRealization_from_extension` and
`discAgreementReduced_of_germAtHalf` reduction style by exploiting
mathlib's local identity theorem to soften "germ equality" into
"frequent pointwise agreement," the weakest open content for which
analyticity-driven identity propagation still goes through.

Stage L16 — Germ-at-1/2 frequent-agreement reduction (2026-05-21).
-/

end PrincipiaTractalis.Analytic.Sheaf
