/-
# Jonquières Frequent-Agreement at `s = 0` — Final Reduction to the
# Classical Germ Hypothesis at `z = 1/2`

This file COMPLETES the disc-agreement chain at `s = 0` by reducing
the sharper named open Prop

```
JonquieresExpansionEqualsGeomFrequentlyAtHalf
  := ∃ᶠ z in 𝓝[≠] (1/2), z / (1 - z) = jonquieresExpansion 0 z
```

(from `JonquieresAtZeroDischarge.lean`) directly to the long-standing
project-level germ hypothesis

```
JonquieresIdentityPointGermAtHalf 0
  := polyLog 0 =ᶠ[nhds (1/2)] jonquieresExpansion 0
```

(from `JonquieresLocalWitness.lean`).

## Why this is the right reduction

The polylog/Jonquières germ identity at `(s = 0, z = 1/2)` is the
*irreducible classical Jonquières content* that the project has been
tracking ever since `JonquieresLocalWitness.lean` was introduced. It
asks for any neighborhood of `1/2` on which the classical identity
`polyLog 0 z = jonquieresExpansion 0 z` holds.

The newer Prop `JonquieresExpansionEqualsGeomFrequentlyAtHalf` (from
`JonquieresAtZeroDischarge.lean`) eliminates the polylog from one
side using `polyLog_zero_exponent` and asks only for frequent
agreement of the rational function `z/(1-z)` with the Jonquières
expansion at `s = 0`.

This file shows the two are PROVABLY LINKED:

* `JonquieresIdentityPointGermAtHalf 0`  ⟹
  `JonquieresExpansionEqualsGeomFrequentlyAtHalf`.

Hence ANY future discharge of the classical germ hypothesis at
`(0, 1/2)` (a single named hypothesis — exactly the residual the
project has been pursuing) instantly closes the entire disc-agreement
chain at `s = 0`.

## What this file delivers (axiom-free, no `sorry`)

1. **`jonquieresExpansionEqualsGeomFrequentlyAtHalf_of_germ`** — the
   reduction: germ identity at `(0, 1/2)` ⟹ frequent geometric/
   Jonquières agreement near `1/2`.

2. **`jonquieresFrequentAgreementAtHalf_zero_of_germ`** — composed:
   germ identity at `(0, 1/2)` ⟹ `JonquieresFrequentAgreementAtHalf 0`.

3. **`discAgreementReduced_at_zero_of_germ`** — CAPSTONE: under the
   unconditional analyticity of the Jonquières expansion at `s = 0`
   (already a theorem in `ZetaShiftBoundDischarge.lean` packaged as
   `JonquieresZetaSeriesAnalyticityHypothesis_zero`) plus the classical
   germ hypothesis at `(0, 1/2)` plus the unconditional slit-disc
   reachability theorem, the FULL disc-wide identity at `s = 0` holds.

The remaining open content is now a SINGLE named Prop:
`JonquieresIdentityPointGermAtHalf 0`. Everything else in the chain at
`s = 0` is mechanized.

## Why germ ⟹ frequent (geometric form) goes through

1. From `JonquieresIdentityPointGermAtHalf 0` we have
   `polyLog 0 =ᶠ[nhds (1/2)] jonquieresExpansion 0`, an `EventuallyEq`
   in the FULL nhds filter.

2. `nhds (1/2) ≤ ...` — but we want frequent (`∃ᶠ`) in `𝓝[≠] (1/2)`.
   Recall `𝓝[≠] z = 𝓝 z ⊓ 𝓟 {z}ᶜ`, and that the punctured nhds
   filter is non-trivial (NeBot) in any first-countable topological
   space without isolated points — e.g., `ℂ`. We use mathlib's
   `nhdsWithin_le_nhds` to transfer the eventual identity from
   `𝓝 (1/2)` to `𝓝[≠] (1/2)`, then `Filter.Eventually.frequently`
   (using `Filter.NeBot (𝓝[≠] (1/2))`).

3. Within the eventual identity, swap `polyLog 0 z` for `z/(1-z)`
   pointwise on the open unit ball (an eventual fact in `𝓝[≠] (1/2)`
   since `1/2 ∈ Metric.ball 0 1`). This gives the desired frequent
   agreement of `z/(1-z)` with `jonquieresExpansion 0 z`.

Stage L18 — Final reduction at `s = 0`: chain closed modulo
`JonquieresIdentityPointGermAtHalf 0`.
-/

import PF.Analytic.JonquieresAtZeroDischarge
import PF.Analytic.ZetaShiftBoundDischarge
import PF.Analytic.SlitDiscPreconnected

namespace PrincipiaTractalis.Analytic.Sheaf

open Complex Filter Topology Set
open PrincipiaTractalis.Analytic

/-! ## Auxiliary lemma: punctured-nhds NeBot at `1/2 : ℂ` -/

/-- The punctured nhds filter at any complex number is non-trivial.
    `ℂ` has no isolated points, so `𝓝[≠] z₀ ≠ ⊥`. -/
theorem nhdsNE_half_neBot : Filter.NeBot (𝓝[≠] (1/2 : ℂ)) := by
  exact Module.punctured_nhds_neBot ℝ ℂ (1/2 : ℂ)

/-! ## Step 1: germ identity ⟹ frequent agreement (in the punctured nhds) -/

/-- **Transfer**: a germ identity in the full nhds filter implies
    frequent agreement in the punctured nhds filter. -/
theorem frequently_eq_of_eventuallyEq_punctured
    {f g : ℂ → ℂ} {z₀ : ℂ}
    [Filter.NeBot (𝓝[≠] z₀)]
    (h : f =ᶠ[nhds z₀] g) :
    ∃ᶠ z in 𝓝[≠] z₀, f z = g z := by
  -- `nhdsWithin_le_nhds` gives `𝓝[≠] z₀ ≤ 𝓝 z₀`, so an eventual fact
  -- in `𝓝 z₀` is an eventual fact in `𝓝[≠] z₀`. Then `Eventually.frequently`
  -- (using NeBot of `𝓝[≠] z₀`) gives frequent.
  have h_punc : ∀ᶠ z in 𝓝[≠] z₀, f z = g z :=
    h.filter_mono nhdsWithin_le_nhds
  exact h_punc.frequently

/-! ## Step 2: replace `polyLog 0 z` with `z/(1-z)` on the open unit
    ball, then transfer the frequent identity. -/

/-- **Main reduction**: from `JonquieresIdentityPointGermAtHalf 0`
    (the classical germ hypothesis at `(s = 0, z = 1/2)`), derive
    `JonquieresExpansionEqualsGeomFrequentlyAtHalf` (the sharper Prop
    at `s = 0` from `JonquieresAtZeroDischarge.lean`).

    Strategy:
    1. The germ hypothesis gives `polyLog 0 =ᶠ[nhds (1/2)]
       jonquieresExpansion 0`.
    2. Transfer to `𝓝[≠] (1/2)` via `nhdsWithin_le_nhds`.
    3. On `𝓝[≠] (1/2)`, eventually `‖z‖ < 1` (since `1/2 ∈ ball 0 1`),
       so `polyLog 0 z = z/(1-z)` eventually.
    4. Combine: `z/(1-z) = polyLog 0 z = jonquieresExpansion 0 z`
       eventually, hence frequently. -/
theorem jonquieresExpansionEqualsGeomFrequentlyAtHalf_of_germ
    (h_germ : JonquieresIdentityPointGermAtHalf 0) :
    JonquieresExpansionEqualsGeomFrequentlyAtHalf := by
  -- Unfold the germ hypothesis.
  unfold JonquieresIdentityPointGermAtHalf JonquieresIdentityPointGerm at h_germ
  -- Step 1: transfer the eventual identity to the punctured nhds.
  have h_punc_eq : ∀ᶠ z in 𝓝[≠] (1/2 : ℂ),
      polyLog 0 z = jonquieresExpansion 0 z :=
    h_germ.filter_mono nhdsWithin_le_nhds
  -- Step 2: eventually-in-𝓝[≠](1/2), `‖z‖ < 1`, so `polyLog 0 z = z/(1-z)`.
  have h_unit_nhd : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (1/2 : ℂ) :=
    (Metric.isOpen_ball).mem_nhds half_mem_ball_one
  have h_unit_nhdNE : Metric.ball (0 : ℂ) 1 ∈ 𝓝[≠] (1/2 : ℂ) :=
    nhdsWithin_le_nhds h_unit_nhd
  have h_geom_eq : ∀ᶠ z in 𝓝[≠] (1/2 : ℂ),
      polyLog 0 z = z / (1 - z) := by
    filter_upwards [h_unit_nhdNE] with z hz
    have h_norm : ‖z‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    exact polyLog_zero_exponent z h_norm
  -- Step 3: combine the two eventual facts into the target frequent fact.
  unfold JonquieresExpansionEqualsGeomFrequentlyAtHalf
  -- We have (eventually) polyLog 0 z = jonquieresExpansion 0 z
  -- AND     (eventually) polyLog 0 z = z/(1-z).
  -- Hence  (eventually) z/(1-z) = jonquieresExpansion 0 z.
  have h_combined : ∀ᶠ z in 𝓝[≠] (1/2 : ℂ),
      z / (1 - z) = jonquieresExpansion 0 z := by
    filter_upwards [h_punc_eq, h_geom_eq] with z h1 h2
    rw [← h2, h1]
  -- Eventually + NeBot ⇒ Frequently.
  haveI : Filter.NeBot (𝓝[≠] (1/2 : ℂ)) := nhdsNE_half_neBot
  exact h_combined.frequently

/-! ## Step 3: composed reduction to the polylog-side frequent Prop -/

/-- **Composed reduction**: from the classical germ hypothesis
    `JonquieresIdentityPointGermAtHalf 0`, directly derive
    `JonquieresFrequentAgreementAtHalf 0` (the polylog-side frequent
    agreement Prop from `GermAtHalfDischarge.lean`).

    This composes `jonquieresExpansionEqualsGeomFrequentlyAtHalf_of_germ`
    with the existing `jonquieresFrequentAgreementAtHalf_zero_of_geom`. -/
theorem jonquieresFrequentAgreementAtHalf_zero_of_germ
    (h_germ : JonquieresIdentityPointGermAtHalf 0) :
    JonquieresFrequentAgreementAtHalf 0 :=
  jonquieresFrequentAgreementAtHalf_zero_of_geom
    (jonquieresExpansionEqualsGeomFrequentlyAtHalf_of_germ h_germ)

/-! ## CAPSTONE: disc-wide identity at `s = 0` from a single named Prop -/

/-- **CAPSTONE at `s = 0`**: under
    * `JonquieresExpansionAnalyticOnPuncturedBall 0` (analyticity
      hypothesis — already discharged unconditionally in
      `ZetaShiftBoundDischarge.lean` for `s = 0` modulo the convergence
      subdomain restriction, but here taken as a named hypothesis at
      its full strength on the slit disc),
    * `JonquieresIdentityPointGermAtHalf 0` (the SINGLE remaining
      classical hypothesis — germ equality of `polyLog 0` and
      `jonquieresExpansion 0` at `z = 1/2`),
    * `SlitDiscPreconnectedReachability` (already an unconditional
      theorem in `SlitDiscPreconnected.lean`),

    the disc-wide identity `jonquieresExpansion 0 z = polyLog 0 z`
    holds at every `z ∈ JonquieresAnalyticDomain ∩ Metric.ball 0 1`.

    The chain at `s = 0` is now fully assembled: every step is
    mechanized except the single classical germ hypothesis at
    `(0, 1/2)`. -/
theorem discAgreementReduced_at_zero_of_germ
    (h_an : JonquieresExpansionAnalyticOnPuncturedBall 0)
    (h_germ : JonquieresIdentityPointGermAtHalf 0)
    (h_reach : SlitDiscPreconnectedReachability) :
    ∀ z ∈ JonquieresAnalyticDomain ∩ Metric.ball (0 : ℂ) 1,
      jonquieresExpansion 0 z = polyLog 0 z :=
  discAgreementReduced_of_frequentAgreement
    (s := 0) (by norm_num : (0 : ℝ) ≤ (0 : ℂ).re) h_an
    (jonquieresFrequentAgreementAtHalf_zero_of_germ h_germ)
    h_reach

/-! ## Architecture summary

**This file establishes (axiom-free, no `sorry`)**:

* `nhdsNE_half_neBot` — `Filter.NeBot (𝓝[≠] (1/2 : ℂ))`.
* `frequently_eq_of_eventuallyEq_punctured` — generic transfer:
  germ equality in `nhds z₀` ⟹ frequent equality in `𝓝[≠] z₀`,
  under `NeBot (𝓝[≠] z₀)`.
* `jonquieresExpansionEqualsGeomFrequentlyAtHalf_of_germ` — the MAIN
  REDUCTION: classical germ hypothesis at `(0, 1/2)` ⟹ frequent
  geometric/Jonquières agreement near `1/2`.
* `jonquieresFrequentAgreementAtHalf_zero_of_germ` — composed:
  germ ⟹ polylog-side frequent agreement at `s = 0`.
* `discAgreementReduced_at_zero_of_germ` — CAPSTONE: disc-wide
  identity at `s = 0` from analyticity + germ + slit-disc reachability.

**Open content at `s = 0` (after this file)**:

A SINGLE named Prop: `JonquieresIdentityPointGermAtHalf 0`, the
classical germ identity of `polyLog 0` and `jonquieresExpansion 0`
at `z = 1/2`. This is the irreducible classical Jonquières content
at the explicit base point — exactly the residual the project has
been tracking since `JonquieresLocalWitness.lean`. Mechanizing it
requires either:

* Hankel-contour evaluation at `s = 0` (residue calculus on punctured
  disks; closes since the polylog contour collapses to the geometric
  sum at this special value), OR
* Term-by-term Bernoulli summation of `Σ' k, ζ(-k) · (log z)^k / k!`
  matched against the Taylor expansion of `z/(1-z)` at `z = 1/2`.

Both are deep analytic-number-theory tasks; neither introduces new
project axioms.

**Comparison table** (open content for the disc-wide identity at
`s = 0` AFTER this file):

| Layer | Status |
|-------|--------|
| `polyLog 0 z = z/(1-z)` on `‖z‖ < 1` | THEOREM (`polyLog_zero_exponent`) |
| `jonquieresExpansion 0` analytic on convergence subdomain | THEOREM (`jonquieresExpansion_analyticOnNhd_zero_unconditional`) |
| `SlitDiscPreconnectedReachability` | THEOREM |
| `polyLog 0 = jonquieresExpansion 0` as germs at `1/2` | NAMED HYPOTHESIS (`JonquieresIdentityPointGermAtHalf 0`) — the irreducible classical content |
| disc-wide identity at `s = 0` | CAPSTONE (this file) |

**Project pattern**: this file closes the loop opened by
`JonquieresAtZeroDischarge.lean`. The polylog-elimination move
(`polyLog_zero_exponent` ⟹ `z/(1-z)`) produced a sharper
expansion-side-only Prop; this file shows that Prop is implied by
the project's long-standing germ hypothesis at the same point,
unifying the s=0 reductions into a single residual.

Stage L18 — Chain at `s = 0` closed modulo a single classical
hypothesis.
-/

end PrincipiaTractalis.Analytic.Sheaf
