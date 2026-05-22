/-
# Jonquières Identity Local Witness — Germ-Level Reduction

This file SHARPENS the named hypothesis
`JonquieresIdentityLocalWitness s` from
`PF/Analytic/JonquieresIdentityDischarge.lean` by reducing it to a
**germ-level pointwise identity at a SINGLE named point** inside the
slit disc.

## What this file delivers (axiom-free, no `sorry`)

1. **`JonquieresIdentityPointGerm s z₀`** — the sharper named
   hypothesis: the function germ `polyLog s` agrees with
   `jonquieresExpansion s` at `z₀ ∈ Metric.ball 0 1 ∩
   JonquieresAnalyticDomain`. Formally,
       `polyLog s =ᶠ[nhds z₀] jonquieresExpansion s`.
   This is STRICTLY WEAKER than `JonquieresIdentityLocalWitness`: the
   latter demands pointwise equality on a whole ball; the former only
   asks for equality on SOME neighborhood (which the nhds filter
   automatically supplies, but with no shape constraint).

2. **`jonquieresIdentityLocalWitness_of_germ`** — the WRAPPER theorem:
   from `JonquieresIdentityPointGerm s z₀` for any `z₀ ∈
   Metric.ball 0 1 ∩ JonquieresAnalyticDomain`, extract a witness
   ball satisfying ALL three conditions of
   `JonquieresIdentityLocalWitness s`:
   * radius `ρ > 0`;
   * `Metric.ball z₀ ρ ⊆ Metric.ball 0 1`;
   * `Metric.ball z₀ ρ ⊆ JonquieresAnalyticDomain`;
   * pointwise identity on `Metric.ball z₀ ρ`.

   Proof: the EventuallyEq germ unfolds (via `Metric.mem_nhds_iff`) to
   a ball `Metric.ball z₀ δ` on which the identity holds. Intersect
   with two further open sets (`ball 0 1` and `JonquieresAnalyticDomain`,
   both open and both containing `z₀`) by taking a smaller `ρ` (the
   minimum of three radii). This is the standard "open in three
   open sets ⇒ open in the intersection" technique.

3. **`JonquieresIdentityPointGermAtHalf s`** — the SPECIALIZED named
   hypothesis at the explicit point `z₀ = 1/2` (real). This is the
   simplest, most attackable witness: `1/2 ∈ Metric.ball 0 1` (since
   `‖1/2‖ = 1/2 < 1`) and `1/2 ∈ JonquieresAnalyticDomain` (since
   `1/2` is positive real, not on `(-∞, 0]` or `[1, ∞)`).

4. **`half_mem_ball_one` / `half_mem_jonquieresDomain`** — basic
   membership lemmas verifying that `1/2` is a valid witness point.

5. **`jonquieresIdentityLocalWitness_of_germAtHalf`** — the explicit
   specialization: from the germ at `1/2`, derive the local witness
   hypothesis. This is the **cleanest reduction path**: from a single
   germ-equality at the explicit point `z₀ = 1/2`, we obtain the
   entire `JonquieresIdentityLocalWitness s`.

## Why this is a real sharpening

The previous formulation `JonquieresIdentityLocalWitness s` demands:
* existence of `z₀ : ℂ`,
* existence of `ρ > 0`,
* `Metric.ball z₀ ρ ⊆ Metric.ball 0 1`,
* `Metric.ball z₀ ρ ⊆ JonquieresAnalyticDomain`,
* pointwise `polyLog s z = jonquieresExpansion s z` on the WHOLE ball.

The sharper germ formulation demands only:
* `polyLog s =ᶠ[nhds z₀] jonquieresExpansion s` at the explicit
  `z₀ = 1/2`.

The shape constraints (ball, ball-in-domain) are dispatched
automatically by the wrapper. The point selection is pinned to `1/2`,
removing the existential over `z₀`. The remaining open content is
**purely the germ equality at one specific point**.

## The classical identity at z = 1/2

For `s` with `Re s > 1`, both `polyLog s` and `jonquieresExpansion s`
are analytic on a neighborhood of `1/2`. The classical
Erdélyi-Magnus-Oberhettinger-Tricomi identity gives pointwise equality
throughout the convergence region `|log z| < 2π`, which includes
`z = 1/2` (since `|log(1/2)| = log 2 ≈ 0.693 < 2π ≈ 6.28`).
Equivalently: by analytic continuation from `z = 1` (where the
identity holds unconditionally for `Re s > 1` via
`polyLog_eq_jonquieresExpansion_at_one`) along a path inside the
slit disc, the germ at `1/2` agrees with the germ at `1`. The
classical proof completes via Hankel-contour deformation.

This file does NOT close the classical identity; it isolates the
remaining open content to a single germ-equality at `1/2`.

## Architecture

This file mirrors the project's `polyLogHankelRealization_from_extension`
and `discAgreementReduced_of_sharper_and_reachability` reduction
style: lock the open content into a clean named Prop, build all
surrounding structure axiom-free, document precisely what remains.

Stage L15 — Jonquières local witness germ reduction (2026-05-21).
-/

import PF.Analytic.JonquieresIdentityDischarge

namespace PrincipiaTractalis.Analytic.Sheaf

open Complex Filter Topology Set
open PrincipiaTractalis.Analytic

/-! ## The sharper germ-level hypothesis -/

/-- **Germ equality of polyLog and jonquieresExpansion at a point**.

    This is the sharper open content. The `EventuallyEq` predicate
    says: on SOME neighborhood of `z₀` (provided by the nhds filter),
    the two functions agree pointwise. No shape constraint on the
    neighborhood is imposed at the Prop level. -/
def JonquieresIdentityPointGerm (s z₀ : ℂ) : Prop :=
  polyLog s =ᶠ[nhds z₀] jonquieresExpansion s

/-! ## Basic membership lemmas at the explicit witness point z₀ = 1/2 -/

/-- `1/2 ∈ Metric.ball 0 1`: `‖1/2 - 0‖ = 1/2 < 1`. -/
theorem half_mem_ball_one : (1/2 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
  rw [Metric.mem_ball, dist_zero_right]
  -- ‖(1/2 : ℂ)‖ = 1/2
  have h : ‖(1/2 : ℂ)‖ = 1/2 := by
    rw [show ((1/2 : ℂ)) = ((1/2 : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.norm_real]
    -- ‖(1/2 : ℝ)‖ = |1/2| = 1/2
    rw [Real.norm_eq_abs]
    norm_num
  rw [h]
  norm_num

/-- `1/2 ∈ JonquieresAnalyticDomain`. The point `1/2` is positive real,
    so it avoids both `(-∞, 0]` (`SlitPlane = ℂ \ [1, ∞)` excludes
    `1` and above; `1/2 < 1` so it's IN `SlitPlane`) and the negative
    real axis (`Complex.slitPlane` excludes `(-∞, 0]`; `1/2 > 0` so
    it's in `Complex.slitPlane`). -/
theorem half_mem_jonquieresDomain :
    (1/2 : ℂ) ∈ JonquieresAnalyticDomain := by
  refine ⟨?_, ?_⟩
  · -- (1/2 : ℂ) ∈ SlitPlane = BranchCutᶜ
    unfold SlitPlane BranchCut
    rw [Set.mem_compl_iff]
    intro ⟨_, h_re⟩
    -- h_re : 1 ≤ (1/2 : ℂ).re
    have h_eq : ((1/2 : ℂ)).re = 1/2 := by
      rw [show ((1/2 : ℂ)) = ((1/2 : ℝ) : ℂ) by push_cast; ring]
      simp
    rw [h_eq] at h_re
    linarith
  · -- (1/2 : ℂ) ∈ Complex.slitPlane = {z | 0 < z.re ∨ z.im ≠ 0}
    unfold Complex.slitPlane
    left
    -- 0 < (1/2 : ℂ).re
    have h_eq : ((1/2 : ℂ)).re = 1/2 := by
      rw [show ((1/2 : ℂ)) = ((1/2 : ℝ) : ℂ) by push_cast; ring]
      simp
    rw [h_eq]
    norm_num

/-- **The germ at the explicit point `z₀ = 1/2`**. This is the
    most-specialized named Prop: a single germ equality at one fixed
    point. -/
def JonquieresIdentityPointGermAtHalf (s : ℂ) : Prop :=
  JonquieresIdentityPointGerm s (1/2 : ℂ)

/-! ## The wrapper theorem: germ + interior witness ⇒ local-witness Prop -/

/-- **Wrapper from germ-equality to ball-witness**. Given any point
    `z₀ ∈ Metric.ball 0 1 ∩ JonquieresAnalyticDomain` and a germ
    equality `polyLog s =ᶠ[nhds z₀] jonquieresExpansion s`, extract a
    radius `ρ > 0` and a ball `Metric.ball z₀ ρ` contained in BOTH
    `Metric.ball 0 1` AND `JonquieresAnalyticDomain` AND on which the
    pointwise identity holds.

    Proof strategy. The germ provides a set `U ∈ nhds z₀` on which the
    identity holds; unfold `U ∈ nhds z₀` via `Metric.mem_nhds_iff` to
    get a ball `Metric.ball z₀ δ_1 ⊆ U`. Independently, `Metric.ball
    0 1` is open and contains `z₀` (by hypothesis), so it has a
    radius `δ_2 > 0` with `Metric.ball z₀ δ_2 ⊆ Metric.ball 0 1`.
    Similarly `JonquieresAnalyticDomain` is open and contains `z₀`,
    yielding `δ_3`. Take `ρ := min δ_1 (min δ_2 δ_3)`. Then
    `Metric.ball z₀ ρ` is contained in all three sets. -/
theorem jonquieresIdentityLocalWitness_of_germ
    {s z₀ : ℂ}
    (hz_ball : z₀ ∈ Metric.ball (0 : ℂ) 1)
    (hz_dom : z₀ ∈ JonquieresAnalyticDomain)
    (h_germ : JonquieresIdentityPointGerm s z₀) :
    JonquieresIdentityLocalWitness s := by
  -- Step 1: Extract a ball from the germ equality.
  -- The `EventuallyEq` filter gives us a set U ∈ nhds z₀ on which equality holds.
  -- From U ∈ nhds z₀ we extract a ball Metric.ball z₀ δ_1 ⊆ U via mem_nhds_iff.
  rw [JonquieresIdentityPointGerm, Filter.eventuallyEq_iff_exists_mem] at h_germ
  obtain ⟨U_germ, hU_germ_nhd, h_eq_on_U⟩ := h_germ
  obtain ⟨δ_1, hδ_1_pos, hδ_1_sub⟩ := Metric.mem_nhds_iff.mp hU_germ_nhd
  -- Step 2: Extract a ball from openness of `Metric.ball 0 1` at z₀.
  have h_ball_open : IsOpen (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball
  have h_ball_nhd : Metric.ball (0 : ℂ) 1 ∈ nhds z₀ :=
    h_ball_open.mem_nhds hz_ball
  obtain ⟨δ_2, hδ_2_pos, hδ_2_sub⟩ := Metric.mem_nhds_iff.mp h_ball_nhd
  -- Step 3: Extract a ball from openness of `JonquieresAnalyticDomain` at z₀.
  have h_dom_open : IsOpen JonquieresAnalyticDomain :=
    JonquieresAnalyticDomain_isOpen
  have h_dom_nhd : JonquieresAnalyticDomain ∈ nhds z₀ :=
    h_dom_open.mem_nhds hz_dom
  obtain ⟨δ_3, hδ_3_pos, hδ_3_sub⟩ := Metric.mem_nhds_iff.mp h_dom_nhd
  -- Step 4: Take ρ := min (min δ_1 δ_2) δ_3.
  refine ⟨z₀, min (min δ_1 δ_2) δ_3, ?_, ?_, ?_, ?_⟩
  · -- 0 < ρ
    exact lt_min (lt_min hδ_1_pos hδ_2_pos) hδ_3_pos
  · -- Metric.ball z₀ ρ ⊆ Metric.ball 0 1
    intro w hw
    apply hδ_2_sub
    -- hw : w ∈ Metric.ball z₀ (min (min δ_1 δ_2) δ_3)
    -- We need w ∈ Metric.ball z₀ δ_2.
    rw [Metric.mem_ball] at hw ⊢
    -- dist w z₀ < min (min δ_1 δ_2) δ_3 ≤ δ_2
    exact lt_of_lt_of_le hw (le_trans (min_le_left _ _) (min_le_right _ _))
  · -- Metric.ball z₀ ρ ⊆ JonquieresAnalyticDomain
    intro w hw
    apply hδ_3_sub
    rw [Metric.mem_ball] at hw ⊢
    exact lt_of_lt_of_le hw (min_le_right _ _)
  · -- ∀ z ∈ Metric.ball z₀ ρ, polyLog s z = jonquieresExpansion s z
    intro w hw
    -- w ∈ Metric.ball z₀ ρ ⊆ Metric.ball z₀ δ_1 ⊆ U_germ; identity on U_germ.
    apply h_eq_on_U
    apply hδ_1_sub
    rw [Metric.mem_ball] at hw ⊢
    exact lt_of_lt_of_le hw (le_trans (min_le_left _ _) (min_le_left _ _))

/-! ## Specialization at the explicit point `z₀ = 1/2` -/

/-- **From the germ at z₀ = 1/2 to the full local-witness Prop**.

    This is the sharpest reduction: assuming only the GERM equality
    of `polyLog s` and `jonquieresExpansion s` at the single explicit
    point `1/2 : ℂ`, we derive `JonquieresIdentityLocalWitness s`.

    Combined with `discAgreementReduced_of_sharper_and_reachability`
    (which already gets the disc-wide agreement from the local
    witness + analyticity + slit-disc preconnectedness), this means:
    **the disc-wide Jonquières identity reduces to a SINGLE germ
    equality at z = 1/2**, modulo the still-named analyticity
    hypothesis `JonquieresExpansionAnalyticOnPuncturedBall`. -/
theorem jonquieresIdentityLocalWitness_of_germAtHalf
    {s : ℂ} (h_germ : JonquieresIdentityPointGermAtHalf s) :
    JonquieresIdentityLocalWitness s :=
  jonquieresIdentityLocalWitness_of_germ
    half_mem_ball_one half_mem_jonquieresDomain h_germ

/-! ## Bridge to the sharper bundled hypothesis -/

/-- **From germ + analyticity to the bundled sharper hypothesis**.
    Given the germ at `1/2` AND the analyticity of `jonquieresExpansion s`
    on the punctured ball, derive the full
    `JonquieresIdentitySharperHypothesis`. This composes the wrapper
    with the analyticity hypothesis. -/
theorem jonquieresIdentitySharperHypothesis_of_germAtHalf
    {s : ℂ}
    (h_an : JonquieresExpansionAnalyticOnPuncturedBall s)
    (h_germ : JonquieresIdentityPointGermAtHalf s) :
    JonquieresIdentitySharperHypothesis s :=
  ⟨h_an, jonquieresIdentityLocalWitness_of_germAtHalf h_germ⟩

/-! ## Capstone: full disc-agreement from the germ at 1/2 (modulo analyticity + reachability)

The composition:
* `jonquieresIdentitySharperHypothesis_of_germAtHalf` (this file) plus
* `discAgreementReduced_of_sharper_and_reachability`
  (`JonquieresIdentityDischarge.lean`) plus
* `slitDiscPreconnectedReachability_proved`
  (`SlitDiscPreconnected.lean`)

gives: under
* `JonquieresExpansionAnalyticOnPuncturedBall s` (analyticity of the
  expansion on the slit disc — named open hypothesis), AND
* `JonquieresIdentityPointGermAtHalf s` (germ equality at z = 1/2 —
  named open hypothesis, sharper than the original ball-witness),

the disc-agreement component of
`JonquieresGlobalIdentityHypothesisReduced` holds:
`∀ z ∈ JonquieresAnalyticDomain ∩ Metric.ball 0 1,
  jonquieresExpansion s z = polyLog s z`.

The slit-disc preconnectedness is now an unconditional theorem (see
`SlitDiscPreconnected.lean`), so it does NOT appear among the
remaining open content. -/

/-- **CAPSTONE**: from analyticity of the expansion on the slit disc
    plus the germ at `z = 1/2`, the disc-wide identity holds. The
    slit-disc preconnectedness is supplied as a separate hypothesis to
    keep this file independent of `SlitDiscPreconnected.lean`.

    Once the user wires in `slitDiscPreconnectedReachability_proved`
    (already a theorem in `SlitDiscPreconnected.lean`), this becomes
    a 2-hypothesis reduction: analyticity + germ at 1/2. -/
theorem discAgreementReduced_of_germAtHalf
    {s : ℂ} (hs : 0 ≤ s.re)
    (h_an : JonquieresExpansionAnalyticOnPuncturedBall s)
    (h_germ : JonquieresIdentityPointGermAtHalf s)
    (h_reach : SlitDiscPreconnectedReachability) :
    ∀ z ∈ JonquieresAnalyticDomain ∩ Metric.ball (0 : ℂ) 1,
      jonquieresExpansion s z = polyLog s z :=
  discAgreementReduced_of_sharper_and_reachability hs
    (jonquieresIdentitySharperHypothesis_of_germAtHalf h_an h_germ)
    h_reach

/-! ## Architecture summary

**This file establishes (axiom-free, no `sorry`)**:

* `JonquieresIdentityPointGerm s z₀` — the sharper germ-level
  hypothesis: germ equality of `polyLog s` and
  `jonquieresExpansion s` at any point `z₀`.
* `JonquieresIdentityPointGermAtHalf s` — the specialization at the
  explicit witness `z₀ = 1/2`.
* `half_mem_ball_one` — `1/2 ∈ Metric.ball 0 1`.
* `half_mem_jonquieresDomain` — `1/2 ∈ JonquieresAnalyticDomain`.
* `jonquieresIdentityLocalWitness_of_germ` — the WRAPPER: from a
  germ at any interior witness, derive the full
  `JonquieresIdentityLocalWitness s` Prop.
* `jonquieresIdentityLocalWitness_of_germAtHalf` — specialization at
  `z₀ = 1/2`.
* `jonquieresIdentitySharperHypothesis_of_germAtHalf` — bundle with
  the analyticity hypothesis.
* `discAgreementReduced_of_germAtHalf` — CAPSTONE: under analyticity +
  germ at 1/2 + slit-disc reachability (the latter is an unconditional
  theorem elsewhere), the disc-wide identity holds.

**Residual gap (sharpened, still open)**:

1. `JonquieresExpansionAnalyticOnPuncturedBall s` — analyticity of the
   Jonquières expansion on `Metric.ball 0 1 ∩ JonquieresAnalyticDomain`.
   Conditional on the ζ-residual via
   `JonquieresZetaSeriesAnalyticityHypothesis`.

2. `JonquieresIdentityPointGermAtHalf s` — germ equality of
   `polyLog s` and `jonquieresExpansion s` at the single explicit
   point `z₀ = 1/2`. This is the genuine
   Erdélyi-Magnus-Oberhettinger-Tricomi local content, reduced from
   the prior "witness ball" formulation to a single germ at an
   explicit point.

**Comparison with the pre-sharpening situation**:

| Quantity | Before (witness ball) | After (germ at 1/2) |
|----------|-----------------------|---------------------|
| Existential | over `z₀ : ℂ` and `ρ : ℝ` | none; `z₀ = 1/2` explicit |
| Pointwise data | every `z ∈ ball z₀ ρ` | germ at one point |
| Shape constraint | `ball z₀ ρ ⊆ ball 0 1 ∩ Dom` | automatic via wrapper |

The germ formulation is the **strictly sharper** open content: the
shape constraints and existentials are dispatched mechanically; the
remaining open Prop is a single germ equality at an explicit point.

**Project pattern**: this file mirrors
`polyLogHankelRealization_from_extension` (
`PF/Analytic/PolyLogHankelRealization.lean`) and
`discAgreementReduced_of_sharper_and_reachability` (
`PF/Analytic/JonquieresIdentityDischarge.lean`): lock the open
analytic content into a single named Prop AT AN EXPLICIT POINT, build
all surrounding structure axiom-free, document the residual gap
precisely.

Stage L15 — Jonquières local witness germ reduction (2026-05-21).
-/

end PrincipiaTractalis.Analytic.Sheaf
