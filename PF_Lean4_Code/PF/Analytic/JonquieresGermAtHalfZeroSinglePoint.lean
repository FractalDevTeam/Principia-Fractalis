/-
# Jonquières Germ at `(s, z) = (0, 1/2)` — Sharpest Polylog-Free Reduction

This file extends `JonquieresAtZeroFinalDischarge.lean` by REMOVING
the named analyticity hypothesis `JonquieresExpansionAnalyticOnPuncturedBall 0`
from the germ-side reduction at `s = 0`, using the now-unconditional
analyticity of `jonquieresExpansion 0` at `1/2` from
`JonquieresExpansionAnalyticOnPuncturedBallDischarge.lean`.

## Strategic position

At `s = 0` both sides of the classical Jonquières identity have
**explicit, mechanizable analyticity at `1/2`**:

* **polylog side**: `polyLog 0 z = z / (1 - z)` on `Metric.ball 0 1`
  (theorem `polyLog_zero_exponent`). Since `1/2 ∈ ball 0 1`, the
  rational function `z/(1-z)` is the polylog's germ at `1/2`, and the
  polylog is analytic at `1/2` directly via `polyLog_analyticAt_half`
  (already requires only `0 ≤ Re s`, which holds at `s = 0`).

* **expansion side**: `jonquieresExpansion 0` is analytic on the
  achievable subdomain `ball 0 1 ∩ JonquieresAnalyticDomain ∩
  {‖log z‖ < 2π}` (unconditional theorem
  `jonquieresExpansionAnalyticOnAchievableSubdomain_zero`).
  Since `1/2` lies in the achievable subdomain
  (`half_mem_achievableSubdomain`: `‖log (1/2)‖ = log 2 < 2π`), we
  derive **unconditional** analyticity of `jonquieresExpansion 0` at
  `1/2`.

This means the germ-side reduction at `s = 0` can be made
unconditional in the analyticity hypothesis. The only remaining
classical content is the value-side germ identity itself.

## What this file delivers (axiom-free, no `sorry`)

1. **`jonquieresExpansion_analyticAt_half_zero_unconditional`** —
   UNCONDITIONAL `AnalyticAt ℂ (jonquieresExpansion 0) (1/2 : ℂ)`.
   No named analyticity hypothesis required at the point `1/2`.

2. **`polyLog_zero_eventuallyEq_geom_at_half`** —
   `polyLog 0 =ᶠ[nhds (1/2 : ℂ)] (fun z => z / (1 - z))`. Direct
   from `polyLog_zero_exponent` on the unit-ball neighborhood.

3. **`JonquieresExpansionEqualsGeomGermAtHalf : Prop`** — the
   polylog-free germ-side residual at `(s, z) = (0, 1/2)`:
   ```
   jonquieresExpansion 0 =ᶠ[nhds (1/2 : ℂ)] (fun z => z / (1 - z))
   ```
   Strictly weaker than `JonquieresIdentityPointGermAtHalf 0`: the
   polylog has been eliminated using its unconditional closed form.

4. **`jonquieresIdentityPointGermAtHalf_zero_of_geom_germ`** —
   UNCONDITIONAL reduction: the polylog-free germ Prop (3) ⟹
   `JonquieresIdentityPointGermAtHalf 0`. No analyticity hypothesis
   used in this reduction — the polylog's closed form provides the
   germ identity polyLog 0 = z/(1-z) for free, and the new Prop
   provides z/(1-z) = jonquieresExpansion 0; transitivity gives the
   target.

5. **`jonquieresExpansionEqualsGeomGermAtHalf_of_frequent`** —
   IDENTITY-THEOREM reduction: from the polylog-free FREQUENT
   agreement Prop `JonquieresExpansionEqualsGeomFrequentlyAtHalf`,
   plus the unconditional analyticity at `1/2`, derive the
   polylog-free germ Prop. Uses mathlib's local identity theorem
   `AnalyticAt.frequently_eq_iff_eventually_eq` applied to the
   rational function `z/(1-z)` (analytic at `1/2`) and
   `jonquieresExpansion 0` (analytic at `1/2`, unconditionally).

6. **`jonquieresIdentityPointGermAtHalf_zero_of_geom_frequent`** —
   composed: polylog-free frequent agreement ⟹ germ identity at
   `(0, 1/2)`. The CHEAPEST closure path identified to date for the
   `s = 0` chain.

7. **`jonquieres0_at_half_value_identity` and
   `polyLog_eq_jonquieresExpansion_at_half_iff_value`** — explicit
   characterization of the SINGLE-POINT identity at `z = 1/2`:
   `polyLog 0 (1/2) = jonquieresExpansion 0 (1/2)` IFF
   `jonquieresExpansion 0 (1/2) = 1`. Honest note: single-point
   equality is strictly weaker than germ equality (germ equality
   requires Taylor coefficient matching to all orders), so this
   lemma alone does NOT discharge the germ Prop.

## Honest framing on irreducibility

The germ identity `polyLog 0 =ᶠ[nhds(1/2)] jonquieresExpansion 0`
(equivalently, after polylog elimination,
`jonquieresExpansion 0 =ᶠ[nhds(1/2)] z/(1-z)`) is the irreducible
classical Jonquières / Lerch content at the explicit base point. It
asserts that the Mellin–Barnes series
```
jonquieresExpansion 0 z
  = -1/log z + Σ_{k≥0} ζ(-k) (log z)^k / k!
  = -1/log z + (-1/2) + (-1/12)(log z) + 0 + (1/120)(log z)^3/6 + ...
```
sums to the rational closed form `z/(1-z)` on a neighborhood of
`1/2`. The single-point value `jonquieresExpansion 0 (1/2) = 1` is
the simplest scalar identity in this family, but it does NOT imply
the germ identity (which requires equality of all Taylor coefficients
at `1/2`).

The PATHS to fully discharge the germ identity reduce to either:

* **Hankel-contour evaluation at `s = 0`**: the polylog Hankel contour
  collapses to the geometric sum at this special value (residue
  calculus on the punctured disc).

* **Term-by-term Bernoulli matching**: equate the Taylor coefficients
  of the ζ-series at `z = 1/2` with the Taylor coefficients of
  `z/(1-z)` at `z = 1/2`, exploiting `ζ(-2k) = 0`,
  `ζ(-(2k-1)) = -B_{2k}/(2k)`.

Both are classical analytic number theory; neither introduces project
axioms. This file isolates the open content cleanly and provides the
machinery so that future closure of either path becomes a drop-in
discharge.

Stage L22 — Sharpest polylog-free germ reduction at `(s, z) = (0, 1/2)`.
-/

import PF.Analytic.JonquieresAtZeroFinalDischarge
import PF.Analytic.JonquieresExpansionAnalyticOnPuncturedBallDischarge
import PF.Analytic.PolyLogAnalyticAtHalfNegInt

namespace PrincipiaTractalis.Analytic.Sheaf

open Complex Filter Topology Set
open PrincipiaTractalis.Analytic

/-! ## Step 1: unconditional analyticity of `jonquieresExpansion 0` at `1/2` -/

/-- **UNCONDITIONAL `AnalyticAt ℂ (jonquieresExpansion 0) (1/2 : ℂ)`**.

    Direct application of
    `jonquieresExpansionAnalyticOnAchievableSubdomain_zero` to the
    explicit witness `half_mem_achievableSubdomain`. -/
theorem jonquieresExpansion_analyticAt_half_zero_unconditional :
    AnalyticAt ℂ (jonquieresExpansion 0) (1/2 : ℂ) :=
  jonquieresExpansionAnalyticOnAchievableSubdomain_zero
    (1/2 : ℂ) half_mem_achievableSubdomain

/-! ## Step 2: polylog at `s = 0` is eventually `z/(1-z)` near `1/2` -/

/-- **`polyLog 0 =ᶠ[nhds (1/2 : ℂ)] (fun z => z / (1 - z))`**.

    On the open unit ball (a neighborhood of `1/2`), the polylog at
    `s = 0` equals the rational function `z/(1-z)` pointwise
    (theorem `polyLog_zero_exponent`). Hence the equality is eventual
    in the nhds filter at `1/2`. -/
theorem polyLog_zero_eventuallyEq_geom_at_half :
    (polyLog 0) =ᶠ[nhds (1/2 : ℂ)] (fun z : ℂ => z / (1 - z)) := by
  have h_unit_nhd : Metric.ball (0 : ℂ) 1 ∈ nhds (1/2 : ℂ) :=
    Metric.isOpen_ball.mem_nhds half_mem_ball_one
  filter_upwards [h_unit_nhd] with z hz
  have h_norm : ‖z‖ < 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  exact polyLog_zero_exponent z h_norm

/-! ## Step 3: the polylog-free germ-side residual Prop -/

/-- **Polylog-free germ-side residual at `(s, z) = (0, 1/2)`**.

    The Jonquières expansion at `s = 0` agrees with the rational
    function `z/(1-z)` on a neighborhood of `1/2`. This is STRICTLY
    WEAKER than `JonquieresIdentityPointGermAtHalf 0`: the polylog
    has been ELIMINATED using its unconditional closed form
    `polyLog 0 z = z/(1-z)` on `Metric.ball 0 1`. The remaining
    content is purely about the Jonquières expansion side. -/
def JonquieresExpansionEqualsGeomGermAtHalf : Prop :=
  (jonquieresExpansion 0) =ᶠ[nhds (1/2 : ℂ)] (fun z : ℂ => z / (1 - z))

/-! ## Step 4: UNCONDITIONAL reduction (germ ⟹ germ) -/

/-- **UNCONDITIONAL reduction**: the polylog-free germ Prop
    `JonquieresExpansionEqualsGeomGermAtHalf` implies the classical
    germ identity `JonquieresIdentityPointGermAtHalf 0`.

    NO analyticity hypothesis required. The polylog's closed form
    provides one direction of the chain
    `polyLog 0 ≡ z/(1-z) ≡ jonquieresExpansion 0` (the first link is
    unconditional via `polyLog_zero_eventuallyEq_geom_at_half`); the
    polylog-free germ Prop provides the other (the second link).
    Transitivity of `EventuallyEq` concludes. -/
theorem jonquieresIdentityPointGermAtHalf_zero_of_geom_germ
    (h : JonquieresExpansionEqualsGeomGermAtHalf) :
    JonquieresIdentityPointGermAtHalf 0 := by
  unfold JonquieresIdentityPointGermAtHalf JonquieresIdentityPointGerm
  -- polyLog 0 =ᶠ z/(1-z) (unconditional) AND z/(1-z) =ᶠ jonquieresExpansion 0
  -- (the input). Transitivity gives polyLog 0 =ᶠ jonquieresExpansion 0.
  unfold JonquieresExpansionEqualsGeomGermAtHalf at h
  exact polyLog_zero_eventuallyEq_geom_at_half.trans h.symm

/-! ## Step 5: IDENTITY-THEOREM reduction (frequent ⟹ germ) -/

/-- **Rational function `fun z => z / (1 - z)` is analytic at `1/2`**.

    The denominator `(1 - 1/2) = 1/2 ≠ 0`, so `AnalyticAt.div`
    applies. -/
theorem rational_geom_analyticAt_half :
    AnalyticAt ℂ (fun z : ℂ => z / (1 - z)) (1/2 : ℂ) := by
  have h_num : AnalyticAt ℂ (fun z : ℂ => z) (1/2 : ℂ) := analyticAt_id
  have h_den : AnalyticAt ℂ (fun z : ℂ => (1 : ℂ) - z) (1/2 : ℂ) :=
    analyticAt_const.sub analyticAt_id
  have h_den_ne : (fun z : ℂ => (1 : ℂ) - z) (1/2 : ℂ) ≠ 0 := by
    simp only
    norm_num
  exact h_num.fun_div h_den h_den_ne

/-- **IDENTITY-THEOREM reduction**: from the polylog-free frequent
    agreement Prop `JonquieresExpansionEqualsGeomFrequentlyAtHalf`,
    derive the polylog-free germ Prop
    `JonquieresExpansionEqualsGeomGermAtHalf`.

    Both `fun z => z/(1-z)` and `jonquieresExpansion 0` are analytic
    at `1/2`, so by mathlib's local identity theorem
    `AnalyticAt.frequently_eq_iff_eventually_eq`, frequent agreement
    in `𝓝[≠] (1/2)` is equivalent to germ equality in `nhds (1/2)`. -/
theorem jonquieresExpansionEqualsGeomGermAtHalf_of_frequent
    (h_freq : JonquieresExpansionEqualsGeomFrequentlyAtHalf) :
    JonquieresExpansionEqualsGeomGermAtHalf := by
  unfold JonquieresExpansionEqualsGeomGermAtHalf
  unfold JonquieresExpansionEqualsGeomFrequentlyAtHalf at h_freq
  -- h_freq: ∃ᶠ z in 𝓝[≠] (1/2 : ℂ), z / (1 - z) = jonquieresExpansion 0 z
  -- Goal: jonquieresExpansion 0 =ᶠ[nhds (1/2)] (fun z => z/(1-z))
  -- Use frequently_eq_iff_eventually_eq, after symmetrizing.
  have h_freq_sym : ∃ᶠ z in 𝓝[≠] (1/2 : ℂ),
      jonquieresExpansion 0 z = z / (1 - z) := by
    exact h_freq.mp (Filter.Eventually.of_forall (fun _ heq => heq.symm))
  exact (AnalyticAt.frequently_eq_iff_eventually_eq
    jonquieresExpansion_analyticAt_half_zero_unconditional
    rational_geom_analyticAt_half).mp h_freq_sym

/-! ## Step 6: composed reduction (frequent ⟹ classical germ) -/

/-- **CHEAPEST CLOSURE PATH at `s = 0`**: from the polylog-free
    frequent agreement Prop `JonquieresExpansionEqualsGeomFrequentlyAtHalf`,
    derive the classical germ identity
    `JonquieresIdentityPointGermAtHalf 0` UNCONDITIONALLY (no named
    analyticity hypothesis required).

    Composes
    `jonquieresExpansionEqualsGeomGermAtHalf_of_frequent` with
    `jonquieresIdentityPointGermAtHalf_zero_of_geom_germ`. -/
theorem jonquieresIdentityPointGermAtHalf_zero_of_geom_frequent
    (h_freq : JonquieresExpansionEqualsGeomFrequentlyAtHalf) :
    JonquieresIdentityPointGermAtHalf 0 :=
  jonquieresIdentityPointGermAtHalf_zero_of_geom_germ
    (jonquieresExpansionEqualsGeomGermAtHalf_of_frequent h_freq)

/-! ## Step 7: explicit single-point value characterization

The literal scalar identity at `z = 1/2` reads
`polyLog 0 (1/2) = jonquieresExpansion 0 (1/2)`, which (via
`polyLog_zero_exponent` at `z = 1/2`) is EQUIVALENT to
`jonquieresExpansion 0 (1/2) = 1`. This is the simplest residual in
the family but is STRICTLY WEAKER than the germ identity (which
requires equality of all Taylor coefficients at `1/2`). The lemma
below makes that equivalence explicit. -/

/-- **Single-point value characterization at `z = 1/2`**:
    `polyLog 0 (1/2) = jonquieresExpansion 0 (1/2)` IFF
    `jonquieresExpansion 0 (1/2) = 1`. -/
theorem polyLog_zero_eq_jonquieresExpansion_at_half_iff_value :
    polyLog 0 (1/2 : ℂ) = jonquieresExpansion 0 (1/2 : ℂ) ↔
      jonquieresExpansion 0 (1/2 : ℂ) = 1 := by
  have h_half_in_ball : ‖(1/2 : ℂ)‖ < 1 := by
    have : (1/2 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := half_mem_ball_one
    simpa [Metric.mem_ball, dist_zero_right] using this
  have h_polylog_half : polyLog 0 (1/2 : ℂ) = 1 := by
    rw [polyLog_zero_exponent (1/2 : ℂ) h_half_in_ball]
    norm_num
  constructor
  · intro h
    rw [← h, h_polylog_half]
  · intro h
    rw [h_polylog_half, h]

/-- **The literal scalar identity**: `polyLog 0 (1/2) = 1`. This is
    the numerical anchor of the germ identity at `(s, z) = (0, 1/2)`,
    coming UNCONDITIONALLY from `polyLog_zero_exponent`. -/
theorem polyLog_zero_at_half_eq_one : polyLog 0 (1/2 : ℂ) = 1 := by
  have h_half_in_ball : ‖(1/2 : ℂ)‖ < 1 := by
    have : (1/2 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := half_mem_ball_one
    simpa [Metric.mem_ball, dist_zero_right] using this
  rw [polyLog_zero_exponent (1/2 : ℂ) h_half_in_ball]
  norm_num

/-! ## Architecture summary

**This file establishes (axiom-free, no `sorry`)**:

* `jonquieresExpansion_analyticAt_half_zero_unconditional` — at
  `s = 0`, the Jonquières expansion is UNCONDITIONALLY analytic at
  `1/2 : ℂ`. No named hypothesis required.

* `polyLog_zero_eventuallyEq_geom_at_half` — `polyLog 0 =ᶠ[nhds(1/2)]
  (fun z => z/(1-z))` (unconditional germ identity polylog ≡
  rational at `1/2`).

* `JonquieresExpansionEqualsGeomGermAtHalf` — the polylog-free
  germ-side residual at `(s, z) = (0, 1/2)`:
  `jonquieresExpansion 0 =ᶠ[nhds(1/2)] (fun z => z/(1-z))`.

* `rational_geom_analyticAt_half` — `fun z => z/(1-z)` is analytic
  at `1/2`.

* `jonquieresIdentityPointGermAtHalf_zero_of_geom_germ` —
  UNCONDITIONAL reduction: polylog-free germ Prop ⟹
  `JonquieresIdentityPointGermAtHalf 0`. NO analyticity hypothesis.

* `jonquieresExpansionEqualsGeomGermAtHalf_of_frequent` — IDENTITY-
  THEOREM reduction: polylog-free FREQUENT agreement ⟹ polylog-free
  GERM agreement. Uses unconditional analyticity at `1/2`.

* `jonquieresIdentityPointGermAtHalf_zero_of_geom_frequent` —
  COMPOSED: polylog-free frequent agreement ⟹ classical germ identity
  at `(0, 1/2)`. UNCONDITIONAL.

* `polyLog_zero_eq_jonquieresExpansion_at_half_iff_value` and
  `polyLog_zero_at_half_eq_one` — single-point value
  characterization. The literal scalar identity is
  `jonquieresExpansion 0 (1/2) = 1`. Honest note: this is
  STRICTLY WEAKER than the germ identity.

**Sharpest open content at `s = 0` after this file**:

The classical germ residual `JonquieresIdentityPointGermAtHalf 0`
admits multiple sharper polylog-free equivalents:

| Form | Description |
|------|-------------|
| `JonquieresIdentityPointGermAtHalf 0` | original: `polyLog 0 =ᶠ jonquieresExpansion 0` |
| `JonquieresExpansionEqualsGeomGermAtHalf` (this file) | polylog-eliminated: `jonquieresExpansion 0 =ᶠ z/(1-z)` |
| `JonquieresExpansionEqualsGeomFrequentlyAtHalf` (existing) | weakened to frequent: `∃ᶠ z in 𝓝[≠] (1/2), z/(1-z) = jonquieresExpansion 0 z` |
| `jonquieresExpansion 0 (1/2) = 1` (single-point value) | STRICTLY WEAKER — does NOT discharge the germ Prop alone |

The cheapest closure path is now: discharge
`JonquieresExpansionEqualsGeomFrequentlyAtHalf` (find ANY single
sequence `z_n → 1/2`, `z_n ≠ 1/2`, where the Jonquières expansion
matches `z_n/(1-z_n)`), then chain through
`jonquieresIdentityPointGermAtHalf_zero_of_geom_frequent` to obtain
the classical germ identity at `(0, 1/2)`, then through
`discAgreementReduced_at_zero_of_germ` (modulo the analyticity
precondition on the full punctured ball) to obtain disc-wide
agreement at `s = 0`.

**What is genuinely irreducible**:

The classical Mellin-Barnes identity
```
-1/log z + Σ_{k≥0} ζ(-k) (log z)^k / k!  =  z/(1-z)
```
on a neighborhood of `z = 1/2` is genuinely classical analytic
number theory content. No mechanical lemma in mathlib closes this
directly; both Hankel-contour evaluation and term-by-term Bernoulli
matching require substantial new machinery. This file isolates the
content as cleanly as possible and provides the wiring so that
either approach can be slotted in as a one-line drop-in.

**Architectural pattern**: this file mirrors
`PolyLogAnalyticAtHalfNegInt.lean`'s approach at `s = -1, -2` (which
uses the unconditional rational closed forms `polyLog(-N) = R_N(z)`
plus mathlib's `AnalyticAt.congr`), but applies it to the polylog at
`s = 0` using `polyLog_zero_exponent` PLUS the unconditional
analyticity of `jonquieresExpansion 0` at `1/2` from the achievable-
subdomain capstone in
`JonquieresExpansionAnalyticOnPuncturedBallDischarge.lean`.

Stage L22 — Sharpest polylog-free germ reduction at `(s, z) = (0, 1/2)`.
-/

end PrincipiaTractalis.Analytic.Sheaf
