/-
# polyLog Analyticity at z = 1/2 for Negative Integer s — s = -1, -2

This file EXTENDS `polyLog_analyticAt_half` (from `GermAtHalfDischarge.lean`,
currently restricted to `0 ≤ Re s`) to the NEGATIVE INTEGER values
`s = -1` and `s = -2`, by leveraging the unconditional rational closed
forms

```
polyLog (-1) z = z / (1 - z)^2          (proven, JonquieresAtNegOneDischarge)
polyLog (-2) z = z * (1 + z) / (1 - z)^3 (proven, JonquieresAtNegTwoDischarge)
```

on the open unit disc `‖z‖ < 1`.

## Strategy

`AnalyticAt.congr` transfers analyticity across an `EventuallyEq` of
functions in `nhds z₀`. For each negative integer `s = -N`:

1. The unit ball `Metric.ball 0 1` is open and contains `1/2`, so it
   sits in `nhds (1/2)`.
2. On the ball, the closed form `polyLog (-N) z = R_N(z)` holds
   pointwise (where `R_N` is the rational closed form). This gives
   `polyLog (-N) =ᶠ[nhds (1/2)] R_N`.
3. `R_N` is analytic at `1/2` via mathlib's `AnalyticAt.div`,
   `AnalyticAt.pow`, `analyticAt_id`, `analyticAt_const`, since the
   denominator `(1 - 1/2)^k = (1/2)^k ≠ 0`.
4. By `AnalyticAt.congr`, `polyLog (-N)` inherits analyticity at `1/2`.

## What this file delivers (axiom-free, no `sorry`)

1. **`polyLog_analyticAt_half_neg_one`** —
   `AnalyticAt ℂ (polyLog (-1)) (1/2 : ℂ)`.

2. **`polyLog_analyticAt_half_neg_two`** —
   `AnalyticAt ℂ (polyLog (-2)) (1/2 : ℂ)`.

3. **`jonquieresIdentityPointGermAtHalf_neg_one_of_frequentAgreement`**
   — sibling of `jonquieresIdentityPointGermAtHalf_of_frequentAgreement`
   for `s = -1`, BYPASSING the `0 ≤ Re s` hypothesis by using the
   negative-integer analyticity from this file.

4. **`jonquieresIdentityPointGermAtHalf_neg_two_of_frequentAgreement`**
   — analogous for `s = -2`.

## Architecture

```
polyLog_neg_one_eq_geom_sq (JonquieresAtNegOneDischarge.lean)
       ↓ (EventuallyEq on nhds(1/2) via ball ∈ nhds)
polyLog (-1) =ᶠ[nhds (1/2)] (fun z => z / (1 - z)^2)
       ↓ AnalyticAt.congr from rational AnalyticAt
polyLog_analyticAt_half_neg_one : AnalyticAt ℂ (polyLog (-1)) (1/2)
       ↓ AnalyticAt.frequently_eq_iff_eventually_eq
       ↓ + JonquieresExpansionAnalyticOnPuncturedBall(-1) analyticity hyp
jonquieresIdentityPointGermAtHalf_neg_one_of_frequentAgreement
```

Stage L21 — Negative-integer polylog analyticity at z = 1/2.
-/

import PF.Analytic.JonquieresAtNegOneDischarge
import PF.Analytic.JonquieresAtNegTwoDischarge

namespace PrincipiaTractalis.Analytic.Sheaf

open Complex Filter Topology Set
open PrincipiaTractalis.Analytic

/-! ## Analyticity of the rational closed forms at `z = 1/2` -/

/-- The rational function `fun z => z / (1 - z)^2` is analytic at `1/2`.
    The denominator `(1 - 1/2)^2 = 1/4 ≠ 0`, so `AnalyticAt.div` applies. -/
theorem rational_neg_one_analyticAt_half :
    AnalyticAt ℂ (fun z : ℂ => z / (1 - z)^2) (1/2 : ℂ) := by
  -- Numerator: z ↦ z is analytic at 1/2
  have h_num : AnalyticAt ℂ (fun z : ℂ => z) (1/2 : ℂ) := analyticAt_id
  -- Denominator: z ↦ (1 - z)^2 is analytic at 1/2
  have h_one_sub : AnalyticAt ℂ (fun z : ℂ => (1 : ℂ) - z) (1/2 : ℂ) :=
    analyticAt_const.sub analyticAt_id
  have h_den : AnalyticAt ℂ (fun z : ℂ => (1 - z)^2) (1/2 : ℂ) :=
    h_one_sub.pow 2
  -- Denominator non-zero at 1/2: (1 - 1/2)^2 = (1/2)^2 = 1/4 ≠ 0
  have h_den_ne : (fun z : ℂ => (1 - z)^2) (1/2 : ℂ) ≠ 0 := by
    simp only
    norm_num
  exact h_num.fun_div h_den h_den_ne

/-- The rational function `fun z => z * (1 + z) / (1 - z)^3` is analytic
    at `1/2`. -/
theorem rational_neg_two_analyticAt_half :
    AnalyticAt ℂ (fun z : ℂ => z * (1 + z) / (1 - z)^3) (1/2 : ℂ) := by
  -- Numerator: z * (1 + z)
  have h_z : AnalyticAt ℂ (fun z : ℂ => z) (1/2 : ℂ) := analyticAt_id
  have h_one_add : AnalyticAt ℂ (fun z : ℂ => (1 : ℂ) + z) (1/2 : ℂ) :=
    analyticAt_const.add analyticAt_id
  have h_num : AnalyticAt ℂ (fun z : ℂ => z * (1 + z)) (1/2 : ℂ) :=
    h_z.mul h_one_add
  -- Denominator: (1 - z)^3
  have h_one_sub : AnalyticAt ℂ (fun z : ℂ => (1 : ℂ) - z) (1/2 : ℂ) :=
    analyticAt_const.sub analyticAt_id
  have h_den : AnalyticAt ℂ (fun z : ℂ => (1 - z)^3) (1/2 : ℂ) :=
    h_one_sub.pow 3
  -- Denominator non-zero at 1/2: (1 - 1/2)^3 = (1/2)^3 = 1/8 ≠ 0
  have h_den_ne : (fun z : ℂ => (1 - z)^3) (1/2 : ℂ) ≠ 0 := by
    simp only
    norm_num
  exact h_num.fun_div h_den h_den_ne

/-! ## Polylog at the negative integers `s = -1, -2` is analytic at `1/2` -/

/-- **`polyLog (-1)` is analytic at `1/2 : ℂ`**.

    Proof: on the open unit ball (which is a neighborhood of `1/2`),
    `polyLog (-1) z = z / (1 - z)^2` (theorem `polyLog_neg_one_eq_geom_sq`),
    and the rational function on the right is analytic at `1/2` (theorem
    `rational_neg_one_analyticAt_half`). Apply `AnalyticAt.congr`. -/
theorem polyLog_analyticAt_half_neg_one :
    AnalyticAt ℂ (polyLog (-1)) (1/2 : ℂ) := by
  -- EventuallyEq: polyLog (-1) =ᶠ[nhds (1/2)] (fun z => z / (1 - z)^2)
  have h_unit_nhd : Metric.ball (0 : ℂ) 1 ∈ nhds (1/2 : ℂ) :=
    Metric.isOpen_ball.mem_nhds half_mem_ball_one
  have h_eventually : (fun z : ℂ => z / (1 - z)^2) =ᶠ[nhds (1/2 : ℂ)] polyLog (-1) := by
    filter_upwards [h_unit_nhd] with z hz
    have h_norm : ‖z‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    exact (polyLog_neg_one_eq_geom_sq z h_norm).symm
  -- Transfer analyticity via congr.
  exact rational_neg_one_analyticAt_half.congr h_eventually

/-- **`polyLog (-2)` is analytic at `1/2 : ℂ`**.

    Proof: on the open unit ball, `polyLog (-2) z = z * (1 + z) / (1 - z)^3`
    (theorem `polyLog_neg_two_eq_rational`); the rational function is
    analytic at `1/2` (theorem `rational_neg_two_analyticAt_half`).
    Apply `AnalyticAt.congr`. -/
theorem polyLog_analyticAt_half_neg_two :
    AnalyticAt ℂ (polyLog (-2)) (1/2 : ℂ) := by
  have h_unit_nhd : Metric.ball (0 : ℂ) 1 ∈ nhds (1/2 : ℂ) :=
    Metric.isOpen_ball.mem_nhds half_mem_ball_one
  have h_eventually :
      (fun z : ℂ => z * (1 + z) / (1 - z)^3) =ᶠ[nhds (1/2 : ℂ)] polyLog (-2) := by
    filter_upwards [h_unit_nhd] with z hz
    have h_norm : ‖z‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    exact (polyLog_neg_two_eq_rational z h_norm).symm
  exact rational_neg_two_analyticAt_half.congr h_eventually

/-! ## Germ-equality reductions for `s = -1, -2` (bypassing `0 ≤ Re s`)

These are the negative-integer analogs of
`jonquieresIdentityPointGermAtHalf_of_frequentAgreement` from
`GermAtHalfDischarge.lean`. The original requires `0 ≤ Re s` because
it invokes `polyLog_analyticAt_half`; here we instead invoke the
negative-integer analyticity proven above.
-/

/-- **Reduction at `s = -1`**: frequent agreement near `1/2` +
    analyticity of the expansion ⇒ germ equality at `1/2`. Bypasses
    `0 ≤ Re s` by using `polyLog_analyticAt_half_neg_one`. -/
theorem jonquieresIdentityPointGermAtHalf_neg_one_of_frequentAgreement
    (h_an : JonquieresExpansionAnalyticOnPuncturedBall (-1))
    (h_freq : JonquieresFrequentAgreementAtHalf (-1)) :
    JonquieresIdentityPointGermAtHalf (-1) := by
  unfold JonquieresIdentityPointGermAtHalf JonquieresIdentityPointGerm
  exact (AnalyticAt.frequently_eq_iff_eventually_eq
    polyLog_analyticAt_half_neg_one
    (jonquieresExpansion_analyticAt_half h_an)).mp h_freq

/-- **Reduction at `s = -2`**: frequent agreement near `1/2` +
    analyticity of the expansion ⇒ germ equality at `1/2`. Bypasses
    `0 ≤ Re s` by using `polyLog_analyticAt_half_neg_two`. -/
theorem jonquieresIdentityPointGermAtHalf_neg_two_of_frequentAgreement
    (h_an : JonquieresExpansionAnalyticOnPuncturedBall (-2))
    (h_freq : JonquieresFrequentAgreementAtHalf (-2)) :
    JonquieresIdentityPointGermAtHalf (-2) := by
  unfold JonquieresIdentityPointGermAtHalf JonquieresIdentityPointGerm
  exact (AnalyticAt.frequently_eq_iff_eventually_eq
    polyLog_analyticAt_half_neg_two
    (jonquieresExpansion_analyticAt_half h_an)).mp h_freq

/-! ## Composed wrappers: rational frequent-agreement ⇒ germ at 1/2

Compose the rational-side frequent agreement Props from
`JonquieresAtNegOneDischarge.lean` and `JonquieresAtNegTwoDischarge.lean`
through the new germ-equality reductions.
-/

/-- **`s = -1` composed**: rational frequent agreement + analyticity ⇒
    germ equality at `1/2`. -/
theorem jonquieresIdentityPointGermAtHalf_neg_one_of_rational
    (h_an : JonquieresExpansionAnalyticOnPuncturedBall (-1))
    (h_rat : JonquieresExpansionEqualsRationalAtNegOne) :
    JonquieresIdentityPointGermAtHalf (-1) :=
  jonquieresIdentityPointGermAtHalf_neg_one_of_frequentAgreement h_an
    (jonquieresFrequentAgreementAtHalf_neg_one_of_rational h_rat)

/-- **`s = -2` composed**: rational frequent agreement + analyticity ⇒
    germ equality at `1/2`. -/
theorem jonquieresIdentityPointGermAtHalf_neg_two_of_rational
    (h_an : JonquieresExpansionAnalyticOnPuncturedBall (-2))
    (h_rat : JonquieresExpansionEqualsRationalAtNegTwo) :
    JonquieresIdentityPointGermAtHalf (-2) :=
  jonquieresIdentityPointGermAtHalf_neg_two_of_frequentAgreement h_an
    (jonquieresFrequentAgreementAtHalf_neg_two_of_rational h_rat)

/-! ## Architecture summary

**This file establishes (axiom-free, no `sorry`)**:

* `rational_neg_one_analyticAt_half` — `fun z => z / (1 - z)^2` is
  analytic at `1/2 : ℂ`.
* `rational_neg_two_analyticAt_half` — `fun z => z * (1 + z) / (1 - z)^3`
  is analytic at `1/2 : ℂ`.
* `polyLog_analyticAt_half_neg_one` — **MAIN**: `polyLog (-1)` is
  analytic at `1/2 : ℂ`.
* `polyLog_analyticAt_half_neg_two` — **MAIN**: `polyLog (-2)` is
  analytic at `1/2 : ℂ`.
* `jonquieresIdentityPointGermAtHalf_neg_one_of_frequentAgreement` —
  germ-equality reduction at `s = -1` bypassing `0 ≤ Re s`.
* `jonquieresIdentityPointGermAtHalf_neg_two_of_frequentAgreement` —
  germ-equality reduction at `s = -2` bypassing `0 ≤ Re s`.
* `jonquieresIdentityPointGermAtHalf_neg_one_of_rational` — composed
  from `JonquieresExpansionEqualsRationalAtNegOne`.
* `jonquieresIdentityPointGermAtHalf_neg_two_of_rational` — composed
  from `JonquieresExpansionEqualsRationalAtNegTwo`.

**Note on disc-agreement at `s = -1, -2`**:

The downstream theorem `discAgreementReduced_of_germAtHalf` (and its
ancestors `discAgreementReduced_of_sharper_and_reachability`,
`polyLog_eq_jonquieresExpansion_on_preconnected`) currently require
`0 ≤ Re s` because they invoke `polyLog_analyticOnNhd_ball` for the
propagation step. Extending those to `s = -1, -2` requires an
ON-DISC analyticity version of `polyLog_analyticOnNhd_ball` at these
specific negative-integer values (mechanically: lift the
`polyLog_neg_one_eq_geom_sq` / `polyLog_neg_two_eq_rational`
closed-form rewrite to `AnalyticOnNhd ℂ (polyLog (-N)) (Metric.ball 0 1)`
via uniform congr on the open ball). That is a separate, larger
refactor; this file delivers the pointwise analyticity at `z = 1/2`
plus the germ-equality reductions, which are the immediate
prerequisites the user requested.

Stage L21 — Negative-integer polylog analyticity at z = 1/2.
-/

end PrincipiaTractalis.Analytic.Sheaf
