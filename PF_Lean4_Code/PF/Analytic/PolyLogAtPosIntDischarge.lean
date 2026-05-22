/-
# Disc-Agreement Capstones at Positive Integer `s ∈ {2, 3, 4}`

This file extends the disc-agreement reduction chain to **positive
integer exponents** `s = 2, 3, 4`. It mirrors the structure of
`PolyLogAnalyticOnBallNegInt.lean` (which provides the s ∈ {-1,-2,
-3,-4} capstones) and `JonquieresAtZeroFinalDischarge.lean` (which
provides the s = 0 capstone).

## Why positive integers are structurally simpler

For positive integer `s = N` (with `N ≥ 0`), the on-disc analyticity
of `polyLog s` is **automatic**: the project's existing
`polyLog_analyticOnNhd_ball` (in `PolyLogHankelRealization.lean`)
applies directly to any `s : ℂ` with `0 ≤ s.re`, which holds for
`((N : ℕ) : ℂ).re = (N : ℝ) ≥ 0`.

In contrast, the negative-integer chain in
`PolyLogAnalyticOnBallNegInt.lean` had to prove on-ball analyticity
individually for each `s ∈ {-1,-2,-3,-4}` via the explicit rational
closed forms (since `polyLog_analyticOnNhd_ball` requires `0 ≤ Re s`).

## Why no z = 1/2 closed form is provided

For `s ∈ {2, 3, 4}`, there is **no elementary closed form** for
`polyLog s z` on the open unit disc:

* `s = 2` (dilogarithm): `Li_2(z) = ∑ z^n/n²`. The only known closed
  forms at specific points are isolated identities (e.g., Landen's
  `Li_2(1/2) = π²/12 − (log 2)²/2`), and mathlib has neither a
  dilogarithm definition nor Landen's identity.
* `s = 3, 4` (trilog, tetralog): no known elementary closed forms in
  general; only isolated values (`Li_2(1) = π²/6`, `Li_4(1) = π⁴/90`)
  on the boundary.

So unlike the s = -1, -2, -3, -4 chain, there is **no closed-form
function** that "eliminates the polylog side" of the Jonquières
identity at points near `z = 1/2`. The disc-agreement capstones at
`s ∈ {2, 3, 4}` therefore take the same shape as the s = 0 capstone
in `JonquieresAtZeroFinalDischarge.lean`: a 3-hypothesis reduction
to the named open germ-equality + analyticity + reachability.

## Boundary-value contribution at `s = 2`: `Li_2(1) = π²/6` (Basel)

We DO supply one substantive numerical identity:
`polyLog 2 (1 : ℂ) = (π : ℂ)² / 6` (Basel problem / Euler's
identity). This is proved via mathlib's `hasSum_zeta_two` (real-valued
`Σ 1/n² = π²/6`), reindexed across the `n ↦ n+1` shift in the
project's `polyLog` definition. This does NOT advance the disc-
agreement chain (z=1 is on the boundary, not the interior `z = 1/2`
that the Jonquières chain pivots through), but it is the SINGLE
exact polyLog value at positive integer `s` accessible to mathlib's
current zeta machinery.

## What this file delivers (axiom-free, no `sorry`)

1. **`polyLog_two_at_one_eq_pi_sq_div_six`** — `polyLog 2 (1 : ℂ) =
   (π : ℂ)² / 6` via `hasSum_zeta_two`.

2. **`polyLog_analyticOnNhd_ball_pos_int`** — convenience wrapper:
   `polyLog (N : ℂ)` is analytic on `ball 0 1` for any `N : ℕ`.

3. **`discAgreementReduced_at_two_of_germ`** — full disc-wide
   identity at `s = 2` from
   `JonquieresExpansionAnalyticOnPuncturedBall 2`
   + `JonquieresIdentityPointGermAtHalf 2`
   + `SlitDiscPreconnectedReachability`.

4. **`discAgreementReduced_at_three_of_germ`** — same at `s = 3`.

5. **`discAgreementReduced_at_four_of_germ`** — same at `s = 4`.

## Architecture

```
hasSum_zeta_two   (mathlib)              GermAtHalfDischarge.lean
        ↓                                     ↓
polyLog_two_at_one_eq_pi_sq_div_six    discAgreementReduced_of_germAtHalf
                                              ↓
                              discAgreementReduced_at_{two,three,four}_of_germ
                                              (THIS FILE)
```

Stage L23 — Disc-agreement capstones at positive integer `s ∈ {2,3,4}`
+ Basel boundary value at `s = 2`.
-/

import PF.Analytic.GermAtHalfDischarge
import Mathlib.NumberTheory.ZetaValues

namespace PrincipiaTractalis.Analytic.Sheaf

open Complex Filter Topology Set
open PrincipiaTractalis.Analytic

/-! ## Basel: `polyLog 2 (1 : ℂ) = (π : ℂ)² / 6`

Reindex mathlib's `hasSum_zeta_two : HasSum (fun n => 1/(n:ℝ)²) (π²/6)`
across the `(n+1)` shift built into `polyLog`. -/

/-- **`Li_2(1) = π²/6`** (Basel problem). The single closed-form
    polyLog value at positive integer `s` that mathlib currently
    supports through `hasSum_zeta_two`. -/
theorem polyLog_two_at_one_eq_pi_sq_div_six :
    polyLog 2 (1 : ℂ) = (Real.pi : ℂ) ^ 2 / 6 := by
  unfold polyLog
  -- Each term: 1^(n+1) / ((n+1):ℂ)^(2:ℂ) = 1 / ((n+1):ℂ)^2.
  -- Real form: ∑' n:ℕ, 1/((n+1):ℝ)^2 = π²/6 (reindex of hasSum_zeta_two).
  -- Step 1: rewrite each summand to 1 / ((n+1):ℂ)^2 (natural power, not cpow).
  have h_term : ∀ n : ℕ,
      (1 : ℂ) ^ (n + 1) / ((n + 1 : ℕ) : ℂ) ^ (2 : ℂ) =
        1 / ((n + 1 : ℕ) : ℂ) ^ 2 := by
    intro n
    rw [one_pow]
    -- ((n+1):ℂ)^(2:ℂ) = ((n+1):ℂ)^(2:ℕ) for natural base.
    have h_n_ne : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero n
    have h_cpow_nat : ((n + 1 : ℕ) : ℂ) ^ (2 : ℂ) = ((n + 1 : ℕ) : ℂ) ^ (2 : ℕ) := by
      rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) from by norm_cast]
      exact Complex.cpow_natCast _ 2
    rw [h_cpow_nat]
  simp_rw [h_term]
  -- Step 2: hasSum_zeta_two reindexed via n ↦ n+1.
  -- hasSum_zeta_two : HasSum (fun n : ℕ => 1 / (n : ℝ)^2) (π²/6).
  -- Note: at n = 0, 1/(0:ℝ)^2 = 1/0 = 0 in mathlib (no exception).
  -- Reindexed: HasSum (fun n : ℕ => 1 / ((n+1 : ℕ) : ℝ)^2) (π²/6).
  have h_real_shift :
      HasSum (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2) (Real.pi ^ 2 / 6) := by
    -- Use the n ↦ n+1 shift on hasSum_zeta_two.
    -- hasSum_nat_add_iff: HasSum (fun n => f (n+k)) g ↔ HasSum f (g + ∑ i<k, f i).
    -- For k = 1, ∑ i<1, f i = f 0. With f n = 1/(n:ℝ)^2, f 0 = 1/0^2 = 0
    -- (real division by zero convention in mathlib).
    have h_orig := hasSum_zeta_two
    have h_zero_term : ∑ i ∈ Finset.range 1, (1 : ℝ) / (i : ℝ) ^ 2 = 0 := by
      simp
    -- The iff direction we want is mp: given HasSum (fun n => f(n+1)) g, ...
    -- Actually we want mpr inverse: HasSum f (g + ∑) → HasSum (fun n => f(n+1)) g.
    -- That is exactly `(hasSum_nat_add_iff 1).mpr` applied to h_orig
    -- after rewriting π²/6 as π²/6 + 0.
    have h_orig' : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2)
        ((Real.pi ^ 2 / 6) + ∑ i ∈ Finset.range 1, (1 : ℝ) / (i : ℝ) ^ 2) := by
      rw [h_zero_term, add_zero]; exact h_orig
    have h_shift := (hasSum_nat_add_iff (k := 1)
      (f := fun n : ℕ => 1 / (n : ℝ) ^ 2)).mpr h_orig'
    -- h_shift : HasSum (fun n => 1 / ((n+1):ℕ:ℝ)^2) (π²/6)
    convert h_shift using 1
  -- Step 3: lift the real `HasSum` to complex via `ofReal`.
  have h_complex_shift :
      HasSum (fun n : ℕ => ((1 / ((n + 1 : ℕ) : ℝ) ^ 2 : ℝ) : ℂ))
        (((Real.pi ^ 2 / 6 : ℝ) : ℂ)) :=
    h_real_shift.map (Complex.ofRealAm.toLinearMap.toAddMonoidHom)
      (Complex.continuous_ofReal)
  -- Step 4: align the complex sum with our tsum form.
  have h_cast_term : ∀ n : ℕ,
      ((1 / ((n + 1 : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) = 1 / ((n + 1 : ℕ) : ℂ) ^ 2 := by
    intro n
    push_cast
    rfl
  have h_cast_sum : (((Real.pi ^ 2 / 6 : ℝ) : ℂ)) = (Real.pi : ℂ) ^ 2 / 6 := by
    push_cast
    rfl
  rw [← h_cast_sum]
  rw [show (fun n : ℕ => (1 : ℂ) / ((n + 1 : ℕ) : ℂ) ^ 2) =
        (fun n : ℕ => ((1 / ((n + 1 : ℕ) : ℝ) ^ 2 : ℝ) : ℂ)) from by
    funext n; rw [h_cast_term n]]
  exact h_complex_shift.tsum_eq

/-! ## Convenience analyticity wrapper at positive integer s -/

/-- **`polyLog (N : ℂ)` is analytic on the open unit ball** for any
    `N : ℕ`. Specialization of `polyLog_analyticOnNhd_ball` to
    natural-number `s`; the side condition `0 ≤ ((N : ℕ) : ℂ).re`
    holds since `((N : ℕ) : ℂ).re = (N : ℝ) ≥ 0`. -/
theorem polyLog_analyticOnNhd_ball_pos_int (N : ℕ) :
    AnalyticOnNhd ℂ (polyLog ((N : ℕ) : ℂ)) (Metric.ball (0 : ℂ) 1) := by
  apply polyLog_analyticOnNhd_ball
  show (0 : ℝ) ≤ ((N : ℕ) : ℂ).re
  rw [show (((N : ℕ) : ℂ)).re = (N : ℝ) from by norm_cast]
  exact Nat.cast_nonneg N

/-! ## Disc-agreement capstones at positive integer `s ∈ {2, 3, 4}`

Each capstone reduces to the same 3-hypothesis open content as the
s = 0 capstone in `JonquieresAtZeroFinalDischarge.lean`:
* `JonquieresExpansionAnalyticOnPuncturedBall s`,
* `JonquieresIdentityPointGermAtHalf s`,
* `SlitDiscPreconnectedReachability`. -/

/-- **CAPSTONE at `s = 2`**: full disc-wide identity from analyticity
    of the Jonquières expansion on the slit disc + the germ at `1/2`
    + slit-disc reachability. The polylog on-disc analyticity is
    automatic at `s = 2` since `((2 : ℂ)).re = 2 ≥ 0`. -/
theorem discAgreementReduced_at_two_of_germ
    (h_an : JonquieresExpansionAnalyticOnPuncturedBall 2)
    (h_germ : JonquieresIdentityPointGermAtHalf 2)
    (h_reach : SlitDiscPreconnectedReachability) :
    ∀ z ∈ JonquieresAnalyticDomain ∩ Metric.ball (0 : ℂ) 1,
      jonquieresExpansion 2 z = polyLog 2 z :=
  discAgreementReduced_of_germAtHalf
    (s := 2) (by norm_num : (0 : ℝ) ≤ ((2 : ℂ)).re)
    h_an h_germ h_reach

/-- **CAPSTONE at `s = 3`**. -/
theorem discAgreementReduced_at_three_of_germ
    (h_an : JonquieresExpansionAnalyticOnPuncturedBall 3)
    (h_germ : JonquieresIdentityPointGermAtHalf 3)
    (h_reach : SlitDiscPreconnectedReachability) :
    ∀ z ∈ JonquieresAnalyticDomain ∩ Metric.ball (0 : ℂ) 1,
      jonquieresExpansion 3 z = polyLog 3 z :=
  discAgreementReduced_of_germAtHalf
    (s := 3) (by norm_num : (0 : ℝ) ≤ ((3 : ℂ)).re)
    h_an h_germ h_reach

/-- **CAPSTONE at `s = 4`**. -/
theorem discAgreementReduced_at_four_of_germ
    (h_an : JonquieresExpansionAnalyticOnPuncturedBall 4)
    (h_germ : JonquieresIdentityPointGermAtHalf 4)
    (h_reach : SlitDiscPreconnectedReachability) :
    ∀ z ∈ JonquieresAnalyticDomain ∩ Metric.ball (0 : ℂ) 1,
      jonquieresExpansion 4 z = polyLog 4 z :=
  discAgreementReduced_of_germAtHalf
    (s := 4) (by norm_num : (0 : ℝ) ≤ ((4 : ℂ)).re)
    h_an h_germ h_reach

/-! ## Architecture summary

**This file establishes (axiom-free, no `sorry`)**:

* `polyLog_two_at_one_eq_pi_sq_div_six` — Basel: `polyLog 2 (1 : ℂ) =
  (π : ℂ)² / 6`. Sole closed-form polyLog value at positive integer
  `s` accessible via mathlib's `hasSum_zeta_two`.
* `polyLog_analyticOnNhd_ball_pos_int` — convenience wrapper of
  `polyLog_analyticOnNhd_ball` at natural-number `s`.
* `discAgreementReduced_at_two_of_germ` — full disc-agreement at `s = 2`.
* `discAgreementReduced_at_three_of_germ` — full disc-agreement at `s = 3`.
* `discAgreementReduced_at_four_of_germ` — full disc-agreement at `s = 4`.

**Open content at each `s ∈ {2, 3, 4}` (after this file)**:

Per `s`, exactly TWO named hypotheses:
* `JonquieresExpansionAnalyticOnPuncturedBall s` (analyticity of the
  expansion on the slit disc).
* `JonquieresIdentityPointGermAtHalf s` (germ equality at `1/2`).

This brings the positive-integer chain into the same shape as the
s = 0 chain capstone `discAgreementReduced_at_zero_of_germ` and the
s = -1, -2, -3, -4 chain capstones in
`PolyLogAnalyticOnBallNegInt.lean`.

**Contrast with negative-integer chain**:
At negative integers `s = -N`, the project's
`JonquieresAtNegN/Discharge.lean` files SHARPEN the germ hypothesis
into a "rational closed form ↔ Jonquières expansion" frequent-
agreement Prop (eliminating the polylog side via the rational
identity). At positive integers `s ∈ {2,3,4}`, no analogous closed
form exists (no elementary form for the dilog/trilog/tetralog on the
disc), so the germ hypothesis remains in its irreducible
polylog-vs-expansion form. The disc-wide identity is therefore
strictly conditional on the classical Jonquières germ identity at
`(s, 1/2)` for each such `s`.

Stage L23 — Disc-agreement capstones at positive integer `s ∈ {2,3,4}`
+ Basel boundary value at `s = 2`.
-/

end PrincipiaTractalis.Analytic.Sheaf
