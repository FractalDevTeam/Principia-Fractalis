/-
# Jonquières Frequent-Agreement at `s = -1` — Closed-Form Reduction (Rational)

This file SHARPENS `JonquieresFrequentAgreementAtHalf (-1)` (the
disc-agreement residual specialized to `s = -1`) by leveraging the
EXACT closed form `polyLog (-1) z = z / (1 - z)^2` on the open unit
disc.

## Why `s = -1` is special

At `s = -1`, the polylog series becomes

```
polyLog (-1) z = Σ' n, z^(n+1) / ((n+1):ℂ)^(-1)
              = Σ' n, (n+1) · z^(n+1)
              = z / (1 - z)^2    on ‖z‖ < 1
```

This is **unconditional** (no named hypotheses) — it is purely
mathlib's `tsum_coe_mul_geometric_of_norm_lt_one` (the derivative of
the geometric series).

Therefore, on the open unit disc,
`JonquieresFrequentAgreementAtHalf (-1)` is EQUIVALENT to:

```
∃ᶠ z in 𝓝[≠] (1/2), z / (1 - z)^2 = jonquieresExpansion (-1) z.
```

The polylog side has DISAPPEARED — replaced by a rational function.

## What this file delivers (axiom-free, no `sorry`)

1. **`polyLog_neg_one_eq_geom_sq`** — the unconditional closed form:
   `polyLog (-1) z = z / (1 - z)^2` for `‖z‖ < 1`.

2. **`JonquieresExpansionEqualsRationalAtNegOne`** — the sharper
   named open Prop at `s = -1`.

3. **`jonquieresFrequentAgreementAtHalf_neg_one_of_rational`** —
   the REDUCTION theorem.

4. **`jonquieresFrequentAgreementAtHalf_neg_one_of_sequence_rational`**
   — sequential constructor.

5. **`rational_at_half_eq_two`** — the explicit value at `z = 1/2`:
   `(1/2) / (1 - 1/2)^2 = 2`.

## Architecture

```
JonquieresExpansionEqualsRationalAtNegOne           (THIS FILE)
       ↓ jonquieresFrequentAgreementAtHalf_neg_one_of_rational
JonquieresFrequentAgreementAtHalf (-1)               (GermAtHalfDischarge.lean)
       ↓ jonquieresIdentityPointGermAtHalf_of_frequentAgreement
       ↓ (NOTE: GermAtHalfDischarge requires 0 ≤ Re s; for s = -1
       ↓  this reduction step needs the negative-`s` analyticity
       ↓  branch from ZetaShiftBoundNegNat.lean. This file provides
       ↓  the polylog-side closed form and the polylog⇒rational
       ↓  reduction; the downstream germ-equality discharge would
       ↓  need a sibling of `polyLog_analyticAt_half` for negative s
       ↓  via `PolyLogAnalyticExtension.lean`, which is outside the
       ↓  scope of this file.)
```

Stage L19 — Frequent agreement at s = -1 via the rational closed form.
-/

import PF.Analytic.GermAtHalfDischarge

namespace PrincipiaTractalis.Analytic.Sheaf

open Complex Filter Topology Set
open PrincipiaTractalis.Analytic

/-! ## The closed form: `Li_{-1}(z) = z / (1 - z)^2` on the open unit disc -/

/-- **`Li_{-1}(z) = z / (1 - z)^2` for `‖z‖ < 1`.** Derived from
    mathlib's `hasSum_choose_mul_geometric_of_norm_lt_one` at `k = 1`
    (`∑' n : ℕ, (n+1) · z^n = 1 / (1 - z)^2`), then multiplied by `z`. -/
theorem polyLog_neg_one_eq_geom_sq (z : ℂ) (hz : ‖z‖ < 1) :
    polyLog (-1) z = z / (1 - z)^2 := by
  unfold polyLog
  -- Each term: z^(n+1) / ((n+1):ℂ)^(-1) = z^(n+1) * (n+1)
  have h_term : ∀ n : ℕ,
      z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) ^ (-1 : ℂ) =
        ((n + 1 : ℕ) : ℂ) * z ^ (n + 1) := by
    intro n
    rw [cpow_neg_one]
    -- z^(n+1) / ((n+1):ℂ)⁻¹ = z^(n+1) * (n+1)
    have hne : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
      have h_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
      have h_ne_real : ((n + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt h_pos
      exact_mod_cast h_ne_real
    field_simp
  simp_rw [h_term]
  -- Goal: Σ' n, (n+1) * z^(n+1) = z / (1 - z)^2
  -- Strategy: rewrite (n+1) * z^(n+1) = z * ((n+1) * z^n), pull `z` out, use mathlib.
  -- Mathlib: hasSum_choose_mul_geometric_of_norm_lt_one 1 hz :
  --   HasSum (fun n => (n + 1).choose 1 * z^n) (1 / (1 - z)^(1+1))
  -- And (n + 1).choose 1 = n + 1.
  have h_choose : HasSum (fun n : ℕ => ((n + 1 : ℕ).choose 1 : ℂ) * z ^ n)
      (1 / (1 - z) ^ (1 + 1)) :=
    hasSum_choose_mul_geometric_of_norm_lt_one 1 hz
  have h_choose_eq : ∀ n : ℕ, ((n + 1 : ℕ).choose 1 : ℂ) = ((n + 1 : ℕ) : ℂ) := by
    intro n
    have h : (n + 1).choose 1 = n + 1 := by
      rw [Nat.choose_one_right]
    exact_mod_cast h
  have h_n_plus_one_pow_n : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℂ) * z ^ n)
      (1 / (1 - z) ^ 2) := by
    have h_two : (1 : ℕ) + 1 = 2 := rfl
    rw [h_two] at h_choose
    have h_funext : (fun n : ℕ => ((n + 1 : ℕ).choose 1 : ℂ) * z ^ n) =
        (fun n : ℕ => ((n + 1 : ℕ) : ℂ) * z ^ n) := by
      funext n
      rw [h_choose_eq]
    rw [h_funext] at h_choose
    exact h_choose
  -- Multiply by z on the left:
  -- HasSum (fun n => z * ((n+1) * z^n)) (z * 1/(1-z)^2) = (z/(1-z)^2)
  have h_mul : HasSum (fun n : ℕ => z * (((n + 1 : ℕ) : ℂ) * z ^ n))
      (z * (1 / (1 - z) ^ 2)) :=
    h_n_plus_one_pow_n.mul_left z
  -- Rewrite z * ((n+1) * z^n) = (n+1) * z^(n+1)
  have h_eq_term : ∀ n : ℕ,
      z * (((n + 1 : ℕ) : ℂ) * z ^ n) = ((n + 1 : ℕ) : ℂ) * z ^ (n + 1) := by
    intro n
    rw [pow_succ]
    ring
  have h_final : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℂ) * z ^ (n + 1))
      (z * (1 / (1 - z) ^ 2)) := by
    have h_funext : (fun n : ℕ => z * (((n + 1 : ℕ) : ℂ) * z ^ n)) =
        (fun n : ℕ => ((n + 1 : ℕ) : ℂ) * z ^ (n + 1)) := by
      funext n
      exact h_eq_term n
    rw [h_funext] at h_mul
    exact h_mul
  -- z * (1/(1-z)^2) = z/(1-z)^2
  have h_simp : z * (1 / (1 - z) ^ 2) = z / (1 - z) ^ 2 := by ring
  rw [h_simp] at h_final
  exact h_final.tsum_eq

/-! ## The sharper named Prop at `s = -1` -/

/-- **Frequent agreement of the rational closed form `z/(1-z)^2` with
    the Jonquières expansion at `s = -1`, near `1/2`**.

    The polylog has been replaced (via the unconditional closed form
    `polyLog (-1) z = z / (1 - z)^2` on the open unit disc) by a
    rational function. -/
def JonquieresExpansionEqualsRationalAtNegOne : Prop :=
  ∃ᶠ z in 𝓝[≠] (1/2 : ℂ),
    z / (1 - z)^2 = jonquieresExpansion (-1) z

/-! ## The reduction theorem -/

/-- **Reduction**: from the sharper Prop (no polylog mention), derive
    `JonquieresFrequentAgreementAtHalf (-1)`. -/
theorem jonquieresFrequentAgreementAtHalf_neg_one_of_rational
    (h : JonquieresExpansionEqualsRationalAtNegOne) :
    JonquieresFrequentAgreementAtHalf (-1) := by
  unfold JonquieresExpansionEqualsRationalAtNegOne at h
  unfold JonquieresFrequentAgreementAtHalf
  have h_unit_nhd : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (1/2 : ℂ) :=
    (Metric.isOpen_ball).mem_nhds half_mem_ball_one
  have h_unit_nhdNE : Metric.ball (0 : ℂ) 1 ∈ 𝓝[≠] (1/2 : ℂ) :=
    nhdsWithin_le_nhds h_unit_nhd
  have h_eventually_rat :
      ∀ᶠ z in 𝓝[≠] (1/2 : ℂ), polyLog (-1) z = z / (1 - z)^2 := by
    filter_upwards [h_unit_nhdNE] with z hz
    have h_norm : ‖z‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    exact polyLog_neg_one_eq_geom_sq z h_norm
  exact h.mp (h_eventually_rat.mono (fun z hz_eq h_rat => by
    rw [hz_eq, ← h_rat]))

/-! ## Sequential constructor -/

/-- **Sequential constructor for the sharper Prop**. -/
theorem jonquieresExpansionEqualsRationalAtNegOne_of_sequence
    (z : ℕ → ℂ)
    (h_ne : ∀ n, z n ≠ (1/2 : ℂ))
    (h_tend : Tendsto z atTop (𝓝 (1/2 : ℂ)))
    (h_eq : ∀ n, z n / (1 - z n)^2 = jonquieresExpansion (-1) (z n)) :
    JonquieresExpansionEqualsRationalAtNegOne := by
  unfold JonquieresExpansionEqualsRationalAtNegOne
  have h_tendNE : Tendsto z atTop (𝓝[≠] (1/2 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨h_tend, ?_⟩
    exact Filter.Eventually.of_forall h_ne
  exact h_tendNE.frequently (Filter.Eventually.frequently
    (Filter.Eventually.of_forall h_eq))

/-- **Sequential constructor for `JonquieresFrequentAgreementAtHalf (-1)`
    via the rational form**. -/
theorem jonquieresFrequentAgreementAtHalf_neg_one_of_sequence_rational
    (z : ℕ → ℂ)
    (h_ne : ∀ n, z n ≠ (1/2 : ℂ))
    (h_tend : Tendsto z atTop (𝓝 (1/2 : ℂ)))
    (h_eq : ∀ n, z n / (1 - z n)^2 = jonquieresExpansion (-1) (z n)) :
    JonquieresFrequentAgreementAtHalf (-1) :=
  jonquieresFrequentAgreementAtHalf_neg_one_of_rational
    (jonquieresExpansionEqualsRationalAtNegOne_of_sequence
      z h_ne h_tend h_eq)

/-! ## Explicit form at the single point `z = 1/2` -/

/-- **Rational closed form at `z = 1/2`**: `(1/2) / (1 - 1/2)^2 = 2`. -/
theorem rational_at_half_eq_two : (1/2 : ℂ) / (1 - 1/2)^2 = 2 := by
  norm_num

/-- **Reduction at the single point**: if the Jonquières expansion at
    `(s, z) = (-1, 1/2)` numerically equals `2`, the literal pointwise
    identity holds there. -/
theorem polyLog_neg_one_eq_jonquieresExpansion_at_half_of_value
    (h : jonquieresExpansion (-1) (1/2 : ℂ) = 2) :
    polyLog (-1) (1/2 : ℂ) = jonquieresExpansion (-1) (1/2 : ℂ) := by
  rw [h]
  rw [polyLog_neg_one_eq_geom_sq (1/2 : ℂ) (by
    have : (1/2 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := half_mem_ball_one
    simpa [Metric.mem_ball, dist_zero_right] using this)]
  exact rational_at_half_eq_two

/-! ## Architecture summary

**This file establishes (axiom-free, no `sorry`)**:

* `polyLog_neg_one_eq_geom_sq` — the unconditional closed form
  `polyLog (-1) z = z / (1 - z)^2` for `‖z‖ < 1`. Proved directly via
  mathlib's `hasSum_coe_mul_geometric_of_norm_lt_one`.
* `JonquieresExpansionEqualsRationalAtNegOne` — the sharper open
  Prop at `s = -1`: frequent agreement of `z/(1-z)^2` with the
  Jonquières expansion at `s = -1`, near `1/2`. No polylog mention.
* `jonquieresFrequentAgreementAtHalf_neg_one_of_rational` —
  REDUCTION.
* `jonquieresExpansionEqualsRationalAtNegOne_of_sequence` —
  sequential constructor.
* `jonquieresFrequentAgreementAtHalf_neg_one_of_sequence_rational` —
  composition.
* `rational_at_half_eq_two` — `(1/2) / (1 - 1/2)^2 = 2`.
* `polyLog_neg_one_eq_jonquieresExpansion_at_half_of_value` —
  point-wise reduction at `z = 1/2`.

**Residual gap (sharpest formulation at `s = -1`)**:

`JonquieresExpansionEqualsRationalAtNegOne` — a *purely
expansion-side* frequent-equality Prop: it asks for points
arbitrarily close to (but distinct from) `1/2` where the Jonquières
expansion at `s = -1` equals the rational function `z/(1-z)^2`.

Stage L19 — Frequent agreement at s = -1 via the rational closed form.
-/

end PrincipiaTractalis.Analytic.Sheaf
