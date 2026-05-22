/-
# Jonquières Frequent-Agreement at `s = -2` — Closed-Form Reduction (Rational)

This file SHARPENS `JonquieresFrequentAgreementAtHalf (-2)` (the
disc-agreement residual specialized to `s = -2`) by leveraging the
EXACT closed form `polyLog (-2) z = z(1 + z) / (1 - z)^3` on the
open unit disc.

## Why `s = -2` is special

At `s = -2`, the polylog series becomes

```
polyLog (-2) z = Σ' n, z^(n+1) / ((n+1):ℂ)^(-2)
              = Σ' n, (n+1)^2 · z^(n+1)
              = z(1 + z) / (1 - z)^3    on ‖z‖ < 1.
```

Derivation: use `(n+1)^2 = (n+2)(n+1) - (n+1)`, then mathlib's
`hasSum_choose_mul_geometric_of_norm_lt_one` at `k = 1, 2` gives
`Σ' n, (n+1) · z^n = 1/(1-z)^2` and
`Σ' n, (n+1)(n+2)/2 · z^n = 1/(1-z)^3`, so
`Σ' n, (n+1)(n+2) · z^n = 2/(1-z)^3` and
`Σ' n, (n+1)^2 · z^n = 2/(1-z)^3 - 1/(1-z)^2`. Multiplying by `z`:
`z · (2/(1-z)^3 - 1/(1-z)^2) = (2z - z(1-z))/(1-z)^3
   = (z + z^2)/(1-z)^3 = z(1+z)/(1-z)^3`.

This is **unconditional** (no named hypotheses).

## What this file delivers (axiom-free, no `sorry`)

1. **`polyLog_neg_two_eq_rational`** — the unconditional closed form:
   `polyLog (-2) z = z(1 + z) / (1 - z)^3` for `‖z‖ < 1`.

2. **`JonquieresExpansionEqualsRationalAtNegTwo`** — the sharper
   named open Prop at `s = -2`.

3. **`jonquieresFrequentAgreementAtHalf_neg_two_of_rational`** —
   the REDUCTION theorem.

4. **`rational_at_half_eq_six`** — `(1/2)(3/2)/(1/2)^3 = 6`.

Stage L20 — Frequent agreement at s = -2 via the rational closed form.
-/

import PF.Analytic.GermAtHalfDischarge

namespace PrincipiaTractalis.Analytic.Sheaf

open Complex Filter Topology Set
open PrincipiaTractalis.Analytic

/-! ## The closed form: `Li_{-2}(z) = z(1+z) / (1-z)^3` on the open unit disc -/

/-- **`Li_{-2}(z) = z(1+z)/(1-z)^3` for `‖z‖ < 1`.** -/
theorem polyLog_neg_two_eq_rational (z : ℂ) (hz : ‖z‖ < 1) :
    polyLog (-2) z = z * (1 + z) / (1 - z)^3 := by
  unfold polyLog
  -- Each term: z^(n+1) / ((n+1):ℂ)^(-2) = ((n+1):ℂ)^2 * z^(n+1)
  have hne : ∀ n : ℕ, ((n + 1 : ℕ) : ℂ) ≠ 0 := by
    intro n
    have h_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    have h_ne_real : ((n + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt h_pos
    exact_mod_cast h_ne_real
  have h_term : ∀ n : ℕ,
      z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) ^ (-2 : ℂ) =
        ((n + 1 : ℕ) : ℂ) ^ 2 * z ^ (n + 1) := by
    intro n
    have h_neg_two : (-2 : ℂ) = -(2 : ℕ) := by push_cast; ring
    rw [h_neg_two, cpow_neg, cpow_natCast]
    have hne_pow : ((n + 1 : ℕ) : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ (hne n)
    field_simp
  simp_rw [h_term]
  -- Goal: Σ' n, ((n+1):ℂ)^2 * z^(n+1) = z(1+z) / (1-z)^3
  -- Strategy:
  --   (n+1)^2 = (n+2)(n+1) - (n+1)
  -- So Σ ((n+1))^2 z^(n+1) = z · [Σ (n+1)(n+2) z^n  -  Σ (n+1) z^n].
  -- Mathlib: hasSum_choose_mul_geometric_of_norm_lt_one (k=1, k=2) gives
  --   Σ (n+1).choose 1 z^n = 1/(1-z)^2
  --   Σ (n+2).choose 2 z^n = 1/(1-z)^3
  -- Recall (n+1).choose 1 = n+1 and (n+2).choose 2 = (n+2)(n+1)/2.
  -- Step A: HasSum Σ (n+1) z^n = 1/(1-z)^2
  have h1 : HasSum (fun n : ℕ => ((n + 1 : ℕ).choose 1 : ℂ) * z ^ n)
      (1 / (1 - z) ^ (1 + 1)) :=
    hasSum_choose_mul_geometric_of_norm_lt_one 1 hz
  have h1_eq : (fun n : ℕ => ((n + 1 : ℕ).choose 1 : ℂ) * z ^ n) =
      (fun n : ℕ => ((n + 1 : ℕ) : ℂ) * z ^ n) := by
    funext n
    have h : ((n + 1 : ℕ).choose 1 : ℂ) = ((n + 1 : ℕ) : ℂ) := by
      have h_nat : (n + 1).choose 1 = n + 1 := Nat.choose_one_right _
      exact_mod_cast h_nat
    rw [h]
  rw [h1_eq] at h1
  have h1' : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℂ) * z ^ n)
      (1 / (1 - z) ^ 2) := by
    have : (1 : ℕ) + 1 = 2 := rfl
    rw [this] at h1
    exact h1
  -- Step B: HasSum Σ (n+2).choose 2 z^n = 1/(1-z)^3
  have h2 : HasSum (fun n : ℕ => ((n + 2 : ℕ).choose 2 : ℂ) * z ^ n)
      (1 / (1 - z) ^ (2 + 1)) :=
    hasSum_choose_mul_geometric_of_norm_lt_one 2 hz
  have h2' : HasSum (fun n : ℕ => ((n + 2 : ℕ).choose 2 : ℂ) * z ^ n)
      (1 / (1 - z) ^ 3) := by
    have : (2 : ℕ) + 1 = 3 := rfl
    rw [this] at h2
    exact h2
  -- Express (n+1)(n+2) in terms of (n+2).choose 2:
  --   (n+2).descFactorial 2 = (n+1)(n+2) AND
  --   (n+2).descFactorial 2 = 2! · (n+2).choose 2 = 2 · (n+2).choose 2
  -- So (n+1)(n+2) = 2 · (n+2).choose 2.
  have h_choose_two : ∀ n : ℕ,
      ((n + 1 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ) = 2 * ((n + 2 : ℕ).choose 2 : ℂ) := by
    intro n
    have hdesc1 : (n + 2).descFactorial 2 = (n + 1) * (n + 2) := by
      -- descFactorial (n+2) 2 = ((n+2) - 1) · descFactorial (n+2) 1
      --                       = (n + 1) · ((n+2) · descFactorial (n+2) 0)
      --                       = (n + 1) · ((n + 2) · 1)
      rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_zero]
      -- Goal: ((n+2) - 1) * ((n+2) - 0) * 1 = (n + 1) * (n + 2)
      -- Use omega to handle Nat subtractions.
      have h1 : n + 2 - 1 = n + 1 := by omega
      have h2 : n + 2 - 0 = n + 2 := by omega
      rw [h1, h2]
      ring
    have hdesc2 : (n + 2).descFactorial 2 = 2 * (n + 2).choose 2 := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      rfl
    have hcast : (n + 1) * (n + 2) = 2 * (n + 2).choose 2 := by
      rw [← hdesc1, hdesc2]
    exact_mod_cast hcast
  -- HasSum Σ (n+1)(n+2) z^n = 2/(1-z)^3, via (h2'.mul_left 2)
  have h_prod : HasSum (fun n : ℕ =>
      ((n + 1 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ) * z ^ n)
      (2 / (1 - z) ^ 3) := by
    have h_funext : (fun n : ℕ => (2 : ℂ) * (((n + 2 : ℕ).choose 2 : ℂ) * z ^ n))
        = (fun n : ℕ => ((n + 1 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ) * z ^ n) := by
      funext n
      rw [h_choose_two]
      ring
    have h_two_mul : HasSum (fun n : ℕ => (2 : ℂ) * (((n + 2 : ℕ).choose 2 : ℂ) * z ^ n))
        (2 * (1 / (1 - z) ^ 3)) := h2'.mul_left 2
    rw [h_funext] at h_two_mul
    have h_simp : (2 : ℂ) * (1 / (1 - z) ^ 3) = 2 / (1 - z) ^ 3 := by ring
    rw [h_simp] at h_two_mul
    exact h_two_mul
  -- Now form the difference: Σ ((n+1)(n+2) - (n+1)) z^n = (n+1)² · z^n
  -- HasSum.sub gives: HasSum (fun n => (...)(n+2)·z^n - (n+1)·z^n) (2/(1-z)^3 - 1/(1-z)^2)
  have h_diff : HasSum (fun n : ℕ =>
      ((n + 1 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ) * z ^ n -
        ((n + 1 : ℕ) : ℂ) * z ^ n)
      (2 / (1 - z) ^ 3 - 1 / (1 - z) ^ 2) :=
    h_prod.sub h1'
  -- Each summand equals ((n+1):ℂ)^2 · z^n
  have h_diff_eq : ∀ n : ℕ,
      ((n + 1 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ) * z ^ n -
        ((n + 1 : ℕ) : ℂ) * z ^ n
        = ((n + 1 : ℕ) : ℂ) ^ 2 * z ^ n := by
    intro n
    have h_alg : ((n + 1 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ) -
                  ((n + 1 : ℕ) : ℂ) = ((n + 1 : ℕ) : ℂ) ^ 2 := by
      have hcast : ((n + 2 : ℕ) : ℂ) = ((n + 1 : ℕ) : ℂ) + 1 := by push_cast; ring
      rw [hcast]; ring
    calc ((n + 1 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ) * z ^ n -
        ((n + 1 : ℕ) : ℂ) * z ^ n
        = (((n + 1 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ) - ((n + 1 : ℕ) : ℂ)) * z ^ n := by ring
      _ = ((n + 1 : ℕ) : ℂ) ^ 2 * z ^ n := by rw [h_alg]
  have h_sq : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℂ) ^ 2 * z ^ n)
      (2 / (1 - z) ^ 3 - 1 / (1 - z) ^ 2) := by
    have h_funext : (fun n : ℕ =>
        ((n + 1 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ) * z ^ n -
          ((n + 1 : ℕ) : ℂ) * z ^ n)
        = (fun n : ℕ => ((n + 1 : ℕ) : ℂ) ^ 2 * z ^ n) := by
      funext n
      exact h_diff_eq n
    rw [h_funext] at h_diff
    exact h_diff
  -- Multiply by z on the left
  have h_zmul : HasSum (fun n : ℕ => z * (((n + 1 : ℕ) : ℂ) ^ 2 * z ^ n))
      (z * (2 / (1 - z) ^ 3 - 1 / (1 - z) ^ 2)) :=
    h_sq.mul_left z
  -- Rewrite z · ((n+1)² · z^n) = ((n+1):ℂ)^2 · z^(n+1)
  have h_zmul_eq : ∀ n : ℕ,
      z * (((n + 1 : ℕ) : ℂ) ^ 2 * z ^ n) =
        ((n + 1 : ℕ) : ℂ) ^ 2 * z ^ (n + 1) := by
    intro n
    rw [pow_succ]; ring
  have h_zmul' : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℂ) ^ 2 * z ^ (n + 1))
      (z * (2 / (1 - z) ^ 3 - 1 / (1 - z) ^ 2)) := by
    have h_funext : (fun n : ℕ => z * (((n + 1 : ℕ) : ℂ) ^ 2 * z ^ n))
        = (fun n : ℕ => ((n + 1 : ℕ) : ℂ) ^ 2 * z ^ (n + 1)) := by
      funext n
      exact h_zmul_eq n
    rw [h_funext] at h_zmul
    exact h_zmul
  -- Simplify the target value: z · (2/(1-z)^3 - 1/(1-z)^2) = z(1+z)/(1-z)^3
  have hne_one_sub : (1 - z) ≠ 0 := by
    intro h
    have : z = 1 := by linear_combination -h
    rw [this] at hz
    simp at hz
  have h_simp_target : z * (2 / (1 - z) ^ 3 - 1 / (1 - z) ^ 2) =
      z * (1 + z) / (1 - z) ^ 3 := by
    field_simp
    ring
  rw [h_simp_target] at h_zmul'
  exact h_zmul'.tsum_eq

/-! ## The sharper named Prop at `s = -2` -/

/-- **Frequent agreement of the rational closed form `z(1+z)/(1-z)^3` with
    the Jonquières expansion at `s = -2`, near `1/2`**. -/
def JonquieresExpansionEqualsRationalAtNegTwo : Prop :=
  ∃ᶠ z in 𝓝[≠] (1/2 : ℂ),
    z * (1 + z) / (1 - z)^3 = jonquieresExpansion (-2) z

/-! ## The reduction theorem -/

/-- **Reduction**: from the sharper Prop (no polylog mention), derive
    `JonquieresFrequentAgreementAtHalf (-2)`. -/
theorem jonquieresFrequentAgreementAtHalf_neg_two_of_rational
    (h : JonquieresExpansionEqualsRationalAtNegTwo) :
    JonquieresFrequentAgreementAtHalf (-2) := by
  unfold JonquieresExpansionEqualsRationalAtNegTwo at h
  unfold JonquieresFrequentAgreementAtHalf
  have h_unit_nhd : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (1/2 : ℂ) :=
    (Metric.isOpen_ball).mem_nhds half_mem_ball_one
  have h_unit_nhdNE : Metric.ball (0 : ℂ) 1 ∈ 𝓝[≠] (1/2 : ℂ) :=
    nhdsWithin_le_nhds h_unit_nhd
  have h_eventually_rat :
      ∀ᶠ z in 𝓝[≠] (1/2 : ℂ), polyLog (-2) z = z * (1 + z) / (1 - z)^3 := by
    filter_upwards [h_unit_nhdNE] with z hz
    have h_norm : ‖z‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    exact polyLog_neg_two_eq_rational z h_norm
  exact h.mp (h_eventually_rat.mono (fun z hz_eq h_rat => by
    rw [hz_eq, ← h_rat]))

/-! ## Sequential constructor -/

/-- **Sequential constructor for the sharper Prop**. -/
theorem jonquieresExpansionEqualsRationalAtNegTwo_of_sequence
    (z : ℕ → ℂ)
    (h_ne : ∀ n, z n ≠ (1/2 : ℂ))
    (h_tend : Tendsto z atTop (𝓝 (1/2 : ℂ)))
    (h_eq : ∀ n, z n * (1 + z n) / (1 - z n)^3 = jonquieresExpansion (-2) (z n)) :
    JonquieresExpansionEqualsRationalAtNegTwo := by
  unfold JonquieresExpansionEqualsRationalAtNegTwo
  have h_tendNE : Tendsto z atTop (𝓝[≠] (1/2 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨h_tend, ?_⟩
    exact Filter.Eventually.of_forall h_ne
  exact h_tendNE.frequently (Filter.Eventually.frequently
    (Filter.Eventually.of_forall h_eq))

/-- **Sequential constructor for `JonquieresFrequentAgreementAtHalf (-2)`
    via the rational form**. -/
theorem jonquieresFrequentAgreementAtHalf_neg_two_of_sequence_rational
    (z : ℕ → ℂ)
    (h_ne : ∀ n, z n ≠ (1/2 : ℂ))
    (h_tend : Tendsto z atTop (𝓝 (1/2 : ℂ)))
    (h_eq : ∀ n, z n * (1 + z n) / (1 - z n)^3 = jonquieresExpansion (-2) (z n)) :
    JonquieresFrequentAgreementAtHalf (-2) :=
  jonquieresFrequentAgreementAtHalf_neg_two_of_rational
    (jonquieresExpansionEqualsRationalAtNegTwo_of_sequence
      z h_ne h_tend h_eq)

/-! ## Explicit form at the single point `z = 1/2` -/

/-- **Rational closed form at `z = 1/2`**:
    `(1/2)(1 + 1/2) / (1 - 1/2)^3 = 6`. -/
theorem rational_at_half_eq_six :
    (1/2 : ℂ) * (1 + 1/2) / (1 - 1/2)^3 = 6 := by
  norm_num

/-- **Reduction at the single point**: if the Jonquières expansion at
    `(s, z) = (-2, 1/2)` numerically equals `6`, the literal pointwise
    identity holds there. -/
theorem polyLog_neg_two_eq_jonquieresExpansion_at_half_of_value
    (h : jonquieresExpansion (-2) (1/2 : ℂ) = 6) :
    polyLog (-2) (1/2 : ℂ) = jonquieresExpansion (-2) (1/2 : ℂ) := by
  rw [h]
  rw [polyLog_neg_two_eq_rational (1/2 : ℂ) (by
    have : (1/2 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := half_mem_ball_one
    simpa [Metric.mem_ball, dist_zero_right] using this)]
  exact rational_at_half_eq_six

/-! ## Architecture summary

**This file establishes (axiom-free, no `sorry`)**:

* `polyLog_neg_two_eq_rational` — unconditional closed form
  `polyLog (-2) z = z(1+z) / (1-z)^3` for `‖z‖ < 1`.
* `JonquieresExpansionEqualsRationalAtNegTwo` — sharper open Prop.
* `jonquieresFrequentAgreementAtHalf_neg_two_of_rational` — REDUCTION.
* `jonquieresExpansionEqualsRationalAtNegTwo_of_sequence` —
  sequential constructor.
* `jonquieresFrequentAgreementAtHalf_neg_two_of_sequence_rational` —
  composition.
* `rational_at_half_eq_six` — `(1/2)(3/2)/(1/2)^3 = 6`.

Stage L20 — Frequent agreement at s = -2 via the rational closed form.
-/

end PrincipiaTractalis.Analytic.Sheaf
