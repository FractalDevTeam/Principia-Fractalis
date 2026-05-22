/-
# Jonquières Frequent-Agreement at `s = -3` — Closed-Form Reduction (Rational)

This file SHARPENS `JonquieresFrequentAgreementAtHalf (-3)` (the
disc-agreement residual specialized to `s = -3`) by leveraging the
EXACT closed form `polyLog (-3) z = z(1 + 4z + z^2) / (1 - z)^4` on
the open unit disc (Eulerian polynomial A_3(z) = 1 + 4z + z^2).

## Why `s = -3` is special

At `s = -3`, the polylog series becomes

```
polyLog (-3) z = Σ' n, z^(n+1) / ((n+1):ℂ)^(-3)
              = Σ' n, (n+1)^3 · z^(n+1)
              = z(1 + 4z + z^2) / (1 - z)^4    on ‖z‖ < 1.
```

Derivation via the descending-factorial decomposition
`(n+1)^3 = (n+1)(n+2)(n+3) - 3(n+1)(n+2) + (n+1)`
plus mathlib's `hasSum_choose_mul_geometric_of_norm_lt_one` at
`k = 1, 2, 3`:
- `Σ (n+1) z^n               = 1/(1-z)^2`
- `Σ (n+1)(n+2) z^n          = 2/(1-z)^3`
- `Σ (n+1)(n+2)(n+3) z^n     = 6/(1-z)^4`

So
`Σ (n+1)^3 z^n = 6/(1-z)^4 - 6/(1-z)^3 + 1/(1-z)^2`

and multiplying by `z`, common denominator `(1-z)^4`,
`z · (6 - 6(1-z) + (1-z)^2) / (1-z)^4
   = z · (1 + 4z + z^2) / (1-z)^4`.

This is **unconditional** (no named hypotheses).

## Numerical check at `z = 1/2`

`A_3(1/2) = 1 + 2 + 1/4 = 13/4`. So
`Li_{-3}(1/2) = (1/2)(13/4) / (1/2)^4 = (13/8) · 16 = 26`.

## What this file delivers (axiom-free, no `sorry`)

1. **`polyLog_neg_three_eq_rational`** — the unconditional closed form:
   `polyLog (-3) z = z(1 + 4z + z^2) / (1 - z)^4` for `‖z‖ < 1`.

2. **`JonquieresExpansionEqualsRationalAtNegThree`** — the sharper
   named open Prop at `s = -3`.

3. **`jonquieresFrequentAgreementAtHalf_neg_three_of_rational`** —
   the REDUCTION theorem.

4. **`rational_at_half_eq_twentySix`** — `(1/2)(1 + 2 + 1/4)/(1/2)^4 = 26`.

Stage L21 — Frequent agreement at s = -3 via the Eulerian-polynomial
closed form.
-/

import PF.Analytic.GermAtHalfDischarge

namespace PrincipiaTractalis.Analytic.Sheaf

open Complex Filter Topology Set
open PrincipiaTractalis.Analytic

/-! ## The closed form: `Li_{-3}(z) = z(1 + 4z + z^2) / (1-z)^4` on the open unit disc -/

/-- **`Li_{-3}(z) = z(1 + 4z + z^2)/(1-z)^4` for `‖z‖ < 1`.** -/
theorem polyLog_neg_three_eq_rational (z : ℂ) (hz : ‖z‖ < 1) :
    polyLog (-3) z = z * (1 + 4*z + z^2) / (1 - z)^4 := by
  unfold polyLog
  -- Each term: z^(n+1) / ((n+1):ℂ)^(-3) = ((n+1):ℂ)^3 * z^(n+1)
  have hne : ∀ n : ℕ, ((n + 1 : ℕ) : ℂ) ≠ 0 := by
    intro n
    have h_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    have h_ne_real : ((n + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt h_pos
    exact_mod_cast h_ne_real
  have h_term : ∀ n : ℕ,
      z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) ^ (-3 : ℂ) =
        ((n + 1 : ℕ) : ℂ) ^ 3 * z ^ (n + 1) := by
    intro n
    have h_neg_three : (-3 : ℂ) = -(3 : ℕ) := by push_cast; ring
    rw [h_neg_three, cpow_neg, cpow_natCast]
    have hne_pow : ((n + 1 : ℕ) : ℂ) ^ 3 ≠ 0 := pow_ne_zero _ (hne n)
    field_simp
  simp_rw [h_term]
  -- Goal: Σ' n, ((n+1):ℂ)^3 * z^(n+1) = z(1+4z+z^2) / (1-z)^4
  -- Strategy:
  --   (n+1)^3 = (n+1)(n+2)(n+3) - 3(n+1)(n+2) + (n+1)
  -- Step A: Σ (n+1) z^n = 1/(1-z)^2
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
  -- Step B: Σ (n+2).choose 2 z^n = 1/(1-z)^3, and (n+1)(n+2) = 2 · (n+2).choose 2
  have h2 : HasSum (fun n : ℕ => ((n + 2 : ℕ).choose 2 : ℂ) * z ^ n)
      (1 / (1 - z) ^ (2 + 1)) :=
    hasSum_choose_mul_geometric_of_norm_lt_one 2 hz
  have h2' : HasSum (fun n : ℕ => ((n + 2 : ℕ).choose 2 : ℂ) * z ^ n)
      (1 / (1 - z) ^ 3) := by
    have : (2 : ℕ) + 1 = 3 := rfl
    rw [this] at h2
    exact h2
  have h_choose_two : ∀ n : ℕ,
      ((n + 1 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ) = 2 * ((n + 2 : ℕ).choose 2 : ℂ) := by
    intro n
    have hdesc1 : (n + 2).descFactorial 2 = (n + 1) * (n + 2) := by
      rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_zero]
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
  have h_prod2 : HasSum (fun n : ℕ =>
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
  -- Step C: Σ (n+3).choose 3 z^n = 1/(1-z)^4, and (n+1)(n+2)(n+3) = 6 · (n+3).choose 3
  have h3 : HasSum (fun n : ℕ => ((n + 3 : ℕ).choose 3 : ℂ) * z ^ n)
      (1 / (1 - z) ^ (3 + 1)) :=
    hasSum_choose_mul_geometric_of_norm_lt_one 3 hz
  have h3' : HasSum (fun n : ℕ => ((n + 3 : ℕ).choose 3 : ℂ) * z ^ n)
      (1 / (1 - z) ^ 4) := by
    have : (3 : ℕ) + 1 = 4 := rfl
    rw [this] at h3
    exact h3
  have h_choose_three : ∀ n : ℕ,
      ((n + 1 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ) * ((n + 3 : ℕ) : ℂ) =
        6 * ((n + 3 : ℕ).choose 3 : ℂ) := by
    intro n
    have hdesc1 : (n + 3).descFactorial 3 = (n + 1) * (n + 2) * (n + 3) := by
      rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_succ,
          Nat.descFactorial_zero]
      have h1 : n + 3 - 2 = n + 1 := by omega
      have h2 : n + 3 - 1 = n + 2 := by omega
      have h3 : n + 3 - 0 = n + 3 := by omega
      rw [h1, h2, h3]
      ring
    have hdesc2 : (n + 3).descFactorial 3 = 6 * (n + 3).choose 3 := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      rfl
    have hcast : (n + 1) * (n + 2) * (n + 3) = 6 * (n + 3).choose 3 := by
      rw [← hdesc1, hdesc2]
    exact_mod_cast hcast
  have h_prod3 : HasSum (fun n : ℕ =>
      ((n + 1 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ) * ((n + 3 : ℕ) : ℂ) * z ^ n)
      (6 / (1 - z) ^ 4) := by
    have h_funext : (fun n : ℕ => (6 : ℂ) * (((n + 3 : ℕ).choose 3 : ℂ) * z ^ n))
        = (fun n : ℕ =>
          ((n + 1 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ) * ((n + 3 : ℕ) : ℂ) * z ^ n) := by
      funext n
      rw [h_choose_three]
      ring
    have h_six_mul : HasSum (fun n : ℕ => (6 : ℂ) * (((n + 3 : ℕ).choose 3 : ℂ) * z ^ n))
        (6 * (1 / (1 - z) ^ 4)) := h3'.mul_left 6
    rw [h_funext] at h_six_mul
    have h_simp : (6 : ℂ) * (1 / (1 - z) ^ 4) = 6 / (1 - z) ^ 4 := by ring
    rw [h_simp] at h_six_mul
    exact h_six_mul
  -- Combine: HasSum (P3 - 3·P2 + P1) = 6/(1-z)^4 - 3·(2/(1-z)^3) + 1/(1-z)^2
  -- First: P3 - 3·P2
  have h_three_prod2 : HasSum (fun n : ℕ =>
      (3 : ℂ) * (((n + 1 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ) * z ^ n))
      (3 * (2 / (1 - z) ^ 3)) := h_prod2.mul_left 3
  have h_sub1 : HasSum (fun n : ℕ =>
      ((n + 1 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ) * ((n + 3 : ℕ) : ℂ) * z ^ n -
        (3 : ℂ) * (((n + 1 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ) * z ^ n))
      (6 / (1 - z) ^ 4 - 3 * (2 / (1 - z) ^ 3)) :=
    h_prod3.sub h_three_prod2
  -- Then + P1
  have h_add : HasSum (fun n : ℕ =>
      (((n + 1 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ) * ((n + 3 : ℕ) : ℂ) * z ^ n -
        (3 : ℂ) * (((n + 1 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ) * z ^ n)) +
        ((n + 1 : ℕ) : ℂ) * z ^ n)
      ((6 / (1 - z) ^ 4 - 3 * (2 / (1 - z) ^ 3)) + 1 / (1 - z) ^ 2) :=
    h_sub1.add h1'
  -- Each summand equals ((n+1):ℂ)^3 · z^n
  have h_decomp : ∀ n : ℕ,
      (((n + 1 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ) * ((n + 3 : ℕ) : ℂ) * z ^ n -
        (3 : ℂ) * (((n + 1 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ) * z ^ n)) +
        ((n + 1 : ℕ) : ℂ) * z ^ n
        = ((n + 1 : ℕ) : ℂ) ^ 3 * z ^ n := by
    intro n
    have h_alg :
        ((n + 1 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ) * ((n + 3 : ℕ) : ℂ) -
            3 * (((n + 1 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ)) +
          ((n + 1 : ℕ) : ℂ)
            = ((n + 1 : ℕ) : ℂ) ^ 3 := by
      have hc2 : ((n + 2 : ℕ) : ℂ) = ((n + 1 : ℕ) : ℂ) + 1 := by push_cast; ring
      have hc3 : ((n + 3 : ℕ) : ℂ) = ((n + 1 : ℕ) : ℂ) + 2 := by push_cast; ring
      rw [hc2, hc3]; ring
    calc (((n + 1 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ) * ((n + 3 : ℕ) : ℂ) * z ^ n -
            (3 : ℂ) * (((n + 1 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ) * z ^ n)) +
            ((n + 1 : ℕ) : ℂ) * z ^ n
        = (((n + 1 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ) * ((n + 3 : ℕ) : ℂ) -
            3 * (((n + 1 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ)) +
            ((n + 1 : ℕ) : ℂ)) * z ^ n := by ring
      _ = ((n + 1 : ℕ) : ℂ) ^ 3 * z ^ n := by rw [h_alg]
  have h_cube : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℂ) ^ 3 * z ^ n)
      ((6 / (1 - z) ^ 4 - 3 * (2 / (1 - z) ^ 3)) + 1 / (1 - z) ^ 2) := by
    have h_funext : (fun n : ℕ =>
        (((n + 1 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ) * ((n + 3 : ℕ) : ℂ) * z ^ n -
          (3 : ℂ) * (((n + 1 : ℕ) : ℂ) * ((n + 2 : ℕ) : ℂ) * z ^ n)) +
          ((n + 1 : ℕ) : ℂ) * z ^ n)
        = (fun n : ℕ => ((n + 1 : ℕ) : ℂ) ^ 3 * z ^ n) := by
      funext n
      exact h_decomp n
    rw [h_funext] at h_add
    exact h_add
  -- Multiply by z on the left
  have h_zmul : HasSum (fun n : ℕ => z * (((n + 1 : ℕ) : ℂ) ^ 3 * z ^ n))
      (z * ((6 / (1 - z) ^ 4 - 3 * (2 / (1 - z) ^ 3)) + 1 / (1 - z) ^ 2)) :=
    h_cube.mul_left z
  -- Rewrite z · ((n+1)^3 · z^n) = ((n+1):ℂ)^3 · z^(n+1)
  have h_zmul_eq : ∀ n : ℕ,
      z * (((n + 1 : ℕ) : ℂ) ^ 3 * z ^ n) =
        ((n + 1 : ℕ) : ℂ) ^ 3 * z ^ (n + 1) := by
    intro n
    rw [pow_succ]; ring
  have h_zmul' : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℂ) ^ 3 * z ^ (n + 1))
      (z * ((6 / (1 - z) ^ 4 - 3 * (2 / (1 - z) ^ 3)) + 1 / (1 - z) ^ 2)) := by
    have h_funext : (fun n : ℕ => z * (((n + 1 : ℕ) : ℂ) ^ 3 * z ^ n))
        = (fun n : ℕ => ((n + 1 : ℕ) : ℂ) ^ 3 * z ^ (n + 1)) := by
      funext n
      exact h_zmul_eq n
    rw [h_funext] at h_zmul
    exact h_zmul
  -- Simplify the target value:
  -- z·(6/(1-z)^4 - 6/(1-z)^3 + 1/(1-z)^2) = z(1 + 4z + z²)/(1-z)^4
  have hne_one_sub : (1 - z) ≠ 0 := by
    intro h
    have : z = 1 := by linear_combination -h
    rw [this] at hz
    simp at hz
  have h_simp_target :
      z * ((6 / (1 - z) ^ 4 - 3 * (2 / (1 - z) ^ 3)) + 1 / (1 - z) ^ 2) =
        z * (1 + 4*z + z^2) / (1 - z) ^ 4 := by
    field_simp
    ring
  rw [h_simp_target] at h_zmul'
  exact h_zmul'.tsum_eq

/-! ## The sharper named Prop at `s = -3` -/

/-- **Frequent agreement of the rational closed form `z(1+4z+z²)/(1-z)^4`
    with the Jonquières expansion at `s = -3`, near `1/2`**. -/
def JonquieresExpansionEqualsRationalAtNegThree : Prop :=
  ∃ᶠ z in 𝓝[≠] (1/2 : ℂ),
    z * (1 + 4*z + z^2) / (1 - z)^4 = jonquieresExpansion (-3) z

/-! ## The reduction theorem -/

/-- **Reduction**: from the sharper Prop (no polylog mention), derive
    `JonquieresFrequentAgreementAtHalf (-3)`. -/
theorem jonquieresFrequentAgreementAtHalf_neg_three_of_rational
    (h : JonquieresExpansionEqualsRationalAtNegThree) :
    JonquieresFrequentAgreementAtHalf (-3) := by
  unfold JonquieresExpansionEqualsRationalAtNegThree at h
  unfold JonquieresFrequentAgreementAtHalf
  have h_unit_nhd : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (1/2 : ℂ) :=
    (Metric.isOpen_ball).mem_nhds half_mem_ball_one
  have h_unit_nhdNE : Metric.ball (0 : ℂ) 1 ∈ 𝓝[≠] (1/2 : ℂ) :=
    nhdsWithin_le_nhds h_unit_nhd
  have h_eventually_rat :
      ∀ᶠ z in 𝓝[≠] (1/2 : ℂ),
        polyLog (-3) z = z * (1 + 4*z + z^2) / (1 - z)^4 := by
    filter_upwards [h_unit_nhdNE] with z hz
    have h_norm : ‖z‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    exact polyLog_neg_three_eq_rational z h_norm
  exact h.mp (h_eventually_rat.mono (fun z hz_eq h_rat => by
    rw [hz_eq, ← h_rat]))

/-! ## Sequential constructor -/

/-- **Sequential constructor for the sharper Prop**. -/
theorem jonquieresExpansionEqualsRationalAtNegThree_of_sequence
    (z : ℕ → ℂ)
    (h_ne : ∀ n, z n ≠ (1/2 : ℂ))
    (h_tend : Tendsto z atTop (𝓝 (1/2 : ℂ)))
    (h_eq : ∀ n,
      z n * (1 + 4*(z n) + (z n)^2) / (1 - z n)^4 =
        jonquieresExpansion (-3) (z n)) :
    JonquieresExpansionEqualsRationalAtNegThree := by
  unfold JonquieresExpansionEqualsRationalAtNegThree
  have h_tendNE : Tendsto z atTop (𝓝[≠] (1/2 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨h_tend, ?_⟩
    exact Filter.Eventually.of_forall h_ne
  exact h_tendNE.frequently (Filter.Eventually.frequently
    (Filter.Eventually.of_forall h_eq))

/-- **Sequential constructor for `JonquieresFrequentAgreementAtHalf (-3)`
    via the rational form**. -/
theorem jonquieresFrequentAgreementAtHalf_neg_three_of_sequence_rational
    (z : ℕ → ℂ)
    (h_ne : ∀ n, z n ≠ (1/2 : ℂ))
    (h_tend : Tendsto z atTop (𝓝 (1/2 : ℂ)))
    (h_eq : ∀ n,
      z n * (1 + 4*(z n) + (z n)^2) / (1 - z n)^4 =
        jonquieresExpansion (-3) (z n)) :
    JonquieresFrequentAgreementAtHalf (-3) :=
  jonquieresFrequentAgreementAtHalf_neg_three_of_rational
    (jonquieresExpansionEqualsRationalAtNegThree_of_sequence
      z h_ne h_tend h_eq)

/-! ## Explicit form at the single point `z = 1/2` -/

/-- **Rational closed form at `z = 1/2`**:
    `(1/2)(1 + 4·(1/2) + (1/2)²)/(1 - 1/2)^4 = 26`. -/
theorem rational_at_half_eq_twentySix :
    (1/2 : ℂ) * (1 + 4*(1/2) + (1/2)^2) / (1 - 1/2)^4 = 26 := by
  norm_num

/-- **Reduction at the single point**: if the Jonquières expansion at
    `(s, z) = (-3, 1/2)` numerically equals `26`, the literal pointwise
    identity holds there. -/
theorem polyLog_neg_three_eq_jonquieresExpansion_at_half_of_value
    (h : jonquieresExpansion (-3) (1/2 : ℂ) = 26) :
    polyLog (-3) (1/2 : ℂ) = jonquieresExpansion (-3) (1/2 : ℂ) := by
  rw [h]
  rw [polyLog_neg_three_eq_rational (1/2 : ℂ) (by
    have : (1/2 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := half_mem_ball_one
    simpa [Metric.mem_ball, dist_zero_right] using this)]
  exact rational_at_half_eq_twentySix

/-! ## Architecture summary

**This file establishes (axiom-free, no `sorry`)**:

* `polyLog_neg_three_eq_rational` — unconditional closed form
  `polyLog (-3) z = z(1+4z+z²) / (1-z)^4` for `‖z‖ < 1`. The
  rational numerator `1 + 4z + z²` is the Eulerian polynomial `A_3(z)`.
* `JonquieresExpansionEqualsRationalAtNegThree` — sharper open Prop.
* `jonquieresFrequentAgreementAtHalf_neg_three_of_rational` — REDUCTION.
* `jonquieresExpansionEqualsRationalAtNegThree_of_sequence` —
  sequential constructor.
* `jonquieresFrequentAgreementAtHalf_neg_three_of_sequence_rational` —
  composition.
* `rational_at_half_eq_twentySix` — `(1/2)(13/4)/(1/2)^4 = 26`.
* `polyLog_neg_three_eq_jonquieresExpansion_at_half_of_value` —
  point-wise reduction at `z = 1/2`.

Stage L21 — Frequent agreement at s = -3 via the Eulerian-polynomial
closed form.
-/

end PrincipiaTractalis.Analytic.Sheaf
