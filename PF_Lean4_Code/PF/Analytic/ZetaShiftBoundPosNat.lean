/-
# `ZetaShiftPolyExpBound` Discharge at `s = (N+2 : ℕ)` for every `N : ℕ`

This file extends the `s = -N` discharge of `ZetaShiftPolyExpBound`
(see `PF/Analytic/ZetaShiftBoundNegNat.lean`) to ALL positive integer
base points `s = ((N + 2 : ℕ) : ℂ)` for `N : ℕ`, i.e. `s ∈ {2, 3, 4, …}`,
axiom-free.

(The cases `s = 0` and `s = -N : ℤ ≤ 0` are already handled by the
previous two files; this file fills in the dilogarithm region `s = 2`,
the trilogarithm region `s = 3`, … The pole at `s = 1` is also handled
as a special case `zetaShiftPolyExpBound_one` by skipping `k ∈ {0, 1}`
via `K := 2`, so `s - k = -(k - 1)` is always a non-positive integer
strictly below the pole.)

## Mathematical content

For `s = ((N + 2 : ℕ) : ℂ)` and `k ≥ N + 3`, the shift `s - k` is a
non-positive complex integer:

  `s - k = ((N + 2 : ℕ) : ℂ) - (k : ℂ) = -((k - N - 2 : ℕ) : ℂ)`

with `j := k - N - 2 ≥ 1`. So `ζ(s - k) = ζ(-j)`, and we can apply the
same Bernoulli case-split as in `ZetaShiftBoundDischarge.lean`:

* `j` even (`j ≥ 2`) ⇒ `ζ(-j) = 0`.
* `j = 2m - 1` odd with `m ≥ 1` ⇒ `|ζ(-j)| ≤ (π/6) · j!/(2π)^j`.

Converting `j!/(2π)^j` to `k!/(2π)^k`-shape (with `j + (N+2) = k`):

  `j! ≤ k!`  (since `j ≤ k`)
  `(2π)^k = (2π)^(N+2) · (2π)^j`  ⇒  `1/(2π)^j = (2π)^(N+2) / (2π)^k`

So
  `(π/6) · j!/(2π)^j ≤ (π/6) · k! · (2π)^(N+2) / (2π)^k`
                    `= A · k! / (2π)^k`

with `A := (π/6) · (2π)^(N+2)`. Witnesses: `A` as above, `d := 0`,
`K := N + 3`.

## What this file delivers (axiom-free, no `sorry`)

* `factorial_mono_real` — `j ≤ k ⇒ (j! : ℝ) ≤ (k! : ℝ)`.
* `zetaShiftPolyExpBound_pos_nat` — **THE DISCHARGE**:
  `ZetaShiftPolyExpBound ((N + 2 : ℕ) : ℂ)` for every `N : ℕ`.
* `jonquieresZetaSeries_analyticOnNhd_pos_nat_unconditional`,
  `jonquieresExpansion_analyticOnNhd_pos_nat_unconditional`,
  `JonquieresZetaSeriesAnalyticityHypothesis_pos_nat` — unconditional
  capstones at every `s = ((N + 2 : ℕ) : ℂ)` (the dilogarithm region
  onwards). In particular `s = 2` (dilogarithm) and `s = 3`
  (trilogarithm) are now unconditional.

Stage L17 — `ZetaShiftPolyExpBound` discharge at every positive
integer base point `s = N + 2` (`N : ℕ`).
-/

import PF.Analytic.ZetaShiftBoundNegNat

namespace PrincipiaTractalis.Analytic.Sheaf

open Complex Filter Topology Set Metric Real
open PrincipiaTractalis.Analytic

/-! ## Step 1: monotonicity of the factorial -/

/-- The factorial is monotone in the natural-number argument, cast to
    `ℝ`. Direct from `Nat.factorial_le` + `Nat.cast_le`. -/
theorem factorial_mono_real {j k : ℕ} (hjk : j ≤ k) :
    (j.factorial : ℝ) ≤ (k.factorial : ℝ) := by
  exact_mod_cast Nat.factorial_le hjk

/-! ## Step 2: the discharge for `s = ((N + 2 : ℕ) : ℂ)` -/

/-- **MAIN THEOREM**: `ZetaShiftPolyExpBound ((N + 2 : ℕ) : ℂ)` for every
    `N : ℕ`, axiom-free.

    Witnesses: `A = (π/6) · (2π)^(N+2)`, `d = 0`, `K = N + 3`.

    Proof: for `k ≥ N + 3`, `s - k = -(k - N - 2)` with `j := k - N - 2 ≥ 1`.
    Reuse the parity case-split via
    `zeta_neg_nat_norm_even_eq_zero` / `zeta_neg_nat_norm_odd_bound`.
    The factorial / `(2π)^k` conversion uses `j! ≤ k!` (monotone) and
    `(2π)^k = (2π)^(N+2) · (2π)^j`. -/
theorem zetaShiftPolyExpBound_pos_nat (N : ℕ) :
    ZetaShiftPolyExpBound (((N + 2 : ℕ) : ℂ)) := by
  refine ⟨(Real.pi / 6) * (2 * Real.pi) ^ (N + 2), by positivity, 0, N + 3, ?_⟩
  intro k hk
  -- Goal: ‖ζ((N+2 : ℕ) - k)‖ ≤ A · (k+1)^0 · k! / (2π)^k
  -- Simplify (k+1)^0 = 1.
  simp only [pow_zero, mul_one]
  -- Step 1: rewrite (N+2 : ℕ) - k = -((k - N - 2 : ℕ) : ℂ).
  -- Since k ≥ N+3 > N+2, this is a valid natural subtraction.
  have hk_ge : N + 2 ≤ k := by omega
  set j : ℕ := k - (N + 2) with hj_def
  have hj_ge1 : 1 ≤ j := by rw [hj_def]; omega
  have hj_le_k : j ≤ k := by rw [hj_def]; omega
  have hjN : j + (N + 2) = k := by rw [hj_def]; omega
  -- Complex subtraction equality.
  have hsub : ((N + 2 : ℕ) : ℂ) - (k : ℂ) = -((j : ℕ) : ℂ) := by
    have hcast_k : (k : ℂ) = ((j + (N + 2) : ℕ) : ℂ) := by
      rw [hjN]
    rw [hcast_k]
    push_cast
    ring
  rw [hsub]
  -- Step 2: bound on ‖ζ(-j)‖ via parity case-split.
  have hzeta_le :
      ‖riemannZeta (-((j : ℕ) : ℂ))‖ ≤
        (Real.pi / 6) * (j.factorial : ℝ) / (2 * Real.pi) ^ j := by
    rcases Nat.even_or_odd j with hj_even | hj_odd
    · -- j even with j ≥ 1 ⇒ j ≥ 2.
      have hj2 : 2 ≤ j := by
        rcases Nat.lt_or_ge j 2 with hlt | hge
        · interval_cases j
          exact absurd hj_even (by decide)
        · exact hge
      rw [zeta_neg_nat_norm_even_eq_zero hj_even hj2]
      positivity
    · -- j odd: j = 2*m + 1 for some m ⇒ j = 2*(m+1) - 1 with m+1 ≥ 1.
      obtain ⟨m, hm_eq⟩ := hj_odd
      set m' := m + 1 with hm'_def
      have hj_eq : j = 2 * m' - 1 := by
        simp [hm'_def, hm_eq, Nat.mul_succ]
      have hm'_pos : 1 ≤ m' := by rw [hm'_def]; omega
      have hbound := zeta_neg_nat_norm_odd_bound hm'_pos
      rw [hj_eq]
      exact hbound
  -- Step 3: bound (π/6) · j! / (2π)^j ≤ A · k! / (2π)^k.
  -- (π/6) · j! / (2π)^j
  --   = (π/6) · j! · (2π)^(N+2) / ((2π)^(N+2) · (2π)^j)
  --   = (π/6) · j! · (2π)^(N+2) / (2π)^k                       [(2π)^(N+2) · (2π)^j = (2π)^k]
  --   ≤ (π/6) · k! · (2π)^(N+2) / (2π)^k                       [j! ≤ k!]
  --   = A · k! / (2π)^k                                          [A := (π/6) · (2π)^(N+2)]
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h2pi_pow_pos_j : (0 : ℝ) < (2 * Real.pi) ^ j := pow_pos h2pi_pos _
  have h2pi_pow_pos_k : (0 : ℝ) < (2 * Real.pi) ^ k := pow_pos h2pi_pos _
  have h2pi_pow_pos_N2 : (0 : ℝ) < (2 * Real.pi) ^ (N + 2) := pow_pos h2pi_pos _
  have hk_pow_eq : (2 * Real.pi) ^ k = (2 * Real.pi) ^ (N + 2) * (2 * Real.pi) ^ j := by
    have hkeq : k = (N + 2) + j := by omega
    rw [hkeq, pow_add]
  refine le_trans hzeta_le ?_
  -- Goal: (π/6) · j! / (2π)^j ≤ ((π/6) · (2π)^(N+2)) · k! / (2π)^k
  -- Rewrite RHS denominator using hk_pow_eq.
  -- Strategy: multiply numerator and denominator on LHS by (2π)^(N+2),
  -- then apply j! ≤ k!.
  have hπ6_nn : (0 : ℝ) ≤ Real.pi / 6 := by positivity
  have hfact_j_nn : (0 : ℝ) ≤ (j.factorial : ℝ) := by exact_mod_cast j.factorial.zero_le
  have hfact_k_nn : (0 : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast k.factorial.zero_le
  -- Convert LHS: (π/6) · j! / (2π)^j = (π/6) · j! · (2π)^(N+2) / (2π)^k.
  have hLHS_eq :
      (Real.pi / 6) * (j.factorial : ℝ) / (2 * Real.pi) ^ j
      = (Real.pi / 6) * (j.factorial : ℝ) * (2 * Real.pi) ^ (N + 2) / (2 * Real.pi) ^ k := by
    rw [hk_pow_eq]
    field_simp
  rw [hLHS_eq]
  -- Now goal: (π/6) · j! · (2π)^(N+2) / (2π)^k ≤ ((π/6) · (2π)^(N+2)) · k! / (2π)^k.
  -- Use div_le_div_of_nonneg_right with the numerator bound.
  have hnum_le :
      (Real.pi / 6) * (j.factorial : ℝ) * (2 * Real.pi) ^ (N + 2) ≤
      ((Real.pi / 6) * (2 * Real.pi) ^ (N + 2)) * (k.factorial : ℝ) := by
    have hfact_le : (j.factorial : ℝ) ≤ (k.factorial : ℝ) := factorial_mono_real hj_le_k
    have hcoeff_nn : (0 : ℝ) ≤ (Real.pi / 6) * (2 * Real.pi) ^ (N + 2) :=
      mul_nonneg hπ6_nn h2pi_pow_pos_N2.le
    -- (π/6) · j! · (2π)^(N+2) = ((π/6) · (2π)^(N+2)) · j!
    have hreshape :
        (Real.pi / 6) * (j.factorial : ℝ) * (2 * Real.pi) ^ (N + 2)
        = ((Real.pi / 6) * (2 * Real.pi) ^ (N + 2)) * (j.factorial : ℝ) := by ring
    rw [hreshape]
    exact mul_le_mul_of_nonneg_left hfact_le hcoeff_nn
  exact div_le_div_of_nonneg_right hnum_le h2pi_pow_pos_k.le

/-! ## Step 3: unconditional capstones at every `s = ((N + 2 : ℕ) : ℂ)` -/

/-- **HEADLINE CAPSTONE (axiom-free, no `sorry`)**: at every
    `s = ((N + 2 : ℕ) : ℂ)` for `N : ℕ`, the Jonquières ζ-series is
    analytic on the convergence subdomain unconditionally.

    Special cases: `N = 0` gives `s = 2` (dilogarithm), `N = 1` gives
    `s = 3` (trilogarithm), etc. -/
theorem jonquieresZetaSeries_analyticOnNhd_pos_nat_unconditional (N : ℕ) :
    AnalyticOnNhd ℂ (jonquieresZetaSeries (((N + 2 : ℕ) : ℂ)))
      (JonquieresAnalyticDomain ∩ {z : ℂ | ‖Complex.log z‖ < 2 * Real.pi}) :=
  jonquieresZetaSeries_analyticOnNhd_of_zetaShiftPolyExpBound
    (zetaShiftPolyExpBound_pos_nat N)

/-- **Companion capstone**: the full Jonquières expansion at every
    `s = ((N + 2 : ℕ) : ℂ)` is analytic on the convergence subdomain,
    unconditionally. -/
theorem jonquieresExpansion_analyticOnNhd_pos_nat_unconditional (N : ℕ) :
    AnalyticOnNhd ℂ (jonquieresExpansion (((N + 2 : ℕ) : ℂ)))
      (JonquieresAnalyticDomain ∩ {z : ℂ | ‖Complex.log z‖ < 2 * Real.pi}) :=
  jonquieresExpansion_analyticOnNhd_of_zetaShiftPolyExpBound
    (zetaShiftPolyExpBound_pos_nat N)

/-- **Companion capstone**: the `JonquieresZetaSeriesAnalyticityHypothesis`
    at every `s = ((N + 2 : ℕ) : ℂ)` is discharged unconditionally. -/
theorem JonquieresZetaSeriesAnalyticityHypothesis_pos_nat (N : ℕ) :
    JonquieresZetaSeriesAnalyticityHypothesis (((N + 2 : ℕ) : ℂ)) :=
  JonquieresZetaSeriesAnalyticityHypothesis_of_zetaShiftPolyExpBound
    (zetaShiftPolyExpBound_pos_nat N)

/-! ## Step 4: handling the pole at `s = 1`

`ζ` has a simple pole at `s = 1`. The shifted argument `s - k = 1 - k`
is fine for `k ≥ 2` (then `1 - k = -(k - 1)` is a non-positive integer
with `k - 1 ≥ 1`). At `k = 1`, `s - k = 0` and `ζ(0) = -1/2` is finite;
at `k = 0`, `s - k = 1` itself is the pole, but the bound only
constrains `k ≥ K` and we can take `K = 2` to skip both. -/

/-- **Companion**: `ZetaShiftPolyExpBound 1` holds with `K := 2`
    (which skips both `k = 0` at the pole and `k = 1` at `ζ(0)`).
    Reuses the same Bernoulli case-split as the `s = N+2` proof. -/
theorem zetaShiftPolyExpBound_one : ZetaShiftPolyExpBound (1 : ℂ) := by
  refine ⟨(Real.pi / 6) * (2 * Real.pi) ^ (1 : ℕ), by positivity, 0, 2, ?_⟩
  intro k hk
  -- Goal: ‖ζ(1 - k)‖ ≤ A · (k+1)^0 · k! / (2π)^k
  simp only [pow_zero, mul_one]
  -- For k ≥ 2, set j := k - 1 ≥ 1, so 1 - k = -j.
  set j : ℕ := k - 1 with hj_def
  have hj_ge1 : 1 ≤ j := by rw [hj_def]; omega
  have hj_le_k : j ≤ k := by rw [hj_def]; omega
  have hjN : j + 1 = k := by rw [hj_def]; omega
  -- Complex subtraction equality.
  have hsub : (1 : ℂ) - (k : ℂ) = -((j : ℕ) : ℂ) := by
    have hcast_k : (k : ℂ) = ((j + 1 : ℕ) : ℂ) := by rw [hjN]
    rw [hcast_k]
    push_cast
    ring
  rw [hsub]
  -- Bound on ‖ζ(-j)‖ via parity case-split (same as pos_nat proof).
  have hzeta_le :
      ‖riemannZeta (-((j : ℕ) : ℂ))‖ ≤
        (Real.pi / 6) * (j.factorial : ℝ) / (2 * Real.pi) ^ j := by
    rcases Nat.even_or_odd j with hj_even | hj_odd
    · have hj2 : 2 ≤ j := by
        rcases Nat.lt_or_ge j 2 with hlt | hge
        · interval_cases j
          exact absurd hj_even (by decide)
        · exact hge
      rw [zeta_neg_nat_norm_even_eq_zero hj_even hj2]
      positivity
    · obtain ⟨m, hm_eq⟩ := hj_odd
      set m' := m + 1 with hm'_def
      have hj_eq : j = 2 * m' - 1 := by
        simp [hm'_def, hm_eq, Nat.mul_succ]
      have hm'_pos : 1 ≤ m' := by rw [hm'_def]; omega
      have hbound := zeta_neg_nat_norm_odd_bound hm'_pos
      rw [hj_eq]
      exact hbound
  -- Convert: (π/6) · j!/(2π)^j ≤ (π/6 · (2π)^1) · k! / (2π)^k.
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h2pi_pow_pos_j : (0 : ℝ) < (2 * Real.pi) ^ j := pow_pos h2pi_pos _
  have h2pi_pow_pos_k : (0 : ℝ) < (2 * Real.pi) ^ k := pow_pos h2pi_pos _
  have h2pi_pow_pos_1 : (0 : ℝ) < (2 * Real.pi) ^ (1 : ℕ) := pow_pos h2pi_pos _
  have hk_pow_eq : (2 * Real.pi) ^ k = (2 * Real.pi) ^ (1 : ℕ) * (2 * Real.pi) ^ j := by
    have hkeq : k = 1 + j := by omega
    rw [hkeq, pow_add]
  refine le_trans hzeta_le ?_
  have hπ6_nn : (0 : ℝ) ≤ Real.pi / 6 := by positivity
  have hfact_j_nn : (0 : ℝ) ≤ (j.factorial : ℝ) := by exact_mod_cast j.factorial.zero_le
  have hLHS_eq :
      (Real.pi / 6) * (j.factorial : ℝ) / (2 * Real.pi) ^ j
      = (Real.pi / 6) * (j.factorial : ℝ) * (2 * Real.pi) ^ (1 : ℕ) / (2 * Real.pi) ^ k := by
    rw [hk_pow_eq]
    field_simp
  rw [hLHS_eq]
  have hnum_le :
      (Real.pi / 6) * (j.factorial : ℝ) * (2 * Real.pi) ^ (1 : ℕ) ≤
      ((Real.pi / 6) * (2 * Real.pi) ^ (1 : ℕ)) * (k.factorial : ℝ) := by
    have hfact_le : (j.factorial : ℝ) ≤ (k.factorial : ℝ) := factorial_mono_real hj_le_k
    have hcoeff_nn : (0 : ℝ) ≤ (Real.pi / 6) * (2 * Real.pi) ^ (1 : ℕ) :=
      mul_nonneg hπ6_nn h2pi_pow_pos_1.le
    have hreshape :
        (Real.pi / 6) * (j.factorial : ℝ) * (2 * Real.pi) ^ (1 : ℕ)
        = ((Real.pi / 6) * (2 * Real.pi) ^ (1 : ℕ)) * (j.factorial : ℝ) := by ring
    rw [hreshape]
    exact mul_le_mul_of_nonneg_left hfact_le hcoeff_nn
  exact div_le_div_of_nonneg_right hnum_le h2pi_pow_pos_k.le

/-- Unconditional capstone at `s = 1`: full Jonquières expansion is
    analytic on the convergence subdomain. -/
theorem jonquieresExpansion_analyticOnNhd_one_unconditional :
    AnalyticOnNhd ℂ (jonquieresExpansion (1 : ℂ))
      (JonquieresAnalyticDomain ∩ {z : ℂ | ‖Complex.log z‖ < 2 * Real.pi}) :=
  jonquieresExpansion_analyticOnNhd_of_zetaShiftPolyExpBound
    zetaShiftPolyExpBound_one

/-- Unconditional capstone at `s = 1`: ζ-series half is analytic on the
    convergence subdomain. -/
theorem jonquieresZetaSeries_analyticOnNhd_one_unconditional :
    AnalyticOnNhd ℂ (jonquieresZetaSeries (1 : ℂ))
      (JonquieresAnalyticDomain ∩ {z : ℂ | ‖Complex.log z‖ < 2 * Real.pi}) :=
  jonquieresZetaSeries_analyticOnNhd_of_zetaShiftPolyExpBound
    zetaShiftPolyExpBound_one

/-! ## Step 5: specialized headline statements for the dilogarithm,
    trilogarithm, tetralogarithm.  -/

/-- `ZetaShiftPolyExpBound 2` — the dilogarithm region, unconditional. -/
theorem zetaShiftPolyExpBound_two : ZetaShiftPolyExpBound (2 : ℂ) := by
  have h := zetaShiftPolyExpBound_pos_nat 0
  -- ((0 + 2 : ℕ) : ℂ) = (2 : ℂ)
  have heq : (((0 + 2 : ℕ) : ℂ)) = (2 : ℂ) := by norm_num
  rw [heq] at h
  exact h

/-- `ZetaShiftPolyExpBound 3` — the trilogarithm region, unconditional. -/
theorem zetaShiftPolyExpBound_three : ZetaShiftPolyExpBound (3 : ℂ) := by
  have h := zetaShiftPolyExpBound_pos_nat 1
  have heq : (((1 + 2 : ℕ) : ℂ)) = (3 : ℂ) := by norm_num
  rw [heq] at h
  exact h

/-- `ZetaShiftPolyExpBound 4` — the tetralogarithm region, unconditional. -/
theorem zetaShiftPolyExpBound_four : ZetaShiftPolyExpBound (4 : ℂ) := by
  have h := zetaShiftPolyExpBound_pos_nat 2
  have heq : (((2 + 2 : ℕ) : ℂ)) = (4 : ℂ) := by norm_num
  rw [heq] at h
  exact h

/-! ## Architecture summary

**This file establishes (axiom-free, no sorry)**:

* `factorial_mono_real` — factorial monotonicity in `ℝ`.
* `zetaShiftPolyExpBound_pos_nat` — **THE DISCHARGE**: for every
  `N : ℕ`, `ZetaShiftPolyExpBound ((N + 2 : ℕ) : ℂ)` holds unconditionally
  with witnesses `A = (π/6) · (2π)^(N+2)`, `d = 0`, `K = N + 3`.
* `jonquieresZetaSeries_analyticOnNhd_pos_nat_unconditional`,
  `jonquieresExpansion_analyticOnNhd_pos_nat_unconditional`,
  `JonquieresZetaSeriesAnalyticityHypothesis_pos_nat` —
  unconditional capstones at every positive-integer base point ≥ 2.
* `zetaShiftPolyExpBound_one` — `ZetaShiftPolyExpBound 1` at the
  ζ-pole base point, via `K = 2`. Companion analyticity capstones
  `jonquieresExpansion_analyticOnNhd_one_unconditional` and
  `jonquieresZetaSeries_analyticOnNhd_one_unconditional`.
* `zetaShiftPolyExpBound_two`, `zetaShiftPolyExpBound_three`,
  `zetaShiftPolyExpBound_four` — headline specializations.

**Status**:
* `s = 0` — `zetaShiftPolyExpBound_zero` (ZetaShiftBoundDischarge.lean).
* `s = -N : ℤ ≤ 0` — `zetaShiftPolyExpBound_neg_nat` (ZetaShiftBoundNegNat.lean).
* `s = 1` — `zetaShiftPolyExpBound_one` (THIS FILE, via `K = 2` which
  skips the pole at `k = 0` and the finite `ζ(0)` at `k = 1`).
* `s = N + 2 : ℤ ≥ 2` — `zetaShiftPolyExpBound_pos_nat` (THIS FILE).

Combined with the s=0 and s=-N files, the `ZetaShiftPolyExpBound`
residual is now **unconditionally discharged at every integer `s ∈ ℤ`**.
The full chain:

  `ZetaShiftPolyExpBound s`  (discharged for every integer s ∈ ℤ)
        ⇓
  `JonquieresZetaUniformGrowthBridge s`
        ⇓
  `JonquieresZetaSeriesAnalyticityHypothesis s`
        ⇓
  `jonquieresExpansion s` analytic on `JonquieresAnalyticDomain ∩
                                       {z | ‖log z‖ < 2π}`

is now closed unconditionally at every integer `s ∈ ℤ`.

For general non-integer complex `s`, the residual remains open —
requires functional equation + Stirling + uniform sine bound,
none of which are formalized in mathlib at the level needed.

Stage L17 — `ZetaShiftPolyExpBound` discharge at every positive
integer base point `s = N + 2` (`N : ℕ`).
-/

end PrincipiaTractalis.Analytic.Sheaf
