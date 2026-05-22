/-
# `ZetaShiftPolyExpBound` Discharge at `s = -N` for every `N : ℕ`

This file extends the `s = 0` discharge of `ZetaShiftPolyExpBound`
(see `PF/Analytic/ZetaShiftBoundDischarge.lean`) to ALL non-positive
integer base points `s = -(N : ℂ)` for `N : ℕ`, axiom-free.

## Mathematical content

For `s = -(N : ℂ)`, the shift `s - k = -(N + k : ℂ)`, so
`ζ(s - k) = ζ(-(N + k))`.  Setting `j := N + k` reduces to the
already-formalized Bernoulli closed form / growth bound at index `j`:

* `j` even (`j ≥ 2`) ⇒ `ζ(-j) = 0` via `bernoulli'_odd_eq_zero`
  on the odd index `j + 1`.
* `j = 2m - 1` odd with `m ≥ 1` ⇒ `|ζ(-j)| ≤ (π/6) · j!/(2π)^j`
  via `bernoulli_growth_bound_explicit`.

Converting `(N+k)!/(2π)^{N+k}` back to `k!/(2π)^k`-shape:

  `(N+k)! / k! = (k+1)(k+2)…(k+N) ≤ ((N+1)(k+1))^N = (N+1)^N · (k+1)^N`

  `(2π)^{N+k} = (2π)^N · (2π)^k`

So
  `(π/6) · (N+k)! / (2π)^{N+k}
    ≤ (π/6) · (N+1)^N · (k+1)^N · k! / ((2π)^N · (2π)^k)
    ≤ (π/6) · (N+1)^N · (k+1)^N · k! / (2π)^k`,

since `(2π)^N ≥ 1`.

Concrete witnesses:
  * `A := (π/6) · (N+1)^N`
  * `d := N`
  * `K := 1`

(For `N = 0`, this collapses to the `s = 0` discharge with `A = π/6`,
`d = 0`, `K = 1`; in particular this file SUBSUMES the `s = 0` case.)

## What this file delivers (axiom-free, no `sorry`)

* `factorial_ratio_le_pow` — `(N+k)!/k! ≤ ((N+1)(k+1))^N`.
* `zetaShiftPolyExpBound_neg_nat` — **the discharge**:
  `ZetaShiftPolyExpBound (-(N : ℂ))` for every `N : ℕ`.
* `jonquieresZetaSeries_analyticOnNhd_neg_nat_unconditional`,
  `jonquieresExpansion_analyticOnNhd_neg_nat_unconditional`,
  `JonquieresZetaSeriesAnalyticityHypothesis_neg_nat` — unconditional
  capstones at every `s = -(N : ℂ)`.

Stage L16 — `ZetaShiftPolyExpBound` discharge at every non-positive
integer base point.
-/

import PF.Analytic.ZetaShiftBoundDischarge

namespace PrincipiaTractalis.Analytic.Sheaf

open Complex Filter Topology Set Metric Real
open PrincipiaTractalis.Analytic

/-! ## Step 1: the rising-factorial bound -/

/-- `(N+k)! / k! = (k+1)(k+2)…(k+N) ≤ ((N+1)(k+1))^N`.

    Each of the `N` factors satisfies `(k+i) ≤ (N+1)(k+1)` for
    `1 ≤ i ≤ N`, since `(N+1)(k+1) = (N+1)k + (N+1) ≥ k + N ≥ k + i`. -/
theorem factorial_ratio_le_pow (N k : ℕ) :
    ((N + k).factorial : ℝ) ≤ ((N + 1 : ℝ) * (k + 1 : ℝ)) ^ N
      * (k.factorial : ℝ) := by
  induction N with
  | zero =>
    -- (0 + k)! = k!; ((0+1)(k+1))^0 = 1.
    simp
  | succ N ih =>
    -- (N+1+k)! = (N+1+k) · (N+k)!
    have hfact_succ : ((N + 1 + k).factorial : ℝ)
        = ((N + 1 + k : ℕ) : ℝ) * ((N + k).factorial : ℝ) := by
      have h : (N + 1 + k).factorial = (N + 1 + k) * (N + k).factorial := by
        have hrw : N + 1 + k = (N + k) + 1 := by ring
        rw [hrw, Nat.factorial_succ]
      exact_mod_cast h
    rw [hfact_succ]
    -- ((N+1+1)(k+1))^(N+1) = ((N+2)(k+1)) · ((N+2)(k+1))^N
    -- Bound: (N+1+k) ≤ (N+2)(k+1) and (N+k)! ≤ ((N+1)(k+1))^N · k!
    --          ≤ ((N+2)(k+1))^N · k! (since N+1 ≤ N+2).
    have h_factor_le : ((N + 1 + k : ℕ) : ℝ) ≤ ((N + 1 + 1 : ℝ) * ((k : ℝ) + 1)) := by
      have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
      have hcast : ((N + 1 + k : ℕ) : ℝ) = (N : ℝ) + 1 + (k : ℝ) := by push_cast; ring
      rw [hcast]
      nlinarith
    have h_factor_nn : (0 : ℝ) ≤ ((N + 1 + k : ℕ) : ℝ) := Nat.cast_nonneg _
    have h_base_nn : (0 : ℝ) ≤ ((N + 1 : ℝ) * ((k : ℝ) + 1)) := by
      have : (0 : ℝ) ≤ ((k : ℝ) + 1) := by positivity
      have : (0 : ℝ) ≤ ((N : ℝ) + 1) := by positivity
      positivity
    have h_base2_nn : (0 : ℝ) ≤ ((N + 1 + 1 : ℝ) * ((k : ℝ) + 1)) := by
      have : (0 : ℝ) ≤ ((k : ℝ) + 1) := by positivity
      positivity
    have h_base_le : ((N + 1 : ℝ) * ((k : ℝ) + 1)) ≤ ((N + 1 + 1 : ℝ) * ((k : ℝ) + 1)) := by
      have hk1_nn : (0 : ℝ) ≤ ((k : ℝ) + 1) := by positivity
      have hN1_le : ((N + 1 : ℝ)) ≤ ((N + 1 + 1 : ℝ)) := by linarith
      exact mul_le_mul_of_nonneg_right hN1_le hk1_nn
    have h_fact_nn : (0 : ℝ) ≤ ((k.factorial : ℝ)) := by
      exact_mod_cast (k.factorial.zero_le)
    have h_Nk_fact_nn : (0 : ℝ) ≤ ((N + k).factorial : ℝ) := by
      exact_mod_cast ((N + k).factorial).zero_le
    -- ih : (N+k)! ≤ ((N+1)(k+1))^N · k!
    -- Step A: (N+k)! ≤ ((N+2)(k+1))^N · k! via base monotonicity.
    have h_pow_le : ((N + 1 : ℝ) * ((k : ℝ) + 1)) ^ N
        ≤ ((N + 1 + 1 : ℝ) * ((k : ℝ) + 1)) ^ N :=
      pow_le_pow_left₀ h_base_nn h_base_le N
    have ih2 : ((N + k).factorial : ℝ) ≤
        ((N + 1 + 1 : ℝ) * ((k : ℝ) + 1)) ^ N * (k.factorial : ℝ) := by
      apply le_trans ih
      apply mul_le_mul_of_nonneg_right h_pow_le h_fact_nn
    -- Step B: multiply with h_factor_le.
    -- We want: (N+1+k) · (N+k)! ≤ ((N+2)(k+1))^(N+1) · k!
    --       = ((N+2)(k+1)) · ((N+2)(k+1))^N · k!
    have hmul1 : ((N + 1 + k : ℕ) : ℝ) * ((N + k).factorial : ℝ)
        ≤ ((N + 1 + 1 : ℝ) * ((k : ℝ) + 1)) *
          (((N + 1 + 1 : ℝ) * ((k : ℝ) + 1)) ^ N * (k.factorial : ℝ)) := by
      have h1 : ((N + 1 + k : ℕ) : ℝ) * ((N + k).factorial : ℝ)
          ≤ ((N + 1 + 1 : ℝ) * ((k : ℝ) + 1)) * ((N + k).factorial : ℝ) :=
        mul_le_mul_of_nonneg_right h_factor_le h_Nk_fact_nn
      have h2 : ((N + 1 + 1 : ℝ) * ((k : ℝ) + 1)) * ((N + k).factorial : ℝ)
          ≤ ((N + 1 + 1 : ℝ) * ((k : ℝ) + 1)) *
            (((N + 1 + 1 : ℝ) * ((k : ℝ) + 1)) ^ N * (k.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left ih2 h_base2_nn
      exact le_trans h1 h2
    -- Reshape RHS to ((N+1+1)(k+1))^(N+1) · k!.
    have h_reshape : ((N + 1 + 1 : ℝ) * ((k : ℝ) + 1)) *
        (((N + 1 + 1 : ℝ) * ((k : ℝ) + 1)) ^ N * (k.factorial : ℝ))
        = ((N + 1 + 1 : ℝ) * ((k : ℝ) + 1)) ^ (N + 1) * (k.factorial : ℝ) := by
      rw [pow_succ]
      ring
    -- And the LHS cast (N+1) cast on the goal vs the (N : ℝ) + 1 form.
    have h_goal_RHS_eq :
        ((↑(N + 1) + 1 : ℝ) * ((k : ℝ) + 1)) ^ (N + 1) * (k.factorial : ℝ)
        = ((N + 1 + 1 : ℝ) * ((k : ℝ) + 1)) ^ (N + 1) * (k.factorial : ℝ) := by
      have : ((↑(N + 1) + 1 : ℝ)) = ((N + 1 + 1 : ℝ)) := by push_cast; ring
      rw [this]
    rw [h_goal_RHS_eq, ← h_reshape]
    exact hmul1

/-! ## Step 2: the discharge -/

/-- **MAIN THEOREM**: `ZetaShiftPolyExpBound (-(N : ℂ))` for every `N : ℕ`,
    axiom-free.

    Witnesses: `A = (π/6) · (N+1)^N`, `d = N`, `K = 1`.

    Proof: substitute `s - k = -(N+k)` and apply the same Bernoulli
    case-split as the `s = 0` discharge, then bound the rising factorial
    `(N+k)!/k! ≤ ((N+1)(k+1))^N` and `(2π)^N ≥ 1`. -/
theorem zetaShiftPolyExpBound_neg_nat (N : ℕ) :
    ZetaShiftPolyExpBound (-(N : ℂ)) := by
  refine ⟨(Real.pi / 6) * ((N : ℝ) + 1) ^ N, by positivity, N, 1, ?_⟩
  intro k hk
  -- Goal: ‖ζ(-N - k)‖ ≤ A · (k+1)^N · k! / (2π)^k
  -- Step 1: rewrite -N - k = -(N+k).
  have hsub : (-(N : ℂ)) - (k : ℂ) = -((N + k : ℕ) : ℂ) := by push_cast; ring
  rw [hsub]
  -- Step 2: apply the Bernoulli identity at index j := N + k.
  set j : ℕ := N + k with hj_def
  have hj_ge1 : 1 ≤ j := by rw [hj_def]; omega
  -- Bound on ‖ζ(-j)‖: case-split on parity of j.
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
  -- Step 3: bound (π/6) · j! / (2π)^j ≤ A · (k+1)^N · k! / (2π)^k.
  -- (π/6) · j! / (2π)^j
  --   = (π/6) · (N+k)! / ((2π)^N · (2π)^k)
  --   ≤ (π/6) · ((N+1)(k+1))^N · k! / ((2π)^N · (2π)^k)   [factorial ratio]
  --   ≤ (π/6) · ((N+1)(k+1))^N · k! / (2π)^k             [(2π)^N ≥ 1]
  --   = A · (k+1)^N · k! / (2π)^k                         [(N+1)^N · (k+1)^N pulled apart]
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h2pi_pow_pos_j : (0 : ℝ) < (2 * Real.pi) ^ j := pow_pos h2pi_pos _
  have h2pi_pow_pos_k : (0 : ℝ) < (2 * Real.pi) ^ k := pow_pos h2pi_pos _
  have h2pi_pow_pos_N : (0 : ℝ) < (2 * Real.pi) ^ N := pow_pos h2pi_pos _
  have h2pi_pow_ge_one_N : (1 : ℝ) ≤ (2 * Real.pi) ^ N := by
    have h1 : (1 : ℝ) ≤ 2 * Real.pi := by
      have : (3 : ℝ) ≤ 2 * Real.pi := by
        have := Real.pi_gt_three
        linarith
      linarith
    exact one_le_pow₀ h1
  have hj_pow_eq : (2 * Real.pi) ^ j = (2 * Real.pi) ^ N * (2 * Real.pi) ^ k := by
    rw [hj_def, pow_add]
  -- Apply factorial_ratio_le_pow.
  have hfact_le := factorial_ratio_le_pow N k
  -- hfact_le : ((N+k)! : ℝ) ≤ ((N+1)(k+1))^N · k!
  have hfact_le' : (j.factorial : ℝ)
      ≤ ((N : ℝ) + 1) ^ N * ((k : ℝ) + 1) ^ N * (k.factorial : ℝ) := by
    rw [hj_def]
    calc ((N + k).factorial : ℝ)
        ≤ (((N : ℝ) + 1) * ((k : ℝ) + 1)) ^ N * (k.factorial : ℝ) := hfact_le
      _ = ((N : ℝ) + 1) ^ N * ((k : ℝ) + 1) ^ N * (k.factorial : ℝ) := by
          rw [mul_pow]
  -- Now (π/6) · j! / (2π)^j
  --     ≤ (π/6) · ((N+1)^N · (k+1)^N · k!) / ((2π)^N · (2π)^k)
  --     ≤ (π/6) · ((N+1)^N · (k+1)^N · k!) / (2π)^k
  --     = A · (k+1)^N · k! / (2π)^k.
  -- Step A: multiply hzeta_le into the goal.
  -- Goal: ‖ζ(-j)‖ ≤ (π/6) · (N+1)^N * (k+1)^N · k! / (2π)^k
  refine le_trans hzeta_le ?_
  -- Now goal: (π/6) · j! / (2π)^j ≤ (π/6)·(N+1)^N · (k+1)^N · k! / (2π)^k
  -- Use the factorial bound and (2π)^N ≥ 1.
  have hπ6_nn : (0 : ℝ) ≤ Real.pi / 6 := by positivity
  -- Let X := (N+1)^N · (k+1)^N · k!. Then we'll show:
  --   (π/6) · j! / (2π)^j ≤ (π/6) · X / (2π)^k.
  set X : ℝ := ((N : ℝ) + 1) ^ N * ((k : ℝ) + 1) ^ N * (k.factorial : ℝ) with hX_def
  -- Bound on numerator: π/6 · j! ≤ π/6 · X (using hfact_le' and hπ6_nn).
  have hnum_le : (Real.pi / 6) * (j.factorial : ℝ) ≤ (Real.pi / 6) * X :=
    mul_le_mul_of_nonneg_left hfact_le' hπ6_nn
  -- Bound on denominator (divisor side): (2π)^k ≤ (2π)^j, so 1/(2π)^j ≤ 1/(2π)^k.
  have h2pi_pow_le : (2 * Real.pi) ^ k ≤ (2 * Real.pi) ^ j := by
    rw [hj_pow_eq]
    -- (2π)^k ≤ (2π)^N · (2π)^k iff 1 ≤ (2π)^N, given (2π)^k > 0.
    have : (1 : ℝ) * (2 * Real.pi) ^ k ≤ (2 * Real.pi) ^ N * (2 * Real.pi) ^ k :=
      mul_le_mul_of_nonneg_right h2pi_pow_ge_one_N h2pi_pow_pos_k.le
    linarith
  -- LHS = (π/6 · j!) / (2π)^j ≤ (π/6 · X) / (2π)^j ≤ (π/6 · X) / (2π)^k.
  have hX_nn : 0 ≤ X := by
    rw [hX_def]
    have hk_nn : (0 : ℝ) ≤ ((k : ℝ) + 1) ^ N := by positivity
    have hN_nn : (0 : ℝ) ≤ ((N : ℝ) + 1) ^ N := by positivity
    have hf_nn : (0 : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast (k.factorial).zero_le
    positivity
  have hπ6X_nn : 0 ≤ (Real.pi / 6) * X := mul_nonneg hπ6_nn hX_nn
  -- (π/6 · j!) / (2π)^j ≤ (π/6 · X) / (2π)^j
  have hstep1 : (Real.pi / 6) * (j.factorial : ℝ) / (2 * Real.pi) ^ j
      ≤ (Real.pi / 6) * X / (2 * Real.pi) ^ j :=
    div_le_div_of_nonneg_right hnum_le h2pi_pow_pos_j.le
  -- (π/6 · X) / (2π)^j ≤ (π/6 · X) / (2π)^k
  have hstep2 : (Real.pi / 6) * X / (2 * Real.pi) ^ j
      ≤ (Real.pi / 6) * X / (2 * Real.pi) ^ k :=
    div_le_div_of_nonneg_left hπ6X_nn h2pi_pow_pos_k h2pi_pow_le
  -- Combine.
  refine le_trans hstep1 (le_trans hstep2 ?_)
  -- Final: (π/6) * X / (2π)^k = (π/6) * (N+1)^N * (k+1)^N * k! / (2π)^k.
  -- The RHS of the original goal is:
  --   (π/6) * (N+1)^N * (k+1)^N * k! / (2π)^k
  -- after expanding A = (π/6) * (N+1)^N.
  apply le_of_eq
  rw [hX_def]
  ring

/-! ## Step 3: unconditional capstones at every `s = -(N : ℂ)` -/

/-- **HEADLINE CAPSTONE (axiom-free, no `sorry`)**: at every
    `s = -(N : ℂ)` for `N : ℕ`, the Jonquières ζ-series is analytic
    on the convergence subdomain unconditionally. -/
theorem jonquieresZetaSeries_analyticOnNhd_neg_nat_unconditional (N : ℕ) :
    AnalyticOnNhd ℂ (jonquieresZetaSeries (-(N : ℂ)))
      (JonquieresAnalyticDomain ∩ {z : ℂ | ‖Complex.log z‖ < 2 * Real.pi}) :=
  jonquieresZetaSeries_analyticOnNhd_of_zetaShiftPolyExpBound
    (zetaShiftPolyExpBound_neg_nat N)

/-- **Companion capstone**: the full Jonquières expansion at every
    `s = -(N : ℂ)` is analytic on the convergence subdomain,
    unconditionally. -/
theorem jonquieresExpansion_analyticOnNhd_neg_nat_unconditional (N : ℕ) :
    AnalyticOnNhd ℂ (jonquieresExpansion (-(N : ℂ)))
      (JonquieresAnalyticDomain ∩ {z : ℂ | ‖Complex.log z‖ < 2 * Real.pi}) :=
  jonquieresExpansion_analyticOnNhd_of_zetaShiftPolyExpBound
    (zetaShiftPolyExpBound_neg_nat N)

/-- **Companion capstone**: the `JonquieresZetaSeriesAnalyticityHypothesis`
    at every `s = -(N : ℂ)` is discharged unconditionally. -/
theorem JonquieresZetaSeriesAnalyticityHypothesis_neg_nat (N : ℕ) :
    JonquieresZetaSeriesAnalyticityHypothesis (-(N : ℂ)) :=
  JonquieresZetaSeriesAnalyticityHypothesis_of_zetaShiftPolyExpBound
    (zetaShiftPolyExpBound_neg_nat N)

/-! ## Architecture summary

**This file establishes (axiom-free, no sorry)**:

* `factorial_ratio_le_pow` — rising-factorial bound
  `(N+k)!/k! ≤ ((N+1)(k+1))^N` (induction on N).
* `zetaShiftPolyExpBound_neg_nat` — **THE DISCHARGE**: for every
  `N : ℕ`, `ZetaShiftPolyExpBound (-(N : ℂ))` holds unconditionally
  with witnesses `A = (π/6) · (N+1)^N`, `d = N`, `K = 1`.
* `jonquieresZetaSeries_analyticOnNhd_neg_nat_unconditional`,
  `jonquieresExpansion_analyticOnNhd_neg_nat_unconditional`,
  `JonquieresZetaSeriesAnalyticityHypothesis_neg_nat` —
  unconditional capstones at every non-positive integer base point.

**Status**:
The `s = -N` family (every `N : ℕ`) is now COMPLETELY discharged,
axiom-free. The `N = 0` case recovers `zetaShiftPolyExpBound_zero`.

For general complex `s` (off the integer locus), the residual remains
open — its proof requires the ζ functional equation + Stirling for
`Γ(1+k-s)` + uniform sine bound, none of which are formalized in
mathlib at the level needed here.

Stage L16 — `ZetaShiftPolyExpBound` discharge at every non-positive
integer base point.
-/

end PrincipiaTractalis.Analytic.Sheaf
