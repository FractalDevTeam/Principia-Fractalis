/-
# `ZetaShiftPolyExpBound` Discharge at Integer s = 0

This file delivers an **axiom-free** discharge of the named residual
`ZetaShiftPolyExpBound s` from `PF/Analytic/ZetaBridgeDischarge.lean`
at the integer base point `s = 0`:

  `ZetaShiftPolyExpBound 0 :
      ∃ A ≥ 0, ∃ d : ℕ, ∃ K : ℕ, ∀ k ≥ K,
        ‖ζ(0 - k)‖ ≤ A · (k+1)^d · k! / (2π)^k`

## Mathematical content

For `s = 0` (and more generally any `s = -N : ℤ ≤ 0`), the shift
`s - k = -k : ℂ` lands on the trivial / Bernoulli locus, where mathlib's
`riemannZeta_neg_nat_eq_bernoulli` gives the exact closed form:

  `ζ(-k) = (-1)^k · B_{k+1} / (k+1)`

Combined with the already-proven `bernoulli_growth_bound_explicit`
(`|B_{2m}| ≤ (π²/3) · (2m)! / (2π)^{2m}`, axiom-free, from
`BernoulliGrowthBound.lean`), parity-splitting on `k+1`:

* `k` even ⇒ `k+1` odd ≥ 3 ⇒ `B_{k+1} = 0` ⇒ `ζ(-k) = 0`.
* `k = 2m-1` odd ⇒ `k+1 = 2m` even ⇒ `|B_{2m}| ≤ (π²/3) · (2m)!/(2π)^{2m}`.

In the odd case we need to relate `(2m)!/(2π)^{2m}` (with `2m = k+1`) to
`k!/(2π)^k`. The conversion factor is `(k+1) · 2π = (k+1) · 2π`:

  `(k+1)! / (2π)^{k+1} = (k+1) · k! / ((2π) · (2π)^k)`
  ⇒ `(k+1)!/(2π)^{k+1} = ((k+1)/(2π)) · k!/(2π)^k`

So `|ζ(-k)| = |B_{k+1}|/(k+1) ≤ (π²/3) · (k+1)!/((2π)^{k+1} · (k+1))`
            = `(π²/3) · k! · 1/(2π · (2π)^k)`
            = `(π²/(3·2π)) · k!/(2π)^k`
            = `(π/6) · k!/(2π)^k`

So the bound holds with `A = π/6`, `d = 0`, `K = 2` (so we skip the
`k=0` edge case where `s - k = 0` and `ζ(0) = -1/2` — finitely many
small `k` are absorbed by raising `A`; here we just start at `K=2`).

Actually, simplest: take `A = max(π/6, ‖ζ(0)‖, ‖ζ(-1)‖) + 1` and `K = 0`.
Even cleaner: take `A = 1 + π/6`, `d = 0`, `K = 2`. The bound at `k = 0`
(ζ(0) = -1/2) and `k = 1` (ζ(-1) = -1/12) is trivial to handle if needed;
here we just require `k ≥ K`.

## What this file delivers (axiom-free, no `sorry`)

* `zeta_neg_nat_norm_le_bernoulli_quotient` — `‖ζ(-k)‖ ≤ |B_{k+1}|/(k+1)`
  as an exact equality from `riemannZeta_neg_nat_eq_bernoulli`.
* `zeta_neg_nat_norm_bound_even_k` — for even `k ≥ 2`, `‖ζ(-k)‖ = 0`.
* `zeta_neg_nat_norm_bound_odd_k` — for odd `k = 2m-1` with `m ≥ 1`,
  `‖ζ(-k)‖ ≤ (π/6) · k!/(2π)^k` via `bernoulli_growth_bound_explicit`.
* `zetaShiftPolyExpBound_zero` — **the discharge**:
  `ZetaShiftPolyExpBound 0` holds with `A = π/6`, `d = 0`, `K = 2`.
* `jonquieresZetaSeries_analyticOnNhd_zero_unconditional` — the
  unconditional capstone at `s = 0`: the Jonquières ζ-series is
  analytic on the convergence subdomain, NO named hypothesis needed.

Stage L15 — `ZetaShiftPolyExpBound` discharge at the integer base point.
-/

import PF.Analytic.ZetaBridgeDischarge
import PF.Analytic.BernoulliGrowthBound
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.Bernoulli

namespace PrincipiaTractalis.Analytic.Sheaf

open Complex Filter Topology Set Metric Real
open PrincipiaTractalis.Analytic

/-! ## Step 1: norm of ζ(-k) via the Bernoulli closed form -/

/-- For any `k : ℕ`, the absolute value `‖ζ(-k)‖` is exactly
    `|B_{k+1}| / (k+1)` (real, nonneg). Direct from
    `riemannZeta_neg_nat_eq_bernoulli`. -/
theorem zeta_neg_nat_norm_eq_bernoulli (k : ℕ) :
    ‖riemannZeta (-(k : ℂ))‖ = |(bernoulli (k + 1) : ℝ)| / ((k : ℝ) + 1) := by
  have hformula := riemannZeta_neg_nat_eq_bernoulli k
  rw [hformula]
  -- Goal: ‖(-1)^k * (bernoulli (k+1) : ℚ) / (k+1)‖ = |B_{k+1}| / (k+1)
  rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  congr 1
  · -- ‖((bernoulli (k+1) : ℚ) : ℂ)‖ = |(bernoulli (k+1) : ℝ)|
    have hcast : ((bernoulli (k + 1) : ℚ) : ℂ) = ((bernoulli (k + 1) : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  · -- ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1
    have hcast : ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs]
    have h : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
    exact abs_of_nonneg h

/-! ## Step 2: even-k case — ζ(-k) = 0 for even k ≥ 2 -/

/-- For `k` even with `k ≥ 2`, the value `ζ(-k) = 0` because `B_{k+1} = 0`
    (`k+1` is odd and `> 1`, so `bernoulli'_odd_eq_zero` applies). -/
theorem zeta_neg_nat_norm_even_eq_zero {k : ℕ} (hk_even : Even k) (hk : 2 ≤ k) :
    ‖riemannZeta (-(k : ℂ))‖ = 0 := by
  rw [zeta_neg_nat_norm_eq_bernoulli]
  have hk1_odd : Odd (k + 1) := Even.add_one hk_even
  have hk1_gt1 : 1 < k + 1 := by omega
  -- bernoulli n = (-1)^n * bernoulli' n; bernoulli' (k+1) = 0 for odd k+1 > 1.
  have hb' : bernoulli' (k + 1) = 0 := bernoulli'_odd_eq_zero hk1_odd hk1_gt1
  have hb : bernoulli (k + 1) = 0 := by
    rw [bernoulli, hb']
    simp
  rw [hb]
  push_cast
  simp

/-! ## Step 3: odd-k case — bound from `bernoulli_growth_bound_explicit` -/

/-- For `k = 2m - 1` odd with `m ≥ 1` (so `k ≥ 1`), the bound holds.
    Here we write `k+1 = 2m`. -/
theorem zeta_neg_nat_norm_odd_bound {m : ℕ} (hm : 1 ≤ m) :
    ‖riemannZeta (-((2 * m - 1 : ℕ) : ℂ))‖ ≤
      (Real.pi / 6) * ((2 * m - 1 : ℕ).factorial : ℝ) /
        (2 * Real.pi) ^ (2 * m - 1) := by
  -- Let k = 2m-1, so k+1 = 2m.
  set k : ℕ := 2 * m - 1 with hk_def
  have hm_pos : 0 < 2 * m := by omega
  have hk1 : k + 1 = 2 * m := by
    rw [hk_def]; omega
  -- Apply zeta_neg_nat_norm_eq_bernoulli at k.
  rw [zeta_neg_nat_norm_eq_bernoulli]
  -- Now goal: |B_{k+1}| / ((k : ℝ) + 1) ≤ (π/6) * k! / (2π)^k.
  -- Substitute k+1 = 2m on the Bernoulli index.
  rw [show k + 1 = 2 * m from hk1]
  -- Goal: |B_{2m}| / ((k : ℝ) + 1) ≤ (π/6) * k! / (2π)^k where k = 2m - 1.
  -- bernoulli_growth_bound_explicit: |B_{2m}| ≤ (π²/3) * (2m)! / (2π)^{2m}.
  have hB := bernoulli_growth_bound_explicit hm
  -- hB: |B_{2m}| ≤ (π²/3) * (2m)! / (2π)^{2m}
  -- Divide both sides by 2m > 0:
  have h2m_pos : (0 : ℝ) < (2 * m : ℕ) := by
    have : 0 < 2 * m := hm_pos
    exact_mod_cast this
  -- The cast of (2*m : ℕ) = ((2 : ℕ) * m : ℕ) into ℝ.
  have h2m_eq : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
  have h2m_pos' : (0 : ℝ) < 2 * (m : ℝ) := by rw [← h2m_eq]; exact h2m_pos
  -- Step A: |B_{2m}| / (2m) ≤ (π²/3) * (2m)! / ((2π)^{2m} * (2m)).
  have hstep1 : |(bernoulli (2 * m) : ℝ)| / ((2 * m : ℕ) : ℝ)
      ≤ ((Real.pi ^ 2 / 3) * ((2 * m).factorial : ℝ) / (2 * Real.pi) ^ (2 * m))
        / ((2 * m : ℕ) : ℝ) :=
    div_le_div_of_nonneg_right hB h2m_pos.le
  -- Step B: arithmetic rearrangement.
  -- (2m)! = (2m) * (2m-1)! = (2m) * k!  (since k = 2m-1).
  have hfact_eq : ((2 * m).factorial : ℝ) = (2 * m : ℕ) * ((2 * m - 1).factorial : ℝ) := by
    have h : (2 * m).factorial = (2 * m) * (2 * m - 1).factorial := by
      have hsucc : 2 * m = (2 * m - 1) + 1 := by omega
      conv_lhs => rw [hsucc]
      rw [Nat.factorial_succ]
      have heq : (2 * m - 1) + 1 = 2 * m := by omega
      rw [heq]
    exact_mod_cast h
  -- (2π)^{2m} = (2π) * (2π)^{2m-1}.
  have h2pi_pow_eq : (2 * Real.pi) ^ (2 * m) = (2 * Real.pi) * (2 * Real.pi) ^ (2 * m - 1) := by
    have hsucc : 2 * m = (2 * m - 1) + 1 := by omega
    conv_lhs => rw [hsucc]
    rw [pow_succ]
    ring
  -- Now compute the RHS of hstep1.
  -- (π²/3) * (2m)! / (2π)^{2m} / (2m)
  --   = (π²/3) * (2m) * (2m-1)! / ((2π) * (2π)^{2m-1}) / (2m)
  --   = (π²/3) / (2π) * (2m-1)! / (2π)^{2m-1}
  --   = (π/6) * (2m-1)! / (2π)^{2m-1}    [since π²/(3·2π) = π/6]
  have hRHS_eq :
      ((Real.pi ^ 2 / 3) * ((2 * m).factorial : ℝ) / (2 * Real.pi) ^ (2 * m))
        / ((2 * m : ℕ) : ℝ)
      = (Real.pi / 6) * ((2 * m - 1).factorial : ℝ) / (2 * Real.pi) ^ (2 * m - 1) := by
    rw [hfact_eq, h2pi_pow_eq, h2m_eq]
    have h2m_ne : (2 * (m : ℝ)) ≠ 0 := h2m_pos'.ne'
    have h2pi_ne : (2 * Real.pi) ≠ 0 := by positivity
    have h2pi_pow_ne : ((2 * Real.pi) ^ (2 * m - 1)) ≠ 0 := by positivity
    field_simp
    ring
  rw [hRHS_eq] at hstep1
  -- hstep1: |B_{2m}| / ((2*m : ℕ) : ℝ) ≤ (π/6) * (2m-1)! / (2π)^(2m-1).
  -- Goal (LHS of the theorem, after rw [zeta_neg_nat_norm_eq_bernoulli] then rw [hk1]):
  --   |B_{2m}| / ((k : ℝ) + 1) ≤ (π/6) * k! / (2π)^k    where k = 2m - 1
  -- Bridge LHS: (k : ℝ) + 1 = ((2*m : ℕ) : ℝ).
  have hLHS_cast : ((k : ℝ) + 1) = ((2 * m : ℕ) : ℝ) := by
    rw [hk_def]
    have h1 : (((2 * m - 1 : ℕ) : ℝ) + 1) = ((2 * m - 1 + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [h1]
    have heq : (2 * m - 1) + 1 = 2 * m := by omega
    rw [heq]
  rw [hLHS_cast]
  exact hstep1

/-! ## Step 4: the unconditional discharge for s = 0 -/

/-- **MAIN THEOREM**: `ZetaShiftPolyExpBound 0` is unconditionally true,
    axiom-free.

    Concrete witnesses: `A = π/6`, `d = 0`, `K = 1`. For every `k ≥ 1`:
    * `k` odd ⇒ `k = 2m - 1` for some `m ≥ 1` ⇒
      `‖ζ(-k)‖ ≤ (π/6) · k!/(2π)^k`.
    * `k` even with `k ≥ 2` ⇒ `B_{k+1} = 0` ⇒
      `‖ζ(-k)‖ = 0 ≤ (π/6) · k!/(2π)^k`.

    The `s = 0` substitution: `s - k = -k`, so `ζ(s - k) = ζ(-k)`. -/
theorem zetaShiftPolyExpBound_zero : ZetaShiftPolyExpBound 0 := by
  refine ⟨Real.pi / 6, by positivity, 0, 1, ?_⟩
  intro k hk
  -- Goal: ‖ζ(0 - k)‖ ≤ (π/6) * (k+1)^0 * k! / (2π)^k
  -- Simplify (k+1)^0 = 1 and 0 - k = -k.
  have hsub : (0 : ℂ) - (k : ℂ) = -(k : ℂ) := by ring
  rw [hsub]
  simp only [pow_zero, mul_one]
  -- Now: ‖ζ(-k)‖ ≤ (π/6) * k! / (2π)^k.
  -- Case-split on parity of k.
  rcases Nat.even_or_odd k with hk_even | hk_odd
  · -- Even k. We need k ≥ 2 for bernoulli to vanish; k = 0 is excluded by hk.
    -- k ≥ 1 even ⇒ k ≥ 2.
    have hk2 : 2 ≤ k := by
      rcases Nat.lt_or_ge k 2 with hlt | hge
      · -- k < 2 and k ≥ 1 ⇒ k = 1. But hk_even says Even k.
        interval_cases k
        exact absurd hk_even (by decide)
      · exact hge
    rw [zeta_neg_nat_norm_even_eq_zero hk_even hk2]
    positivity
  · -- Odd k. Write k = 2m - 1 with m ≥ 1.
    obtain ⟨m, hm_eq⟩ := hk_odd
    -- hm_eq : k = 2 * m + 1.
    -- So k + 1 = 2 * (m + 1), i.e., k = 2 * (m+1) - 1.
    set m' := m + 1 with hm'_def
    have hk_eq : k = 2 * m' - 1 := by
      simp [hm'_def, hm_eq, Nat.mul_succ]
    have hm'_pos : 1 ≤ m' := by rw [hm'_def]; omega
    have hbound := zeta_neg_nat_norm_odd_bound hm'_pos
    -- hbound: ‖ζ(-(2*m' - 1))‖ ≤ (π/6) * (2*m' - 1)!/(2π)^(2*m' - 1)
    -- which equals goal after substituting k = 2m' - 1.
    rw [hk_eq]
    exact hbound

/-! ## Step 5: unconditional capstone -/

/-- **HEADLINE CAPSTONE (axiom-free, no `sorry`)**: at `s = 0`, the
    Jonquières ζ-series is analytic on the convergence subdomain
    `JonquieresAnalyticDomain ∩ {z | ‖log z‖ < 2π}` **unconditionally**.

    No named hypothesis required: the `ZetaShiftPolyExpBound 0` residual
    is discharged here directly via `riemannZeta_neg_nat_eq_bernoulli`
    + the proven `bernoulli_growth_bound_explicit`. -/
theorem jonquieresZetaSeries_analyticOnNhd_zero_unconditional :
    AnalyticOnNhd ℂ (jonquieresZetaSeries 0)
      (JonquieresAnalyticDomain ∩ {z : ℂ | ‖Complex.log z‖ < 2 * Real.pi}) :=
  jonquieresZetaSeries_analyticOnNhd_of_zetaShiftPolyExpBound
    zetaShiftPolyExpBound_zero

/-- **Companion capstone**: the full Jonquières expansion at `s = 0`
    is analytic on the convergence subdomain, unconditionally. -/
theorem jonquieresExpansion_analyticOnNhd_zero_unconditional :
    AnalyticOnNhd ℂ (jonquieresExpansion 0)
      (JonquieresAnalyticDomain ∩ {z : ℂ | ‖Complex.log z‖ < 2 * Real.pi}) :=
  jonquieresExpansion_analyticOnNhd_of_zetaShiftPolyExpBound
    zetaShiftPolyExpBound_zero

/-- **Companion capstone**: the `JonquieresZetaSeriesAnalyticityHypothesis`
    at `s = 0` is discharged unconditionally. -/
theorem JonquieresZetaSeriesAnalyticityHypothesis_zero :
    JonquieresZetaSeriesAnalyticityHypothesis 0 :=
  JonquieresZetaSeriesAnalyticityHypothesis_of_zetaShiftPolyExpBound
    zetaShiftPolyExpBound_zero

/-! ## Architecture summary

**This file establishes (axiom-free, no sorry)**:

* `zeta_neg_nat_norm_eq_bernoulli` — exact rewrite of `‖ζ(-k)‖` via
  the Bernoulli closed form `(-1)^k · B_{k+1}/(k+1)`.
* `zeta_neg_nat_norm_even_eq_zero` — even `k ≥ 2` ⇒ `‖ζ(-k)‖ = 0`
  via `bernoulli'_odd_eq_zero`.
* `zeta_neg_nat_norm_odd_bound` — odd `k = 2m - 1` (m ≥ 1) ⇒
  `‖ζ(-k)‖ ≤ (π/6) · k!/(2π)^k` via the proven
  `bernoulli_growth_bound_explicit`.
* `zetaShiftPolyExpBound_zero` — **THE DISCHARGE**: `ZetaShiftPolyExpBound 0`
  is unconditionally true. Witnesses `A = π/6`, `d = 0`, `K = 1`.
* `jonquieresZetaSeries_analyticOnNhd_zero_unconditional`,
  `jonquieresExpansion_analyticOnNhd_zero_unconditional`,
  `JonquieresZetaSeriesAnalyticityHypothesis_zero` — unconditional
  capstones at `s = 0` for the full analyticity chain.

**Status**:
The `s = 0` base case of `ZetaShiftPolyExpBound` is now a THEOREM, not a
named residual. For general complex `s`, the residual remains open —
its proof requires the ζ functional equation + Stirling for `Γ(1+k-s)`
+ uniform sin bound + `ζ(1+k-s) ≤ ζ(2)` for large k. The `s = 0`
discharge above is the only `s` value where the bound reduces to
mathlib's existing Bernoulli identity without the functional-equation
detour. Extension paths to `s = -N` for any nonneg integer `N` would
follow analogously (`ζ(-N - k) = ζ(-(N+k))` ⇒ apply the same Bernoulli
identity at index `N+k`).

Stage L15 — `ZetaShiftPolyExpBound` discharge at the integer base point.
-/

end PrincipiaTractalis.Analytic.Sheaf
