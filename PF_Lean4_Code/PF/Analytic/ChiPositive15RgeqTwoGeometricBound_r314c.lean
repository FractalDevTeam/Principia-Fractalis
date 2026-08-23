/-
# r314c: Pointwise geometric bound `tail(y) ≤ 2·exp(−4πy)/(1 − exp(−4π))` for `y ≥ 1`

★ 2026-08-22 r314c — pointwise geometric domination of the theta tail.
Establishes: `∀ y ≥ 1, tail(y) ≤ 2·exp(−4πy)/(1 − exp(−4π))`.

## Route

- Shift r313's `hasSum_evenKernel_zero_sub_one` at `n ↦ n + 1` via
  `hasSum_nat_add_iff 1` to obtain
    `HasSum (fun n : ℕ => 2·exp(−π · (n+2)² · y)) (tail y)`
  for `y > 0`.

- Termwise domination: `∀ n : ℕ, y ≥ 1 → 2·exp(−π(n+2)²·y) ≤ 2·exp(−4πy) · (exp(−4π))^n`.
  Uses `(n+2)² ≥ 4 + 4n` (proof: `(n+2)² = n² + 4n + 4 ≥ 4n + 4` since `n² ≥ 0`),
  then `π(n+2)²·y ≥ π(4 + 4n)·y = 4πy + 4πn·y ≥ 4πy + 4πn` (for `y ≥ 1`), so
  `exp(−π(n+2)²·y) ≤ exp(−4πy − 4πn) = exp(−4πy) · exp(−4π·n) = exp(−4πy) · (exp(−4π))^n`.

- Geometric HasSum: `HasSum (fun n : ℕ => (exp(−4π))^n) (1/(1 − exp(−4π)))` via
  `hasSum_geometric_of_lt_one` (needs `0 ≤ exp(−4π) < 1`).

- Combine via `Summable.tsum_le_tsum`: `tail(y) = ∑' n, 2·exp(−π(n+2)²·y) ≤
  ∑' n, 2·exp(−4πy)·(exp(−4π))^n = 2·exp(−4πy)/(1 − exp(−4π))`.

## Framework-first status (per MASTER DIRECTIVE)

NOT a numerical discharge. Pointwise geometric bound. Establishes the
exponential decay rate for the theta tail necessary for the integrable
domination in r314d.

Standing rules absolute: no `sorry`, no `native_decide`, no floating-point-as-proof,
no hidden oracle, no assumed transcendental enclosure.

## What r314c delivers

- `hasSum_tail_shifted` : `HasSum (fun n : ℕ => 2·exp(−π(n+2)²·y)) (tail y)` for `y > 0`.
- `sq_add_two_ge` : `∀ n : ℕ, (n + 2)^2 ≥ 4 + 4·n` (elementary).
- `exp_neg_four_pi_lt_one` : `0 ≤ exp(−4π) < 1`.
- `termwise_tail_bound` : `∀ y ≥ 1, ∀ n : ℕ, 2·exp(−π(n+2)²·y) ≤ 2·exp(−4πy)·(exp(−4π))^n`.
- `tail_le_geometric_dominator` : `∀ y ≥ 1, tail(y) ≤ 2·exp(−4πy)/(1 − exp(−4π))`.

## r314d direction

Integrate `tail·y^(-3/4) ≤ (2·exp(-4πy)/(1-exp(-4π))) · y^(-3/4)` on `Ioi 1` via
`setIntegral_mono_on` + `integral_const_mul` + `∫ exp(-4πy)·y^(-3/4) ≤ ∫ exp(-4πy) = exp(-4π)/(4π)`.
Endpoint: `|R_geq_2| ≤ exp(−4π)/(2π·(1 − exp(−4π)))`.

Book anchors: Ch 20 § 20.4, Ch 34A § 34A.5.
-/

import PF.Analytic.ChiPositive15RgeqTwoPointwiseBound_r314b
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace PrincipiaTractalis.ChiPositive15RgeqTwoGeometricBound

open MeasureTheory Set Real
open HurwitzZeta
open PrincipiaTractalis.ChiPositive15ThetaTruncation
open PrincipiaTractalis.ChiPositive15RgeqTwoIntegralForm
open PrincipiaTractalis.ChiPositive15RgeqTwoPointwiseBound

/-! ## §1 HasSum of the shifted tail series. -/

/-- **`hasSum_tail_shifted`** — for `y > 0`,

  `HasSum (fun n : ℕ => 2·exp(−π · (n + 2)² · y)) (tail y)`.

Via `hasSum_nat_add_iff 1` applied to r313's `hasSum_evenKernel_zero_sub_one`,
peeling off the `n = 0` term (which is `2·exp(−π·1²·y) = 2·exp(−π·y)`, matching
the `−2·exp(−π·y)` correction defining `tail`). -/
theorem hasSum_tail_shifted {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℕ => 2 * Real.exp (-Real.pi * ((n : ℝ) + 2)^2 * y)) (tail y) := by
  have h_orig := hasSum_evenKernel_zero_sub_one hy
  -- h_orig : HasSum (fun n => 2 * rexp (-π * (n+1)² * y)) (evenKernel 0 y - 1)
  -- Apply hasSum_nat_add_iff 1: HasSum (fun n => f (n+1)) g ↔ HasSum f (g + f 0)
  -- With f n = 2 * rexp (-π * (n+1)² * y), f 0 = 2 * rexp (-π * y).
  -- Setting g = tail y = evenKernel 0 y - 1 - 2 * rexp (-π * y):
  --   g + f 0 = evenKernel 0 y - 1 ✓ (matches h_orig).
  -- So HasSum (fun n => f (n+1)) (tail y). And f (n+1) = 2 * rexp (-π * (n+2)² * y).
  have h_shifted := (hasSum_nat_add_iff (f := fun n : ℕ => 2 * Real.exp (-Real.pi * ((n : ℝ) + 1)^2 * y))
                     (g := tail y) 1).mpr ?_
  · -- Convert (fun n => f (n+1)) to (fun n => 2 * rexp (-π * (n+2)² * y))
    convert h_shifted using 1
    funext n
    push_cast
    ring_nf
  · -- Show: HasSum f (tail y + ∑ i ∈ range 1, f i) = HasSum f (evenKernel 0 y - 1)
    convert h_orig using 1
    -- Need: tail y + ∑ i ∈ range 1, 2 * rexp (-π * (i+1)² * y) = evenKernel 0 y - 1
    simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, one_pow, mul_one]
    unfold tail
    ring

/-! ## §2 Elementary inequality `(n + 2)² ≥ 4 + 4·n`. -/

/-- **`sq_add_two_ge`** — `∀ n : ℕ, ((n : ℝ) + 2)^2 ≥ 4 + 4·n`.

Elementary: `(n + 2)² = n² + 4n + 4 ≥ 4n + 4` since `n² ≥ 0`. -/
theorem sq_add_two_ge (n : ℕ) : ((n : ℝ) + 2)^2 ≥ 4 + 4 * n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [sq_nonneg ((n : ℝ))]

/-! ## §3 `0 ≤ exp(−4π) < 1`. -/

/-- **`exp_neg_four_pi_nonneg`** — `0 ≤ exp(−4π)`. -/
theorem exp_neg_four_pi_nonneg : 0 ≤ Real.exp (-(4 * Real.pi)) := (Real.exp_pos _).le

/-- **`exp_neg_four_pi_lt_one`** — `exp(−4π) < 1`. -/
theorem exp_neg_four_pi_lt_one : Real.exp (-(4 * Real.pi)) < 1 := by
  rw [Real.exp_lt_one_iff]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  linarith

/-- **`one_sub_exp_neg_four_pi_pos`** — `0 < 1 − exp(−4π)`. -/
theorem one_sub_exp_neg_four_pi_pos : 0 < 1 - Real.exp (-(4 * Real.pi)) := by
  linarith [exp_neg_four_pi_lt_one]

/-! ## §4 Termwise bound `2·exp(−π(n+2)²·y) ≤ 2·exp(−4πy)·(exp(−4π))^n`. -/

/-- **`termwise_tail_bound`** — for `y ≥ 1` and any `n : ℕ`,

  `2·exp(−π·(n+2)²·y) ≤ 2·exp(−4πy) · (exp(−4π))^n`.

Uses `(n+2)² ≥ 4 + 4n` and `y ≥ 1`:
`π(n+2)²y ≥ π(4 + 4n)y = 4πy + 4πny ≥ 4πy + 4πn`. -/
theorem termwise_tail_bound {y : ℝ} (hy : 1 ≤ y) (n : ℕ) :
    2 * Real.exp (-Real.pi * ((n : ℝ) + 2)^2 * y)
      ≤ 2 * Real.exp (-(4 * Real.pi * y)) * (Real.exp (-(4 * Real.pi)))^n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hy_pos : (0 : ℝ) < y := lt_of_lt_of_le zero_lt_one hy
  -- Reduce to bounds on exp arguments.
  -- Claim: -π·(n+2)²·y ≤ -(4·π·y) - 4·π·n
  -- Equivalently: π·(n+2)²·y ≥ 4·π·y + 4·π·n
  have h_sq := sq_add_two_ge n
  have h_exp_arg :
      Real.pi * ((n : ℝ) + 2)^2 * y ≥ 4 * Real.pi * y + 4 * Real.pi * n := by
    have h1 : Real.pi * ((n : ℝ) + 2)^2 * y ≥ Real.pi * (4 + 4 * n) * y := by
      apply mul_le_mul_of_nonneg_right _ hy_pos.le
      apply mul_le_mul_of_nonneg_left h_sq hpi.le
    have h2 : Real.pi * (4 + 4 * n) * y = 4 * Real.pi * y + 4 * Real.pi * n * y := by ring
    have h3 : 4 * Real.pi * n * y ≥ 4 * Real.pi * n := by
      have : 4 * Real.pi * n ≥ 0 := by positivity
      nlinarith
    linarith
  -- Now: exp(-π(n+2)²y) ≤ exp(-(4πy) - 4πn)
  have h_exp_bound :
      Real.exp (-Real.pi * ((n : ℝ) + 2)^2 * y)
        ≤ Real.exp (-(4 * Real.pi * y) - 4 * Real.pi * n) := by
    apply Real.exp_le_exp.mpr
    linarith
  -- exp(-(4πy) - 4πn) = exp(-(4πy)) * exp(-(4πn)) = exp(-(4πy)) * (exp(-4π))^n
  have h_rewrite :
      Real.exp (-(4 * Real.pi * y) - 4 * Real.pi * n)
        = Real.exp (-(4 * Real.pi * y)) * (Real.exp (-(4 * Real.pi)))^n := by
    rw [sub_eq_add_neg, Real.exp_add]
    congr 1
    rw [show -(4 * Real.pi * n) = n * -(4 * Real.pi) from by ring, Real.exp_nat_mul]
  rw [h_rewrite] at h_exp_bound
  -- Multiply both sides by 2 (positive)
  have h_two_pos : (0 : ℝ) < 2 := by norm_num
  linarith [mul_le_mul_of_nonneg_left h_exp_bound h_two_pos.le]

/-! ## §5 Geometric HasSum. -/

/-- **`hasSum_geometric_exp_neg_four_pi`** — `HasSum (fun n : ℕ => (exp(−4π))^n) (1 / (1 − exp(−4π)))`. -/
theorem hasSum_geometric_exp_neg_four_pi :
    HasSum (fun n : ℕ => (Real.exp (-(4 * Real.pi)))^n) (1 / (1 - Real.exp (-(4 * Real.pi)))) := by
  have h := hasSum_geometric_of_lt_one exp_neg_four_pi_nonneg exp_neg_four_pi_lt_one
  rw [one_div]
  exact h

/-- **`hasSum_two_exp_geometric`** — for `y ≥ 1`,

  `HasSum (fun n : ℕ => 2·exp(−4πy) · (exp(−4π))^n) (2·exp(−4πy)/(1 − exp(−4π)))`. -/
theorem hasSum_two_exp_geometric {y : ℝ} (_hy : 1 ≤ y) :
    HasSum (fun n : ℕ => 2 * Real.exp (-(4 * Real.pi * y)) * (Real.exp (-(4 * Real.pi)))^n)
           (2 * Real.exp (-(4 * Real.pi * y)) / (1 - Real.exp (-(4 * Real.pi)))) := by
  have h_geom := hasSum_geometric_exp_neg_four_pi
  have := h_geom.mul_left (2 * Real.exp (-(4 * Real.pi * y)))
  convert this using 1
  rw [mul_one_div]

/-! ## §6 THE r314c CORE BOUND. -/

/-- **`tail_le_geometric_dominator`** — THE r314c CORE POINTWISE BOUND:

  `∀ y ≥ 1, tail(y) ≤ 2·exp(−4πy) / (1 − exp(−4π))`.

Combines §1 (`hasSum_tail_shifted`), §4 (termwise bound), and §5 (geometric
HasSum) via `Summable.tsum_le_tsum` (or `HasSum.hasSum`). -/
theorem tail_le_geometric_dominator {y : ℝ} (hy : 1 ≤ y) :
    tail y ≤ 2 * Real.exp (-(4 * Real.pi * y)) / (1 - Real.exp (-(4 * Real.pi))) := by
  have hy_pos : (0 : ℝ) < y := lt_of_lt_of_le zero_lt_one hy
  have h_tail := hasSum_tail_shifted hy_pos
  have h_geom := hasSum_two_exp_geometric hy
  have h_termwise : ∀ n : ℕ,
      2 * Real.exp (-Real.pi * ((n : ℝ) + 2)^2 * y)
        ≤ 2 * Real.exp (-(4 * Real.pi * y)) * (Real.exp (-(4 * Real.pi)))^n :=
    fun n => termwise_tail_bound hy n
  -- Use hasSum_le: given both HasSum and termwise bound, sums are ordered.
  exact hasSum_le h_termwise h_tail h_geom

/-! ## §7 Axiom checks. -/

#print axioms
  PrincipiaTractalis.ChiPositive15RgeqTwoGeometricBound.hasSum_tail_shifted
#print axioms
  PrincipiaTractalis.ChiPositive15RgeqTwoGeometricBound.sq_add_two_ge
#print axioms
  PrincipiaTractalis.ChiPositive15RgeqTwoGeometricBound.exp_neg_four_pi_lt_one
#print axioms
  PrincipiaTractalis.ChiPositive15RgeqTwoGeometricBound.termwise_tail_bound
#print axioms
  PrincipiaTractalis.ChiPositive15RgeqTwoGeometricBound.hasSum_two_exp_geometric
#print axioms
  PrincipiaTractalis.ChiPositive15RgeqTwoGeometricBound.tail_le_geometric_dominator

end PrincipiaTractalis.ChiPositive15RgeqTwoGeometricBound
