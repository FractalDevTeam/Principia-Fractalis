/-
# Polylogarithm — Foundational Definition and Convergence

The polylogarithm is the complex-valued function

  Li_s(z) := Σ_{n=1}^∞ z^n / n^s

defined initially on the open unit disk `|z| < 1` for any complex `s`,
and extended by analytic continuation to a larger domain via the
Jonquières expansion (not implemented here).

The book's `fractal_continuation_derivation.py` identifies the P-class
ground-state eigenvalue with a polylog value:

  λ_0(H_P) = π/(10√2) = Re[Li_{s*}^{[m*]}(e^{iπ√2})]

for specific `s* ≈ 0.182, m* = -1` (a non-principal Riemann sheet).
Formalizing this identity is the analytic-number-theory finale of the
L4 retirement path.

This file establishes the **foundation**: the polylogarithm as a tsum
on `ℕ` (with the n=0 term zero, indexed via the `n+1` shift), with
convergence on the open unit disk for `Re s ≥ 0`.

Stage L4 — polylogarithm foundation.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.InfiniteSum

namespace PrincipiaTractalis.Analytic

open Complex

/-! ## Definition -/

/-- **The polylogarithm** `Li_s(z) := Σ_{n=1}^∞ z^n / n^s`, defined via the
    `n+1` shift over `ℕ` so the n=0 term contributes `z^1 / 1^s = z / 1 = z`
    (rather than the singular `z^0 / 0^s`). -/
noncomputable def polyLog (s : ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) ^ s

/-! ## Basic value at zero -/

/-- `Li_s(0) = 0` for any `s` (every term has factor `z^(n+1) = 0`). -/
theorem polyLog_zero (s : ℂ) : polyLog s 0 = 0 := by
  unfold polyLog
  -- Each summand is 0 since z = 0 ⟹ z^(n+1) = 0
  have h_zero : ∀ n : ℕ, (0 : ℂ) ^ (n + 1) / ((n + 1 : ℕ) : ℂ) ^ s = 0 := by
    intro n
    rw [zero_pow (Nat.succ_ne_zero n), zero_div]
  simp_rw [h_zero]
  exact tsum_zero

/-! ## Convergence on the open unit disk for `Re s ≥ 0`

The summand `‖z^(n+1) / (n+1)^s‖` is bounded by `‖z‖^(n+1)` (when `Re s ≥ 0`),
since `‖(n+1)^s‖ = (n+1)^{Re s} ≥ 1`. The geometric series `Σ ‖z‖^(n+1)`
converges for `‖z‖ < 1`, so the polylog series converges absolutely. -/

/-- Termwise norm bound: `‖z^(n+1) / (n+1)^s‖ ≤ ‖z‖^(n+1)` when `Re s ≥ 0`. -/
theorem norm_polyLog_term_le
    {s z : ℂ} (hs : 0 ≤ s.re) (n : ℕ) :
    ‖z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) ^ s‖ ≤ ‖z‖ ^ (n + 1) := by
  -- ‖z^(n+1)‖ = ‖z‖^(n+1)
  rw [norm_div, norm_pow]
  -- ‖((n+1):ℂ)^s‖ = (n+1)^Re(s) ≥ 1 since n+1 ≥ 1 and Re s ≥ 0
  have h_pos : (0 : ℝ) < (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
  have h_norm : ‖((n + 1 : ℕ) : ℂ) ^ s‖ = (n + 1 : ℕ) ^ s.re := by
    rw [show (((n + 1 : ℕ) : ℂ) : ℂ) = (((n + 1 : ℕ) : ℝ) : ℂ) from by
      norm_cast]
    exact Complex.norm_cpow_eq_rpow_re_of_pos h_pos s
  rw [h_norm]
  -- Goal: ‖z‖^(n+1) / (n+1)^Re(s) ≤ ‖z‖^(n+1)
  -- (n+1)^Re(s) ≥ 1, so dividing by it gives a value ≤ ‖z‖^(n+1)
  have h_denom_ge_one : (1 : ℝ) ≤ (n + 1 : ℕ) ^ s.re := by
    have h_base_ge_one : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
    exact Real.one_le_rpow h_base_ge_one hs
  have h_norm_z_nn : 0 ≤ ‖z‖ ^ (n + 1) := pow_nonneg (norm_nonneg _) _
  calc ‖z‖ ^ (n + 1) / (n + 1 : ℕ) ^ s.re
      ≤ ‖z‖ ^ (n + 1) / 1 := by
        apply div_le_div_of_nonneg_left h_norm_z_nn (by norm_num) h_denom_ge_one
    _ = ‖z‖ ^ (n + 1) := by rw [div_one]

/-- **The polylog series is summable** when `‖z‖ < 1` and `Re s ≥ 0`. -/
theorem summable_polyLog_term
    {s z : ℂ} (hs : 0 ≤ s.re) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) ^ s) := by
  -- Bound by ‖z‖^(n+1), which sums (geometric)
  apply Summable.of_norm_bounded (g := fun n => ‖z‖ ^ (n + 1))
  · -- Geometric series Σ ‖z‖^(n+1) converges
    have h_summ_geom : Summable (fun n : ℕ => ‖z‖ ^ n) :=
      summable_geometric_of_lt_one (norm_nonneg _) hz
    -- Σ_n ‖z‖^(n+1) = ‖z‖ · Σ_n ‖z‖^n, so Summable
    have : (fun n : ℕ => ‖z‖ ^ (n + 1)) = (fun n => ‖z‖ * ‖z‖ ^ n) := by
      funext n; rw [pow_succ, mul_comm]
    rw [this]
    exact h_summ_geom.mul_left _
  · intro n
    exact norm_polyLog_term_le hs n

/-! ## Convergence-summable bridge

Combine the two facts to express the polylog directly as a convergent
series with bounded norm. -/

/-- The polylog as a `HasSum` statement (when convergent). -/
theorem hasSum_polyLog
    {s z : ℂ} (hs : 0 ≤ s.re) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) ^ s) (polyLog s z) :=
  (summable_polyLog_term hs hz).hasSum

end PrincipiaTractalis.Analytic
