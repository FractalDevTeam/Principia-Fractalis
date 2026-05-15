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
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Calculus.SmoothSeries

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

/-! ## Closed-form identity: `Li_0(z) = z / (1 - z)` on the open unit disk

The simplest polylog: at `s = 0`, the denominator `(n+1)^0 = 1`, so
the series reduces to the geometric series `Σ z^(n+1) = z / (1 − z)`. -/

/-- **`Li_0(z) = z / (1 − z)` for `‖z‖ < 1`.** Direct consequence of the
    geometric series `Σ z^n = 1/(1−z)`. -/
theorem polyLog_zero_exponent (z : ℂ) (hz : ‖z‖ < 1) :
    polyLog 0 z = z / (1 - z) := by
  unfold polyLog
  -- For s = 0: (n+1)^0 = 1, so each term is z^(n+1).
  have h_term : ∀ n : ℕ,
      z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) ^ (0 : ℂ) = z ^ (n + 1) := by
    intro n
    rw [cpow_zero, div_one]
  simp_rw [h_term]
  -- Σ' n, z^(n+1) = z · Σ' n, z^n = z · 1/(1-z) = z/(1-z)
  have h_factor : ∀ n : ℕ, z ^ (n + 1) = z * z ^ n := by
    intro n; rw [pow_succ, mul_comm]
  simp_rw [h_factor]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hz]
  rw [show (1 : ℂ) - z = -(z - 1) from by ring]
  field_simp

/-! ## Continuity at z = 0 and basic structural properties

The polylog is continuous (in fact analytic) on the open unit disk. We
prove the simplest consequence: the polylog can be expressed as a
limit of partial sums. -/

/-- The polylog as the limit of partial sums on the open unit disk
    for `Re s ≥ 0`. -/
theorem polyLog_eq_tendsto_partial_sum
    {s z : ℂ} (hs : 0 ≤ s.re) (hz : ‖z‖ < 1) :
    Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) ^ s)
      Filter.atTop (nhds (polyLog s z)) := by
  exact (hasSum_polyLog hs hz).tendsto_sum_nat

/-! ## `Li_1(z) = −log(1 − z)` (the Mercator identity) — partial-sum step

The substantive combinatorial identity: the polylog partial sum at `s = 1`
equals minus the mathlib Taylor polynomial of `log(1 + w)` evaluated at
`w = −z`. The sign manipulation collapses the alternating-sign Mercator
coefficient with the `−z` substitution. -/

/-- **Partial-sum bridge** for `Li_1`:
    `Σ_{n < N} z^(n+1) / (n+1) = −Complex.logTaylor (N+1) (−z)`.

    Proof by induction on `N`. The step uses `Complex.logTaylor_succ`
    targeted at `logTaylor (N+1+1)` (via `conv`) to expose the extra term,
    then verifies the per-step increment via the sign identity
    `(−1)^(N+2) · (−z)^(N+1) = −z^(N+1)`. -/
theorem partial_polyLog_one_eq_neg_logTaylor (z : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range N, z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) =
      -Complex.logTaylor (N + 1) (-z) := by
  induction N with
  | zero =>
    -- LHS = 0 (empty sum). RHS = -logTaylor 1 (-z) = -(j=0 term) = -((-1)·1/0) = 0.
    simp [Complex.logTaylor]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    -- Goal: -logTaylor(N+1)(-z) + z^(N+1)/((N+1):ℕ:ℂ) = -logTaylor(N+1+1)(-z)
    -- Use logTaylor_succ at the RHS only, via conv
    conv_rhs => rw [show N + 1 + 1 = (N + 1) + 1 from rfl, Complex.logTaylor_succ]
    -- After conv: -logTaylor(N+1)(-z) + z^(N+1)/(N+1) = -(logTaylor(N+1) + extra)(-z)
    simp only [Pi.add_apply]
    -- Now: -logTaylor(N+1)(-z) + z^(N+1)/(N+1) = -(logTaylor(N+1)(-z) + (-1)^(N+1+1) · (-z)^(N+1) / (N+1))
    -- Rearrange: cancel -logTaylor(N+1)(-z) from both sides, need to show
    -- z^(N+1)/(N+1) = -((-1)^(N+1+1) · (-z)^(N+1) / (N+1))
    -- i.e. (-1)^(N+1+1) · (-z)^(N+1) = -z^(N+1)
    have h_sign : (-1 : ℂ) ^ (N + 1 + 1) * (-z) ^ (N + 1) = -(z ^ (N + 1)) := by
      rw [show (-z : ℂ) ^ (N + 1) = (-1 : ℂ) ^ (N + 1) * z ^ (N + 1) from neg_pow z (N + 1)]
      rw [← mul_assoc, ← pow_add]
      have h_eq : N + 1 + 1 + (N + 1) = 2 * (N + 1) + 1 := by ring
      rw [h_eq, pow_succ, pow_mul]
      simp
    -- Substitute h_sign into the goal
    have h_term : (-1 : ℂ) ^ (N + 1 + 1) * (-z) ^ (N + 1) / ((N + 1 : ℕ) : ℂ) =
                  -(z ^ (N + 1)) / ((N + 1 : ℕ) : ℂ) := by
      rw [h_sign]
    rw [h_term]
    ring

/-- **`Li_1(z) = −log(1 − z)` for `‖z‖ < 1`** (the Mercator series).

    Combine `partial_polyLog_one_eq_neg_logTaylor` (per-N equality) with
    `Complex.norm_log_sub_logTaylor_le` (giving `logTaylor(N+1)(−z) →
    log(1 − z)`), then `tendsto_nhds_unique` against
    `polyLog_eq_tendsto_partial_sum`. -/
theorem polyLog_one (z : ℂ) (hz : ‖z‖ < 1) :
    polyLog 1 z = -Complex.log (1 - z) := by
  have h_norm_neg : ‖(-z : ℂ)‖ < 1 := by rwa [norm_neg]
  -- Step 1: `logTaylor (N+1) (−z) → log(1 + (−z)) = log(1 − z)` as N → ∞.
  have h_tendsto_log :
      Filter.Tendsto
        (fun N : ℕ => Complex.logTaylor (N + 1) (-z))
        Filter.atTop (nhds (Complex.log (1 + (-z)))) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    -- The mathlib bound function tends to 0.
    have h_bound_tendsto :
        Filter.Tendsto
          (fun N : ℕ => ‖(-z : ℂ)‖ ^ (N + 1) * (1 - ‖(-z : ℂ)‖)⁻¹ / (N + 1 : ℝ))
          Filter.atTop (nhds 0) := by
      have h_pow_zero : Filter.Tendsto (fun N : ℕ => ‖(-z : ℂ)‖ ^ (N + 1))
          Filter.atTop (nhds 0) := by
        have h0 := tendsto_pow_atTop_nhds_zero_of_lt_one
          (norm_nonneg (-z : ℂ)) h_norm_neg
        exact h0.comp (Filter.tendsto_add_atTop_nat 1)
      have h_prod1 : Filter.Tendsto
          (fun N : ℕ => ‖(-z : ℂ)‖ ^ (N + 1) * (1 - ‖(-z : ℂ)‖)⁻¹)
          Filter.atTop (nhds 0) := by
        simpa using h_pow_zero.mul_const (1 - ‖(-z : ℂ)‖)⁻¹
      have h_div : Filter.Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)⁻¹)
          Filter.atTop (nhds 0) := by
        have := tendsto_one_div_add_atTop_nhds_zero_nat
        refine this.congr (fun N => ?_)
        push_cast; rw [one_div]
      have h_combined := h_prod1.mul h_div
      simp only [mul_zero] at h_combined
      refine h_combined.congr (fun N => ?_)
      rw [div_eq_mul_inv]
      push_cast
      ring
    obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp h_bound_tendsto ε hε
    refine ⟨N₀, fun N hN => ?_⟩
    have h_bnd := Complex.norm_log_sub_logTaylor_le N h_norm_neg
    rw [dist_eq_norm]
    have h_bnd_at_N := hN₀ N hN
    have h_nn : (0 : ℝ) ≤ ‖(-z : ℂ)‖ ^ (N + 1) * (1 - ‖(-z : ℂ)‖)⁻¹ / (N + 1) := by
      have h1 : (0 : ℝ) ≤ ‖(-z : ℂ)‖ ^ (N + 1) := pow_nonneg (norm_nonneg _) _
      have h2 : (0 : ℝ) ≤ (1 - ‖(-z : ℂ)‖)⁻¹ := by
        have : 0 < 1 - ‖(-z : ℂ)‖ := by linarith
        positivity
      have h3 : (0 : ℝ) ≤ (N + 1 : ℝ) := by positivity
      positivity
    rw [Real.dist_eq, sub_zero, abs_of_nonneg h_nn] at h_bnd_at_N
    calc ‖Complex.logTaylor (N + 1) (-z) - Complex.log (1 + -z)‖
        = ‖Complex.log (1 + -z) - Complex.logTaylor (N + 1) (-z)‖ := by
          rw [← norm_neg]; congr 1; ring
      _ ≤ ‖(-z : ℂ)‖ ^ (N + 1) * (1 - ‖(-z : ℂ)‖)⁻¹ / (N + 1) := h_bnd
      _ < ε := h_bnd_at_N
  -- Step 2: bridge the polylog partial sum to logTaylor convergence
  have h_tendsto_partial :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ n ∈ Finset.range N, z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) ^ (1 : ℂ))
        Filter.atTop (nhds (-Complex.log (1 + -z))) := by
    refine h_tendsto_log.neg.congr (fun N => ?_)
    rw [← partial_polyLog_one_eq_neg_logTaylor]
    apply Finset.sum_congr rfl
    intro n _
    rw [Complex.cpow_one]
  rw [show (1 : ℂ) + -z = 1 - z from by ring] at h_tendsto_partial
  -- Step 3: limit uniqueness against polyLog's own tendsto
  have h_polylog_tendsto := polyLog_eq_tendsto_partial_sum
    (show (0 : ℝ) ≤ (1 : ℂ).re from by simp) hz
  exact tendsto_nhds_unique h_polylog_tendsto h_tendsto_partial

/-! ## Derivative recurrence (concrete case): `d/dz Li_1(z) = Li_0(z) / z`

The general derivative recurrence is `d/dz Li_{s+1}(z) = Li_s(z) / z`. For
the specific case `s = 0` (giving `d/dz Li_1(z) = Li_0(z) / z`), we can
derive directly from the closed forms `Li_1(z) = −log(1 − z)` and
`Li_0(z) = z / (1 − z)`:

  `d/dz [−log(1 − z)] = (1 − z)⁻¹ = 1 / (1 − z) = Li_0(z) / z`. -/

/-- **Derivative of `Li_1`**: for `‖z‖ < 1`,
    `HasDerivAt (polyLog 1) (1/(1−z)) z`.

    Uses `polyLog_one` to identify `polyLog 1` with `−log(1 − ·)` in a
    neighborhood of `z`, then `Complex.hasDerivAt_log` for the chain
    rule computation. -/
theorem polyLog_one_hasDerivAt {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (polyLog 1) (1 / (1 - z)) z := by
  -- polyLog 1 = -log(1-·) in a neighborhood of z.
  have h_eq : polyLog 1 =ᶠ[nhds z] fun w => -Complex.log (1 - w) := by
    have h_open : IsOpen (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball
    have h_z_mem : z ∈ Metric.ball (0 : ℂ) 1 := by
      simp [Metric.mem_ball]; exact hz
    have h_ball : Metric.ball (0 : ℂ) 1 ∈ nhds z :=
      h_open.mem_nhds h_z_mem
    filter_upwards [h_ball] with w hw
    have : ‖w‖ < 1 := by simpa [Metric.mem_ball] using hw
    exact polyLog_one w this
  -- Derivative of -log(1-w) at z:
  -- 1 - z is in the slit plane (positive real part since ‖z‖ < 1)
  have h_slit : (1 - z) ∈ Complex.slitPlane := by
    -- (1 - z).re = 1 - z.re > 0 since z.re ≤ ‖z‖ < 1
    refine Or.inl ?_
    simp only [Complex.sub_re, Complex.one_re]
    have h_re_le : z.re ≤ ‖z‖ := Complex.re_le_norm z
    linarith
  -- d/dz [log (1 - z)] via chain rule with (1 - z)
  have h_inner : HasDerivAt (fun w : ℂ => (1 : ℂ) - w) (-1) z := by
    have h1 : HasDerivAt (fun w : ℂ => (1 : ℂ)) 0 z := hasDerivAt_const z 1
    have h2 : HasDerivAt (fun w : ℂ => w) 1 z := hasDerivAt_id z
    have := h1.sub h2
    simpa using this
  have h_log : HasDerivAt (fun w => Complex.log (1 - w))
      (((1 - z)⁻¹) * (-1)) z :=
    (Complex.hasDerivAt_log h_slit).comp z h_inner
  -- Negate: derivative of -log(1-w) is -((1-z)⁻¹ · (-1)) = (1-z)⁻¹ = 1/(1-z)
  have h_neg_log : HasDerivAt (fun w => -Complex.log (1 - w))
      (-((1 - z)⁻¹ * (-1))) z := h_log.neg
  have h_simplify : -((1 - z)⁻¹ * (-1)) = 1 / (1 - z) := by
    have h_ne : (1 : ℂ) - z ≠ 0 := by
      intro h
      have : (1 - z).re = 0 := by rw [h]; simp
      have := h_slit
      rcases this with hre | him
      · linarith
      · have : (1 - z).im = 0 := by rw [h]; simp
        exact him this
    field_simp
  rw [← h_simplify]
  exact h_neg_log.congr_of_eventuallyEq h_eq

/-- **Connection to `Li_0`**: `1/(1−z) = Li_0(z) / z` for `‖z‖ < 1` and `z ≠ 0`.

    Combined with `polyLog_one_hasDerivAt`, this gives the s = 0 case of
    the derivative recurrence: `d/dz Li_1(z) = Li_0(z) / z`. -/
theorem polyLog_zero_div_z {z : ℂ} (hz : ‖z‖ < 1) (hz_ne : z ≠ 0) :
    polyLog 0 z / z = 1 / (1 - z) := by
  rw [polyLog_zero_exponent z hz]
  -- (z/(1-z)) / z = 1/(1-z) for z ≠ 0
  field_simp

/-- **The derivative recurrence at s = 1**: `d/dz Li_1(z) = Li_0(z) / z`
    for `‖z‖ < 1` and `z ≠ 0`. This is the concrete case of the general
    polylog recurrence `d/dz Li_{s+1}(z) = Li_s(z) / z`. -/
theorem polyLog_one_hasDerivAt_eq_polyLog_zero_div
    {z : ℂ} (hz : ‖z‖ < 1) (hz_ne : z ≠ 0) :
    HasDerivAt (polyLog 1) (polyLog 0 z / z) z := by
  rw [polyLog_zero_div_z hz hz_ne]
  exact polyLog_one_hasDerivAt hz

/-! ## General derivative recurrence: `d/dz Li_{s+1}(z) = Li_s(z) / z`

For arbitrary complex `s` with `Re s ≥ 0` and `‖z‖ < 1`, the polylog
satisfies the derivative recurrence

  `d/dz Li_{s+1}(z) = Σ' n : ℕ, z^n / ((n+1):ℂ)^s = Li_s(z) / z (when z ≠ 0)`.

Proof: term-by-term differentiation via `hasDerivAt_tsum_of_isPreconnected`.
Each summand `z^(n+1) / ((n+1):ℂ)^(s+1)` has derivative
`z^n / ((n+1):ℂ)^s` (using `cpow_add` to factor `((n+1):ℂ)^(s+1) =
((n+1):ℂ)^s · (n+1)`). The derivative series is bounded by `r^n` on
`Metric.ball 0 r` for any `r < 1`, which is summable; the original series
is summable at `0`. The derivative-of-sum theorem then yields the result. -/

/-- **Term-by-term derivative**: each polylog summand `y^(n+1)/(n+1)^(s+1)`
    has derivative `y^n/(n+1)^s`. -/
theorem polyLog_term_hasDerivAt (s : ℂ) (n : ℕ) (y : ℂ) :
    HasDerivAt (fun w => w ^ (n + 1) / ((n + 1 : ℕ) : ℂ) ^ (s + 1))
      (y ^ n / ((n + 1 : ℕ) : ℂ) ^ s) y := by
  have h_n_ne : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have h_split : ((n + 1 : ℕ) : ℂ) ^ (s + 1) =
                 ((n + 1 : ℕ) : ℂ) ^ s * ((n + 1 : ℕ) : ℂ) := by
    rw [Complex.cpow_add _ _ h_n_ne, Complex.cpow_one]
  have h_pow : HasDerivAt (fun w : ℂ => w ^ (n + 1))
      ((((n + 1 : ℕ)) : ℂ) * y ^ n) y := by
    have h := hasDerivAt_pow (n + 1) y
    -- h : HasDerivAt (fun x => x^(n+1)) (↑(n+1) * y^(n+1-1)) y
    -- Simplify y^(n+1-1) = y^n via Nat.add_sub_cancel
    simp only [Nat.add_sub_cancel] at h
    exact h
  have h_div := h_pow.div_const (((n + 1 : ℕ) : ℂ) ^ (s + 1))
  -- h_div: HasDerivAt (fun w => w^(n+1) / ((n+1):ℂ)^(s+1))
  --   (((n+1):ℂ) * y^n / ((n+1):ℂ)^(s+1)) y
  -- Want: HasDerivAt (...) (y^n / ((n+1):ℂ)^s) y
  -- Use h_split + algebra: ((n+1) * y^n) / ((n+1)^s * (n+1)) = y^n / (n+1)^s
  have h_target : ((n + 1 : ℕ) : ℂ) * y ^ n / ((n + 1 : ℕ) : ℂ) ^ (s + 1) =
                  y ^ n / ((n + 1 : ℕ) : ℂ) ^ s := by
    rw [h_split]
    have h_ne_s : ((n + 1 : ℕ) : ℂ) ^ s ≠ 0 := by
      have : ((n + 1 : ℕ) : ℂ) = ((n : ℕ) + 1 : ℂ) := by push_cast; ring
      rw [this]
      exact Complex.natCast_add_one_cpow_ne_zero n s
    field_simp
  rw [← h_target]
  exact h_div

/-- **General derivative recurrence** for the polylog at `s + 1` on the
    open unit disk:
    `HasDerivAt (polyLog (s+1)) (Σ' n, z^n / ((n+1):ℂ)^s) z`.

    Proof: term-by-term differentiation via
    `hasDerivAt_tsum_of_isPreconnected` on the ball of radius
    `(‖z‖ + 1)/2 < 1`. The derivative summand `y^n/(n+1)^s` is bounded
    in norm by `r^n` on the ball (using `(n+1)^Re(s) ≥ 1` for `Re(s) ≥ 0`),
    which is summable. -/
theorem polyLog_succ_hasDerivAt {s : ℂ} (hs : 0 ≤ s.re) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (polyLog (s + 1))
      (∑' n : ℕ, z ^ n / ((n + 1 : ℕ) : ℂ) ^ s) z := by
  -- Choose r with ‖z‖ < r < 1
  set r := (‖z‖ + 1) / 2 with hr_def
  have hz_lt_r : ‖z‖ < r := by show ‖z‖ < (‖z‖ + 1) / 2; linarith
  have hr_lt_one : r < 1 := by show (‖z‖ + 1) / 2 < 1; linarith
  have hr_nn : (0 : ℝ) ≤ r := by
    have h : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
    show 0 ≤ (‖z‖ + 1) / 2; linarith
  -- The geometric majorant
  have hu_sum : Summable (fun n : ℕ => r ^ n) :=
    summable_geometric_of_lt_one hr_nn hr_lt_one
  -- Each summand and its derivative
  let g : ℕ → ℂ → ℂ :=
    fun n y => y ^ (n + 1) / ((n + 1 : ℕ) : ℂ) ^ (s + 1)
  let g' : ℕ → ℂ → ℂ := fun n y => y ^ n / ((n + 1 : ℕ) : ℂ) ^ s
  -- The open ball t
  let t : Set ℂ := Metric.ball 0 r
  have ht_open : IsOpen t := Metric.isOpen_ball
  have hz_in_t : z ∈ t := by
    simp [t, Metric.mem_ball, hz_lt_r]
  have h0_in_t : (0 : ℂ) ∈ t := by
    simp [t, Metric.mem_ball]
    have hr_pos : 0 < r := by
      show 0 < (‖z‖ + 1) / 2; linarith [norm_nonneg z]
    exact hr_pos
  -- Each g n has derivative g' n
  have hg_deriv : ∀ (n : ℕ) (y : ℂ), y ∈ t → HasDerivAt (g n) (g' n y) y := by
    intro n y _hy
    exact polyLog_term_hasDerivAt s n y
  -- Bound on g'
  have hg_bound : ∀ (n : ℕ) (y : ℂ), y ∈ t → ‖g' n y‖ ≤ r ^ n := by
    intro n y hy
    simp only [t, Metric.mem_ball, dist_zero_right] at hy
    have h_y_le : ‖y‖ ≤ r := le_of_lt hy
    -- ‖y^n / ((n+1):ℂ)^s‖ = ‖y‖^n / (n+1)^Re(s) ≤ r^n / 1 = r^n
    show ‖y ^ n / ((n + 1 : ℕ) : ℂ) ^ s‖ ≤ r ^ n
    rw [norm_div, norm_pow]
    have h_denom : ‖((n + 1 : ℕ) : ℂ) ^ s‖ = (n + 1 : ℕ) ^ s.re := by
      have h_pos : (0 : ℝ) < (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
      rw [show (((n + 1 : ℕ) : ℂ) : ℂ) = (((n + 1 : ℕ) : ℝ) : ℂ) from by norm_cast]
      exact Complex.norm_cpow_eq_rpow_re_of_pos h_pos s
    rw [h_denom]
    -- ‖y‖^n / (n+1)^Re(s) ≤ ‖y‖^n ≤ r^n (using (n+1)^Re(s) ≥ 1 and y bound)
    have h_denom_ge : (1 : ℝ) ≤ (n + 1 : ℕ) ^ s.re := by
      have h_base : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
      exact Real.one_le_rpow h_base hs
    have h_num_nn : (0 : ℝ) ≤ ‖y‖ ^ n := pow_nonneg (norm_nonneg _) _
    have h_num_le : ‖y‖ ^ n ≤ r ^ n :=
      pow_le_pow_left₀ (norm_nonneg _) h_y_le n
    calc ‖y‖ ^ n / (n + 1 : ℕ) ^ s.re
        ≤ ‖y‖ ^ n / 1 := by
          apply div_le_div_of_nonneg_left h_num_nn (by norm_num) h_denom_ge
      _ = ‖y‖ ^ n := by rw [div_one]
      _ ≤ r ^ n := h_num_le
  -- g summable at 0
  have hg0 : Summable (fun n => g n 0) := by
    have h_eq : ∀ n, g n (0 : ℂ) = 0 := by
      intro n
      simp only [g]
      rw [zero_pow (Nat.succ_ne_zero n), zero_div]
    simp_rw [h_eq]
    exact summable_zero
  -- Preconnected
  have h_preconn : IsPreconnected t :=
    (convex_ball 0 r).isPreconnected
  -- Apply hasDerivAt_tsum_of_isPreconnected
  have := hasDerivAt_tsum_of_isPreconnected (u := fun n => r ^ n)
    hu_sum ht_open h_preconn hg_deriv hg_bound h0_in_t hg0 hz_in_t
  -- The conclusion is `HasDerivAt (fun z => ∑' n, g n z) (∑' n, g' n z) z`,
  -- which equals `HasDerivAt (polyLog (s+1)) (∑' n, z^n / ((n+1):ℂ)^s) z`
  -- definitionally.
  exact this

/-- **Connection to `Li_s`**: `polyLog s z / z = Σ' n, z^n / ((n+1):ℂ)^s`
    for `‖z‖ < 1` and `z ≠ 0`. -/
theorem polyLog_div_z {s : ℂ} (hs : 0 ≤ s.re) {z : ℂ} (hz : ‖z‖ < 1)
    (hz_ne : z ≠ 0) :
    polyLog s z / z = ∑' n : ℕ, z ^ n / ((n + 1 : ℕ) : ℂ) ^ s := by
  unfold polyLog
  -- (Σ' n, z^(n+1) / (n+1)^s) / z = Σ' n, z^n / (n+1)^s
  rw [← tsum_div_const]
  apply tsum_congr
  intro n
  rw [pow_succ]
  field_simp

/-- **The general derivative recurrence**: `d/dz Li_{s+1}(z) = Li_s(z) / z`
    for `‖z‖ < 1`, `z ≠ 0`, and `Re s ≥ 0`. -/
theorem polyLog_succ_hasDerivAt_eq_polyLog_div
    {s : ℂ} (hs : 0 ≤ s.re) {z : ℂ} (hz : ‖z‖ < 1) (hz_ne : z ≠ 0) :
    HasDerivAt (polyLog (s + 1)) (polyLog s z / z) z := by
  rw [polyLog_div_z hs hz hz_ne]
  exact polyLog_succ_hasDerivAt hs hz

/-! ## Roadmap for future polylog development

With `Li_0(z) = z/(1−z)`, `Li_1(z) = −log(1−z)`, the derivative
recurrence at `s = 1` (`d/dz Li_1 = Li_0/z`), AND the **general
derivative recurrence** `d/dz Li_{s+1}(z) = Li_s(z) / z` now
established as axiom-free theorems, the next pieces:

1. (RETIRED — proved above) ~~General derivative recurrence~~.

2. **Functional equation / reflection**: `Li_s(z) + Li_s(−z) = 2^{1−s} Li_s(z²)`.

3. **Jonquières analytic continuation**: `Li_s(z) = Γ(1−s)·(−log z)^{s−1}
   + Σ_{k=0}^∞ ζ(s−k)·(log z)^k / k!` for `|z|` near 1.

4. **Monodromy / Riemann sheets**: `Li_s^{[m]}(z) = Li_s(z) + 2πi·m·(log z)^{s−1}/Γ(s)`
   on the m-th sheet. This is the key tool for the book's
   `Re[Li_{s*}^{[−1]}(e^{iπ√2})] = π/(10√2)` identity.

5. **Numerical evaluation at e^{iπ√2}**: identify the specific (s*, m*)
   from `fractal_continuation_derivation.py` (s* ≈ 0.182, m* = −1) as
   formal Lean values, prove the identity holds.

Steps 3-5 are the analytic-number-theory pieces required to retire
`alpha_class_self_adjointness_canonical` via the polylog route. -/

end PrincipiaTractalis.Analytic
