/-
# Kernel Self-Similarity at the Limit `k → ∞` — Uniform Convergence

Companion to `PF/Analytic/KernelSelfSimilarityLimit.lean`. The limit
file proves pointwise convergence of the iterated partial sums to
`V_P(x, y)` and Tendsto-to-zero of the rescaled residual. This file
proves the stronger statement that convergence is UNIFORM in `(x, y)`:

  sup_{(x,y)} |V_P(x, y) − V_P^(k)(x, y)|  →  0  as  k → ∞.

The bound is `O(a^{-k})`, sharper than pointwise convergence.

## Significance

Uniform convergence on `K × K` (any pseudo-metric space) immediately
implies:

* L^p convergence on `[0,1]²` for every `1 ≤ p ≤ ∞` (since `[0,1]²`
  has finite measure).
* Operator-norm convergence of the induced integral operators when
  the carrier domain has finite measure.

The squared form `(V_P − V_P^(k))²(x,y) ≤ a^{-2k} · (a/(a−1))²` is the
Hilbert-Schmidt building block: integrated over a finite-measure
domain, it gives the L² convergence rate which lifts to operator-norm
convergence on the Hilbert-Schmidt scale.

All theorems kernel-only `[propext, Classical.choice, Quot.sound]`;
zero project axioms.

Author: Pablo Cohen + Claude Opus 4.7. 2026-06-12.
-/

import PF.Analytic.KernelSelfSimilarity

namespace PrincipiaTractalis.IntegralKernel

open Filter Real
open scoped Topology

/-! ## §1 — Uniform L^∞ convergence -/

/-- **Uniform L^∞ convergence**: for every `ε > 0` there exists `K` such
    that for all `k ≥ K` and all `(x, y) : ℝ × ℝ`,
    `|V_P(x, y) − V_P^(k)(x, y)| ≤ ε`.

    Direct from the uniform truncation-error bound `|V_P − V_P^(k)| ≤
    a^{-k} · a/(a−1)` (uniform in `(x, y)`) and `a^{-k} → 0` as `k → ∞`. -/
theorem truncatedFractalKernelReal_converges_uniformly
    (α a : ℝ) (ha : 1 < a) (hα : 0 ≤ α) :
    ∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K, ∀ x y : ℝ,
      |fractalKernelReal α a ((x, y) : ℝ × ℝ)
        - truncatedFractalKernelReal α a k ((x, y) : ℝ × ℝ)| ≤ ε := by
  intro ε hε
  have ha_pos : 0 < a := lt_trans zero_lt_one ha
  have ha_minus_one_pos : 0 < a - 1 := by linarith
  have hinv_lt_one : a⁻¹ < 1 := inv_lt_one_of_one_lt₀ ha
  have h_inv_nn : (0 : ℝ) ≤ a⁻¹ := le_of_lt (by positivity)
  -- a^{-k} · a/(a-1) → 0.
  have h_bound_tendsto :
      Tendsto (fun k : ℕ => a ^ (-(k : ℤ)) * (a / (a - 1)))
        atTop (𝓝 0) := by
    have h_zpow : Tendsto (fun k : ℕ => (a : ℝ) ^ (-(k : ℤ)))
        atTop (𝓝 0) := by
      have h_inv : Tendsto (fun k : ℕ => (a⁻¹ : ℝ) ^ k)
          atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one h_inv_nn hinv_lt_one
      have h_eq : ∀ k : ℕ, (a⁻¹ : ℝ) ^ k = a ^ (-(k : ℤ)) := fun k => by
        rw [zpow_neg, zpow_natCast, inv_pow]
      simp_rw [h_eq] at h_inv
      exact h_inv
    have := h_zpow.mul_const (a / (a - 1))
    simpa using this
  -- Get K such that for k ≥ K, the bound is ≤ ε.
  rw [Metric.tendsto_atTop] at h_bound_tendsto
  rcases h_bound_tendsto ε hε with ⟨K, hK⟩
  refine ⟨K, fun k hkK x y => ?_⟩
  have h_uniform := abs_fractalKernelReal_sub_truncated_le α a ha hα k x y
  have h_dist := hK k hkK
  rw [Real.dist_eq, sub_zero] at h_dist
  have h_pos : 0 ≤ a ^ (-(k : ℤ)) * (a / (a - 1)) := by
    have ha_pos : 0 < a := lt_trans zero_lt_one ha
    apply mul_nonneg (le_of_lt (zpow_pos ha_pos _))
    apply div_nonneg (le_of_lt ha_pos) (le_of_lt ha_minus_one_pos)
  rw [abs_of_nonneg h_pos] at h_dist
  linarith

/-! ## §2 — Squared error bound (Hilbert-Schmidt building block) -/

/-- **Squared error bound**: for every `k : ℕ` and every `(x, y) : ℝ × ℝ`,
    `(V_P(x, y) − V_P^(k)(x, y))² ≤ a^{-2k} · (a/(a−1))²`.

    The Hilbert-Schmidt building block: integrating this pointwise
    bound over `(x, y) ∈ [0, 1]²` gives the L²-norm-squared
    approximation error
    `‖V_P − V_P^(k)‖²_{L²([0,1]²)} ≤ a^{-2k} · (a/(a−1))²`,
    which by the finite-measure structure of `[0, 1]²` lifts to
    operator-norm convergence on the Hilbert-Schmidt scale. -/
theorem sq_fractalKernelReal_sub_truncated_le
    (α a : ℝ) (ha : 1 < a) (hα : 0 ≤ α) (k : ℕ) (x y : ℝ) :
    (fractalKernelReal α a ((x, y) : ℝ × ℝ)
      - truncatedFractalKernelReal α a k ((x, y) : ℝ × ℝ)) ^ 2
    ≤ a ^ (-(2 * k : ℤ)) * (a / (a - 1)) ^ 2 := by
  have h_abs := abs_fractalKernelReal_sub_truncated_le α a ha hα k x y
  have ha_pos : 0 < a := lt_trans zero_lt_one ha
  have ha_minus_one_pos : 0 < a - 1 := by linarith
  have h_rhs_nn : 0 ≤ a ^ (-(k : ℤ)) * (a / (a - 1)) := by
    apply mul_nonneg (le_of_lt (zpow_pos ha_pos _))
    exact div_nonneg (le_of_lt ha_pos) (le_of_lt ha_minus_one_pos)
  -- Square both sides of |·| ≤ a^{-k} · a/(a-1) (both sides nonneg).
  have h_diff_abs_nn : 0 ≤ |fractalKernelReal α a ((x, y) : ℝ × ℝ)
        - truncatedFractalKernelReal α a k ((x, y) : ℝ × ℝ)| := abs_nonneg _
  have h_sq : (fractalKernelReal α a ((x, y) : ℝ × ℝ)
        - truncatedFractalKernelReal α a k ((x, y) : ℝ × ℝ)) ^ 2
      ≤ (a ^ (-(k : ℤ)) * (a / (a - 1))) ^ 2 := by
    rw [← sq_abs]
    have h_low : -(a ^ (-(k : ℤ)) * (a / (a - 1)))
        ≤ |fractalKernelReal α a ((x, y) : ℝ × ℝ)
            - truncatedFractalKernelReal α a k ((x, y) : ℝ × ℝ)| := by
      linarith
    exact sq_le_sq' h_low h_abs
  -- Show RHS: (a^{-k} · c)² = a^{-2k} · c².
  have h_pow_sq : (a ^ (-(k : ℤ))) ^ 2 = a ^ (-(2 * k : ℤ)) := by
    rw [pow_two, ← zpow_add₀ (ne_of_gt ha_pos)]
    congr 1
    push_cast; ring
  calc (fractalKernelReal α a ((x, y) : ℝ × ℝ)
        - truncatedFractalKernelReal α a k ((x, y) : ℝ × ℝ)) ^ 2
      ≤ (a ^ (-(k : ℤ)) * (a / (a - 1))) ^ 2 := h_sq
    _ = (a ^ (-(k : ℤ))) ^ 2 * (a / (a - 1)) ^ 2 := by rw [mul_pow]
    _ = a ^ (-(2 * k : ℤ)) * (a / (a - 1)) ^ 2 := by rw [h_pow_sq]

/-! ## §3 — Capstone -/

/-- **★ UNIFORM CONVERGENCE OF TRUNCATED KERNELS ★** —
    `truncatedFractalKernelReal_uniform_capstone`.

    Single citable statement bundling the uniform convergence of
    `V_P^(k) → V_P` and the squared error bound (Hilbert-Schmidt
    building block):

      (U1) For every `ε > 0`, there exists `K` such that for all
           `k ≥ K` and all `(x, y) : ℝ × ℝ`,
           `|V_P(x, y) − V_P^(k)(x, y)| ≤ ε`.

      (U2) For every `k : ℕ` and every `(x, y) : ℝ × ℝ`,
           `(V_P(x, y) − V_P^(k)(x, y))² ≤ a^{-2k} · (a/(a−1))²`.

    Combined with the iterated-recursion-closure capstone
    `fractalKernelReal_iterated_recursion_closes`, this completes the
    uniform-convergence picture of the V_P kernel's self-similarity
    recursion at the limit `k → ∞`: the recursion closes pointwise,
    uniformly, and in L² (on any finite-measure carrier). -/
theorem truncatedFractalKernelReal_uniform_capstone
    (α a : ℝ) (ha : 1 < a) (hα : 0 ≤ α) :
    -- (U1) Uniform convergence.
    (∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K, ∀ x y : ℝ,
      |fractalKernelReal α a ((x, y) : ℝ × ℝ)
        - truncatedFractalKernelReal α a k ((x, y) : ℝ × ℝ)| ≤ ε) ∧
    -- (U2) Squared error bound (Hilbert-Schmidt building block).
    (∀ k : ℕ, ∀ x y : ℝ,
      (fractalKernelReal α a ((x, y) : ℝ × ℝ)
        - truncatedFractalKernelReal α a k ((x, y) : ℝ × ℝ)) ^ 2
      ≤ a ^ (-(2 * k : ℤ)) * (a / (a - 1)) ^ 2) :=
  ⟨truncatedFractalKernelReal_converges_uniformly α a ha hα,
   fun k x y => sq_fractalKernelReal_sub_truncated_le α a ha hα k x y⟩

end PrincipiaTractalis.IntegralKernel

#print axioms
  PrincipiaTractalis.IntegralKernel.truncatedFractalKernelReal_uniform_capstone
