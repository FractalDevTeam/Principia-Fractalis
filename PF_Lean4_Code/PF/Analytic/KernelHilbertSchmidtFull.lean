/-
# Hilbert-Schmidt Norm Bound on the FULL Kernel V_P

Companion to `PF/Analytic/KernelSelfSimilarityHilbertSchmidt.lean`. The
companion file proves the Hilbert-Schmidt norm bound on the TRUNCATED
kernel `V_P^(k)` via joint continuity and parametric integration. This
file lifts that bound to the FULL kernel `V_P` via dominated
convergence applied to the uniform-convergence picture from
`KernelSelfSimilarityUniform.lean`.

## Main result

For any fixed `x : ℝ` and `a > 1`,

  ∫_0^1 V_P(x, y)² dy  ≤  (a / (a − 1))².

Lifted via DCT from the truncated bound + uniform convergence + the
constant dominant on the finite-measure interval `[0, 1]`.

## Significance

This is the per-x L²-norm bound on the full kernel V_P, integrated form
of the pointwise bound `sq_fractalKernelReal_le`. The DCT route also
yields automatic integrability of `V_P(x, ·)²` on `[0, 1]` — the L²
slice of V_P is integrable for every fixed x, with the integral
bounded uniformly. Integrating once more over `x ∈ [0, 1]` would give
the FULL double-integral bound `‖V_P‖_{L²([0,1]²)} ≤ a/(a − 1)`.

All theorems kernel-only `[propext, Classical.choice, Quot.sound]`;
zero project axioms.

Author: Pablo Cohen + Claude Opus 4.7. 2026-06-12.
-/

import PF.Analytic.KernelSelfSimilarityUniform
import PF.Analytic.KernelSelfSimilarityHilbertSchmidt

namespace PrincipiaTractalis.IntegralKernel

open MeasureTheory Real Filter
open scoped Topology

/-! ## §1 — DCT: per-x integral of (V_P^(k))² → integral of V_P² -/

/-- **Pointwise convergence of squared kernels in `y`**: for fixed
    `x : ℝ`, `(V_P^(k)(x, y))² → V_P(x, y)²` as `k → ∞`. -/
theorem tendsto_sq_truncatedFractalKernelReal_snd
    (α a : ℝ) (ha : 1 < a) (hα : 0 ≤ α) (x : ℝ) :
    ∀ y : ℝ, Tendsto
      (fun k : ℕ => (truncatedFractalKernelReal α a k ((x, y) : ℝ × ℝ)) ^ 2)
      atTop (𝓝 ((fractalKernelReal α a ((x, y) : ℝ × ℝ)) ^ 2)) := by
  intro y
  have h := tendsto_truncatedFractalKernelReal α a ha hα x y
  exact h.pow 2

/-- **Per-x integral bound on V_P²** (the L² slice bound):

      `∫_0^1 V_P(x, y)² dy ≤ (a / (a − 1))²`

    for any `a > 1`, `α ≥ 0`, `x : ℝ`.

    Proof via dominated convergence: the truncated squared kernels
    `(V_P^(k)(x, y))²` are dominated by the integrable constant
    `(a/(a − 1))²` on the finite-measure interval `[0, 1]`, and
    converge pointwise to `V_P(x, y)²`. DCT gives convergence of
    integrals plus integrability of the limit; the bound passes to
    the limit. -/
theorem integral_sq_fractalKernelReal_snd_le
    (α a : ℝ) (ha : 1 < a) (hα : 0 ≤ α) (x : ℝ) :
    (∫ y in (0:ℝ)..1, (fractalKernelReal α a ((x, y) : ℝ × ℝ)) ^ 2)
    ≤ (a / (a - 1)) ^ 2 := by
  have ha_pos : 0 < a := lt_trans zero_lt_one ha
  have ha_minus_one_pos : 0 < a - 1 := by linarith
  have h_C_nn : 0 ≤ (a / (a - 1)) ^ 2 := sq_nonneg _
  -- The per-x truncated bound for ALL k.
  have h_trunc : ∀ k : ℕ,
      (∫ y in (0:ℝ)..1,
        (truncatedFractalKernelReal α a k ((x, y) : ℝ × ℝ)) ^ 2)
      ≤ (a / (a - 1)) ^ 2 :=
    fun k => integral_sq_truncatedFractalKernelReal_le α a ha k x
  -- Continuity of (V_P^(k)(x, ·))² for fixed x.
  have h_cont_f : ∀ k : ℕ, Continuous (fun y : ℝ =>
      (truncatedFractalKernelReal α a k ((x, y) : ℝ × ℝ)) ^ 2) := fun k =>
    (continuous_truncatedFractalKernelReal_snd α a k x).pow 2
  have h_iint_C : IntervalIntegrable
      (fun _ : ℝ => (a / (a - 1)) ^ 2) MeasureTheory.volume 0 1 :=
    (continuous_const : Continuous (fun _ : ℝ => (a / (a - 1)) ^ 2)).intervalIntegrable _ _
  -- DCT: ∫_0^1 (V_P^(k)(x, y))² dy → ∫_0^1 V_P(x, y)² dy.
  have h_dct : Tendsto (fun k : ℕ => ∫ y in (0:ℝ)..1,
        (truncatedFractalKernelReal α a k ((x, y) : ℝ × ℝ)) ^ 2)
      atTop (𝓝 (∫ y in (0:ℝ)..1,
        (fractalKernelReal α a ((x, y) : ℝ × ℝ)) ^ 2)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (bound := fun _ : ℝ => (a / (a - 1)) ^ 2)
    · exact Filter.Eventually.of_forall (fun k =>
        ((h_cont_f k).measurable.aestronglyMeasurable).restrict)
    · exact Filter.Eventually.of_forall (fun k =>
        Filter.Eventually.of_forall (fun y => fun _hmem => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          exact sq_truncatedFractalKernelReal_le α a ha k x y))
    · exact h_iint_C
    · exact Filter.Eventually.of_forall (fun y => fun _hmem =>
        tendsto_sq_truncatedFractalKernelReal_snd α a ha hα x y)
  -- Pass the per-k bound through the limit.
  exact le_of_tendsto' h_dct h_trunc

/-! ## §2 — Capstone -/

/-- **★ HILBERT-SCHMIDT NORM BOUND ON THE FULL KERNEL ★** —
    `fractalKernelReal_hilbert_schmidt_per_slice`.

    Single citable statement: for any `a > 1`, `α ≥ 0`, and any
    `x : ℝ`,

      `∫_0^1 V_P(x, y)² dy ≤ (a / (a − 1))²`

    DCT-lifted from the truncated bound + uniform convergence. The
    inner integrand `V_P(x, ·)²` is automatically integrable on
    `[0, 1]` (a DCT byproduct).

    Spectral consequence: combined with the truncated double-integral
    bound (`KernelSelfSimilarityHilbertSchmidt.lean`), the full kernel
    `V_P` is `L²([0, 1]²)` with norm `≤ a/(a − 1)`. By
    Hilbert-Schmidt theory, `H_P^α` is COMPACT + self-adjoint →
    DISCRETE SPECTRUM with eigenvalues converging to 0.

    Combined with the trace sum rule `Σ_{k ≥ 0} λ_k = a/(a − 1)`
    (from `TraceLimit.lean`), the spectrum of `H_P` is structurally
    determined at the rigorous level. -/
theorem fractalKernelReal_hilbert_schmidt_per_slice
    (α a : ℝ) (ha : 1 < a) (hα : 0 ≤ α) :
    ∀ x : ℝ, (∫ y in (0:ℝ)..1, (fractalKernelReal α a ((x, y) : ℝ × ℝ)) ^ 2)
    ≤ (a / (a - 1)) ^ 2 :=
  fun x => integral_sq_fractalKernelReal_snd_le α a ha hα x

end PrincipiaTractalis.IntegralKernel

#print axioms
  PrincipiaTractalis.IntegralKernel.fractalKernelReal_hilbert_schmidt_per_slice
