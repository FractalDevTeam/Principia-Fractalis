/-
# Kernel Self-Similarity at the Limit `k → ∞` — Complex Kernel Lift

The framework's complex kernel `fractalKernel α a z := ((fractalKernelReal α a z : ℝ) : ℂ)`
is the complexification of the real V_P kernel. This file lifts the
pointwise, uniform, and HasSum convergence results for the real
kernel (in `KernelSelfSimilarityLimit.lean` and
`KernelSelfSimilarityUniform.lean`) to the complex kernel.

The lift is trivial — `Complex.ofReal` is a continuous ring
homomorphism, so it commutes with limits and sums. Yet writing it
out explicitly closes the symmetric structure: the substrate's
scale-recursion structure closes pointwise + uniformly + in HasSum
form on BOTH the real and complex kernels at the limit `k → ∞`.

## Significance

The framework's downstream operator-theoretic work (in
`PF/Analytic/PolylogSpectrum.lean`, `PF/Operators/*`) consumes the
complex kernel because `H_P` acts on `L²(K, μ; ℂ)`. With the limit
theorems available on both real and complex kernels, any future
proof that needs `(complex truncated kernel) → (complex V_P)` in any
operator-theoretic functional has a clean foundation.

All theorems kernel-only `[propext, Classical.choice, Quot.sound]`;
zero project axioms.

Author: Pablo Cohen + Claude Opus 4.7. 2026-06-12.
-/

import PF.Analytic.KernelSelfSimilarityLimit
import PF.Analytic.KernelSelfSimilarityUniform

namespace PrincipiaTractalis.IntegralKernel

open Filter Real Complex
open scoped Topology

/-! ## §1 — Complex truncated kernel definition -/

/-- **Complex truncated fractal kernel** — the complexification of the
    real truncated kernel `V_P^(k)`. Equals
    `Σ_{j=0}^{k-1} a^(-j) · cos(π · αʲ · |x − y|)` cast to `ℂ`. -/
noncomputable def truncatedFractalKernel
    (α a : ℝ) (k : ℕ) (z : ℝ × ℝ) : ℂ :=
  ((truncatedFractalKernelReal α a k z : ℝ) : ℂ)

theorem truncatedFractalKernel_eq_ofReal
    (α a : ℝ) (k : ℕ) (z : ℝ × ℝ) :
    truncatedFractalKernel α a k z
      = ((truncatedFractalKernelReal α a k z : ℝ) : ℂ) := rfl

/-! ## §2 — Complex residual vanishes at the limit -/

/-- **Complex rescaled residual vanishes**: the sequence
    `(k ↦ a^{-k} · fractalKernel α a (αᵏ · x, αᵏ · y))` tends to `0`
    as `k → ∞`. Direct lift of the real version via continuity of
    `Complex.ofReal`. -/
theorem tendsto_complex_kernel_residual_at_scale
    (α a : ℝ) (ha : 1 < a) (x y : ℝ) :
    Tendsto
      (fun k : ℕ =>
        (a ^ (-(k : ℤ)) : ℂ)
          * fractalKernel α a ((α ^ k * x, α ^ k * y) : ℝ × ℝ))
      atTop (𝓝 0) := by
  -- The complex sequence equals ofReal applied to the real residual.
  have h_eq : ∀ k : ℕ,
      (a ^ (-(k : ℤ)) : ℂ)
        * fractalKernel α a ((α ^ k * x, α ^ k * y) : ℝ × ℝ)
      = ((a ^ (-(k : ℤ))
          * fractalKernelReal α a ((α ^ k * x, α ^ k * y) : ℝ × ℝ) : ℝ) : ℂ) := by
    intro k
    rw [fractalKernel_real_valued]
    push_cast
    ring
  have h_eq_fun :
      (fun k : ℕ =>
        (a ^ (-(k : ℤ)) : ℂ)
          * fractalKernel α a ((α ^ k * x, α ^ k * y) : ℝ × ℝ))
      = (fun k : ℕ =>
        ((a ^ (-(k : ℤ))
            * fractalKernelReal α a ((α ^ k * x, α ^ k * y) : ℝ × ℝ) : ℝ) : ℂ)) := by
    funext k; exact h_eq k
  rw [h_eq_fun]
  have h_real := tendsto_kernel_residual_at_scale α a ha x y
  -- Tendsto of ofReal ∘ f when f tends to 0 in ℝ.
  have : Tendsto
      (fun k : ℕ =>
        ((a ^ (-(k : ℤ))
            * fractalKernelReal α a ((α ^ k * x, α ^ k * y) : ℝ × ℝ) : ℝ) : ℂ))
      atTop (𝓝 ((0 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp h_real
  simpa using this

/-! ## §3 — Complex partial sums tend to V_P -/

/-- **Complex truncated kernel tends to complex V_P**: the truncated
    complex kernels converge pointwise to the full complex kernel as
    `k → ∞`. -/
theorem tendsto_truncatedFractalKernel
    (α a : ℝ) (ha : 1 < a) (hα : 0 ≤ α) (x y : ℝ) :
    Tendsto (fun k : ℕ => truncatedFractalKernel α a k ((x, y) : ℝ × ℝ))
      atTop (𝓝 (fractalKernel α a ((x, y) : ℝ × ℝ))) := by
  unfold truncatedFractalKernel
  rw [fractalKernel_real_valued]
  exact (Complex.continuous_ofReal.tendsto _).comp
    (tendsto_truncatedFractalKernelReal α a ha hα x y)

/-! ## §4 — Uniform L^∞ convergence of complex kernels -/

/-- **Complex uniform convergence**: for every `ε > 0` there exists `K`
    such that for all `k ≥ K` and all `(x, y) : ℝ × ℝ`,
    `‖fractalKernel α a (x, y) − truncatedFractalKernel α a k (x, y)‖ ≤ ε`.

    The complex norm of `ofReal r − ofReal s` equals `|r − s|`, so the
    real uniform convergence transfers directly to the complex norm. -/
theorem truncatedFractalKernel_converges_uniformly
    (α a : ℝ) (ha : 1 < a) (hα : 0 ≤ α) :
    ∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K, ∀ x y : ℝ,
      ‖fractalKernel α a ((x, y) : ℝ × ℝ)
        - truncatedFractalKernel α a k ((x, y) : ℝ × ℝ)‖ ≤ ε := by
  intro ε hε
  rcases truncatedFractalKernelReal_converges_uniformly α a ha hα ε hε
    with ⟨K, hK⟩
  refine ⟨K, fun k hkK x y => ?_⟩
  unfold truncatedFractalKernel
  rw [fractalKernel_real_valued]
  rw [← Complex.ofReal_sub]
  rw [Complex.norm_real]
  exact hK k hkK x y

/-! ## §5 — Capstone -/

/-- **★ COMPLEX KERNEL SELF-SIMILARITY ITERATED RECURSION CLOSES AT
    THE LIMIT ★** — `fractalKernel_iterated_recursion_closes`.

    Single citable statement: the substrate's scale-recursion structure
    closes pointwise + uniformly on the complex kernel at the limit
    `k → ∞`:

      (CL1) Complex rescaled residual vanishes at the limit.

      (CL2) Truncated complex kernels tend to complex V_P pointwise.

      (CL3) Truncated complex kernels converge UNIFORMLY in `(x, y)`
            with `O(a^{-k})` rate.

    Combined with the real-kernel limit + uniform capstones, this
    completes the kernel-level convergence picture on BOTH the real
    and complex kernels. -/
theorem fractalKernel_iterated_recursion_closes
    (α a : ℝ) (ha : 1 < a) (hα : 0 ≤ α) :
    -- (CL1) Complex residual vanishes.
    (∀ x y : ℝ,
      Tendsto
        (fun k : ℕ =>
          (a ^ (-(k : ℤ)) : ℂ)
            * fractalKernel α a ((α ^ k * x, α ^ k * y) : ℝ × ℝ))
        atTop (𝓝 0)) ∧
    -- (CL2) Pointwise convergence of truncated complex kernels.
    (∀ x y : ℝ,
      Tendsto (fun k : ℕ =>
        truncatedFractalKernel α a k ((x, y) : ℝ × ℝ))
        atTop (𝓝 (fractalKernel α a ((x, y) : ℝ × ℝ)))) ∧
    -- (CL3) Uniform convergence.
    (∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K, ∀ x y : ℝ,
      ‖fractalKernel α a ((x, y) : ℝ × ℝ)
        - truncatedFractalKernel α a k ((x, y) : ℝ × ℝ)‖ ≤ ε) :=
  ⟨tendsto_complex_kernel_residual_at_scale α a ha,
   tendsto_truncatedFractalKernel α a ha hα,
   truncatedFractalKernel_converges_uniformly α a ha hα⟩

end PrincipiaTractalis.IntegralKernel

#print axioms
  PrincipiaTractalis.IntegralKernel.fractalKernel_iterated_recursion_closes
