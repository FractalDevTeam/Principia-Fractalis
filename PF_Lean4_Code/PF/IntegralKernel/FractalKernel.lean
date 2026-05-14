/-
# Fractal Convolution Kernels V_P and V_NP

The book's Ch 21 (Definition 4.2, `def:fractal-convolution`, line 325) defines
the fractal convolution kernels on a compact metric space `(K, d, μ)`:

  V_P(x, y)  = Σ_{n=0}^∞ a^{-n} · cos(π · α^n · d(x, y))
  V_NP(x, y) = V_P(x, y) ⊗ R_φ          (R_φ unitary, golden angle)

with `α = √2`, `a > 1` for convergence.

**This file defines `fractalKernel α a : K × K → ℂ`** — the V_P kernel
generalized over its parameters `α` (resonance frequency) and `a` (decay
base). The book's `V_P` corresponds to `fractalKernel √2 a`; `V_NP` is a
unitary conjugate (handled separately, since `R_φ`-conjugation preserves
self-adjointness via Mathlib's `IsSelfAdjoint.conj_adjoint`).

**Key properties proved here**:
1. `fractalKernel_real_valued` — the kernel is real-valued (the complex
   coercion of a real tsum).
2. `fractalKernel_swap` — symmetric in `(x, y)`, by `dist_comm` + `cos`-evenness.
3. `fractalKernel_isConjSymmetric` — feeds directly into the L1 self-adjoint
   lift via `IntegralKernel.isSelfAdjoint_of_kernel_conjSymm`.

Reference: Principia Fractalis, Chapter 21, Definition 4.2 and Theorem 4.4
(Spectral Properties — Self-adjointness clause).

Stage L2 — kernel definitions and elementary symmetries.
-/

import PF.IntegralKernel.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.MetricSpace.Defs

namespace PrincipiaTractalis.IntegralKernel

open MeasureTheory Real

variable {K : Type*} [PseudoMetricSpace K]

/-- The real-valued **fractal kernel summand** at depth `n`. -/
noncomputable def fractalKernelTerm (α a : ℝ) (z : K × K) (n : ℕ) : ℝ :=
  a ^ (-(n : ℤ)) * Real.cos (Real.pi * α ^ n * dist z.1 z.2)

/-- The **fractal convolution kernel** as a real-valued function on `K × K`,
    before complexification. -/
noncomputable def fractalKernelReal (α a : ℝ) (z : K × K) : ℝ :=
  ∑' n, fractalKernelTerm α a z n

/-- The **fractal convolution kernel** `V_P` of Chapter 21, Definition 4.2,
    as a complex-valued function on `K × K`. This is the complexification of
    `fractalKernelReal`. -/
noncomputable def fractalKernel (α a : ℝ) (z : K × K) : ℂ :=
  ((fractalKernelReal α a z : ℝ) : ℂ)

/-- The fractal kernel is, by construction, the complex coercion of a real
    number. -/
theorem fractalKernel_real_valued (α a : ℝ) (z : K × K) :
    fractalKernel α a z = ((fractalKernelReal α a z : ℝ) : ℂ) := rfl

/-! ## Symmetry in the two arguments

The kernel summand at depth `n` depends on `(x, y)` only through `dist x y`,
which is symmetric. So every summand is invariant under `z ↦ z.swap`, and
the tsum inherits the invariance.
-/

theorem fractalKernelTerm_swap (α a : ℝ) (z : K × K) (n : ℕ) :
    fractalKernelTerm α a z.swap n = fractalKernelTerm α a z n := by
  unfold fractalKernelTerm
  simp [Prod.fst_swap, Prod.snd_swap, dist_comm]

theorem fractalKernelReal_swap (α a : ℝ) (z : K × K) :
    fractalKernelReal α a z.swap = fractalKernelReal α a z := by
  unfold fractalKernelReal
  exact tsum_congr (fun n => fractalKernelTerm_swap α a z n)

theorem fractalKernel_swap (α a : ℝ) (z : K × K) :
    fractalKernel α a z.swap = fractalKernel α a z := by
  unfold fractalKernel
  rw [fractalKernelReal_swap]

/-! ## Conjugate symmetry (the L1 hypothesis)

For a real-valued symmetric kernel, conjugate symmetry is automatic:
`conj (V z.swap) = conj (V z) = V z` (the first equality from swap-symmetry,
the second from real-valuedness).
-/

theorem fractalKernel_isConjSymmetric [MeasurableSpace K] (α a : ℝ)
    (μ : Measure K) :
    IsConjSymmetric (fractalKernel α a) μ := by
  -- The conjugate-symmetric condition holds *pointwise*, so a.e. is trivial.
  refine Filter.Eventually.of_forall (fun z => ?_)
  -- Goal: fractalKernel α a z = conj (fractalKernel α a z.swap)
  rw [fractalKernel_swap]
  -- Goal: fractalKernel α a z = conj (fractalKernel α a z)
  -- Both sides equal the complex coercion of a real number, which conjugates trivially.
  unfold fractalKernel
  simp [Complex.conj_ofReal]

end PrincipiaTractalis.IntegralKernel
