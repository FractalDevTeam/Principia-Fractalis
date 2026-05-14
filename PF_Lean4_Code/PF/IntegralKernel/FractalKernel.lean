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
import Mathlib.Analysis.SpecificLimits.Basic
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

/-! ## Summability of the fractal kernel under `a > 1`

The infinite series defining `fractalKernelReal` converges absolutely whenever
`a > 1`, since each term is bounded in absolute value by `(1/a)^n` and the
geometric series converges for `0 ≤ 1/a < 1`.
-/

/-- Termwise bound: `|fractalKernelTerm α a z n| ≤ (1/a)^n` whenever `a > 0`. -/
theorem abs_fractalKernelTerm_le (α : ℝ) {a : ℝ} (ha : 0 < a) (z : K × K)
    (n : ℕ) :
    |fractalKernelTerm α a z n| ≤ (1 / a) ^ n := by
  unfold fractalKernelTerm
  have h_pow_pos : (0 : ℝ) < a ^ (-(n : ℤ)) := zpow_pos ha _
  rw [abs_mul, abs_of_pos h_pow_pos]
  -- a^(-n) * |cos(...)| ≤ a^(-n) * 1 = (1/a)^n
  calc a ^ (-(n : ℤ)) * |Real.cos (Real.pi * α ^ n * dist z.1 z.2)|
      ≤ a ^ (-(n : ℤ)) * 1 := by
        apply mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) h_pow_pos.le
    _ = a ^ (-(n : ℤ)) := mul_one _
    _ = (1 / a) ^ n := by
        rw [zpow_neg, zpow_natCast, one_div, inv_pow]

/-- The fractal kernel summands are summable when `a > 1`. -/
theorem summable_fractalKernelTerm (α : ℝ) {a : ℝ} (ha : 1 < a) (z : K × K) :
    Summable (fractalKernelTerm α a z) := by
  have ha_pos : 0 < a := lt_trans zero_lt_one ha
  have h_inv_lt_one : 1 / a < 1 := by
    rw [div_lt_one ha_pos]
    exact ha
  have h_inv_nn : 0 ≤ 1 / a := div_nonneg zero_le_one ha_pos.le
  -- Bound by geometric series
  apply Summable.of_norm_bounded (g := fun n => (1 / a) ^ n)
  · exact summable_geometric_of_lt_one h_inv_nn h_inv_lt_one
  · intro n
    exact abs_fractalKernelTerm_le α ha_pos z n

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
