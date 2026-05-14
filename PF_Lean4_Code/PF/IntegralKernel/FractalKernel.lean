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
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

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

/-- Uniform L^∞ bound: `|fractalKernelReal α a z| ≤ a / (a - 1)` for `a > 1`.

    This is the closed form of the geometric majorant `Σ (1/a)^n = a/(a-1)`.
    Combined with finiteness of `μ.prod μ`, it gives `fractalKernel ∈ L²(K × K)`,
    the integrability prerequisite for promoting the kernel action to a bounded
    operator on `Lp ℂ 2 μ`. -/
theorem abs_fractalKernelReal_le (α : ℝ) {a : ℝ} (ha : 1 < a) (z : K × K) :
    |fractalKernelReal α a z| ≤ a / (a - 1) := by
  have ha_pos : 0 < a := lt_trans zero_lt_one ha
  have h_inv_lt_one : 1 / a < 1 := by rw [div_lt_one ha_pos]; exact ha
  have h_inv_nn : 0 ≤ 1 / a := div_nonneg zero_le_one ha_pos.le
  have h_sum_summable : Summable (fun n : ℕ => (1 / a) ^ n) :=
    summable_geometric_of_lt_one h_inv_nn h_inv_lt_one
  -- |tsum| ≤ tsum |·|
  unfold fractalKernelReal
  -- Apply norm_tsum_le_tsum_norm specialized to ℝ (where ‖·‖ = |·|).
  have h_abs_sum :
      Summable (fun n : ℕ => ‖fractalKernelTerm α a z n‖) := by
    simp_rw [Real.norm_eq_abs]
    exact (summable_fractalKernelTerm α ha z).abs
  have h1 : ‖∑' n, fractalKernelTerm α a z n‖ ≤
            ∑' n, ‖fractalKernelTerm α a z n‖ :=
    norm_tsum_le_tsum_norm h_abs_sum
  have h2 : (∑' n : ℕ, ‖fractalKernelTerm α a z n‖) ≤ ∑' n : ℕ, (1 / a) ^ n := by
    refine Summable.tsum_le_tsum ?_ h_abs_sum h_sum_summable
    intro n
    simp_rw [Real.norm_eq_abs]
    exact abs_fractalKernelTerm_le α ha_pos z n
  have h3 : (∑' n : ℕ, (1 / a) ^ n) = (1 - 1 / a)⁻¹ :=
    tsum_geometric_of_lt_one h_inv_nn h_inv_lt_one
  have h4 : (1 - 1 / a)⁻¹ = a / (a - 1) := by
    rw [one_div]
    field_simp
  rw [Real.norm_eq_abs] at h1
  linarith [h1.trans (h2.trans (le_of_eq (h3.trans h4)))]

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

/-! ## Canonical instance: `V_P` at the book's `α = √2`

Chapter 21 fixes the resonance parameter for P-class to `α_P = √2`. The
NP-class kernel `V_NP = V_P ⊗ R_φ` is a unitary conjugate of `V_P` (book
line 510), so its self-adjointness follows from `V_P`'s by
`IsSelfAdjoint.adjoint_conj` once the unitary `R_φ` is in place.
-/

/-- **The book's canonical V_P kernel** (Ch 21, Definition 4.2, line 333):
    `V_P(x, y) = Σ a^{-n} cos(π · 2^{n/2} · d(x, y))`.

    This is `fractalKernel` with the canonical P-class resonance
    `α = √2`. The auxiliary base `a > 1` is left free (to be chosen
    for convergence; book uses `a = 10√2/π` for the spectral-gap
    normalisation). -/
noncomputable def V_P_canonical (a : ℝ) : K × K → ℂ :=
  fractalKernel (Real.sqrt 2) a

theorem V_P_canonical_isConjSymmetric [MeasurableSpace K] (a : ℝ)
    (μ : Measure K) : IsConjSymmetric (V_P_canonical (K := K) a) μ :=
  fractalKernel_isConjSymmetric (Real.sqrt 2) a μ

theorem V_P_canonical_swap (a : ℝ) (z : K × K) :
    V_P_canonical (K := K) a z.swap = V_P_canonical (K := K) a z :=
  fractalKernel_swap (Real.sqrt 2) a z

theorem abs_V_P_canonical_le {a : ℝ} (ha : 1 < a) (z : K × K) :
    |fractalKernelReal (Real.sqrt 2) a z| ≤ a / (a - 1) :=
  abs_fractalKernelReal_le (Real.sqrt 2) ha z

/-! ## Measurability of `fractalKernel`

Under standard topological/measurable-space compatibility on `K`
(`OpensMeasurableSpace K` plus second-countability for the product),
the kernel is Borel-measurable. -/

/-- Each termwise summand is continuous, hence Borel-measurable. -/
theorem measurable_fractalKernelTerm
    [MeasurableSpace K] [SecondCountableTopology K] [OpensMeasurableSpace K]
    (α a : ℝ) (n : ℕ) :
    Measurable (fun z : K × K => fractalKernelTerm α a z n) := by
  unfold fractalKernelTerm
  have h_dist : Continuous (fun p : K × K => dist p.1 p.2) := continuous_dist
  have h_cos_arg : Continuous (fun z : K × K =>
      Real.pi * α ^ n * dist z.1 z.2) :=
    (continuous_const.mul h_dist)
  have h_cos : Continuous (fun z : K × K =>
      Real.cos (Real.pi * α ^ n * dist z.1 z.2)) :=
    Real.continuous_cos.comp h_cos_arg
  have h_scaled : Continuous (fun z : K × K =>
      a ^ (-(n : ℤ)) * Real.cos (Real.pi * α ^ n * dist z.1 z.2)) :=
    continuous_const.mul h_cos
  exact h_scaled.measurable

/-- Partial sums of `fractalKernelTerm` are measurable (finite sum of
    measurables). -/
theorem measurable_fractalKernelPartialSum
    [MeasurableSpace K] [SecondCountableTopology K] [OpensMeasurableSpace K]
    (α a : ℝ) (N : ℕ) :
    Measurable (fun z : K × K =>
      ∑ n ∈ Finset.range N, fractalKernelTerm α a z n) :=
  Finset.measurable_sum _ fun n _ => measurable_fractalKernelTerm α a n

/-- **Measurability of the V_P kernel**: the tsum-defined kernel is the
    pointwise limit of its measurable partial sums (under `a > 1`
    summability), so it is measurable. -/
theorem measurable_fractalKernelReal
    [MeasurableSpace K] [SecondCountableTopology K] [OpensMeasurableSpace K]
    (α : ℝ) {a : ℝ} (ha : 1 < a) :
    Measurable (fractalKernelReal α a : K × K → ℝ) := by
  refine measurable_of_tendsto_metrizable
      (f := fun N => fun z => ∑ n ∈ Finset.range N, fractalKernelTerm α a z n)
      (measurable_fractalKernelPartialSum α a) ?_
  rw [tendsto_pi_nhds]
  intro z
  -- For each z, partial sums tend to the tsum
  unfold fractalKernelReal
  exact (summable_fractalKernelTerm α ha z).hasSum.tendsto_sum_nat

/-- Measurability of the complexified kernel. -/
theorem measurable_fractalKernel
    [MeasurableSpace K] [SecondCountableTopology K] [OpensMeasurableSpace K]
    (α : ℝ) {a : ℝ} (ha : 1 < a) :
    Measurable (fractalKernel α a : K × K → ℂ) :=
  Complex.measurable_ofReal.comp (measurable_fractalKernelReal α ha)

end PrincipiaTractalis.IntegralKernel
