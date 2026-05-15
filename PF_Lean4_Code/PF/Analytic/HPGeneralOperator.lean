/-
# General H_P Operator with Parameter `α`

The polylog-route's spectral analysis requires viewing `H_P` as a
function of the kernel parameter `α` (not the hardcoded `√2`). This
file defines the general `H_P_at α a` operator and establishes:

* Definition via `kernelOperator (fractalKernel α a)`.
* Reduction to `H_P_canonical` at `α = √2`.
* Self-adjointness (same proof as `H_P_canonical_isSelfAdjoint`).

These let us state the manuscript's spectral formula

  `λ_0(H_P_at α a) = π / (10 · α)`

(from `SpectralAnalysisFramework.lean`) as a property of the
general operator, parameterized by α.

Stage L4 — General H_P operator (α-parameterized).
-/

import PF.Analytic.SpectralAnalysisFramework
import PF.IntegralKernel.Bridge

namespace PrincipiaTractalis.Analytic

open Real MeasureTheory
open PrincipiaTractalis.TuringEncoding
open PrincipiaTractalis.IntegralKernel

variable {K : Type*} [PseudoMetricSpace K] [MeasurableSpace K]
  [SecondCountableTopology K] [OpensMeasurableSpace K]
  {μ : Measure K} [SFinite μ] [IsFiniteMeasure μ]

/-! ## General H_P operator -/

/-- **General H_P operator** with parameter `α`:

      `H_P_at α a := kernelOperator (fractalKernel α a)`

    where `α > 0` is the kernel scaling parameter and `a > 1` ensures
    absolute convergence of the fractal-kernel series. The canonical
    `H_P_canonical` is the specific case `α = √2`. -/
noncomputable def H_P_at (α : ℝ) {a : ℝ} (ha : 1 < a) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  kernelOperator
    (measurable_fractalKernel α ha)
    (memLp_fractalKernel α ha μ 2)

/-- **Reduction to `H_P_canonical`**: `H_P_at √2 a = H_P_canonical a`. -/
theorem H_P_at_sqrt2_eq_canonical {a : ℝ} (ha : 1 < a) :
    H_P_at (μ := μ) (Real.sqrt 2) ha = H_P_canonical (μ := μ) ha := rfl

/-- **Self-adjointness of `H_P_at α a`** for any α > 0.

    Same proof structure as `H_P_canonical_isSelfAdjoint`. -/
theorem H_P_at_isSelfAdjoint {α a : ℝ} (ha : 1 < a) :
    IsSelfAdjoint (H_P_at (μ := μ) α ha) := by
  apply isSelfAdjoint_of_kernel_conjSymm
      (V := fractalKernel α a)
      (T := H_P_at (μ := μ) α ha)
  · intro g
    exact coeFn_kernelOperatorFn
      (measurable_fractalKernel α ha)
      (memLp_fractalKernel α ha μ 2) g
  · exact fractalKernel_isConjSymmetric α a μ
  · intro f g
    have h_a_pos : 0 < a := lt_trans zero_lt_one ha
    have h_C_nn : 0 ≤ a / (a - 1) := div_nonneg h_a_pos.le (by linarith)
    have h_Vbdd : ∀ z : K × K,
        ‖(fractalKernel α a) z‖ ≤ a / (a - 1) := by
      intro z
      unfold fractalKernel
      rw [show ‖(((fractalKernelReal α a z : ℝ) : ℂ))‖ =
            |fractalKernelReal α a z| from
          RCLike.norm_ofReal (K := ℂ) _]
      exact abs_fractalKernelReal_le α ha z
    exact integrable_pairingIntegrand_of_bounded
      (measurable_fractalKernel α ha) h_C_nn h_Vbdd
      (Lp.memLp f) (Lp.memLp g)

/-! ## Spectral formula as a structured predicate for the general operator

The manuscript's eigenvalue formula `λ_0(H_P α) = π/(10·α)` becomes a
PROPERTY of the parameterized operator. The framework predicate:

```
HPSpectralFormula α λ := λ = π / (10 · α)
```

is already defined in `SpectralAnalysisFramework.lean`. We re-export
a convenient corollary tying it to the general operator. -/

/-- **Bridge**: if `λ` is the ground-state eigenvalue of `H_P_at α a`
    (in some abstract sense, established by the manuscript's spectral
    analysis), and if `HPSpectralFormula α λ` holds, then we have the
    eigenvalue formula. Trivial bookkeeping. -/
theorem groundState_eigenvalue_equals_pi_div_ten_alpha
    {α : ℝ} {lambda : ℝ}
    (h_formula : HPSpectralFormula α lambda) :
    lambda = Real.pi / (10 * α) := h_formula

/-! ## Connection to axiom retirement

The full chain (already proven in `SpectralAnalysisFramework.lean`):

```
0 < alpha_of_class ClassP                              [manuscript]
  ∧ HPSpectralFormula (alpha_of_class ClassP) λ_HP    [Ch 21 spectral]
  ∧ λ_HP = lambda_zero_HP_book                         [Ch 21 + BookEig + IVT]
  ∧ 0 < alpha_of_class ClassNP                         [manuscript]
  ∧ alpha_of_class ClassNP = phi + 1/4                 [manuscript]
  ⟹ alpha_class_self_adjointness_canonical content
```

With `H_P_at` parameterized as above, the `HPSpectralFormula` hypothesis
acquires concrete meaning: it's a CLAIM about the ground-state
eigenvalue of `H_P_at α a` (i.e., `kernelOperator (fractalKernel α a)`).

**Operator-theoretic content of the manuscript's derivation**:

The fractal-kernel structure `V_P(x,y) = Σ a^(-n) cos(π α^n d(x,y))`
gives an operator with self-similar spectral properties. Manuscript
Ch 21 derives (multi-page analysis):
* The kernel admits a Fourier-cosine decomposition on the domain K.
* The eigenvalues correspond to specific modes indexed by integers.
* The smallest positive eigenvalue (ground state) has the form
  `π/(10·α)` — the factor `10` arises from a 5-fold symmetry or
  specific normalization in the canonical setup.

Mechanizing this derivation requires:
1. Spectral theorem for compact self-adjoint operators on Lp ℂ 2
   (mathlib has this).
2. Computation of `H_P_at α a` action on Fourier-cosine eigenmodes.
3. Identification of the ground-state mode.
4. Computation of its eigenvalue in terms of α.

Each step is tractable but requires the manuscript's specific
arguments. The framework here ensures that once any one specific
derivation gives `HPSpectralFormula (alpha_of_class ClassP) λ_HP`,
the axiom retires.
-/

end PrincipiaTractalis.Analytic
