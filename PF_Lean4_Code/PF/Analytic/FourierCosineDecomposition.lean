/-
# Fourier-Cosine Decomposition of the Fractal Kernel

The first analytic step toward the manuscript's spectral formula
`λ_0(H_P_at α a) = π/(10·α)`: the Fourier-cosine decomposition of
the fractal kernel.

**Setup**: On `K = ℝ` (or any subset like `[0, 1]`) with the usual
absolute-value distance `d(x, y) = |x − y|`, the cosine kernel
`cos(πα^n |x − y|)` admits the rank-2 separable decomposition

  `cos(πα^n (x − y)) = cos(πα^n x) · cos(πα^n y)
                     + sin(πα^n x) · sin(πα^n y)`

(via the cosine subtraction formula `cos(u − v) = cos u · cos v +
sin u · sin v`, plus the evenness `cos(α|x − y|) = cos(α(x − y))`).

This is a **Mercer-type decomposition**: each cosine kernel is the
sum of two rank-1 tensor products, with eigenfunctions `cos(πα^n x)`
and `sin(πα^n x)`.

**Implication for the fractal kernel**: on `K = ℝ`,

  `fractalKernelReal α a (x, y) = Σ a^(-n) · cos(πα^n |x − y|)
                                = Σ a^(-n) · (cos(πα^n x) · cos(πα^n y)
                                             + sin(πα^n x) · sin(πα^n y))`

This expresses `V_P` as a sum of rank-2 tensor-product operators,
each acting on the cosine/sine modes `{cos(πα^n x), sin(πα^n x)}`.

This file:
* Defines the cosine-mode and sine-mode functions.
* Proves the per-term decomposition on `K = ℝ`.
* Provides the fractal-kernel decomposition.

Stage L4 — Fourier-cosine decomposition (spectral derivation step 1).
-/

import PF.Analytic.HPGeneralOperator

namespace PrincipiaTractalis.Analytic

open Real

/-! ## Cosine and sine modes -/

/-- **Cosine mode** at scale `n` with parameter `α`:
    `cosineMode α n x := cos(πα^n x)`.

    For each fixed `α, n`, this is the candidate eigenfunction of the
    `n`-th cosine kernel `cos(πα^n |·|)`. -/
noncomputable def cosineMode (α : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Real.cos (Real.pi * α ^ n * x)

/-- **Sine mode** at scale `n` with parameter `α`:
    `sineMode α n x := sin(πα^n x)`. -/
noncomputable def sineMode (α : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Real.sin (Real.pi * α ^ n * x)

/-! ## Per-term Fourier-cosine decomposition -/

/-- **Rank-2 decomposition of the cosine kernel** on `K = ℝ`:

      `cos(πα^n (x − y)) = cos(πα^n x) · cos(πα^n y) +
                          sin(πα^n x) · sin(πα^n y)`.

    Direct from `Real.cos_sub`. -/
theorem cos_kernel_decomp (α : ℝ) (n : ℕ) (x y : ℝ) :
    Real.cos (Real.pi * α ^ n * (x - y)) =
    cosineMode α n x * cosineMode α n y +
    sineMode α n x * sineMode α n y := by
  unfold cosineMode sineMode
  rw [show Real.pi * α ^ n * (x - y) =
        Real.pi * α ^ n * x - Real.pi * α ^ n * y from by ring]
  exact Real.cos_sub _ _

/-- **Rank-2 decomposition for `|x − y|`**: since `cos` is even,

      `cos(πα^n |x − y|) = cos(πα^n (x − y))
                         = cosineMode α n x · cosineMode α n y +
                           sineMode α n x · sineMode α n y`. -/
theorem cos_kernel_decomp_abs (α : ℝ) (n : ℕ) (x y : ℝ) :
    Real.cos (Real.pi * α ^ n * |x - y|) =
    cosineMode α n x * cosineMode α n y +
    sineMode α n x * sineMode α n y := by
  rw [show Real.cos (Real.pi * α ^ n * |x - y|) =
        Real.cos (Real.pi * α ^ n * (x - y)) by
        rcases le_or_gt 0 (x - y) with h | h
        · rw [abs_of_nonneg h]
        · rw [abs_of_neg h]
          rw [show Real.pi * α ^ n * -(x - y) = -(Real.pi * α ^ n * (x - y))
              from by ring]
          exact Real.cos_neg _]
  exact cos_kernel_decomp α n x y

/-! ## Action of cosine kernel on cosine modes (per-scale eigenvalue) -/

/-- **Inner product of cosine modes**: for the operator action
    perspective, we'll need integrals of `cosineMode α n x · cosineMode α n y`
    against test functions. The natural eigenfunctions of the cosine
    kernel on `[0, 1]` are linear combinations of cosineMode/sineMode.

    The per-scale eigenvalue formula (manuscript Ch 21 derivation):
    for the kernel `cos(πα^n |x - y|)` acting on `L²([0, 1])`, the
    smallest eigenvalue is associated with the lowest-frequency mode,
    giving a contribution `1/(πα^n)` (up to normalization). -/
theorem fractalKernel_term_decomp_at_R
    (α a : ℝ) (n : ℕ) (x y : ℝ) :
    a ^ (-(n : ℤ)) * Real.cos (Real.pi * α ^ n * |x - y|) =
    a ^ (-(n : ℤ)) *
      (cosineMode α n x * cosineMode α n y +
       sineMode α n x * sineMode α n y) := by
  rw [cos_kernel_decomp_abs]

/-! ## Documentation: full Mercer-type decomposition

For `K = ℝ` (or `[0, 1]`), the fractal kernel admits the formal
decomposition:

```
fractalKernelReal α a (x, y) = Σ a^(-n) · (cosineMode α n x · cosineMode α n y +
                                            sineMode α n x · sineMode α n y)
```

In operator form:
```
(H_P_at α a) f (x) = Σ a^(-n) · [
    cosineMode α n x · ⟨cosineMode α n, f⟩_L² +
    sineMode α n x · ⟨sineMode α n, f⟩_L²
]
```

This is a **rank-2-per-scale Mercer decomposition**. The eigenvectors
are linear combinations of `cosineMode α n` and `sineMode α n` for
various `n`. The eigenvalues come from the `a^(-n)` weights modulated
by the orthogonality structure of these modes on the domain.

**Manuscript's ground-state derivation** (Ch 21 outline):

1. **Identify the ground state**: the lowest-frequency mode `n = 0`,
   giving `cos(π·x)` and `sin(π·x)` (since `α^0 = 1`).
2. **Compute its eigenvalue**: action of the entire series Σ a^(-n)·cos(πα^n|·|)
   on `cos(π·x)` gives the lowest eigenvalue.
3. **Closed form**: for the canonical normalization, the result is
   `π/(10·α)` — the factor `10` from a 5-fold normalization in the
   manuscript's specific scaling.

The Fourier-cosine decomposition proven here is **step 1** of the
spectral derivation. Mechanizing steps 2-3 requires:
* Inner-product computations on `L²([0, 1])` or appropriate domain.
* Diagonalization of the cosine-kernel operator.
* Identification of the smallest eigenvalue.

These are tractable in mathlib's `MeasureTheory.L2Space` and
`Mathlib.Analysis.InnerProductSpace.Spectrum` infrastructure, but
each requires focused work to connect to the specific manuscript
normalization.
-/

end PrincipiaTractalis.Analytic
