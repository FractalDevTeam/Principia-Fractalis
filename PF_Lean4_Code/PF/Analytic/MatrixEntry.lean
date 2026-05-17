/-
# Matrix-Entry Framework for the Discrete Eigenvalue Problem

The finite-rank operator `H_P^disc[cantorDiscMeasure n]` acting on
functions on the level-`n` cell midpoints is naturally a `2^n × 2^n`
real matrix. Indexed by length-`n` boolean lists `(bs, bs')`, the
matrix entries are:

  `M_{bs, bs'} := (1/2^n) · V_P(m_{bs}, m_{bs'})`

where `m_{bs} := cellMidpointOfBools bs` is the cell midpoint
indexed by `bs`.

This file:
* Defines `cellMatrixEntry` as the matrix-entry function.
* Proves SYMMETRY of the matrix (`M_{bs, bs'} = M_{bs', bs}`).
* Documents the eigenvalue problem at finite level.

The matrix's eigenvalues at level `n` are the finite-rank
approximations to the eigenvalues of the full operator
`H_P^cantor[μ_H]` (modulo the Wasserstein convergence of
`cantorDiscMeasure n → μ_H`).

Stage L4+ — discrete eigenvalue matrix framework.
-/

import PF.Analytic.CellMidpoint

namespace PrincipiaTractalis.Analytic

open PrincipiaTractalis.IntegralKernel

/-! ## Matrix-entry definition -/

/-- **Matrix entry** for the discrete eigenvalue problem at level `n`:

      `M_{bs, bs'} := (1/2^n) · V_P(m_{bs}, m_{bs'})`

    Indexed by pairs of length-`n` boolean lists, with `m_{bs} :=
    cellMidpointOfBools bs` the cell midpoint indexed by `bs`. The
    `1/2^n` prefactor comes from the Hutchinson measure weights of
    each cell at level `n`. -/
noncomputable def cellMatrixEntry
    (α a : ℝ) (n : ℕ) (bs bs' : List Bool) : ℝ :=
  (1 / (2 : ℝ)^n) *
  cantorKernel α a (cellMidpointOfBools bs) (cellMidpointOfBools bs')

/-! ## ★ Symmetry ★ -/

/-- **★ Matrix symmetry ★**: `M_{bs, bs'} = M_{bs', bs}`.

    The fractal kernel `V_P` is symmetric (`V_P(x, y) = V_P(y, x)`,
    via `fractalKernelReal_swap`), and the `1/2^n` prefactor is the
    same on both sides. So the matrix is symmetric, which makes the
    discrete operator `H_P^disc[cantorDiscMeasure n]` (restricted to
    the midpoint span) **SELF-ADJOINT** as a `2^n × 2^n` real
    symmetric matrix.

    **Spectral consequence**: by the finite-dimensional spectral
    theorem, the matrix has `2^n` real eigenvalues (with real
    eigenvectors). These are the finite-rank approximations to the
    eigenvalues of the full operator `H_P^cantor[μ_H]`. -/
theorem cellMatrixEntry_symm (α a : ℝ) (n : ℕ) (bs bs' : List Bool) :
    cellMatrixEntry α a n bs bs' = cellMatrixEntry α a n bs' bs := by
  unfold cellMatrixEntry cantorKernel
  congr 1
  have h := fractalKernelReal_swap α a
    ((cellMidpointOfBools bs, cellMidpointOfBools bs') : ℝ × ℝ)
  simp [Prod.swap] at h
  rw [← h]

/-! ## Documentation: the discrete eigenvalue problem

At each level `n`, the framework gives a `2^n × 2^n` REAL SYMMETRIC
MATRIX with explicit closed-form entries:

  `M^{(n)}_{bs, bs'} = (1/2^n) · V_P(m_{bs}, m_{bs'})`
                     = `(1/2^n) · Σ_{k≥0} a^(-k) · cos(π · αᵏ · |m_{bs} − m_{bs'}|)`

By the finite-dimensional spectral theorem, `M^{(n)}` has exactly
`2^n` real eigenvalues `λ^{(n)}_1, ..., λ^{(n)}_{2^n}` with
orthonormal eigenvectors.

**Spectral convergence**: as `n → ∞`, the eigenvalues
`λ^{(n)}_k → λ_k(H_P^cantor[μ_H])` for each `k`. This is the
content of the Banach contraction → Wasserstein convergence →
spectral continuity argument. The conjectured polylog values
`λ_k = a^(-k) · Re[Li₁(e^{iπ·αᵏ})]` (on the physical Riemann
sheet) are the predicted limits.

**Computational path**: at any specific `(α, a, n)`, the matrix
`M^{(n)}` has explicit closed-form entries (sums over `k` of the
fractal-kernel terms). The eigenvalue problem can in principle be
SOLVED NUMERICALLY for any specific level `n`, and the convergence
of these numerical eigenvalues toward the polylog formula tested
empirically.

For `α = √2`, the manuscript's finite-dim numerical computations
already give `λ_0(H_P) ≈ 0.2221441469 ± 10⁻¹⁰` (matching `π/(10·√2)`
to 10 digits). The matrix-entry framework here is the formal
Lean-side counterpart of those numerical experiments, with the
matrix entries machine-checked closed forms. -/

end PrincipiaTractalis.Analytic
