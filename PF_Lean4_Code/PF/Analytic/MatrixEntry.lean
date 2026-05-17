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
import PF.IntegralKernel.FractalKernel

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

/-! ## ★ Diagonal entries ★ -/

/-- **Kernel on the diagonal**: `V_P(x, x) = a/(a − 1)` for `a > 1`.

    On the diagonal, every distance is zero, so `cos(π·αⁿ·0) = 1` at
    every depth, and the kernel reduces to the geometric series
    `Σ a^(-n) = 1/(1 − 1/a) = a/(a−1)`. This is the maximum value of
    `V_P`. -/
theorem fractalKernelReal_diagonal {α a : ℝ} (ha : 1 < a) (x : ℝ) :
    fractalKernelReal α a ((x, x) : ℝ × ℝ) = a / (a - 1) := by
  unfold fractalKernelReal fractalKernelTerm
  have hd : dist x x = 0 := dist_self x
  have hterm : ∀ n : ℕ,
      (a : ℝ) ^ (-(n : ℤ)) * Real.cos (Real.pi * α ^ n * dist (x : ℝ) x) =
      (1 / a) ^ n := by
    intro n
    rw [hd, mul_zero, Real.cos_zero, mul_one]
    rw [zpow_neg, zpow_natCast, one_div, inv_pow]
  rw [tsum_congr hterm]
  have ha_pos : (0 : ℝ) < a := lt_trans zero_lt_one ha
  have h_inv_lt_one : (1 / a) < 1 := (div_lt_one ha_pos).mpr ha
  have h_inv_nn : (0 : ℝ) ≤ 1 / a := div_nonneg zero_le_one ha_pos.le
  rw [tsum_geometric_of_lt_one h_inv_nn h_inv_lt_one]
  rw [one_div]
  field_simp

/-- **Matrix diagonal**: `M_{bs, bs} = (1/2^n) · a/(a − 1)`.

    Every diagonal entry of the level-`n` matrix is the SAME constant
    `(1/2^n) · a/(a−1)`, independent of which boolean word `bs`
    indexes the cell. This is because the kernel `V_P` evaluated on
    the diagonal is independent of the point. -/
theorem cellMatrixEntry_diagonal {α a : ℝ} (ha : 1 < a) (n : ℕ)
    (bs : List Bool) :
    cellMatrixEntry α a n bs bs = (1 / (2 : ℝ)^n) * (a / (a - 1)) := by
  unfold cellMatrixEntry cantorKernel
  rw [fractalKernelReal_diagonal ha (cellMidpointOfBools bs)]

/-! ## Documentation: trace identity

The trace of the level-`n` matrix is the sum of its diagonal entries:

  `tr M^{(n)} = Σ_{bs : List Bool, bs.length = n} M^{(n)}_{bs, bs}
              = 2^n · (1/2^n) · a/(a − 1)
              = a/(a − 1)`

So the **trace is independent of the level `n`** — every finite-level
approximation has the same trace. By the spectral theorem, this trace
equals the sum of all `2^n` eigenvalues:

  `Σ_{k=1}^{2^n} λ^{(n)}_k = a/(a − 1)`

In the limit `n → ∞`, this becomes the (formally regularised) trace
of the full operator `H_P^cantor[μ_H]`, which is the polylog-series
sum:

  `Σ_{k≥0} λ_k = a/(a − 1)`  (formal, modulo convergence)

Under the polylog conjecture `λ_k = a^(-k) · Re[Li₁(e^{iπ·αᵏ})]`,
this becomes a constraint on the cosine averages of the principal
branch of `Li₁` evaluated at the points `e^{iπαᵏ}`.

This trace identity is a NONTRIVIAL EMPIRICAL TEST of any candidate
eigenvalue closed form: numerical eigenvalues of `M^{(n)}` must sum
to `a/(a−1)` exactly. -/

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
