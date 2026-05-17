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

open PrincipiaTractalis.IntegralKernel MeasureTheory

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

/-! ## ★ Level-1 explicit matrix ★ -/

/-- **Level-1 off-diagonal distance**: `|m_{[false]} − m_{[true]}| = 2/3`.

    The level-1 cells `[0, 1/3]` and `[2/3, 1]` have midpoints `1/6`
    and `5/6` respectively; their distance is `2/3` (which is the
    "gap" length between the two cells plus the half-cell offsets). -/
theorem cellMidpoint_level1_distance :
    dist (cellMidpointOfBools [false]) (cellMidpointOfBools [true]) = 2/3 := by
  rw [cellMidpointOfBools_false, cellMidpointOfBools_true]
  rw [Real.dist_eq]
  norm_num

/-- **Level-1 matrix off-diagonal entry**: closed form as a tsum.

      `M^{(1)}_{[false], [true]} = (1/2) · Σ a^(-n) · cos(π · αⁿ · 2/3)`

    This is the SINGLE off-diagonal entry (modulo symmetry) of the
    `2 × 2` matrix at level 1. Combined with `cellMatrixEntry_diagonal`,
    the level-1 matrix is:

      `M^{(1)} = (1/2) · [[a/(a−1), V_P(1/6,5/6)], [V_P(1/6,5/6), a/(a−1)]]`

    Its eigenvalues are `(1/2) · (a/(a−1) ± V_P(1/6,5/6))` — explicit
    finite-rank approximations to the spectrum of `H_P^cantor[μ_H]`. -/
theorem cellMatrixEntry_level1_offdiag (α a : ℝ) :
    cellMatrixEntry α a 1 [false] [true] =
    (1 / 2) * ∑' n : ℕ, a ^ (-(n : ℤ)) * Real.cos (Real.pi * α ^ n * (2/3)) := by
  unfold cellMatrixEntry cantorKernel fractalKernelReal fractalKernelTerm
  congr 1
  · norm_num
  · apply tsum_congr
    intro n
    rw [cellMidpoint_level1_distance]

/-! ## ★ Level-0 discrete operator action ★ -/

/-- **Level-0 single eigenvalue**:

      `λ^{(0)}_0 := a/(a − 1)`

    The level-0 measure `cantorDiscMeasure 0 = δ_{1/2}` gives a 1×1
    "matrix" `M^{(0)} = [a/(a−1)]` with the single eigenvalue equal
    to the diagonal entry. -/
noncomputable def lambdaLevel0 (a : ℝ) : ℝ := a / (a - 1)

/-- **★ Level-0 eigenvector identity ★**:

    The constant function `f ≡ 1` is an eigenvector of
    `H_P^disc[cantorDiscMeasure 0]` with eigenvalue `a/(a − 1)`:

      `(H_P^disc[δ_{1/2}] 1)(1/2) = V_P(1/2, 1/2) · 1 = a/(a − 1) = λ^{(0)}_0` -/
theorem level0_eigenvector_identity {α a : ℝ} (ha : 1 < a) :
    H_P_at_disc α a (cantorDiscMeasure 0) (fun _ => (1 : ℝ)) (1/2) =
    lambdaLevel0 a := by
  rw [H_P_at_disc_cantorDiscMeasure_zero]
  unfold lambdaLevel0 cantorKernel
  rw [fractalKernelReal_diagonal ha (1/2)]
  ring

/-- **Level-0 eigenvalue positivity** (a > 1): `λ^{(0)}_0 = a/(a−1) > 0`. -/
theorem lambdaLevel0_pos {a : ℝ} (ha : 1 < a) : 0 < lambdaLevel0 a := by
  unfold lambdaLevel0
  apply div_pos
  · linarith
  · linarith

/-- **Level-0 trace = sole eigenvalue**: at the trivial 1×1 level, the
    trace equals the operator-norm bound exactly. The "spectrum"
    `{λ^{(0)}_0} = {a/(a−1)}` saturates the operator-norm bound. -/
theorem lambdaLevel0_eq_op_norm {a : ℝ} : lambdaLevel0 a = a / (a - 1) := rfl

/-! ## ★ Level-1 discrete operator action ★ -/

/-- **Level-1 explicit operator action**:

      `(H_P^disc[cantorDiscMeasure 1] f)(x) =
            (1/2) · V_P(x, 1/6) · f(1/6) +
            (1/2) · V_P(x, 5/6) · f(5/6)`

    The level-1 discrete operator is a `2 × 2` matrix acting on the
    pair `(f(1/6), f(5/6))`. Specialising `x ∈ {1/6, 5/6}` gives the
    full matrix-vector product (matrix-form action on the midpoint
    span). -/
theorem H_P_at_disc_cantorDiscMeasure_one (α a : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    H_P_at_disc α a (cantorDiscMeasure 1) f x =
      (1/2) * (cantorKernel α a x (1/6) * f (1/6)) +
      (1/2) * (cantorKernel α a x (5/6) * f (5/6)) := by
  unfold H_P_at_disc
  rw [cantorDiscMeasure_one]
  rw [integral_add_measure]
  · rw [integral_smul_measure, integral_smul_measure,
        integral_dirac, integral_dirac]
    simp [ENNReal.toReal_ofNat]
  · refine Integrable.smul_measure ?_ (by simp : ((1/2 : ENNReal) : ENNReal) ≠ ⊤)
    exact integrable_dirac (by
      rw [enorm_mul]
      exact ENNReal.mul_lt_top (by simp [enorm_eq_nnnorm])
        (by simp [enorm_eq_nnnorm]))
  · refine Integrable.smul_measure ?_ (by simp : ((1/2 : ENNReal) : ENNReal) ≠ ⊤)
    exact integrable_dirac (by
      rw [enorm_mul]
      exact ENNReal.mul_lt_top (by simp [enorm_eq_nnnorm])
        (by simp [enorm_eq_nnnorm]))

/-! ## ★ Level-2 discrete operator action ★ -/

/-- **Level-2 explicit operator action**:

      `(H_P^disc[cantorDiscMeasure 2] f)(x) =
            (1/4) · V_P(x, 1/18)  · f(1/18)
          + (1/4) · V_P(x, 13/18) · f(13/18)
          + (1/4) · V_P(x, 5/18)  · f(5/18)
          + (1/4) · V_P(x, 17/18) · f(17/18)`

    The level-2 discrete operator is a 4×4 matrix acting on the
    quadruple `(f(1/18), f(5/18), f(13/18), f(17/18))`. Specialising
    `x ∈ {1/18, 5/18, 13/18, 17/18}` gives the full matrix-vector
    product.

    (Note the ordering: the natural Hutchinson-iteration order is
    `{1/18, 13/18, 5/18, 17/18}` — `f₁` children first, then `f₂`
    children — matching `cantorDiscMeasure_two`.) -/
theorem H_P_at_disc_cantorDiscMeasure_two (α a : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    H_P_at_disc α a (cantorDiscMeasure 2) f x =
      (1/4) * (cantorKernel α a x (1/18) * f (1/18)) +
      (1/4) * (cantorKernel α a x (13/18) * f (13/18)) +
      ((1/4) * (cantorKernel α a x (5/18) * f (5/18)) +
       (1/4) * (cantorKernel α a x (17/18) * f (17/18))) := by
  unfold H_P_at_disc
  rw [cantorDiscMeasure_two]
  -- two-step integral add: ((m₁ + m₂) + (m₃ + m₄))
  -- structurally: μ = (a + b) + (c + d) where each a,b,c,d is (1/4)·dirac
  set ν1 : MeasureTheory.Measure ℝ := (1/4 : ENNReal) • MeasureTheory.Measure.dirac (1/18 : ℝ) with hν1
  set ν2 : MeasureTheory.Measure ℝ := (1/4 : ENNReal) • MeasureTheory.Measure.dirac (13/18 : ℝ) with hν2
  set ν3 : MeasureTheory.Measure ℝ := (1/4 : ENNReal) • MeasureTheory.Measure.dirac (5/18 : ℝ) with hν3
  set ν4 : MeasureTheory.Measure ℝ := (1/4 : ENNReal) • MeasureTheory.Measure.dirac (17/18 : ℝ) with hν4
  -- Each νᵢ is a scaled Dirac → integrand integrable
  have hint : ∀ z : ℝ, MeasureTheory.Integrable
      (fun y => cantorKernel α a x y * f y)
      ((1/4 : ENNReal) • MeasureTheory.Measure.dirac z) := by
    intro z
    refine Integrable.smul_measure ?_ (by simp : ((1/4 : ENNReal) : ENNReal) ≠ ⊤)
    exact integrable_dirac (by
      rw [enorm_mul]
      exact ENNReal.mul_lt_top (by simp [enorm_eq_nnnorm])
        (by simp [enorm_eq_nnnorm]))
  -- (ν1 + ν2) + (ν3 + ν4)
  rw [integral_add_measure (Integrable.add_measure (hint _) (hint _))
                           (Integrable.add_measure (hint _) (hint _))]
  rw [integral_add_measure (hint _) (hint _),
      integral_add_measure (hint _) (hint _)]
  rw [integral_smul_measure, integral_smul_measure,
      integral_smul_measure, integral_smul_measure]
  rw [integral_dirac, integral_dirac, integral_dirac, integral_dirac]
  simp [ENNReal.toReal_ofNat]

/-- **★ Level-2 constant-vector evaluation at x = 1/18 ★**:

    For the constant function `f ≡ 1`,

      `(H_P^disc[cantorDiscMeasure 2] 1)(1/18)
         = (1/4) · (a/(a−1) + V_P(2/3) + V_P(2/9) + V_P(8/9))`

    where `V_P(d) := V_P(x, y)` for any `(x, y)` with `dist(x, y) = d`
    (depending only on distance by symmetry).

    Computes the sum of the first row of `M^{(2)}`. This is the "row
    sum" diagnostic: under the constant test function `1`, the
    operator value at `x = m_{[ff]} = 1/18` equals the sum of all
    matrix entries in row `[ff]`. -/
theorem level2_constant_at_ff {α a : ℝ} (ha : 1 < a) :
    H_P_at_disc α a (cantorDiscMeasure 2) (fun _ => (1 : ℝ)) (1/18) =
    (1/4) * (a/(a-1) +
             fractalKernelReal α a ((1/18, 13/18) : ℝ × ℝ) +
             fractalKernelReal α a ((1/18, 5/18) : ℝ × ℝ) +
             fractalKernelReal α a ((1/18, 17/18) : ℝ × ℝ)) := by
  rw [H_P_at_disc_cantorDiscMeasure_two]
  unfold cantorKernel
  rw [fractalKernelReal_diagonal ha (1/18)]
  ring

/-- **★ Level-2 constant-vector evaluation at x = 5/18 ★**:

      `(H_P^disc[cantorDiscMeasure 2] 1)(5/18)
         = (1/4) · (V_P(2/9) + V_P(4/9) + a/(a−1) + V_P(2/3))`

    The second-row sum of `M^{(2)}`. Compare with `level2_constant_at_ff`
    (first-row sum) to see that the row sums DIFFER — the difference

      `V_P(8/9) − V_P(4/9)`

    is generically nonzero, so the constant function is NOT a level-2
    eigenvector (in contrast with level 1 where the constant IS the
    symmetric eigenvector). The true level-2 sym/antisym eigenvectors
    live in the (a, b, b, a) and (a, b, −b, −a) sub-blocks under the
    IFS reflection `x ↦ 1 − x`. -/
theorem level2_constant_at_ft {α a : ℝ} (ha : 1 < a) :
    H_P_at_disc α a (cantorDiscMeasure 2) (fun _ => (1 : ℝ)) (5/18) =
    (1/4) * (fractalKernelReal α a ((5/18, 1/18) : ℝ × ℝ) +
             fractalKernelReal α a ((5/18, 13/18) : ℝ × ℝ) +
             a/(a-1) +
             fractalKernelReal α a ((5/18, 17/18) : ℝ × ℝ)) := by
  rw [H_P_at_disc_cantorDiscMeasure_two]
  unfold cantorKernel
  rw [fractalKernelReal_diagonal ha (5/18)]
  ring

/-- **★ Level-2 NON-eigenvector statement ★**:

    The first-row sum at `x = 1/18` and second-row sum at `x = 5/18`
    of the constant test function under `H_P^disc[cantorDiscMeasure 2]`
    differ by

      `(1/4) · (V_P(1/18, 17/18) − V_P(5/18, 13/18))`
      `= (1/4) · (V_P(8/9) − V_P(4/9))`

    (where the kernel depends only on distance). When this difference
    is nonzero (the GENERIC case — true for `α = √2` and most other α),
    the constant function is NOT a level-2 eigenvector of
    `H_P^disc[cantorDiscMeasure 2]`. This is the explicit witness for
    the breakdown of the constant as an eigenvector at level 2 (compare
    `level1_sym_eigenvector_at_{left,right}` where it IS an eigenvector). -/
theorem level2_constant_row_diff {α a : ℝ} (ha : 1 < a) :
    H_P_at_disc α a (cantorDiscMeasure 2) (fun _ => (1 : ℝ)) (1/18) -
    H_P_at_disc α a (cantorDiscMeasure 2) (fun _ => (1 : ℝ)) (5/18) =
    (1/4) * (fractalKernelReal α a ((1/18, 17/18) : ℝ × ℝ) -
             fractalKernelReal α a ((5/18, 13/18) : ℝ × ℝ)) := by
  rw [level2_constant_at_ff ha, level2_constant_at_ft ha]
  -- Use V_P symmetry to consolidate the cross terms.
  have hsym1 : fractalKernelReal α a (((1/18 : ℝ), (13/18 : ℝ)) : ℝ × ℝ)
             = fractalKernelReal α a (((13/18 : ℝ), (1/18 : ℝ)) : ℝ × ℝ) := by
    have h := fractalKernelReal_swap α a (((13/18 : ℝ), (1/18 : ℝ)) : ℝ × ℝ)
    have hswap : (((13/18 : ℝ), (1/18 : ℝ)) : ℝ × ℝ).swap
               = (((1/18 : ℝ), (13/18 : ℝ)) : ℝ × ℝ) := rfl
    rw [hswap] at h
    exact h
  -- 5/18 → 13/18 vs 1/18 → 13/18: different (5/18, 13/18)
  -- but symmetry of V_P implies V_P((5/18, 13/18)) = V_P((13/18, 5/18))
  -- and V_P((1/18, 5/18)) = V_P((5/18, 1/18))
  -- This doesn't directly cancel; the difference is genuinely V_P(8/9) - V_P(4/9).
  have hsym2 : fractalKernelReal α a (((1/18 : ℝ), (5/18 : ℝ)) : ℝ × ℝ)
             = fractalKernelReal α a (((5/18 : ℝ), (1/18 : ℝ)) : ℝ × ℝ) := by
    have h := fractalKernelReal_swap α a (((5/18 : ℝ), (1/18 : ℝ)) : ℝ × ℝ)
    have hswap : (((5/18 : ℝ), (1/18 : ℝ)) : ℝ × ℝ).swap
               = (((1/18 : ℝ), (5/18 : ℝ)) : ℝ × ℝ) := rfl
    rw [hswap] at h
    exact h
  -- distance-equality cross-terms:
  -- V_P(1/18, 13/18) (dist 2/3) = V_P(5/18, 17/18) (dist 2/3)
  -- both are the same V_P value at distance 2/3
  have hd_2_3_a : dist ((1/18 : ℝ)) (13/18 : ℝ) = 2/3 := by
    rw [Real.dist_eq]; norm_num
  have hd_2_3_b : dist ((5/18 : ℝ)) (17/18 : ℝ) = 2/3 := by
    rw [Real.dist_eq]; norm_num
  have hd_2_9_a : dist ((1/18 : ℝ)) (5/18 : ℝ) = 2/9 := by
    rw [Real.dist_eq]; norm_num
  have hd_2_9_b : dist ((5/18 : ℝ)) (1/18 : ℝ) = 2/9 := by
    rw [Real.dist_eq]; norm_num
  -- The dist-based equality: V_P depends only on dist, so equal dists give
  -- equal V_P. We use the explicit form `fractalKernelReal_swap` and the
  -- fact that the tsum depends only on dist.
  have h_2_3 : fractalKernelReal α a (((1/18 : ℝ), (13/18 : ℝ)) : ℝ × ℝ)
             = fractalKernelReal α a (((5/18 : ℝ), (17/18 : ℝ)) : ℝ × ℝ) := by
    unfold fractalKernelReal fractalKernelTerm
    apply tsum_congr; intro n
    rw [hd_2_3_a, hd_2_3_b]
  have h_2_9 : fractalKernelReal α a (((1/18 : ℝ), (5/18 : ℝ)) : ℝ × ℝ)
             = fractalKernelReal α a (((5/18 : ℝ), (1/18 : ℝ)) : ℝ × ℝ) := hsym2
  rw [h_2_3]
  -- Now goal: 1/4 * (a/(a-1) + V_P(5/18,17/18) + V_P(1/18,5/18) + V_P(1/18,17/18))
  --        - 1/4 * (V_P(5/18,1/18) + V_P(5/18,13/18) + a/(a-1) + V_P(5/18,17/18))
  --       = 1/4 * (V_P(1/18,17/18) - V_P(5/18,13/18))
  -- This reduces to V_P(1/18, 5/18) = V_P(5/18, 1/18), which is hsym2.
  rw [hsym2]
  ring

/-- **★ Level-2 symmetric-test action at x = 1/18 ★**:

    For any test function `f : ℝ → ℝ` with `f(1/18) = f(17/18) = c` and
    `f(5/18) = f(13/18) = d` (the **symmetric** values under the IFS
    reflection `x ↦ 1 − x`), the operator action at `x = 1/18` is:

      `(H_P^disc[cantorDiscMeasure 2] f)(1/18)
         = (1/4) · ((a/(a−1) + V_P(8/9)) · c
                  + (V_P(2/3)  + V_P(2/9)) · d)`

    This is the FIRST ROW of the symmetric 2×2 sub-block of `M^{(2)}`.
    The symmetric block (under the reflection) has form

      `B_sym = (1/4) · [[d + V_P(8/9),    e + V_P(2/9)],
                        [e + V_P(2/9),    d + V_P(4/9)]]`

    where `d = a/(a−1)` and `e = V_P(2/3)`.

    Combined with the antisymmetric counterpart (a parametric form
    for `f(1/18) = c, f(13/18) = d, f(5/18) = −d, f(17/18) = −c`),
    this fully decomposes the 4×4 problem into two 2×2 problems —
    the IFS-reflection block structure. -/
theorem level2_sym_action_at_ff {α a : ℝ} (ha : 1 < a)
    (c d : ℝ) (f : ℝ → ℝ)
    (h1 : f (1/18) = c) (h2 : f (5/18) = d)
    (h3 : f (13/18) = d) (h4 : f (17/18) = c) :
    H_P_at_disc α a (cantorDiscMeasure 2) f (1/18) =
    (1/4) * ((a/(a-1) + fractalKernelReal α a ((1/18, 17/18) : ℝ × ℝ)) * c +
             (fractalKernelReal α a ((1/18, 13/18) : ℝ × ℝ) +
              fractalKernelReal α a ((1/18, 5/18) : ℝ × ℝ)) * d) := by
  rw [H_P_at_disc_cantorDiscMeasure_two]
  rw [h1, h2, h3, h4]
  unfold cantorKernel
  rw [fractalKernelReal_diagonal ha (1/18)]
  ring

/-- **★ Level-2 antisymmetric-test action at x = 1/18 ★**:

    For any test function `f : ℝ → ℝ` with `f(1/18) = c`, `f(13/18) = d`,
    `f(5/18) = −d`, `f(17/18) = −c` (the **antisymmetric** values under
    the IFS reflection `x ↦ 1 − x`), the operator action at `x = 1/18` is:

      `(H_P^disc[cantorDiscMeasure 2] f)(1/18)
         = (1/4) · ((a/(a−1) − V_P(8/9)) · c
                  + (V_P(2/3)  − V_P(2/9)) · d)`

    This is the FIRST ROW of the antisymmetric 2×2 sub-block of `M^{(2)}`. -/
theorem level2_antisym_action_at_ff {α a : ℝ} (ha : 1 < a)
    (c d : ℝ) (f : ℝ → ℝ)
    (h1 : f (1/18) = c) (h2 : f (5/18) = -d)
    (h3 : f (13/18) = d) (h4 : f (17/18) = -c) :
    H_P_at_disc α a (cantorDiscMeasure 2) f (1/18) =
    (1/4) * ((a/(a-1) - fractalKernelReal α a ((1/18, 17/18) : ℝ × ℝ)) * c +
             (fractalKernelReal α a ((1/18, 13/18) : ℝ × ℝ) -
              fractalKernelReal α a ((1/18, 5/18) : ℝ × ℝ)) * d) := by
  rw [H_P_at_disc_cantorDiscMeasure_two]
  rw [h1, h2, h3, h4]
  unfold cantorKernel
  rw [fractalKernelReal_diagonal ha (1/18)]
  ring

/-- **★ Level-2 symmetric-test action at x = 13/18 ★**:

      `(H_P^disc[cantorDiscMeasure 2] f)(13/18)
         = (1/4) · ((V_P(2/3) + V_P(2/9)) · c
                  + (a/(a−1) + V_P(4/9)) · d)`

    Second row of the symmetric 2×2 sub-block of `M^{(2)}` —
    completing the sym block structure together with
    `level2_sym_action_at_ff`. -/
theorem level2_sym_action_at_tf {α a : ℝ} (ha : 1 < a)
    (c d : ℝ) (f : ℝ → ℝ)
    (h1 : f (1/18) = c) (h2 : f (5/18) = d)
    (h3 : f (13/18) = d) (h4 : f (17/18) = c) :
    H_P_at_disc α a (cantorDiscMeasure 2) f (13/18) =
    (1/4) * ((fractalKernelReal α a ((13/18, 1/18) : ℝ × ℝ) +
              fractalKernelReal α a ((13/18, 17/18) : ℝ × ℝ)) * c +
             (a/(a-1) + fractalKernelReal α a ((13/18, 5/18) : ℝ × ℝ)) * d) := by
  rw [H_P_at_disc_cantorDiscMeasure_two]
  rw [h1, h2, h3, h4]
  unfold cantorKernel
  rw [fractalKernelReal_diagonal ha (13/18)]
  ring

/-- **★ Level-2 antisymmetric-test action at x = 13/18 ★**:

      `(H_P^disc[cantorDiscMeasure 2] f)(13/18)
         = (1/4) · ((V_P(2/3) − V_P(2/9)) · c
                  + (a/(a−1) − V_P(4/9)) · d)`

    Second row of the antisymmetric 2×2 sub-block of `M^{(2)}` —
    completing the antisym block structure. -/
theorem level2_antisym_action_at_tf {α a : ℝ} (ha : 1 < a)
    (c d : ℝ) (f : ℝ → ℝ)
    (h1 : f (1/18) = c) (h2 : f (5/18) = -d)
    (h3 : f (13/18) = d) (h4 : f (17/18) = -c) :
    H_P_at_disc α a (cantorDiscMeasure 2) f (13/18) =
    (1/4) * ((fractalKernelReal α a ((13/18, 1/18) : ℝ × ℝ) -
              fractalKernelReal α a ((13/18, 17/18) : ℝ × ℝ)) * c +
             (a/(a-1) - fractalKernelReal α a ((13/18, 5/18) : ℝ × ℝ)) * d) := by
  rw [H_P_at_disc_cantorDiscMeasure_two]
  rw [h1, h2, h3, h4]
  unfold cantorKernel
  rw [fractalKernelReal_diagonal ha (13/18)]
  ring

/-! ## ★ Level-2 sym/antisym invariance (reflection-symmetric image) ★ -/

/-- **★ Level-2 sym-test action at x = 5/18 ★**:

      `(H_P^disc[cantorDiscMeasure 2] f)(5/18)
         = (1/4) · ((V_P(2/9) + V_P(2/3)) · c + (V_P(4/9) + a/(a−1)) · d)`

    Same form as `level2_sym_action_at_tf` (the value at the IFS-
    reflection partner `13/18`). Confirms that the sym test maps to
    a sym output under `M^{(2)}` (row 3 of the matrix-vector product). -/
theorem level2_sym_action_at_ft {α a : ℝ} (ha : 1 < a)
    (c d : ℝ) (f : ℝ → ℝ)
    (h1 : f (1/18) = c) (h2 : f (5/18) = d)
    (h3 : f (13/18) = d) (h4 : f (17/18) = c) :
    H_P_at_disc α a (cantorDiscMeasure 2) f (5/18) =
    (1/4) * ((fractalKernelReal α a ((5/18, 1/18) : ℝ × ℝ) +
              fractalKernelReal α a ((5/18, 17/18) : ℝ × ℝ)) * c +
             (a/(a-1) + fractalKernelReal α a ((5/18, 13/18) : ℝ × ℝ)) * d) := by
  rw [H_P_at_disc_cantorDiscMeasure_two]
  rw [h1, h2, h3, h4]
  unfold cantorKernel
  rw [fractalKernelReal_diagonal ha (5/18)]
  ring

/-- **★ Level-2 sym-test action at x = 17/18 ★**:

      `(H_P^disc[cantorDiscMeasure 2] f)(17/18)
         = (1/4) · ((a/(a−1) + V_P(8/9)) · c + (V_P(2/3) + V_P(2/9)) · d)`

    Same form as `level2_sym_action_at_ff` (the value at the IFS-
    reflection partner `1/18`). Confirms sym → sym output (row 4). -/
theorem level2_sym_action_at_tt {α a : ℝ} (ha : 1 < a)
    (c d : ℝ) (f : ℝ → ℝ)
    (h1 : f (1/18) = c) (h2 : f (5/18) = d)
    (h3 : f (13/18) = d) (h4 : f (17/18) = c) :
    H_P_at_disc α a (cantorDiscMeasure 2) f (17/18) =
    (1/4) * ((a/(a-1) + fractalKernelReal α a ((17/18, 1/18) : ℝ × ℝ)) * c +
             (fractalKernelReal α a ((17/18, 13/18) : ℝ × ℝ) +
              fractalKernelReal α a ((17/18, 5/18) : ℝ × ℝ)) * d) := by
  rw [H_P_at_disc_cantorDiscMeasure_two]
  rw [h1, h2, h3, h4]
  unfold cantorKernel
  rw [fractalKernelReal_diagonal ha (17/18)]
  ring

/-- **★ Level-2 antisym-test action at x = 5/18 ★**:

    Cross-reflection row of B_anti — verifies antisym → −antisym output. -/
theorem level2_antisym_action_at_ft {α a : ℝ} (ha : 1 < a)
    (c d : ℝ) (f : ℝ → ℝ)
    (h1 : f (1/18) = c) (h2 : f (5/18) = -d)
    (h3 : f (13/18) = d) (h4 : f (17/18) = -c) :
    H_P_at_disc α a (cantorDiscMeasure 2) f (5/18) =
    (1/4) * ((fractalKernelReal α a ((5/18, 1/18) : ℝ × ℝ) -
              fractalKernelReal α a ((5/18, 17/18) : ℝ × ℝ)) * c +
             (-(a/(a-1)) + fractalKernelReal α a ((5/18, 13/18) : ℝ × ℝ)) * d) := by
  rw [H_P_at_disc_cantorDiscMeasure_two]
  rw [h1, h2, h3, h4]
  unfold cantorKernel
  rw [fractalKernelReal_diagonal ha (5/18)]
  ring

/-- **★ Level-2 antisym-test action at x = 17/18 ★**:

    Cross-reflection row of B_anti — verifies antisym → −antisym. -/
theorem level2_antisym_action_at_tt {α a : ℝ} (ha : 1 < a)
    (c d : ℝ) (f : ℝ → ℝ)
    (h1 : f (1/18) = c) (h2 : f (5/18) = -d)
    (h3 : f (13/18) = d) (h4 : f (17/18) = -c) :
    H_P_at_disc α a (cantorDiscMeasure 2) f (17/18) =
    (1/4) * ((-(a/(a-1)) + fractalKernelReal α a ((17/18, 1/18) : ℝ × ℝ)) * c +
             (fractalKernelReal α a ((17/18, 13/18) : ℝ × ℝ) -
              fractalKernelReal α a ((17/18, 5/18) : ℝ × ℝ)) * d) := by
  rw [H_P_at_disc_cantorDiscMeasure_two]
  rw [h1, h2, h3, h4]
  unfold cantorKernel
  rw [fractalKernelReal_diagonal ha (17/18)]
  ring

/-! ## Documentation: level-2 sym/antisym 2×2 block matrices

The level-2 4×4 matrix `M^{(2)}` decomposes under the IFS reflection
`x ↦ 1 − x` (which permutes the level-2 cells via `[ff] ↔ [tt]` and
`[ft] ↔ [tf]`) into two 2×2 sub-blocks acting on the symmetric and
antisymmetric subspaces:

  `B_sym = (1/4) · [[a/(a-1) + V_P(8/9),    V_P(2/3) + V_P(2/9)],
                    [V_P(2/3) + V_P(2/9),   a/(a-1) + V_P(4/9)]]`

  `B_anti = (1/4) · [[a/(a-1) - V_P(8/9),   V_P(2/3) - V_P(2/9)],
                     [V_P(2/3) - V_P(2/9),  a/(a-1) - V_P(4/9)]]`

where `V_P(d) := V_P(x, y)` for any `(x, y)` with `dist(x, y) = d`.

The four theorems
  `level2_sym_action_at_{ff, tf}`,
  `level2_antisym_action_at_{ff, tf}`
together verify the matrix entries of both blocks (first/second rows
of sym/antisym). The block decomposition is a CONSEQUENCE of the
IFS reflection symmetry of the kernel and substrate.

Each 2×2 block has 2 real eigenvalues (by the symmetric 2×2 formula
`λ = ((α+γ) ± √((α−γ)² + 4β²))/2`), giving 4 eigenvalues total — the
full level-2 spectrum in closed form (up to evaluating the inner
`V_P(d)` tsums).

This is the LEVEL-2 ANALOGUE of the level-1 sym/antisym decomposition
(`level1_sym_eigenvector_*` and `level1_antisym_eigenvector_*`).
The pattern generalises: at level n, the IFS reflection produces a
2-fold block decomposition; combined with additional symmetries
(e.g., the two-cell self-similar refinement at each level), the
spectrum should organise into a structured family — the formal
target of the polylog conjecture. -/

/-! ## ★ Level-2 block eigenvalues (closed form) ★ -/

/-- **Level-2 sym block diagonal entries**:

    `A_sym := a/(a−1) + V_P(1/18, 17/18)`  [(1,1) of 4·B_sym]
    `C_sym := a/(a−1) + V_P(5/18, 13/18)`  [(2,2) of 4·B_sym] -/
noncomputable def level2SymA (α a : ℝ) : ℝ :=
  a/(a-1) + fractalKernelReal α a ((1/18, 17/18) : ℝ × ℝ)

noncomputable def level2SymC (α a : ℝ) : ℝ :=
  a/(a-1) + fractalKernelReal α a ((5/18, 13/18) : ℝ × ℝ)

/-- **Level-2 sym block off-diagonal entry**:

    `B_sym_offdiag := V_P(1/18, 13/18) + V_P(1/18, 5/18)`  [(1,2) of 4·B_sym] -/
noncomputable def level2SymOffdiag (α a : ℝ) : ℝ :=
  fractalKernelReal α a ((1/18, 13/18) : ℝ × ℝ) +
  fractalKernelReal α a ((1/18, 5/18) : ℝ × ℝ)

/-- **Level-2 antisym block diagonal entries**:

    `A_anti := a/(a−1) − V_P(1/18, 17/18)`  [(1,1) of 4·B_anti]
    `C_anti := a/(a−1) − V_P(5/18, 13/18)`  [(2,2) of 4·B_anti] -/
noncomputable def level2AntiA (α a : ℝ) : ℝ :=
  a/(a-1) - fractalKernelReal α a ((1/18, 17/18) : ℝ × ℝ)

noncomputable def level2AntiC (α a : ℝ) : ℝ :=
  a/(a-1) - fractalKernelReal α a ((5/18, 13/18) : ℝ × ℝ)

/-- **Level-2 antisym block off-diagonal entry**:

    `B_anti_offdiag := V_P(1/18, 13/18) − V_P(1/18, 5/18)` -/
noncomputable def level2AntiOffdiag (α a : ℝ) : ℝ :=
  fractalKernelReal α a ((1/18, 13/18) : ℝ × ℝ) -
  fractalKernelReal α a ((1/18, 5/18) : ℝ × ℝ)

/-- **Level-2 sym block eigenvalue (larger root)**:

      `λ_sym^+ := (1/8) · ((A_sym + C_sym) + √((A_sym − C_sym)² + 4·B_sym²))`

    Larger eigenvalue of the sym 2×2 block `B_sym`, via the standard
    quadratic formula for symmetric 2×2 matrices. The `1/8` factor is
    `1/4` (the level-2 mass weight) times `1/2` (from the quadratic
    formula). -/
noncomputable def lambdaSymPlusLevel2 (α a : ℝ) : ℝ :=
  (1/8) * ((level2SymA α a + level2SymC α a) +
           Real.sqrt ((level2SymA α a - level2SymC α a)^2 +
                      4 * (level2SymOffdiag α a)^2))

/-- **Level-2 sym block eigenvalue (smaller root)**:

      `λ_sym^− := (1/8) · ((A_sym + C_sym) − √((A_sym − C_sym)² + 4·B_sym²))` -/
noncomputable def lambdaSymMinusLevel2 (α a : ℝ) : ℝ :=
  (1/8) * ((level2SymA α a + level2SymC α a) -
           Real.sqrt ((level2SymA α a - level2SymC α a)^2 +
                      4 * (level2SymOffdiag α a)^2))

/-- **Level-2 antisym block eigenvalue (larger root)**:

      `λ_anti^+ := (1/8) · ((A_anti + C_anti) + √((A_anti − C_anti)² + 4·B_anti²))` -/
noncomputable def lambdaAntiPlusLevel2 (α a : ℝ) : ℝ :=
  (1/8) * ((level2AntiA α a + level2AntiC α a) +
           Real.sqrt ((level2AntiA α a - level2AntiC α a)^2 +
                      4 * (level2AntiOffdiag α a)^2))

/-- **Level-2 antisym block eigenvalue (smaller root)**:

      `λ_anti^− := (1/8) · ((A_anti + C_anti) − √((A_anti − C_anti)² + 4·B_anti²))` -/
noncomputable def lambdaAntiMinusLevel2 (α a : ℝ) : ℝ :=
  (1/8) * ((level2AntiA α a + level2AntiC α a) -
           Real.sqrt ((level2AntiA α a - level2AntiC α a)^2 +
                      4 * (level2AntiOffdiag α a)^2))

/-- **★ Level-2 sym block trace identity ★**:

      `λ_sym^+ + λ_sym^− = (1/4) · (A_sym + C_sym)
                          = (1/4) · (2 · a/(a−1) + V_P(8/9) + V_P(4/9))`

    The trace of the sym 2×2 sub-block of `M^{(2)}`. -/
theorem lambdaSymLevel2_trace (α a : ℝ) :
    lambdaSymPlusLevel2 α a + lambdaSymMinusLevel2 α a =
    (1/4) * (level2SymA α a + level2SymC α a) := by
  unfold lambdaSymPlusLevel2 lambdaSymMinusLevel2
  ring

/-- **★ Level-2 antisym block trace identity ★**:

      `λ_anti^+ + λ_anti^− = (1/4) · (A_anti + C_anti)
                            = (1/4) · (2 · a/(a−1) − V_P(8/9) − V_P(4/9))` -/
theorem lambdaAntiLevel2_trace (α a : ℝ) :
    lambdaAntiPlusLevel2 α a + lambdaAntiMinusLevel2 α a =
    (1/4) * (level2AntiA α a + level2AntiC α a) := by
  unfold lambdaAntiPlusLevel2 lambdaAntiMinusLevel2
  ring

/-- **★ Level-2 full trace identity ★**:

      `λ_sym^+ + λ_sym^− + λ_anti^+ + λ_anti^− = a/(a − 1)`

    The sum of all four level-2 eigenvalues equals the operator-norm
    bound `a/(a − 1)` — matching the general trace identity
    `tr M^{(n)} = a/(a − 1)` (independent of `n`). The `V_P(8/9)` and
    `V_P(4/9)` cross-block terms CANCEL between the sym and antisym
    block contributions. -/
theorem level2_full_trace_identity (α a : ℝ) :
    lambdaSymPlusLevel2 α a + lambdaSymMinusLevel2 α a +
    (lambdaAntiPlusLevel2 α a + lambdaAntiMinusLevel2 α a) =
    a / (a - 1) := by
  rw [lambdaSymLevel2_trace, lambdaAntiLevel2_trace]
  unfold level2SymA level2SymC level2AntiA level2AntiC
  ring

/-! ## ★ Level-2 block eigenvalue ordering ★ -/

/-- **Level-2 sym block eigenvalue ordering**: `λ_sym^− ≤ λ_sym^+`.

    The smaller eigenvalue is `≤` the larger eigenvalue (true for any
    symmetric 2×2 matrix, since the discriminant `(A−C)² + 4B² ≥ 0`). -/
theorem lambdaSym_le_Level2 (α a : ℝ) :
    lambdaSymMinusLevel2 α a ≤ lambdaSymPlusLevel2 α a := by
  unfold lambdaSymPlusLevel2 lambdaSymMinusLevel2
  have hdisc : 0 ≤ (level2SymA α a - level2SymC α a)^2 +
                   4 * (level2SymOffdiag α a)^2 := by
    have h1 : 0 ≤ (level2SymA α a - level2SymC α a)^2 := sq_nonneg _
    have h2 : 0 ≤ 4 * (level2SymOffdiag α a)^2 := by
      have := sq_nonneg (level2SymOffdiag α a); linarith
    linarith
  have hsqrt : 0 ≤ Real.sqrt ((level2SymA α a - level2SymC α a)^2 +
                              4 * (level2SymOffdiag α a)^2) :=
    Real.sqrt_nonneg _
  -- (1/8)(s - √D) ≤ (1/8)(s + √D)  where s = A_sym + C_sym, D ≥ 0
  linarith

/-- **Level-2 antisym block eigenvalue ordering**: `λ_anti^− ≤ λ_anti^+`. -/
theorem lambdaAnti_le_Level2 (α a : ℝ) :
    lambdaAntiMinusLevel2 α a ≤ lambdaAntiPlusLevel2 α a := by
  unfold lambdaAntiPlusLevel2 lambdaAntiMinusLevel2
  have hdisc : 0 ≤ (level2AntiA α a - level2AntiC α a)^2 +
                   4 * (level2AntiOffdiag α a)^2 := by
    have h1 : 0 ≤ (level2AntiA α a - level2AntiC α a)^2 := sq_nonneg _
    have h2 : 0 ≤ 4 * (level2AntiOffdiag α a)^2 := by
      have := sq_nonneg (level2AntiOffdiag α a); linarith
    linarith
  have hsqrt : 0 ≤ Real.sqrt ((level2AntiA α a - level2AntiC α a)^2 +
                              4 * (level2AntiOffdiag α a)^2) :=
    Real.sqrt_nonneg _
  linarith

/-- **Level-2 sym block eigenvalue gap**: explicit closed form.

      `λ_sym^+ − λ_sym^− = (1/4) · √((A_sym − C_sym)² + 4·B_sym_offdiag²)`

    The spectral gap of the sym block (always `≥ 0`). -/
theorem lambdaSymLevel2_gap (α a : ℝ) :
    lambdaSymPlusLevel2 α a - lambdaSymMinusLevel2 α a =
    (1/4) * Real.sqrt ((level2SymA α a - level2SymC α a)^2 +
                       4 * (level2SymOffdiag α a)^2) := by
  unfold lambdaSymPlusLevel2 lambdaSymMinusLevel2
  ring

/-- **Level-2 antisym block eigenvalue gap**: explicit closed form.

      `λ_anti^+ − λ_anti^− = (1/4) · √((A_anti − C_anti)² + 4·B_anti_offdiag²)` -/
theorem lambdaAntiLevel2_gap (α a : ℝ) :
    lambdaAntiPlusLevel2 α a - lambdaAntiMinusLevel2 α a =
    (1/4) * Real.sqrt ((level2AntiA α a - level2AntiC α a)^2 +
                       4 * (level2AntiOffdiag α a)^2) := by
  unfold lambdaAntiPlusLevel2 lambdaAntiMinusLevel2
  ring

/-- **Level-2 sym block determinant**:

      `λ_sym⁺ · λ_sym⁻ = (1/16) · (A_sym · C_sym − B_sym_offdiag²)`

    Product of the two sym-block eigenvalues — the determinant of
    `B_sym` (divided by `1/16` from the scaling). -/
theorem lambdaSymLevel2_det (α a : ℝ) :
    lambdaSymPlusLevel2 α a * lambdaSymMinusLevel2 α a =
    (1/16) * (level2SymA α a * level2SymC α a -
              (level2SymOffdiag α a)^2) := by
  -- Abbreviations
  set S := level2SymA α a + level2SymC α a with hS
  set D := (level2SymA α a - level2SymC α a)^2 + 4 * (level2SymOffdiag α a)^2 with hD
  have hdisc : 0 ≤ D := by
    rw [hD]
    have h1 : 0 ≤ (level2SymA α a - level2SymC α a)^2 := sq_nonneg _
    have h2 : 0 ≤ 4 * (level2SymOffdiag α a)^2 := by
      have := sq_nonneg (level2SymOffdiag α a); linarith
    linarith
  have hsq : (Real.sqrt D)^2 = D := Real.sq_sqrt hdisc
  -- (1/8)(S + √D) · (1/8)(S - √D) = (1/64)(S² - D)
  have hprod : lambdaSymPlusLevel2 α a * lambdaSymMinusLevel2 α a =
               (1/64) * (S^2 - (Real.sqrt D)^2) := by
    unfold lambdaSymPlusLevel2 lambdaSymMinusLevel2
    rw [← hS, ← hD]
    ring
  rw [hprod, hsq, hD, hS]
  -- (1/64) · ((A+C)² - ((A-C)² + 4B²)) = (1/64) · (4AC - 4B²) = (1/16)(AC - B²)
  ring

/-- **Level-2 antisym block determinant**:

      `λ_anti⁺ · λ_anti⁻ = (1/16) · (A_anti · C_anti − B_anti_offdiag²)` -/
theorem lambdaAntiLevel2_det (α a : ℝ) :
    lambdaAntiPlusLevel2 α a * lambdaAntiMinusLevel2 α a =
    (1/16) * (level2AntiA α a * level2AntiC α a -
              (level2AntiOffdiag α a)^2) := by
  set S := level2AntiA α a + level2AntiC α a with hS
  set D := (level2AntiA α a - level2AntiC α a)^2 + 4 * (level2AntiOffdiag α a)^2 with hD
  have hdisc : 0 ≤ D := by
    rw [hD]
    have h1 : 0 ≤ (level2AntiA α a - level2AntiC α a)^2 := sq_nonneg _
    have h2 : 0 ≤ 4 * (level2AntiOffdiag α a)^2 := by
      have := sq_nonneg (level2AntiOffdiag α a); linarith
    linarith
  have hsq : (Real.sqrt D)^2 = D := Real.sq_sqrt hdisc
  have hprod : lambdaAntiPlusLevel2 α a * lambdaAntiMinusLevel2 α a =
               (1/64) * (S^2 - (Real.sqrt D)^2) := by
    unfold lambdaAntiPlusLevel2 lambdaAntiMinusLevel2
    rw [← hS, ← hD]
    ring
  rw [hprod, hsq, hD, hS]
  ring

/-! ## ★ Level-2 block diagonal non-negativity ★ -/

/-- **Level-2 sym block (1,1) entry non-negativity**:

      `A_sym = a/(a−1) + V_P(8/9) ≥ 0`

    Combining `a/(a−1) > 0` (from `a > 1`) with the uniform bound
    `|V_P| ≤ a/(a−1)` gives `A_sym ≥ 0`. -/
theorem level2SymA_nonneg {α a : ℝ} (ha : 1 < a) :
    0 ≤ level2SymA α a := by
  unfold level2SymA
  have habs : |fractalKernelReal α a ((1/18, 17/18) : ℝ × ℝ)| ≤ a / (a - 1) :=
    abs_fractalKernelReal_le α ha _
  have hlow : -(a/(a-1)) ≤ fractalKernelReal α a ((1/18, 17/18) : ℝ × ℝ) :=
    (abs_le.mp habs).1
  linarith

/-- **Level-2 sym block (2,2) entry non-negativity**:

      `C_sym = a/(a−1) + V_P(4/9) ≥ 0` -/
theorem level2SymC_nonneg {α a : ℝ} (ha : 1 < a) :
    0 ≤ level2SymC α a := by
  unfold level2SymC
  have habs : |fractalKernelReal α a ((5/18, 13/18) : ℝ × ℝ)| ≤ a / (a - 1) :=
    abs_fractalKernelReal_le α ha _
  have hlow : -(a/(a-1)) ≤ fractalKernelReal α a ((5/18, 13/18) : ℝ × ℝ) :=
    (abs_le.mp habs).1
  linarith

/-- **Level-2 antisym block (1,1) entry non-negativity**:

      `A_anti = a/(a−1) − V_P(8/9) ≥ 0` -/
theorem level2AntiA_nonneg {α a : ℝ} (ha : 1 < a) :
    0 ≤ level2AntiA α a := by
  unfold level2AntiA
  have habs : |fractalKernelReal α a ((1/18, 17/18) : ℝ × ℝ)| ≤ a / (a - 1) :=
    abs_fractalKernelReal_le α ha _
  have hhigh : fractalKernelReal α a ((1/18, 17/18) : ℝ × ℝ) ≤ a/(a-1) :=
    (abs_le.mp habs).2
  linarith

/-- **Level-2 antisym block (2,2) entry non-negativity**:

      `C_anti = a/(a−1) − V_P(4/9) ≥ 0` -/
theorem level2AntiC_nonneg {α a : ℝ} (ha : 1 < a) :
    0 ≤ level2AntiC α a := by
  unfold level2AntiC
  have habs : |fractalKernelReal α a ((5/18, 13/18) : ℝ × ℝ)| ≤ a / (a - 1) :=
    abs_fractalKernelReal_le α ha _
  have hhigh : fractalKernelReal α a ((5/18, 13/18) : ℝ × ℝ) ≤ a/(a-1) :=
    (abs_le.mp habs).2
  linarith

/-- **★ Level-2 block trace non-negativity ★**:

    Both block traces are non-negative:

      `λ_sym⁺ + λ_sym⁻   = (1/4) · (A_sym + C_sym)   ≥ 0`
      `λ_anti⁺ + λ_anti⁻ = (1/4) · (A_anti + C_anti) ≥ 0`

    Necessary condition for PSD-ness of each block. Combined with the
    determinant identities, fully characterises PSD via Sylvester's
    criterion. -/
theorem level2_block_traces_nonneg {α a : ℝ} (ha : 1 < a) :
    0 ≤ lambdaSymPlusLevel2 α a + lambdaSymMinusLevel2 α a ∧
    0 ≤ lambdaAntiPlusLevel2 α a + lambdaAntiMinusLevel2 α a := by
  refine ⟨?_, ?_⟩
  · rw [lambdaSymLevel2_trace]
    have h1 : 0 ≤ level2SymA α a := level2SymA_nonneg ha
    have h2 : 0 ≤ level2SymC α a := level2SymC_nonneg ha
    linarith
  · rw [lambdaAntiLevel2_trace]
    have h1 : 0 ≤ level2AntiA α a := level2AntiA_nonneg ha
    have h2 : 0 ≤ level2AntiC α a := level2AntiC_nonneg ha
    linarith

/-! ## ★ Level-2 conditional PSD ★ -/

/-- **★ Level-2 sym block conditional PSD ★**:

    Both sym-block eigenvalues are non-negative IFF the determinant
    is non-negative (given the trace is already non-negative, which
    we proved unconditionally):

      `A_sym · C_sym ≥ B_sym_offdiag²  ⟹  λ_sym⁺ ≥ 0  ∧  λ_sym⁻ ≥ 0`

    This is Sylvester's criterion for the 2×2 sym block.
    The hypothesis is the formal PSD criterion for the sym block;
    it is an OPEN ESTIMATE for general α (depends on V_P inner products
    at distances 2/9, 4/9, 2/3, 8/9).

    Proof: combine the trace-non-neg + det-non-neg + the standard
    fact that x² − sx + p = 0 with s ≥ 0 and p ≥ 0 has both roots ≥ 0. -/
theorem level2_sym_PSD_from_det {α a : ℝ} (ha : 1 < a)
    (hdet : (level2SymOffdiag α a)^2 ≤ level2SymA α a * level2SymC α a) :
    0 ≤ lambdaSymMinusLevel2 α a := by
  -- We have trace ≥ 0, det ≥ 0. Use λ⁻ = (1/8)(S - √D) and want this ≥ 0,
  -- i.e., S ≥ √D, i.e., S² ≥ D (when S ≥ 0).
  unfold lambdaSymMinusLevel2
  -- Goal: 0 ≤ (1/8) · ((A+C) - √D)
  -- Suffices: (A+C) ≥ √D.
  -- Since A+C ≥ 0, this is equivalent to (A+C)² ≥ D.
  -- (A+C)² - D = (A+C)² - (A-C)² - 4·B² = 4·AC - 4·B² = 4·(AC - B²) ≥ 0 (by hdet).
  set A := level2SymA α a
  set C := level2SymC α a
  set B := level2SymOffdiag α a
  have hA : 0 ≤ A := level2SymA_nonneg ha
  have hC : 0 ≤ C := level2SymC_nonneg ha
  have hsum_nonneg : 0 ≤ A + C := by linarith
  -- (A+C)² - D = 4(AC - B²)
  have hkey : (A + C)^2 - ((A - C)^2 + 4 * B^2) = 4 * (A * C - B^2) := by ring
  have hD_le_sq : (A - C)^2 + 4 * B^2 ≤ (A + C)^2 := by
    have : 0 ≤ A * C - B^2 := by linarith
    nlinarith
  have hsqrt_le : Real.sqrt ((A - C)^2 + 4 * B^2) ≤ A + C := by
    have habsAC : |A + C| = A + C := abs_of_nonneg hsum_nonneg
    calc Real.sqrt ((A - C)^2 + 4 * B^2)
        ≤ Real.sqrt ((A + C)^2) := Real.sqrt_le_sqrt hD_le_sq
      _ = |A + C| := Real.sqrt_sq_eq_abs (A + C)
      _ = A + C := habsAC
  linarith

/-- **★ Level-2 antisym block conditional PSD ★**:

      `A_anti · C_anti ≥ B_anti_offdiag²  ⟹  λ_anti⁻ ≥ 0` -/
theorem level2_anti_PSD_from_det {α a : ℝ} (ha : 1 < a)
    (hdet : (level2AntiOffdiag α a)^2 ≤ level2AntiA α a * level2AntiC α a) :
    0 ≤ lambdaAntiMinusLevel2 α a := by
  unfold lambdaAntiMinusLevel2
  set A := level2AntiA α a
  set C := level2AntiC α a
  set B := level2AntiOffdiag α a
  have hA : 0 ≤ A := level2AntiA_nonneg ha
  have hC : 0 ≤ C := level2AntiC_nonneg ha
  have hsum_nonneg : 0 ≤ A + C := by linarith
  have hkey : (A + C)^2 - ((A - C)^2 + 4 * B^2) = 4 * (A * C - B^2) := by ring
  have hD_le_sq : (A - C)^2 + 4 * B^2 ≤ (A + C)^2 := by
    have : 0 ≤ A * C - B^2 := by linarith
    nlinarith
  have hsqrt_le : Real.sqrt ((A - C)^2 + 4 * B^2) ≤ A + C := by
    have habsAC : |A + C| = A + C := abs_of_nonneg hsum_nonneg
    calc Real.sqrt ((A - C)^2 + 4 * B^2)
        ≤ Real.sqrt ((A + C)^2) := Real.sqrt_le_sqrt hD_le_sq
      _ = |A + C| := Real.sqrt_sq_eq_abs (A + C)
      _ = A + C := habsAC
  linarith

/-! ## ★ Level-2 sum-of-squares (Frobenius norm) identities ★ -/

/-- **Level-2 sym block sum of squared eigenvalues**:

      `λ_sym⁺² + λ_sym⁻² = (1/16) · (A_sym² + C_sym² + 2·B_sym_offdiag²)`

    The Frobenius norm of the sym 2×2 sub-block (which equals the
    sum of squared eigenvalues by the spectral theorem). Derived via
    Vieta: `λ+² + λ-² = (λ+ + λ-)² − 2·(λ+·λ-)`. -/
theorem lambdaSymLevel2_sumSq (α a : ℝ) :
    (lambdaSymPlusLevel2 α a)^2 + (lambdaSymMinusLevel2 α a)^2 =
    (1/16) * ((level2SymA α a)^2 + (level2SymC α a)^2 +
              2 * (level2SymOffdiag α a)^2) := by
  -- Vieta: λ+² + λ-² = (λ+ + λ-)² - 2·λ+·λ- = (sum)² - 2·prod
  have hsum : lambdaSymPlusLevel2 α a + lambdaSymMinusLevel2 α a =
              (1/4) * (level2SymA α a + level2SymC α a) :=
    lambdaSymLevel2_trace α a
  have hprod : lambdaSymPlusLevel2 α a * lambdaSymMinusLevel2 α a =
               (1/16) * (level2SymA α a * level2SymC α a -
                         (level2SymOffdiag α a)^2) :=
    lambdaSymLevel2_det α a
  have hvieta : (lambdaSymPlusLevel2 α a)^2 + (lambdaSymMinusLevel2 α a)^2 =
                (lambdaSymPlusLevel2 α a + lambdaSymMinusLevel2 α a)^2 -
                2 * (lambdaSymPlusLevel2 α a * lambdaSymMinusLevel2 α a) := by ring
  rw [hvieta, hsum, hprod]
  ring

/-- **Level-2 antisym block sum of squared eigenvalues**:

      `λ_anti⁺² + λ_anti⁻² = (1/16) · (A_anti² + C_anti² + 2·B_anti_offdiag²)` -/
theorem lambdaAntiLevel2_sumSq (α a : ℝ) :
    (lambdaAntiPlusLevel2 α a)^2 + (lambdaAntiMinusLevel2 α a)^2 =
    (1/16) * ((level2AntiA α a)^2 + (level2AntiC α a)^2 +
              2 * (level2AntiOffdiag α a)^2) := by
  have hsum : lambdaAntiPlusLevel2 α a + lambdaAntiMinusLevel2 α a =
              (1/4) * (level2AntiA α a + level2AntiC α a) :=
    lambdaAntiLevel2_trace α a
  have hprod : lambdaAntiPlusLevel2 α a * lambdaAntiMinusLevel2 α a =
               (1/16) * (level2AntiA α a * level2AntiC α a -
                         (level2AntiOffdiag α a)^2) :=
    lambdaAntiLevel2_det α a
  have hvieta : (lambdaAntiPlusLevel2 α a)^2 + (lambdaAntiMinusLevel2 α a)^2 =
                (lambdaAntiPlusLevel2 α a + lambdaAntiMinusLevel2 α a)^2 -
                2 * (lambdaAntiPlusLevel2 α a * lambdaAntiMinusLevel2 α a) := by ring
  rw [hvieta, hsum, hprod]
  ring

/-- **★ Level-2 full sum-of-squared-eigenvalues ★**:

    Adding the sym and antisym block sum-of-squares (with cross-block
    cancellation of the linear `V_P` terms inside the squares):

      `λ_sym⁺² + λ_sym⁻² + λ_anti⁺² + λ_anti⁻²
        = (1/16) · (A_sym² + C_sym² + A_anti² + C_anti²
                  + 2·B_sym² + 2·B_anti²)`

    By the spectral theorem, the LHS equals `‖M^{(2)}‖_F²` (Frobenius
    norm squared of the level-2 matrix). The RHS is the explicit
    expansion in terms of the kernel values `V_P(d)` at the level-2
    distances. -/
theorem level2_full_sumSq (α a : ℝ) :
    (lambdaSymPlusLevel2 α a)^2 + (lambdaSymMinusLevel2 α a)^2 +
    ((lambdaAntiPlusLevel2 α a)^2 + (lambdaAntiMinusLevel2 α a)^2) =
    (1/16) * ((level2SymA α a)^2 + (level2SymC α a)^2 +
              2 * (level2SymOffdiag α a)^2 +
              ((level2AntiA α a)^2 + (level2AntiC α a)^2 +
               2 * (level2AntiOffdiag α a)^2)) := by
  rw [lambdaSymLevel2_sumSq, lambdaAntiLevel2_sumSq]
  ring

/-! ## ★ Level-1 eigenvalue closed form ★ -/

/-- **Level-1 symmetric eigenvalue**: the spectral value paired with
    the symmetric eigenvector `f(1/6) = f(5/6) = 1`:

      `λ⁺^{(1)} := (1/2) · (a/(a−1) + V_P(1/6, 5/6))` -/
noncomputable def lambdaPlusLevel1 (α a : ℝ) : ℝ :=
  (1/2) * ((a / (a - 1)) +
    fractalKernelReal α a ((1/6, 5/6) : ℝ × ℝ))

/-- **Level-1 antisymmetric eigenvalue**: the spectral value paired with
    the antisymmetric eigenvector `f(1/6) = 1, f(5/6) = −1`:

      `λ⁻^{(1)} := (1/2) · (a/(a−1) − V_P(1/6, 5/6))` -/
noncomputable def lambdaMinusLevel1 (α a : ℝ) : ℝ :=
  (1/2) * ((a / (a - 1)) -
    fractalKernelReal α a ((1/6, 5/6) : ℝ × ℝ))

/-- **★ Symmetric eigenvector identity at x = 1/6 ★**:

    For `f(1/6) = f(5/6) = 1`,

      `(H_P^disc[cantorDiscMeasure 1] f)(1/6) = λ⁺^{(1)} · f(1/6) = λ⁺^{(1)}` -/
theorem level1_sym_eigenvector_at_left {α a : ℝ} (ha : 1 < a) :
    H_P_at_disc α a (cantorDiscMeasure 1) (fun _ => (1 : ℝ)) (1/6) =
    lambdaPlusLevel1 α a := by
  rw [H_P_at_disc_cantorDiscMeasure_one]
  unfold lambdaPlusLevel1 cantorKernel
  have hdiag : fractalKernelReal α a (((1/6 : ℝ), (1/6 : ℝ)) : ℝ × ℝ)
              = a / (a - 1) :=
    fractalKernelReal_diagonal ha (1/6)
  rw [hdiag]
  ring

/-- **★ Symmetric eigenvector identity at x = 5/6 ★**:

    For `f(1/6) = f(5/6) = 1`,

      `(H_P^disc[cantorDiscMeasure 1] f)(5/6) = λ⁺^{(1)} · f(5/6) = λ⁺^{(1)}`

    Uses kernel SYMMETRY: `V_P(5/6, 1/6) = V_P(1/6, 5/6)` (via
    `fractalKernelReal_swap`). -/
theorem level1_sym_eigenvector_at_right {α a : ℝ} (ha : 1 < a) :
    H_P_at_disc α a (cantorDiscMeasure 1) (fun _ => (1 : ℝ)) (5/6) =
    lambdaPlusLevel1 α a := by
  rw [H_P_at_disc_cantorDiscMeasure_one]
  unfold lambdaPlusLevel1 cantorKernel
  have hdiag : fractalKernelReal α a (((5/6 : ℝ), (5/6 : ℝ)) : ℝ × ℝ)
              = a / (a - 1) :=
    fractalKernelReal_diagonal ha (5/6)
  have hsymm : fractalKernelReal α a (((5/6 : ℝ), (1/6 : ℝ)) : ℝ × ℝ)
              = fractalKernelReal α a (((1/6 : ℝ), (5/6 : ℝ)) : ℝ × ℝ) := by
    have h := fractalKernelReal_swap α a (((5/6 : ℝ), (1/6 : ℝ)) : ℝ × ℝ)
    have hswap : (((5/6 : ℝ), (1/6 : ℝ)) : ℝ × ℝ).swap
               = (((1/6 : ℝ), (5/6 : ℝ)) : ℝ × ℝ) := rfl
    rw [hswap] at h
    exact h.symm
  rw [hdiag, hsymm]
  ring

/-- **Level-1 antisymmetric test function**: `f(1/6) = 1`, `f(5/6) = −1`.

    Indicator function on `{1/6}` used to extract the antisymmetric
    eigenvector. -/
noncomputable def level1_antisym_test (y : ℝ) : ℝ :=
  if y < (1/2 : ℝ) then (1 : ℝ) else -1

theorem level1_antisym_test_at_left : level1_antisym_test (1/6) = 1 := by
  unfold level1_antisym_test
  rw [if_pos (by norm_num : (1/6 : ℝ) < 1/2)]

theorem level1_antisym_test_at_right : level1_antisym_test (5/6) = -1 := by
  unfold level1_antisym_test
  rw [if_neg (by norm_num : ¬ (5/6 : ℝ) < 1/2)]

/-- **★ Antisymmetric eigenvector identity at x = 1/6 ★**:

    For `f(1/6) = 1, f(5/6) = −1`,

      `(H_P^disc[cantorDiscMeasure 1] f)(1/6) = λ⁻^{(1)} · f(1/6) = λ⁻^{(1)}` -/
theorem level1_antisym_eigenvector_at_left {α a : ℝ} (ha : 1 < a) :
    H_P_at_disc α a (cantorDiscMeasure 1) level1_antisym_test (1/6) =
    lambdaMinusLevel1 α a := by
  rw [H_P_at_disc_cantorDiscMeasure_one]
  rw [level1_antisym_test_at_left, level1_antisym_test_at_right]
  unfold lambdaMinusLevel1 cantorKernel
  have hdiag : fractalKernelReal α a (((1/6 : ℝ), (1/6 : ℝ)) : ℝ × ℝ)
              = a / (a - 1) :=
    fractalKernelReal_diagonal ha (1/6)
  rw [hdiag]
  ring

/-- **★ Antisymmetric eigenvector identity at x = 5/6 ★**:

    For `f(1/6) = 1, f(5/6) = −1`,

      `(H_P^disc[cantorDiscMeasure 1] f)(5/6) = λ⁻^{(1)} · f(5/6) = −λ⁻^{(1)}` -/
theorem level1_antisym_eigenvector_at_right {α a : ℝ} (ha : 1 < a) :
    H_P_at_disc α a (cantorDiscMeasure 1) level1_antisym_test (5/6) =
    -lambdaMinusLevel1 α a := by
  rw [H_P_at_disc_cantorDiscMeasure_one]
  rw [level1_antisym_test_at_left, level1_antisym_test_at_right]
  unfold lambdaMinusLevel1 cantorKernel
  have hdiag : fractalKernelReal α a (((5/6 : ℝ), (5/6 : ℝ)) : ℝ × ℝ)
              = a / (a - 1) :=
    fractalKernelReal_diagonal ha (5/6)
  have hsymm : fractalKernelReal α a (((5/6 : ℝ), (1/6 : ℝ)) : ℝ × ℝ)
              = fractalKernelReal α a (((1/6 : ℝ), (5/6 : ℝ)) : ℝ × ℝ) := by
    have h := fractalKernelReal_swap α a (((5/6 : ℝ), (1/6 : ℝ)) : ℝ × ℝ)
    have hswap : (((5/6 : ℝ), (1/6 : ℝ)) : ℝ × ℝ).swap
               = (((1/6 : ℝ), (5/6 : ℝ)) : ℝ × ℝ) := rfl
    rw [hswap] at h
    exact h.symm
  rw [hdiag, hsymm]
  ring

/-- **★ Level-1 sum of squared eigenvalues (Frobenius identity) ★**:

      `λ⁺² + λ⁻² = (1/2) · ((a/(a−1))² + V_P²(1/6, 5/6))`

    Equals `‖M^{(1)}‖_F²` (Frobenius norm squared of the level-1
    matrix). Derived via Vieta: `(λ+² + λ-²) = (sum)² − 2·prod`. -/
theorem level1_sumSq_identity (α a : ℝ) :
    (lambdaPlusLevel1 α a)^2 + (lambdaMinusLevel1 α a)^2 =
    (1/2) * ((a/(a-1))^2 + (fractalKernelReal α a ((1/6, 5/6) : ℝ × ℝ))^2) := by
  unfold lambdaPlusLevel1 lambdaMinusLevel1
  ring

/-- **★ Cross-level Frobenius monotonicity (level 1 ≤ level 0) ★** (`a > 1`):

      `‖M^{(1)}‖_F² = λ⁺² + λ⁻² ≤ (a/(a−1))² = λ_0² = ‖M^{(0)}‖_F²`

    By the trace-preservation identity, the same total mass `a/(a−1)`
    is distributed across 2 eigenvalues at level 1 versus 1 eigenvalue
    at level 0; by Cauchy-Schwarz / convexity, the sum of squares is
    bounded by the single-eigenvalue case.

    Algebraically: `‖M^{(1)}‖_F² = (1/2)·((a/(a−1))² + V_P²(1/6, 5/6))`
    and `V_P²(1/6, 5/6) ≤ (a/(a−1))²` (from the uniform kernel bound).

    This is the formal "EIGENVALUE SPREADING" inequality: as `n`
    increases, the spectrum spreads and the sum of squares decreases,
    with equality iff all eigenvalues are equal. -/
theorem level1_sumSq_le_level0 {α a : ℝ} (ha : 1 < a) :
    (lambdaPlusLevel1 α a)^2 + (lambdaMinusLevel1 α a)^2 ≤
    (a/(a-1))^2 := by
  rw [level1_sumSq_identity]
  have habs : |fractalKernelReal α a ((1/6, 5/6) : ℝ × ℝ)| ≤ a/(a-1) :=
    abs_fractalKernelReal_le α ha _
  have ha_nn : 0 ≤ a / (a - 1) := by
    apply div_nonneg
    · linarith
    · linarith
  have hsq : (fractalKernelReal α a ((1/6, 5/6) : ℝ × ℝ))^2 ≤ (a/(a-1))^2 := by
    rw [← sq_abs (fractalKernelReal α a ((1/6, 5/6) : ℝ × ℝ))]
    exact sq_le_sq' (by linarith [abs_nonneg (fractalKernelReal α a ((1/6, 5/6) : ℝ × ℝ))]) habs
  linarith

/-- **★ Cross-level Frobenius monotonicity (level 2 ≤ level 0) ★** (`a > 1`):

      `‖M^{(2)}‖_F² = Σ_{k=1}^4 λ_k^{(2)²} ≤ (a/(a−1))² = λ_0² = ‖M^{(0)}‖_F²`

    Same spreading inequality at level 2: the 4 level-2 eigenvalues
    sum to `a/(a−1)` and the sum-of-squares is bounded by the
    single-eigenvalue case at level 0.

    Algebraic proof: the explicit Frobenius² expansion is
      `(1/4)·d² + (1/8)·V_{8/9}² + (1/8)·V_{4/9}² + (1/4)·V_{2/3}² + (1/4)·V_{2/9}²`
    where `d = a/(a-1)`. Using `|V_P| ≤ d` (the uniform bound):
      `(1/4)·d² + (1/8)·d² + (1/8)·d² + (1/4)·d² + (1/4)·d² = d²`. -/
theorem level2_sumSq_le_level0 {α a : ℝ} (ha : 1 < a) :
    (lambdaSymPlusLevel2 α a)^2 + (lambdaSymMinusLevel2 α a)^2 +
    ((lambdaAntiPlusLevel2 α a)^2 + (lambdaAntiMinusLevel2 α a)^2) ≤
    (a/(a-1))^2 := by
  rw [level2_full_sumSq]
  -- Need to bound (1/16)·(A_sym² + C_sym² + 2·B_sym² + A_anti² + C_anti² + 2·B_anti²)
  -- by d² = (a/(a-1))².
  -- The RHS expansion equals (1/4)d² + (1/8)V_{8/9}² + (1/8)V_{4/9}² + (1/4)V_{2/3}² + (1/4)V_{2/9}²
  -- but I'll just bound each piece directly.
  have ha_nn : 0 ≤ a / (a - 1) := div_nonneg (by linarith) (by linarith)
  have hd : (a/(a-1))^2 = (a/(a-1))^2 := rfl
  set d := a/(a-1)
  set v_8_9 := fractalKernelReal α a ((1/18, 17/18) : ℝ × ℝ)
  set v_4_9 := fractalKernelReal α a ((5/18, 13/18) : ℝ × ℝ)
  set v_2_3 := fractalKernelReal α a ((1/18, 13/18) : ℝ × ℝ)
  set v_2_9 := fractalKernelReal α a ((1/18, 5/18) : ℝ × ℝ)
  -- Bounds
  have hbnd : ∀ v : ℝ, v^2 ≤ d^2 → True := fun _ _ => trivial
  have hbnd_8_9 : v_8_9^2 ≤ d^2 := by
    rw [← sq_abs v_8_9]
    have habs : |v_8_9| ≤ d := abs_fractalKernelReal_le α ha _
    exact sq_le_sq' (by linarith [abs_nonneg v_8_9]) habs
  have hbnd_4_9 : v_4_9^2 ≤ d^2 := by
    rw [← sq_abs v_4_9]
    have habs : |v_4_9| ≤ d := abs_fractalKernelReal_le α ha _
    exact sq_le_sq' (by linarith [abs_nonneg v_4_9]) habs
  have hbnd_2_3 : v_2_3^2 ≤ d^2 := by
    rw [← sq_abs v_2_3]
    have habs : |v_2_3| ≤ d := abs_fractalKernelReal_le α ha _
    exact sq_le_sq' (by linarith [abs_nonneg v_2_3]) habs
  have hbnd_2_9 : v_2_9^2 ≤ d^2 := by
    rw [← sq_abs v_2_9]
    have habs : |v_2_9| ≤ d := abs_fractalKernelReal_le α ha _
    exact sq_le_sq' (by linarith [abs_nonneg v_2_9]) habs
  -- Expand the LHS using the definitions
  unfold level2SymA level2SymC level2SymOffdiag
         level2AntiA level2AntiC level2AntiOffdiag
  -- After unfold, the LHS is purely algebraic in d, v_8_9, v_4_9, v_2_3, v_2_9
  show (1/16) * ((d + v_8_9)^2 + (d + v_4_9)^2 + 2 * (v_2_3 + v_2_9)^2 +
                 ((d - v_8_9)^2 + (d - v_4_9)^2 + 2 * (v_2_3 - v_2_9)^2)) ≤ d^2
  -- Expand: = (1/16) * (2d² + 2v_{8/9}² + 2d² + 2v_{4/9}² + 2·(2v_{2/3}² + 2v_{2/9}²))
  --       = (1/16) * (4d² + 2v_{8/9}² + 2v_{4/9}² + 4v_{2/3}² + 4v_{2/9}²)
  --       = (1/4)d² + (1/8)v_{8/9}² + (1/8)v_{4/9}² + (1/4)v_{2/3}² + (1/4)v_{2/9}²
  --       ≤ (1/4 + 1/8 + 1/8 + 1/4 + 1/4)·d² = d²
  nlinarith [hbnd_8_9, hbnd_4_9, hbnd_2_3, hbnd_2_9, sq_nonneg d,
             sq_nonneg v_8_9, sq_nonneg v_4_9, sq_nonneg v_2_3, sq_nonneg v_2_9]

/-! ## ★ Level-2 individual eigenvalue bounds ★ -/

/-- **★ Level-2 sym⁺ eigenvalue bound ★** (`a > 1`): `|λ_sym⁺| ≤ a/(a−1)`. -/
theorem abs_lambdaSymPlusLevel2_le {α a : ℝ} (ha : 1 < a) :
    |lambdaSymPlusLevel2 α a| ≤ a/(a-1) := by
  have ha_nn : 0 ≤ a / (a - 1) := div_nonneg (by linarith) (by linarith)
  have hfrob := level2_sumSq_le_level0 (α := α) ha
  have hsq_pos : (lambdaSymPlusLevel2 α a)^2 ≤ (a/(a-1))^2 := by
    have h1 : 0 ≤ (lambdaSymMinusLevel2 α a)^2 := sq_nonneg _
    have h2 : 0 ≤ (lambdaAntiPlusLevel2 α a)^2 := sq_nonneg _
    have h3 : 0 ≤ (lambdaAntiMinusLevel2 α a)^2 := sq_nonneg _
    linarith
  rw [abs_le]
  constructor
  · nlinarith [sq_nonneg (lambdaSymPlusLevel2 α a + a/(a-1))]
  · nlinarith [sq_nonneg (lambdaSymPlusLevel2 α a - a/(a-1))]

/-- **★ Level-2 sym⁻ eigenvalue bound ★** (`a > 1`): `|λ_sym⁻| ≤ a/(a−1)`. -/
theorem abs_lambdaSymMinusLevel2_le {α a : ℝ} (ha : 1 < a) :
    |lambdaSymMinusLevel2 α a| ≤ a/(a-1) := by
  have ha_nn : 0 ≤ a / (a - 1) := div_nonneg (by linarith) (by linarith)
  have hfrob := level2_sumSq_le_level0 (α := α) ha
  have hsq_pos : (lambdaSymMinusLevel2 α a)^2 ≤ (a/(a-1))^2 := by
    have h1 : 0 ≤ (lambdaSymPlusLevel2 α a)^2 := sq_nonneg _
    have h2 : 0 ≤ (lambdaAntiPlusLevel2 α a)^2 := sq_nonneg _
    have h3 : 0 ≤ (lambdaAntiMinusLevel2 α a)^2 := sq_nonneg _
    linarith
  rw [abs_le]
  constructor
  · nlinarith [sq_nonneg (lambdaSymMinusLevel2 α a + a/(a-1))]
  · nlinarith [sq_nonneg (lambdaSymMinusLevel2 α a - a/(a-1))]

/-- **★ Level-2 anti⁺ eigenvalue bound ★** (`a > 1`): `|λ_anti⁺| ≤ a/(a−1)`. -/
theorem abs_lambdaAntiPlusLevel2_le {α a : ℝ} (ha : 1 < a) :
    |lambdaAntiPlusLevel2 α a| ≤ a/(a-1) := by
  have ha_nn : 0 ≤ a / (a - 1) := div_nonneg (by linarith) (by linarith)
  have hfrob := level2_sumSq_le_level0 (α := α) ha
  have hsq_pos : (lambdaAntiPlusLevel2 α a)^2 ≤ (a/(a-1))^2 := by
    have h1 : 0 ≤ (lambdaSymPlusLevel2 α a)^2 := sq_nonneg _
    have h2 : 0 ≤ (lambdaSymMinusLevel2 α a)^2 := sq_nonneg _
    have h3 : 0 ≤ (lambdaAntiMinusLevel2 α a)^2 := sq_nonneg _
    linarith
  rw [abs_le]
  constructor
  · nlinarith [sq_nonneg (lambdaAntiPlusLevel2 α a + a/(a-1))]
  · nlinarith [sq_nonneg (lambdaAntiPlusLevel2 α a - a/(a-1))]

/-- **★ Level-2 anti⁻ eigenvalue bound ★** (`a > 1`): `|λ_anti⁻| ≤ a/(a−1)`. -/
theorem abs_lambdaAntiMinusLevel2_le {α a : ℝ} (ha : 1 < a) :
    |lambdaAntiMinusLevel2 α a| ≤ a/(a-1) := by
  have ha_nn : 0 ≤ a / (a - 1) := div_nonneg (by linarith) (by linarith)
  have hfrob := level2_sumSq_le_level0 (α := α) ha
  have hsq_pos : (lambdaAntiMinusLevel2 α a)^2 ≤ (a/(a-1))^2 := by
    have h1 : 0 ≤ (lambdaSymPlusLevel2 α a)^2 := sq_nonneg _
    have h2 : 0 ≤ (lambdaSymMinusLevel2 α a)^2 := sq_nonneg _
    have h3 : 0 ≤ (lambdaAntiPlusLevel2 α a)^2 := sq_nonneg _
    linarith
  rw [abs_le]
  constructor
  · nlinarith [sq_nonneg (lambdaAntiMinusLevel2 α a + a/(a-1))]
  · nlinarith [sq_nonneg (lambdaAntiMinusLevel2 α a - a/(a-1))]

/-- **★ Level-2 full spectral radius bound ★** (`a > 1`):

      All 4 level-2 eigenvalues satisfy `|λ| ≤ a/(a−1)`.

    The level-2 SPECTRAL RADIUS is bounded by the operator-norm bound
    `a/(a−1)` — the **same uniform bound** as level 0 and the
    documented general bound from `abs_cellMatrixEntry_le`. -/
theorem level2_spectral_radius_bound {α a : ℝ} (ha : 1 < a) :
    |lambdaSymPlusLevel2 α a|  ≤ a/(a-1) ∧
    |lambdaSymMinusLevel2 α a| ≤ a/(a-1) ∧
    |lambdaAntiPlusLevel2 α a| ≤ a/(a-1) ∧
    |lambdaAntiMinusLevel2 α a| ≤ a/(a-1) :=
  ⟨abs_lambdaSymPlusLevel2_le ha,
   abs_lambdaSymMinusLevel2_le ha,
   abs_lambdaAntiPlusLevel2_le ha,
   abs_lambdaAntiMinusLevel2_le ha⟩

/-- **★ Frobenius monotonicity chain (levels 0, 1, 2) ★** (`a > 1`):

      `‖M^{(0)}‖_F² = (a/(a−1))²`
      `‖M^{(1)}‖_F² ≤ (a/(a−1))²`
      `‖M^{(2)}‖_F² ≤ (a/(a−1))²`

    Both level-1 and level-2 Frobenius norms are bounded by the level-0
    value. The conjectured (but not proven) GENERAL monotonicity:

      `‖M^{(n+1)}‖_F² ≤ ‖M^{(n)}‖_F²`  for all `n ≥ 0`

    would express the spectrum spreading monotonically with refinement
    (a property of the polylog spectrum conjecture). -/
theorem frobenius_chain_levels_0_1_2 {α a : ℝ} (ha : 1 < a) :
    (lambdaLevel0 a)^2 = (a/(a-1))^2 ∧
    (lambdaPlusLevel1 α a)^2 + (lambdaMinusLevel1 α a)^2 ≤ (a/(a-1))^2 ∧
    (lambdaSymPlusLevel2 α a)^2 + (lambdaSymMinusLevel2 α a)^2 +
      ((lambdaAntiPlusLevel2 α a)^2 + (lambdaAntiMinusLevel2 α a)^2) ≤
      (a/(a-1))^2 :=
  ⟨by unfold lambdaLevel0; rfl,
   level1_sumSq_le_level0 ha,
   level2_sumSq_le_level0 ha⟩

/-- **★ Full level-2 spectrum bracketing ★** (`a > 1`):

    All 4 level-2 eigenvalues lie in `[−a/(a−1), a/(a−1)]`:

      `−a/(a−1) ≤ λ_sym^±, λ_anti^± ≤ a/(a−1)`

    Direct from `level2_spectral_radius_bound` via `abs_le`.

    NOTE: this is the operator-norm bracketing. Full PSD (`λ ≥ 0`)
    requires the conditional Sylvester criterion
    (`level2_{sym, anti}_PSD_from_det`) — an OPEN ESTIMATE on the
    V_P inner products at distances {2/9, 4/9, 2/3, 8/9}. -/
theorem level2_spectrum_bracketing {α a : ℝ} (ha : 1 < a) :
    (-(a/(a-1)) ≤ lambdaSymPlusLevel2 α a ∧
     lambdaSymPlusLevel2 α a ≤ a/(a-1)) ∧
    (-(a/(a-1)) ≤ lambdaSymMinusLevel2 α a ∧
     lambdaSymMinusLevel2 α a ≤ a/(a-1)) ∧
    (-(a/(a-1)) ≤ lambdaAntiPlusLevel2 α a ∧
     lambdaAntiPlusLevel2 α a ≤ a/(a-1)) ∧
    (-(a/(a-1)) ≤ lambdaAntiMinusLevel2 α a ∧
     lambdaAntiMinusLevel2 α a ≤ a/(a-1)) := by
  obtain ⟨h1, h2, h3, h4⟩ := level2_spectral_radius_bound ha
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨(abs_le.mp h1).1, (abs_le.mp h1).2⟩
  · exact ⟨(abs_le.mp h2).1, (abs_le.mp h2).2⟩
  · exact ⟨(abs_le.mp h3).1, (abs_le.mp h3).2⟩
  · exact ⟨(abs_le.mp h4).1, (abs_le.mp h4).2⟩

/-- **★ Level-1 trace identity ★**:

      `λ⁺^{(1)} + λ⁻^{(1)} = a/(a − 1)`

    Sum of the two level-1 eigenvalues equals the matrix trace
    (independent of the off-diagonal `V_P(1/6, 5/6)`). -/
theorem level1_trace_identity (α a : ℝ) :
    lambdaPlusLevel1 α a + lambdaMinusLevel1 α a = a / (a - 1) := by
  unfold lambdaPlusLevel1 lambdaMinusLevel1
  ring

/-- **★ Level-1 eigenvalue gap ★**:

      `λ⁺^{(1)} − λ⁻^{(1)} = V_P(1/6, 5/6)`

    The spectral gap at level 1 equals the off-diagonal kernel value.
    This is the "splitting" induced by the bicell structure of the
    level-1 Cantor approximation. -/
theorem level1_gap_identity (α a : ℝ) :
    lambdaPlusLevel1 α a - lambdaMinusLevel1 α a =
    fractalKernelReal α a ((1/6, 5/6) : ℝ × ℝ) := by
  unfold lambdaPlusLevel1 lambdaMinusLevel1
  ring

/-- **★ Level-1 spectral gap bound ★** (`a > 1`):

      `|λ⁺^{(1)} − λ⁻^{(1)}| ≤ a/(a − 1)`

    The level-1 spectral gap is bounded by the operator-norm bound,
    consistent with `|λ±| ≤ a/(a−1)`. From the gap identity:
    `gap = V_P(1/6, 5/6)`, and `|V_P| ≤ a/(a−1)`. -/
theorem abs_level1_gap_le {α a : ℝ} (ha : 1 < a) :
    |lambdaPlusLevel1 α a - lambdaMinusLevel1 α a| ≤ a/(a-1) := by
  rw [level1_gap_identity]
  exact abs_fractalKernelReal_le α ha _

/-- **★ Level-1 determinant identity ★**:

      `λ⁺^{(1)} · λ⁻^{(1)} = (1/4) · ((a/(a−1))² − V_P(1/6, 5/6)²)`

    Product of the two level-1 eigenvalues — the determinant of `M^{(1)}`. -/
theorem level1_det_identity (α a : ℝ) :
    lambdaPlusLevel1 α a * lambdaMinusLevel1 α a =
    (1/4) * ((a/(a-1))^2 - (fractalKernelReal α a ((1/6, 5/6) : ℝ × ℝ))^2) := by
  unfold lambdaPlusLevel1 lambdaMinusLevel1
  ring

/-- **★ Trace consistency across levels ★**:

      `tr M^{(0)} = λ^{(0)}_0 = a/(a − 1) = λ⁺^{(1)} + λ⁻^{(1)} = tr M^{(1)}`

    The trace is INVARIANT under level refinement at levels 0 and 1.
    This is consistent with the general trace identity
    `tr M^{(n)} = a/(a − 1)` (independent of `n`), and is a direct
    test of the level-by-level eigenvalue approximation framework. -/
theorem trace_level0_eq_trace_level1 (α a : ℝ) :
    lambdaLevel0 a = lambdaPlusLevel1 α a + lambdaMinusLevel1 α a := by
  rw [level1_trace_identity]
  rfl

/-! ## ★ Explicit trace computations at levels 0, 1, 2 ★ -/

/-- **Level-0 trace** (1×1 matrix, single diagonal entry):

      `tr M^{(0)} = M^{(0)}_{[], []} = (1/2^0) · a/(a − 1) = a/(a − 1)` -/
theorem trace_level0 {α a : ℝ} (ha : 1 < a) :
    cellMatrixEntry α a 0 [] [] = a / (a - 1) := by
  rw [cellMatrixEntry_diagonal ha]
  simp

/-- **Level-1 trace** (2×2 matrix, sum of 2 equal diagonal entries):

      `tr M^{(1)} = M^{(1)}_{[false], [false]} + M^{(1)}_{[true], [true]}
                  = 2 · (1/2) · a/(a − 1) = a/(a − 1)` -/
theorem trace_level1 {α a : ℝ} (ha : 1 < a) :
    cellMatrixEntry α a 1 [false] [false] +
    cellMatrixEntry α a 1 [true] [true] = a / (a - 1) := by
  rw [cellMatrixEntry_diagonal ha, cellMatrixEntry_diagonal ha]
  ring

/-- **Level-2 trace** (4×4 matrix, sum of 4 equal diagonal entries):

      `tr M^{(2)} = 4 · (1/4) · a/(a − 1) = a/(a − 1)` -/
theorem trace_level2 {α a : ℝ} (ha : 1 < a) :
    cellMatrixEntry α a 2 [false, false] [false, false] +
    cellMatrixEntry α a 2 [false, true] [false, true] +
    cellMatrixEntry α a 2 [true, false] [true, false] +
    cellMatrixEntry α a 2 [true, true] [true, true] = a / (a - 1) := by
  rw [cellMatrixEntry_diagonal ha, cellMatrixEntry_diagonal ha,
      cellMatrixEntry_diagonal ha, cellMatrixEntry_diagonal ha]
  ring

/-- **★ Cross-level trace chain ★**:

      `tr M^{(0)} = tr M^{(1)} = tr M^{(2)} = a/(a − 1)`

    The trace is preserved across the first three refinement levels.
    By the general trace identity (independent of `n`), this extends
    to every level `n ≥ 0`. -/
theorem trace_chain_levels_0_1_2 {α a : ℝ} (ha : 1 < a) :
    cellMatrixEntry α a 0 [] [] = a / (a - 1) ∧
    cellMatrixEntry α a 1 [false] [false] +
      cellMatrixEntry α a 1 [true] [true] = a / (a - 1) ∧
    cellMatrixEntry α a 2 [false, false] [false, false] +
      cellMatrixEntry α a 2 [false, true] [false, true] +
      cellMatrixEntry α a 2 [true, false] [true, false] +
      cellMatrixEntry α a 2 [true, true] [true, true] = a / (a - 1) :=
  ⟨trace_level0 ha, trace_level1 ha, trace_level2 ha⟩

/-! ## ★ Level-1 positive semi-definiteness ★ -/

/-- **★ Level-1 symmetric eigenvalue non-negativity ★**:

      `λ⁺^{(1)} ≥ 0`

    Combining the closed form `λ⁺ = (1/2)(a/(a−1) + V_P(1/6, 5/6))`
    with the uniform bound `|V_P| ≤ a/(a−1)` gives `λ⁺ ≥ 0`. -/
theorem lambdaPlusLevel1_nonneg {α a : ℝ} (ha : 1 < a) :
    0 ≤ lambdaPlusLevel1 α a := by
  unfold lambdaPlusLevel1
  have habs : |fractalKernelReal α a ((1/6, 5/6) : ℝ × ℝ)| ≤ a / (a - 1) :=
    abs_fractalKernelReal_le α ha _
  have hlow : -(a/(a-1)) ≤ fractalKernelReal α a ((1/6, 5/6) : ℝ × ℝ) :=
    (abs_le.mp habs).1
  linarith

/-- **★ Level-1 antisymmetric eigenvalue non-negativity ★**:

      `λ⁻^{(1)} ≥ 0`

    Symmetric argument to `lambdaPlusLevel1_nonneg`. -/
theorem lambdaMinusLevel1_nonneg {α a : ℝ} (ha : 1 < a) :
    0 ≤ lambdaMinusLevel1 α a := by
  unfold lambdaMinusLevel1
  have habs : |fractalKernelReal α a ((1/6, 5/6) : ℝ × ℝ)| ≤ a / (a - 1) :=
    abs_fractalKernelReal_le α ha _
  have hhigh : fractalKernelReal α a ((1/6, 5/6) : ℝ × ℝ) ≤ a/(a-1) :=
    (abs_le.mp habs).2
  linarith

/-- **★ Level-1 matrix is positive semi-definite ★**:

    Both eigenvalues `λ⁺^{(1)}, λ⁻^{(1)}` are non-negative, so the
    real symmetric matrix `M^{(1)}` is POSITIVE SEMI-DEFINITE:

      `M^{(1)} ⪰ 0` (in the partial order on real symmetric matrices)

    This is consistent with the operator `H_P^cantor[μ_H]` being a
    Hilbert-Schmidt KERNEL OPERATOR with non-negative spectrum (since
    `V_P` is a positive-definite kernel in the Bochner sense — sum
    of cosines on a contracting scale series).

    Spectral interpretation: every level-`n` finite-rank approximation
    `M^{(n)}` is expected to be positive semi-definite, paralleling
    the positive-definiteness of `V_P` itself. The level-1 case is
    here proved directly from the closed-form eigenvalues. -/
theorem level1_matrix_psd {α a : ℝ} (ha : 1 < a) :
    0 ≤ lambdaPlusLevel1 α a ∧ 0 ≤ lambdaMinusLevel1 α a :=
  ⟨lambdaPlusLevel1_nonneg ha, lambdaMinusLevel1_nonneg ha⟩

/-- **★ Upper spectral bound: λ⁺^{(1)} ≤ a/(a − 1) ★**:

    The symmetric eigenvalue is bounded above by the operator-norm
    bound `a/(a − 1)`. -/
theorem lambdaPlusLevel1_le {α a : ℝ} (ha : 1 < a) :
    lambdaPlusLevel1 α a ≤ a / (a - 1) := by
  unfold lambdaPlusLevel1
  have habs : |fractalKernelReal α a ((1/6, 5/6) : ℝ × ℝ)| ≤ a / (a - 1) :=
    abs_fractalKernelReal_le α ha _
  have hhigh : fractalKernelReal α a ((1/6, 5/6) : ℝ × ℝ) ≤ a/(a-1) :=
    (abs_le.mp habs).2
  linarith

/-- **★ Upper spectral bound: λ⁻^{(1)} ≤ a/(a − 1) ★**:

    The antisymmetric eigenvalue is bounded above by the operator-norm
    bound `a/(a − 1)`. -/
theorem lambdaMinusLevel1_le {α a : ℝ} (ha : 1 < a) :
    lambdaMinusLevel1 α a ≤ a / (a - 1) := by
  unfold lambdaMinusLevel1
  have habs : |fractalKernelReal α a ((1/6, 5/6) : ℝ × ℝ)| ≤ a / (a - 1) :=
    abs_fractalKernelReal_le α ha _
  have hlow : -(a/(a-1)) ≤ fractalKernelReal α a ((1/6, 5/6) : ℝ × ℝ) :=
    (abs_le.mp habs).1
  linarith

/-- **★ Full level-1 spectral bracketing ★**:

      `0 ≤ λ±^{(1)} ≤ a/(a − 1)`

    Both eigenvalues are sandwiched between 0 and the operator-norm
    bound. This is the uniform spectral constraint at level 1, matching
    the documented general bound from `abs_cellMatrixEntry_le`. -/
theorem level1_spectrum_in_unit_interval {α a : ℝ} (ha : 1 < a) :
    (0 ≤ lambdaPlusLevel1 α a ∧ lambdaPlusLevel1 α a ≤ a/(a-1)) ∧
    (0 ≤ lambdaMinusLevel1 α a ∧ lambdaMinusLevel1 α a ≤ a/(a-1)) :=
  ⟨⟨lambdaPlusLevel1_nonneg ha, lambdaPlusLevel1_le ha⟩,
   ⟨lambdaMinusLevel1_nonneg ha, lambdaMinusLevel1_le ha⟩⟩

/-! ## ★ Level-2 distance structure ★ -/

/-- **Level-2 distance** between cells `[false, false]` (midpoint `1/18`)
    and `[false, true]` (midpoint `5/18`):

      `|1/18 − 5/18| = 2/9`

    Both cells are inside the LEFT half `[0, 1/3]`; their distance is
    `1/3` of the level-1 distance `2/3`. -/
theorem cellMidpoint_level2_dist_ff_ft :
    dist (cellMidpointOfBools [false, false])
         (cellMidpointOfBools [false, true]) = 2/9 := by
  rw [cellMidpointOfBools_ff, cellMidpointOfBools_ft]
  rw [Real.dist_eq]
  norm_num

/-- **Level-2 distance** between cells `[false, false]` (midpoint `1/18`)
    and `[true, false]` (midpoint `13/18`):

      `|1/18 − 13/18| = 2/3`

    These cells are in OPPOSITE halves and form a level-1-scale gap. -/
theorem cellMidpoint_level2_dist_ff_tf :
    dist (cellMidpointOfBools [false, false])
         (cellMidpointOfBools [true, false]) = 2/3 := by
  rw [cellMidpointOfBools_ff, cellMidpointOfBools_tf]
  rw [Real.dist_eq]
  norm_num

/-- **Level-2 distance** between cells `[false, false]` (midpoint `1/18`)
    and `[true, true]` (midpoint `17/18`):

      `|1/18 − 17/18| = 8/9`

    The maximum level-2 distance — the two extreme cells. -/
theorem cellMidpoint_level2_dist_ff_tt :
    dist (cellMidpointOfBools [false, false])
         (cellMidpointOfBools [true, true]) = 8/9 := by
  rw [cellMidpointOfBools_ff, cellMidpointOfBools_tt]
  rw [Real.dist_eq]
  norm_num

/-- **Level-2 distance** between cells `[false, true]` (midpoint `5/18`)
    and `[true, false]` (midpoint `13/18`):

      `|5/18 − 13/18| = 4/9` -/
theorem cellMidpoint_level2_dist_ft_tf :
    dist (cellMidpointOfBools [false, true])
         (cellMidpointOfBools [true, false]) = 4/9 := by
  rw [cellMidpointOfBools_ft, cellMidpointOfBools_tf]
  rw [Real.dist_eq]
  norm_num

/-- **Level-2 distance** between cells `[false, true]` (midpoint `5/18`)
    and `[true, true]` (midpoint `17/18`):

      `|5/18 − 17/18| = 2/3` -/
theorem cellMidpoint_level2_dist_ft_tt :
    dist (cellMidpointOfBools [false, true])
         (cellMidpointOfBools [true, true]) = 2/3 := by
  rw [cellMidpointOfBools_ft, cellMidpointOfBools_tt]
  rw [Real.dist_eq]
  norm_num

/-- **Level-2 distance** between cells `[true, false]` (midpoint `13/18`)
    and `[true, true]` (midpoint `17/18`):

      `|13/18 − 17/18| = 2/9`

    Both cells are inside the RIGHT half `[2/3, 1]`; their distance is
    `1/3` of the level-1 distance `2/3` (mirroring the `ff↔ft` pair on
    the left half). -/
theorem cellMidpoint_level2_dist_tf_tt :
    dist (cellMidpointOfBools [true, false])
         (cellMidpointOfBools [true, true]) = 2/9 := by
  rw [cellMidpointOfBools_tf, cellMidpointOfBools_tt]
  rw [Real.dist_eq]
  norm_num

/-! ## Documentation: level-2 matrix structure

The level-2 matrix `M^{(2)}` is a `4 × 4` real symmetric matrix
indexed by `{[false,false], [false,true], [true,false], [true,true]}`.

Using the diagonal closed form `M^{(2)}_{bs, bs} = (1/4) · a/(a−1)`
(constant), and the six pairwise distances above, the off-diagonal
entries split into THREE distinct distance values (with multiplicities):

  * distance `2/9` (multiplicity 2): pairs `(ff, ft)`, `(tf, tt)`
    — within-half neighbours, mirrored across the `[0, 1/3]` ↔ `[2/3, 1]`
    symmetry.
  * distance `4/9` (multiplicity 1): pair `(ft, tf)`
    — the inner cross-half pair.
  * distance `2/3` (multiplicity 2): pairs `(ff, tf)`, `(ft, tt)`
    — outer-of-pair cross-half pairs.
  * distance `8/9` (multiplicity 1): pair `(ff, tt)`
    — extreme corners.

**Block structure** (by IFS self-similarity): the `[false, *]` ×
`[false, *]` sub-block and the `[true, *]` × `[true, *]` sub-block
each replicate the level-1 matrix structure on the left/right half,
SCALED by `1/3` in distance and `(1/2)` in mass weight.

**Reflective symmetry**: under the map `bs ↦ negate bs` (swap
`false ↔ true` in every position), the level-2 distance pattern is
invariant, reflecting the `x ↦ 1 − x` reflection symmetry of the
Cantor set IFS. This gives the matrix the additional reflection
invariance, which in turn implies that all level-2 eigenvectors come
in `(symmetric, antisymmetric)` pairs under this reflection.

**Spectral consequence**: the four eigenvalues of `M^{(2)}` group as
two pairs under reflection symmetry; combined with the self-similar
block structure, they decompose into the level-1 eigenvalues
`{λ⁺^{(1)}, λ⁻^{(1)}}` PLUS scale-shifted corrections proportional
to `(1/a) · V_P(α·x, α·y)`. -/

/-! ## ★ Distance-parametrised matrix entry (general) ★ -/

/-- **★ Matrix entry as a function of distance ★**:

      `M^{(n)}_{bs, bs'} = (1/2^n) · Σ_{k≥0} a^(-k) · cos(π · αᵏ · d)`

    where `d = dist(m_{bs}, m_{bs'})` is the distance between the two
    cell midpoints. This is the SINGLE FORMULA that produces all
    explicit matrix entries at every level — diagonal (d = 0 → `a/(a-1)`
    via geometric series), level-1 off-diagonal (d = 2/3), level-2
    cases (d ∈ {2/9, 4/9, 2/3, 8/9}), etc.

    Specialising `bs = bs'` recovers `cellMatrixEntry_diagonal`;
    specialising `n = 1, bs = [false], bs' = [true]` recovers
    `cellMatrixEntry_level1_offdiag`. -/
theorem cellMatrixEntry_eq_tsum_distance (α a : ℝ) (n : ℕ)
    (bs bs' : List Bool) :
    cellMatrixEntry α a n bs bs' =
    (1 / (2 : ℝ)^n) * ∑' k : ℕ,
      a ^ (-(k : ℤ)) * Real.cos (Real.pi * α ^ k *
        dist (cellMidpointOfBools bs) (cellMidpointOfBools bs')) := by
  unfold cellMatrixEntry cantorKernel fractalKernelReal fractalKernelTerm
  rfl

/-! ## ★ Level-2 explicit off-diagonal matrix entries ★ -/

/-- **Level-2 entry** `M^{(2)}_{ff, ft}`:

      `M^{(2)}_{[ff], [ft]} = (1/4) · Σ a^(-k) · cos(π · αᵏ · 2/9)` -/
theorem cellMatrixEntry_level2_ff_ft (α a : ℝ) :
    cellMatrixEntry α a 2 [false, false] [false, true] =
    (1 / (2:ℝ)^2) * ∑' k : ℕ,
      a ^ (-(k : ℤ)) * Real.cos (Real.pi * α ^ k * (2/9)) := by
  rw [cellMatrixEntry_eq_tsum_distance]
  rw [cellMidpoint_level2_dist_ff_ft]

/-- **Level-2 entry** `M^{(2)}_{ff, tf}`:

      `M^{(2)}_{[ff], [tf]} = (1/4) · Σ a^(-k) · cos(π · αᵏ · 2/3)` -/
theorem cellMatrixEntry_level2_ff_tf (α a : ℝ) :
    cellMatrixEntry α a 2 [false, false] [true, false] =
    (1 / (2:ℝ)^2) * ∑' k : ℕ,
      a ^ (-(k : ℤ)) * Real.cos (Real.pi * α ^ k * (2/3)) := by
  rw [cellMatrixEntry_eq_tsum_distance]
  rw [cellMidpoint_level2_dist_ff_tf]

/-- **Level-2 entry** `M^{(2)}_{ff, tt}`:

      `M^{(2)}_{[ff], [tt]} = (1/4) · Σ a^(-k) · cos(π · αᵏ · 8/9)` -/
theorem cellMatrixEntry_level2_ff_tt (α a : ℝ) :
    cellMatrixEntry α a 2 [false, false] [true, true] =
    (1 / (2:ℝ)^2) * ∑' k : ℕ,
      a ^ (-(k : ℤ)) * Real.cos (Real.pi * α ^ k * (8/9)) := by
  rw [cellMatrixEntry_eq_tsum_distance]
  rw [cellMidpoint_level2_dist_ff_tt]

/-- **Level-2 entry** `M^{(2)}_{ft, tf}`:

      `M^{(2)}_{[ft], [tf]} = (1/4) · Σ a^(-k) · cos(π · αᵏ · 4/9)` -/
theorem cellMatrixEntry_level2_ft_tf (α a : ℝ) :
    cellMatrixEntry α a 2 [false, true] [true, false] =
    (1 / (2:ℝ)^2) * ∑' k : ℕ,
      a ^ (-(k : ℤ)) * Real.cos (Real.pi * α ^ k * (4/9)) := by
  rw [cellMatrixEntry_eq_tsum_distance]
  rw [cellMidpoint_level2_dist_ft_tf]

/-- **Level-2 entry** `M^{(2)}_{ft, tt}`:

      `M^{(2)}_{[ft], [tt]} = (1/4) · Σ a^(-k) · cos(π · αᵏ · 2/3)` -/
theorem cellMatrixEntry_level2_ft_tt (α a : ℝ) :
    cellMatrixEntry α a 2 [false, true] [true, true] =
    (1 / (2:ℝ)^2) * ∑' k : ℕ,
      a ^ (-(k : ℤ)) * Real.cos (Real.pi * α ^ k * (2/3)) := by
  rw [cellMatrixEntry_eq_tsum_distance]
  rw [cellMidpoint_level2_dist_ft_tt]

/-- **Level-2 entry** `M^{(2)}_{tf, tt}`:

      `M^{(2)}_{[tf], [tt]} = (1/4) · Σ a^(-k) · cos(π · αᵏ · 2/9)` -/
theorem cellMatrixEntry_level2_tf_tt (α a : ℝ) :
    cellMatrixEntry α a 2 [true, false] [true, true] =
    (1 / (2:ℝ)^2) * ∑' k : ℕ,
      a ^ (-(k : ℤ)) * Real.cos (Real.pi * α ^ k * (2/9)) := by
  rw [cellMatrixEntry_eq_tsum_distance]
  rw [cellMidpoint_level2_dist_tf_tt]

/-- **★ Level-2 within-half symmetry ★**:

    The two "within-half" entries are equal:

      `M^{(2)}_{[ff], [ft]} = M^{(2)}_{[tf], [tt]}`

    Both encode the same `2/9` distance: within left half (`[ff], [ft]`)
    and within right half (`[tf], [tt]`) — the IFS reflection symmetry
    `x ↦ 1 − x` maps one to the other. -/
theorem level2_within_half_equality (α a : ℝ) :
    cellMatrixEntry α a 2 [false, false] [false, true] =
    cellMatrixEntry α a 2 [true, false] [true, true] := by
  rw [cellMatrixEntry_level2_ff_ft, cellMatrixEntry_level2_tf_tt]

/-- **★ Level-2 outer-cross symmetry ★**:

    The two "outer-cross" entries are equal:

      `M^{(2)}_{[ff], [tf]} = M^{(2)}_{[ft], [tt]}`

    Both encode the same `2/3` distance (the level-1 distance scaled
    by `1` — i.e., the outer-of-pair cross-half pairs). -/
theorem level2_outer_cross_equality (α a : ℝ) :
    cellMatrixEntry α a 2 [false, false] [true, false] =
    cellMatrixEntry α a 2 [false, true] [true, true] := by
  rw [cellMatrixEntry_level2_ff_tf, cellMatrixEntry_level2_ft_tt]

/-! ## ★ Uniform absolute bound ★ -/

/-- **★ Uniform matrix-entry bound ★** (`a > 1`):

      `|M^{(n)}_{bs, bs'}| ≤ (1/2^n) · a/(a−1)`

    Every entry is bounded by the per-cell mass `1/2^n` times the
    geometric-series majorant `a/(a−1)` (the maximum value of `V_P`,
    attained on the diagonal). -/
theorem abs_cellMatrixEntry_le {α a : ℝ} (ha : 1 < a) (n : ℕ)
    (bs bs' : List Bool) :
    |cellMatrixEntry α a n bs bs'| ≤ (1 / (2 : ℝ)^n) * (a / (a - 1)) := by
  unfold cellMatrixEntry cantorKernel
  rw [abs_mul]
  have hpos : (0 : ℝ) < 2^n := pow_pos (by norm_num : (0:ℝ) < 2) n
  have habs : |(1 / (2 : ℝ)^n)| = 1 / (2 : ℝ)^n :=
    abs_of_pos (one_div_pos.mpr hpos)
  rw [habs]
  apply mul_le_mul_of_nonneg_left _ (le_of_lt (one_div_pos.mpr hpos))
  exact abs_fractalKernelReal_le α ha _

/-! ## Documentation: operator-norm row-sum bound

The sum `Σ_{bs'} |M^{(n)}_{bs, bs'}|` over all length-`n` boolean
words is bounded by `a/(a−1)` — UNIFORM in `n`. There are `2^n`
columns, each contributing at most `(1/2^n) · a/(a−1)` (by
`abs_cellMatrixEntry_le`), so the row sum is at most
`2^n · (1/2^n) · a/(a−1) = a/(a−1)`.

**Spectral consequence**: by the row-sum bound on the operator
norm `‖M^{(n)}‖ ≤ max_bs Σ_{bs'} |M^{(n)}_{bs, bs'}|`, the level-`n`
discrete operator has operator norm bounded by `a/(a−1)` for every
`n`. So all level-`n` eigenvalues satisfy `|λ^{(n)}_k| ≤ a/(a−1)`,
INDEPENDENT OF `n`. This is the **finite-rank operator-norm
stability** that underwrites the spectral convergence argument
(uniform-bound + weak-convergence → spectral convergence).

Formalising the row-sum equality (rather than the per-entry bound)
requires the Finset-of-length-`n`-Boolean-lists infrastructure
documented in `CellMidpoint.lean`. -/

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
