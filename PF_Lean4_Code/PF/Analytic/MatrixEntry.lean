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
