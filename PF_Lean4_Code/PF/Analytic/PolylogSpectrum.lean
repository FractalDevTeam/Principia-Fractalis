/-
# Polylog Spectrum Conjecture — Formal Statement + Matrix Building Blocks

**Open Problem 1** (`OPEN_PROBLEMS.md`): the conjecture that the eigenvalues
of the fractal convolution operator `H_P_at α a` are given by the polylog
formula

  `λ_k = (1/aᵏ) · Re[Li₁(e^{iπ·αᵏ})]`

on a specific physical Riemann sheet determined by the operator's monodromy
structure (manuscript Ch 21 `conj:polylog-spectrum`).

## What this file delivers

1. **The formal conjecture statement** as a structured `Prop`, so future work
   can target it directly with `theorem` rather than `axiom`.
2. **Closed-form inner-product integrals** for the cosine/sine modes on `[0,1]`:
   * `∫_0^1 cos²(αx) dx = 1/2 + sin(2α)/(4α)`            (diagonal)
   * `∫_0^1 sin²(αx) dx = 1/2 − sin(2α)/(4α)`            (diagonal)
   * `∫_0^1 cos(αx)·sin(αx) dx = (1 − cos(2α))/(4α)`     (cross at same scale)
   * `∫_0^1 cos(αx)·cos(βx) dx = sin(α−β)/(2(α−β)) + sin(α+β)/(2(α+β))`  (off-diagonal)
   * `∫_0^1 sin(αx)·sin(βx) dx = sin(α−β)/(2(α−β)) − sin(α+β)/(2(α+β))`  (off-diagonal)
   * `∫_0^1 cos(αx)·sin(βx) dx = (1 − cos(α−β))/(2(α−β)) − (1 − cos(α+β))/(2(α+β))/(-1)`  *(see below)*

   These integrals are the **matrix entries** of `H_P_at α a` in the
   `{cosineMode α n, sineMode α n}` basis. They are the algebraic building
   blocks for any attack on the conjecture.

3. **The conditional retirement theorem**: if the diagonalization argument
   succeeds (i.e., if the eigenvectors of `H_P_at α a` are computed and the
   spectrum matches the polylog formula), the conjecture content follows
   from the building blocks proven here.

## What this file does NOT deliver

The conjecture itself is NOT proven. Specifically:

* The **eigenvector identification** for `H_P_at α a` — i.e., the linear
  combinations of `{cosineMode α n}` that diagonalize the operator — is not
  computed. The manuscript Ch 21 sketches this as a fractal-self-similar
  fixed-point construction; mechanizing it is multi-page operator theory.
* The **Riemann-sheet selection** for `Li₁` (Heuristic `heur:branch-selection`)
  is not characterized in terms of intrinsic operator invariants.
* The **golden-modulation conjugacy** for `H_NP` (Conjecture
  `conj:golden-modulation`) is a separate piece.

This file sets up the formal infrastructure to attack the conjecture; it
does not solve it. See `OPEN_PROBLEMS.md` Problems 1–3.

Stage L4+ — Polylog spectrum infrastructure.
-/

import PF.Analytic.CosineModeInnerProducts
import PF.Analytic.KernelSelfSimilarity
import PF.Analytic.PolylogBoundary
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace PrincipiaTractalis.Analytic

open Real intervalIntegral

/-! ## Diagonal inner-product integrals -/

/-- **Diagonal cosine**: `∫_0^1 cos²(αx) dx = 1/2 + sin(2α)/(4α)`  for `α ≠ 0`.

    Derived via the half-angle identity `cos²(u) = 1/2 + cos(2u)/2` and the
    linear-cosine integral `∫_0^1 cos(βx) dx = sin(β)/β`. -/
theorem integral_cos_sq_alpha_zero_one (α : ℝ) (hα : α ≠ 0) :
    ∫ x in (0:ℝ)..1, Real.cos (α * x) ^ 2 =
    1/2 + Real.sin (2 * α) / (4 * α) := by
  have h2α : 2 * α ≠ 0 := mul_ne_zero (by norm_num) hα
  have hrw : ∀ x : ℝ, Real.cos (α * x) ^ 2 = 1/2 + Real.cos (2 * α * x) / 2 := by
    intro x
    have := Real.cos_sq (α * x)
    rw [show 2 * (α * x) = 2 * α * x from by ring] at this
    linarith
  simp_rw [hrw]
  have hcosInt : IntervalIntegrable (fun x => Real.cos (2 * α * x))
      MeasureTheory.volume 0 1 :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id')).intervalIntegrable _ _
  rw [integral_add (intervalIntegral.intervalIntegrable_const) (hcosInt.div_const _)]
  rw [integral_const, integral_div]
  rw [integral_comp_mul_left Real.cos h2α]
  rw [mul_zero, mul_one]
  rw [integral_cos]
  rw [Real.sin_zero, sub_zero]
  simp [smul_eq_mul]
  field_simp
  ring

/-- **Diagonal sine**: `∫_0^1 sin²(αx) dx = 1/2 − sin(2α)/(4α)`  for `α ≠ 0`.

    Derived from `cos(2u) = 2·cos²(u) − 1` and `sin² + cos² = 1`, giving
    `sin²(u) = 1/2 − cos(2u)/2`. -/
theorem integral_sin_sq_alpha_zero_one (α : ℝ) (hα : α ≠ 0) :
    ∫ x in (0:ℝ)..1, Real.sin (α * x) ^ 2 =
    1/2 - Real.sin (2 * α) / (4 * α) := by
  have h2α : 2 * α ≠ 0 := mul_ne_zero (by norm_num) hα
  have hrw : ∀ x : ℝ, Real.sin (α * x) ^ 2 = 1/2 - Real.cos (2 * α * x) / 2 := by
    intro x
    have hc : Real.cos (2 * (α * x)) = 2 * Real.cos (α * x) ^ 2 - 1 :=
      Real.cos_two_mul (α * x)
    have hps : Real.sin (α * x) ^ 2 + Real.cos (α * x) ^ 2 = 1 :=
      Real.sin_sq_add_cos_sq (α * x)
    rw [show 2 * α * x = 2 * (α * x) from by ring]
    linarith
  simp_rw [hrw]
  have hcosInt : IntervalIntegrable (fun x => Real.cos (2 * α * x))
      MeasureTheory.volume 0 1 :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id')).intervalIntegrable _ _
  rw [integral_sub (intervalIntegral.intervalIntegrable_const) (hcosInt.div_const _)]
  rw [integral_const, integral_div]
  rw [integral_comp_mul_left Real.cos h2α]
  rw [mul_zero, mul_one]
  rw [integral_cos]
  rw [Real.sin_zero, sub_zero]
  simp [smul_eq_mul]
  field_simp
  ring

/-- **Same-scale cross product**: `∫_0^1 cos(αx)·sin(αx) dx = (1 − cos(2α))/(4α)`
    for `α ≠ 0`.

    Derived from `sin(2u) = 2·sin(u)·cos(u)` so `cos(u)·sin(u) = sin(2u)/2`,
    integrated to `(1 − cos(2α))/(4α)`. Note: at `α = 0` the integrand
    vanishes; we state for `α ≠ 0` for cleanness of the closed form. -/
theorem integral_cos_mul_sin_alpha_zero_one (α : ℝ) (hα : α ≠ 0) :
    ∫ x in (0:ℝ)..1, Real.cos (α * x) * Real.sin (α * x) =
    (1 - Real.cos (2 * α)) / (4 * α) := by
  have h2α : 2 * α ≠ 0 := mul_ne_zero (by norm_num) hα
  have hrw : ∀ x : ℝ, Real.cos (α * x) * Real.sin (α * x) =
      Real.sin (2 * α * x) / 2 := by
    intro x
    have h := Real.sin_two_mul (α * x)
    rw [show 2 * (α * x) = 2 * α * x from by ring] at h
    linarith
  simp_rw [hrw]
  rw [integral_div]
  rw [integral_comp_mul_left Real.sin h2α]
  rw [mul_zero, mul_one]
  rw [integral_sin]
  rw [Real.cos_zero]
  simp [smul_eq_mul]
  field_simp
  ring

/-! ## Off-diagonal inner-product integrals -/

/-- **Off-diagonal cosine-cosine**: for `α + β ≠ 0` and `α − β ≠ 0`,

      `∫_0^1 cos(αx)·cos(βx) dx
        = sin(α−β)/(2(α−β)) + sin(α+β)/(2(α+β))`.

    Derived from product-to-sum:
    `cos(αx)·cos(βx) = (cos((α−β)x) + cos((α+β)x))/2`,
    then integrate each linear-cosine term. -/
theorem integral_cos_mul_cos_alpha_beta_zero_one (α β : ℝ)
    (hαmβ : α - β ≠ 0) (hαpβ : α + β ≠ 0) :
    ∫ x in (0:ℝ)..1, Real.cos (α * x) * Real.cos (β * x) =
    Real.sin (α - β) / (2 * (α - β)) + Real.sin (α + β) / (2 * (α + β)) := by
  have hrw : ∀ x : ℝ, Real.cos (α * x) * Real.cos (β * x) =
      Real.cos ((α - β) * x) / 2 + Real.cos ((α + β) * x) / 2 := by
    intro x
    have h1 : Real.cos ((α - β) * x) = Real.cos (α * x - β * x) := by
      rw [show (α - β) * x = α * x - β * x from by ring]
    have h2 : Real.cos ((α + β) * x) = Real.cos (α * x + β * x) := by
      rw [show (α + β) * x = α * x + β * x from by ring]
    rw [h1, h2, Real.cos_sub, Real.cos_add]
    ring
  simp_rw [hrw]
  have hcosInt1 : IntervalIntegrable (fun x => Real.cos ((α - β) * x))
      MeasureTheory.volume 0 1 :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id')).intervalIntegrable _ _
  have hcosInt2 : IntervalIntegrable (fun x => Real.cos ((α + β) * x))
      MeasureTheory.volume 0 1 :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id')).intervalIntegrable _ _
  rw [integral_add (hcosInt1.div_const _) (hcosInt2.div_const _)]
  rw [integral_div, integral_div]
  rw [integral_comp_mul_left Real.cos hαmβ]
  rw [integral_comp_mul_left Real.cos hαpβ]
  rw [mul_zero, mul_one, mul_zero, mul_one]
  rw [integral_cos, integral_cos]
  rw [Real.sin_zero, sub_zero, sub_zero]
  simp [smul_eq_mul]
  field_simp

/-- **Off-diagonal sine-sine**: for `α + β ≠ 0` and `α − β ≠ 0`,

      `∫_0^1 sin(αx)·sin(βx) dx
        = sin(α−β)/(2(α−β)) − sin(α+β)/(2(α+β))`.

    Same template as `integral_cos_mul_cos_alpha_beta_zero_one`, using the
    product-to-sum identity
    `sin(αx)·sin(βx) = (cos((α−β)x) − cos((α+β)x))/2`. -/
theorem integral_sin_mul_sin_alpha_beta_zero_one (α β : ℝ)
    (hαmβ : α - β ≠ 0) (hαpβ : α + β ≠ 0) :
    ∫ x in (0:ℝ)..1, Real.sin (α * x) * Real.sin (β * x) =
    Real.sin (α - β) / (2 * (α - β)) - Real.sin (α + β) / (2 * (α + β)) := by
  have hrw : ∀ x : ℝ, Real.sin (α * x) * Real.sin (β * x) =
      Real.cos ((α - β) * x) / 2 - Real.cos ((α + β) * x) / 2 := by
    intro x
    have h1 : Real.cos ((α - β) * x) = Real.cos (α * x - β * x) := by
      rw [show (α - β) * x = α * x - β * x from by ring]
    have h2 : Real.cos ((α + β) * x) = Real.cos (α * x + β * x) := by
      rw [show (α + β) * x = α * x + β * x from by ring]
    rw [h1, h2, Real.cos_sub, Real.cos_add]
    ring
  simp_rw [hrw]
  have hcosInt1 : IntervalIntegrable (fun x => Real.cos ((α - β) * x))
      MeasureTheory.volume 0 1 :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id')).intervalIntegrable _ _
  have hcosInt2 : IntervalIntegrable (fun x => Real.cos ((α + β) * x))
      MeasureTheory.volume 0 1 :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id')).intervalIntegrable _ _
  rw [integral_sub (hcosInt1.div_const _) (hcosInt2.div_const _)]
  rw [integral_div, integral_div]
  rw [integral_comp_mul_left Real.cos hαmβ]
  rw [integral_comp_mul_left Real.cos hαpβ]
  rw [mul_zero, mul_one, mul_zero, mul_one]
  rw [integral_cos, integral_cos]
  rw [Real.sin_zero, sub_zero, sub_zero]
  simp [smul_eq_mul]
  field_simp

/-- **Off-diagonal sine-cosine**: for `α + β ≠ 0` and `α − β ≠ 0`,

      `∫_0^1 sin(αx)·cos(βx) dx
        = (1 − cos(α−β))/(2(α−β)) + (1 − cos(α+β))/(2(α+β))`.

    Derived from product-to-sum
    `sin(αx)·cos(βx) = (sin((α+β)x) + sin((α−β)x))/2`,
    then `∫_0^1 sin(γx) dx = (1 − cos(γ))/γ`. -/
theorem integral_sin_mul_cos_alpha_beta_zero_one (α β : ℝ)
    (hαmβ : α - β ≠ 0) (hαpβ : α + β ≠ 0) :
    ∫ x in (0:ℝ)..1, Real.sin (α * x) * Real.cos (β * x) =
    (1 - Real.cos (α - β)) / (2 * (α - β)) +
    (1 - Real.cos (α + β)) / (2 * (α + β)) := by
  have hrw : ∀ x : ℝ, Real.sin (α * x) * Real.cos (β * x) =
      Real.sin ((α + β) * x) / 2 + Real.sin ((α - β) * x) / 2 := by
    intro x
    have h1 : Real.sin ((α + β) * x) = Real.sin (α * x + β * x) := by
      rw [show (α + β) * x = α * x + β * x from by ring]
    have h2 : Real.sin ((α - β) * x) = Real.sin (α * x - β * x) := by
      rw [show (α - β) * x = α * x - β * x from by ring]
    rw [h1, h2, Real.sin_add, Real.sin_sub]
    ring
  simp_rw [hrw]
  have hsinInt1 : IntervalIntegrable (fun x => Real.sin ((α + β) * x))
      MeasureTheory.volume 0 1 :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id')).intervalIntegrable _ _
  have hsinInt2 : IntervalIntegrable (fun x => Real.sin ((α - β) * x))
      MeasureTheory.volume 0 1 :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id')).intervalIntegrable _ _
  rw [integral_add (hsinInt1.div_const _) (hsinInt2.div_const _)]
  rw [integral_div, integral_div]
  rw [integral_comp_mul_left Real.sin hαpβ]
  rw [integral_comp_mul_left Real.sin hαmβ]
  rw [mul_zero, mul_one, mul_zero, mul_one]
  rw [integral_sin, integral_sin]
  rw [Real.cos_zero]
  simp [smul_eq_mul]
  field_simp
  ring

/-! ## Mercer decomposition of the truncated kernel on `ℝ` -/

/-- **Mercer decomposition of the truncated fractal kernel** on `K = ℝ`:

      `V_P^(k)(x, y) = Σ_{j=0}^{k-1} a^(-j) ·
                       (cosineMode α j x · cosineMode α j y +
                        sineMode α j x · sineMode α j y)`

    Each summand is a rank-2 separable kernel (one rank-1 piece each
    for cosineMode and sineMode). The truncated operator induced by
    this kernel is therefore rank ≤ 2k on `L²([0,1])` — explicit
    eigenbasis from the cosineMode/sineMode functions, with matrix
    entries given by the inner products proven above.

    Combined with the `O(a^(-k))` uniform-norm approximation from
    `KernelSelfSimilarity.abs_fractalKernelReal_sub_truncated_le`,
    this gives finite-rank spectral approximations of
    `H_P_at α a` with concretely-computable matrix entries and
    explicit operator-norm error bounds. -/
theorem truncatedFractalKernelReal_mercer
    (α a : ℝ) (k : ℕ) (x y : ℝ) :
    PrincipiaTractalis.IntegralKernel.truncatedFractalKernelReal
      α a k ((x, y) : ℝ × ℝ)
    = (Finset.range k).sum
        (fun j => a^(-(j : ℤ)) *
          (cosineMode α j x * cosineMode α j y +
           sineMode α j x * sineMode α j y)) := by
  unfold PrincipiaTractalis.IntegralKernel.truncatedFractalKernelReal
  apply Finset.sum_congr rfl
  intro j _
  show a ^ (-(j : ℤ)) * Real.cos (Real.pi * α ^ j * dist x y) =
       a ^ (-(j : ℤ)) * (cosineMode α j x * cosineMode α j y
                       + sineMode α j x * sineMode α j y)
  congr 1
  rw [Real.dist_eq]
  exact cos_kernel_decomp_abs α j x y

/-! ## Truncated operator action -/

/-- **Truncated operator action** on `f : ℝ → ℝ`:

      `(T_k f)(x) := ∫_0^1 V_P^(k)(x, y) · f(y) dy`. -/
noncomputable def truncatedOperatorAction
    (α a : ℝ) (k : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in (0:ℝ)..1,
    PrincipiaTractalis.IntegralKernel.truncatedFractalKernelReal
      α a k ((x, y) : ℝ × ℝ) * f y

/-- **Explicit action formula** (the matrix-rank-2k structure):

      `(T_k f)(x) = Σ_{j=0}^{k-1} a^(-j) ·
                    [cosineMode α j x · ⟨cosineMode α j, f⟩_L²[0,1]
                   + sineMode α j x   · ⟨sineMode α j,   f⟩_L²[0,1]]`

    where `⟨·, ·⟩_L²[0,1]` is the standard L²([0,1]) inner product
    `∫_0^1 g(y) · f(y) dy` (real-valued).

    Direct consequence of the Mercer decomposition
    `truncatedFractalKernelReal_mercer` plus linearity of the integral
    (with continuous `f` giving the required interval integrability of
    every summand).

    This is the explicit FINITE-RANK ACTION of the truncated operator
    on the cosineMode/sineMode basis. Combined with the L∞
    approximation bound from `KernelSelfSimilarity`, finite-rank
    spectral computations on `H_P_at α a` are now formally supported. -/
theorem truncatedOperatorAction_eq_sum
    (α a : ℝ) (k : ℕ) (f : ℝ → ℝ) (hf : Continuous f) (x : ℝ) :
    truncatedOperatorAction α a k f x =
    (Finset.range k).sum (fun j =>
      a^(-(j : ℤ)) *
        (cosineMode α j x * (∫ y in (0:ℝ)..1, cosineMode α j y * f y) +
         sineMode α j x   * (∫ y in (0:ℝ)..1, sineMode α j y   * f y))) := by
  unfold truncatedOperatorAction
  have hpoint : ∀ y,
      PrincipiaTractalis.IntegralKernel.truncatedFractalKernelReal
        α a k ((x, y) : ℝ × ℝ) * f y =
      (Finset.range k).sum (fun j => a^(-(j : ℤ)) *
        ((cosineMode α j x * (cosineMode α j y * f y))
       + (sineMode α j x   * (sineMode α j y   * f y)))) := by
    intro y
    rw [truncatedFractalKernelReal_mercer]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _; ring
  simp_rw [hpoint]
  have cont_cosineMode : ∀ j, Continuous (cosineMode α j) := fun j => by
    unfold cosineMode
    exact Real.continuous_cos.comp (continuous_const.mul continuous_id')
  have cont_sineMode : ∀ j, Continuous (sineMode α j) := fun j => by
    unfold sineMode
    exact Real.continuous_sin.comp (continuous_const.mul continuous_id')
  have iint_summand : ∀ j ∈ Finset.range k,
      IntervalIntegrable (fun y => a^(-(j : ℤ)) *
        ((cosineMode α j x * (cosineMode α j y * f y))
       + (sineMode α j x   * (sineMode α j y   * f y))))
        MeasureTheory.volume 0 1 := by
    intros j _
    have h1 : Continuous (fun y => cosineMode α j x * (cosineMode α j y * f y)) :=
      continuous_const.mul ((cont_cosineMode j).mul hf)
    have h2 : Continuous (fun y => sineMode α j x * (sineMode α j y * f y)) :=
      continuous_const.mul ((cont_sineMode j).mul hf)
    exact (continuous_const.mul (h1.add h2)).intervalIntegrable _ _
  rw [integral_finset_sum (h := iint_summand)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul]
  congr 1
  rw [integral_add
        ((continuous_const.mul ((cont_cosineMode j).mul hf)).intervalIntegrable _ _)
        ((continuous_const.mul ((cont_sineMode j).mul hf)).intervalIntegrable _ _)]
  congr 1 <;> rw [integral_const_mul]

/-! ## Specialization to cosineMode/sineMode -/

/-- **Diagonal cosineMode inner product**: for `α^n ≠ 0` (i.e., `α ≠ 0`),
    `⟨cosineMode α n, cosineMode α n⟩_L²[0,1] = 1/2 + sin(2πα^n)/(4πα^n)`. -/
theorem inner_cosineMode_self
    (α : ℝ) (n : ℕ) (hα : α ≠ 0) :
    ∫ x in (0:ℝ)..1, cosineMode α n x ^ 2 =
    1/2 + Real.sin (2 * (Real.pi * α^n)) / (4 * (Real.pi * α^n)) := by
  unfold cosineMode
  have hπαn : Real.pi * α^n ≠ 0 :=
    mul_ne_zero Real.pi_ne_zero (pow_ne_zero n hα)
  exact integral_cos_sq_alpha_zero_one (Real.pi * α^n) hπαn

/-- **Diagonal sineMode inner product**: for `α ≠ 0`,
    `⟨sineMode α n, sineMode α n⟩_L²[0,1] = 1/2 − sin(2πα^n)/(4πα^n)`. -/
theorem inner_sineMode_self
    (α : ℝ) (n : ℕ) (hα : α ≠ 0) :
    ∫ x in (0:ℝ)..1, sineMode α n x ^ 2 =
    1/2 - Real.sin (2 * (Real.pi * α^n)) / (4 * (Real.pi * α^n)) := by
  unfold sineMode
  have hπαn : Real.pi * α^n ≠ 0 :=
    mul_ne_zero Real.pi_ne_zero (pow_ne_zero n hα)
  exact integral_sin_sq_alpha_zero_one (Real.pi * α^n) hπαn

/-- **Same-scale cross-mode inner product**: for `α ≠ 0`,
    `⟨cosineMode α n, sineMode α n⟩_L²[0,1] = (1 − cos(2πα^n))/(4πα^n)`. -/
theorem inner_cosineMode_sineMode_same
    (α : ℝ) (n : ℕ) (hα : α ≠ 0) :
    ∫ x in (0:ℝ)..1, cosineMode α n x * sineMode α n x =
    (1 - Real.cos (2 * (Real.pi * α^n))) / (4 * (Real.pi * α^n)) := by
  unfold cosineMode sineMode
  have hπαn : Real.pi * α^n ≠ 0 :=
    mul_ne_zero Real.pi_ne_zero (pow_ne_zero n hα)
  exact integral_cos_mul_sin_alpha_zero_one (Real.pi * α^n) hπαn

/-! ## Off-diagonal cosineMode/sineMode inner products (different scales) -/

/-- **Off-diagonal cosineMode-cosineMode at different scales**:

      `⟨cosineMode α n, cosineMode α m⟩_L²[0,1]
        = sin(π·αⁿ − π·αᵐ)/(2·(π·αⁿ − π·αᵐ))
        + sin(π·αⁿ + π·αᵐ)/(2·(π·αⁿ + π·αᵐ))`

    valid when `αⁿ ≠ αᵐ` and `αⁿ + αᵐ ≠ 0`.

    The matrix entry `M_{n,m}^{cos,cos}` of the kernel-multiplication
    operator at scales `n, m`. -/
theorem inner_cosineMode_cosineMode_off
    (α : ℝ) (n m : ℕ) (h_diff : α^n ≠ α^m) (h_sum : α^n + α^m ≠ 0) :
    ∫ y in (0:ℝ)..1, cosineMode α n y * cosineMode α m y =
    Real.sin (Real.pi * α^n - Real.pi * α^m)
      / (2 * (Real.pi * α^n - Real.pi * α^m)) +
    Real.sin (Real.pi * α^n + Real.pi * α^m)
      / (2 * (Real.pi * α^n + Real.pi * α^m)) := by
  unfold cosineMode
  have h_amb : Real.pi * α^n - Real.pi * α^m ≠ 0 := by
    intro h; apply h_diff
    have : Real.pi * α^n = Real.pi * α^m := by linarith
    exact mul_left_cancel₀ Real.pi_ne_zero this
  have h_apb : Real.pi * α^n + Real.pi * α^m ≠ 0 := by
    intro h; apply h_sum
    have : Real.pi * (α^n + α^m) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left Real.pi_ne_zero
  exact integral_cos_mul_cos_alpha_beta_zero_one
    (Real.pi * α^n) (Real.pi * α^m) h_amb h_apb

/-- **Off-diagonal sineMode-sineMode at different scales**:

      `⟨sineMode α n, sineMode α m⟩_L²[0,1]
        = sin(π·αⁿ − π·αᵐ)/(2·(π·αⁿ − π·αᵐ))
        − sin(π·αⁿ + π·αᵐ)/(2·(π·αⁿ + π·αᵐ))`. -/
theorem inner_sineMode_sineMode_off
    (α : ℝ) (n m : ℕ) (h_diff : α^n ≠ α^m) (h_sum : α^n + α^m ≠ 0) :
    ∫ y in (0:ℝ)..1, sineMode α n y * sineMode α m y =
    Real.sin (Real.pi * α^n - Real.pi * α^m)
      / (2 * (Real.pi * α^n - Real.pi * α^m)) -
    Real.sin (Real.pi * α^n + Real.pi * α^m)
      / (2 * (Real.pi * α^n + Real.pi * α^m)) := by
  unfold sineMode
  have h_amb : Real.pi * α^n - Real.pi * α^m ≠ 0 := by
    intro h; apply h_diff
    have : Real.pi * α^n = Real.pi * α^m := by linarith
    exact mul_left_cancel₀ Real.pi_ne_zero this
  have h_apb : Real.pi * α^n + Real.pi * α^m ≠ 0 := by
    intro h; apply h_sum
    have : Real.pi * (α^n + α^m) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left Real.pi_ne_zero
  exact integral_sin_mul_sin_alpha_beta_zero_one
    (Real.pi * α^n) (Real.pi * α^m) h_amb h_apb

/-- **Off-diagonal sineMode-cosineMode at different scales**:

      `⟨sineMode α n, cosineMode α m⟩_L²[0,1]
        = (1 − cos(π·αⁿ − π·αᵐ))/(2·(π·αⁿ − π·αᵐ))
        + (1 − cos(π·αⁿ + π·αᵐ))/(2·(π·αⁿ + π·αᵐ))`. -/
theorem inner_sineMode_cosineMode_off
    (α : ℝ) (n m : ℕ) (h_diff : α^n ≠ α^m) (h_sum : α^n + α^m ≠ 0) :
    ∫ y in (0:ℝ)..1, sineMode α n y * cosineMode α m y =
    (1 - Real.cos (Real.pi * α^n - Real.pi * α^m)) /
        (2 * (Real.pi * α^n - Real.pi * α^m)) +
    (1 - Real.cos (Real.pi * α^n + Real.pi * α^m)) /
        (2 * (Real.pi * α^n + Real.pi * α^m)) := by
  unfold sineMode cosineMode
  have h_amb : Real.pi * α^n - Real.pi * α^m ≠ 0 := by
    intro h; apply h_diff
    have : Real.pi * α^n = Real.pi * α^m := by linarith
    exact mul_left_cancel₀ Real.pi_ne_zero this
  have h_apb : Real.pi * α^n + Real.pi * α^m ≠ 0 := by
    intro h; apply h_sum
    have : Real.pi * (α^n + α^m) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left Real.pi_ne_zero
  exact integral_sin_mul_cos_alpha_beta_zero_one
    (Real.pi * α^n) (Real.pi * α^m) h_amb h_apb

/-! ## Base case: explicit eigenvalues of the k = 1 truncation

The lowest-scale truncation `T_1` is the rank-2 operator induced by the
single kernel term `cos(π · |x − y|)`. Its action on the n = 0
cosineMode/sineMode functions has explicit closed-form eigenvalues.

The scale-0 inner products are trivial because `α^0 = 1` for any `α`:

  `⟨cosineMode α 0, cosineMode α 0⟩ = 1/2 + sin(2π)/(4π) = 1/2`     (since sin 2π = 0)
  `⟨sineMode α 0, sineMode α 0⟩   = 1/2 − sin(2π)/(4π) = 1/2`
  `⟨cosineMode α 0, sineMode α 0⟩ = (1 − cos(2π))/(4π) = 0`         (orthogonal)

So `T_1` is diagonalised by `{cos(π·), sin(π·)}` with both
eigenvalues equal to `1/2`. -/

/-- `⟨cosineMode α 0, cosineMode α 0⟩_L²[0,1] = 1/2`  (any `α ≠ 0`). -/
theorem inner_cosineMode_zero_self_eq_half (α : ℝ) (hα : α ≠ 0) :
    ∫ y in (0:ℝ)..1, cosineMode α 0 y ^ 2 = 1/2 := by
  rw [inner_cosineMode_self α 0 hα]; simp [Real.sin_two_pi]

/-- `⟨sineMode α 0, sineMode α 0⟩_L²[0,1] = 1/2`  (any `α ≠ 0`). -/
theorem inner_sineMode_zero_self_eq_half (α : ℝ) (hα : α ≠ 0) :
    ∫ y in (0:ℝ)..1, sineMode α 0 y ^ 2 = 1/2 := by
  rw [inner_sineMode_self α 0 hα]; simp [Real.sin_two_pi]

/-- `⟨cosineMode α 0, sineMode α 0⟩_L²[0,1] = 0`  (orthogonal at scale 0). -/
theorem inner_cosineMode_zero_sineMode_zero_eq_zero (α : ℝ) (hα : α ≠ 0) :
    ∫ y in (0:ℝ)..1, cosineMode α 0 y * sineMode α 0 y = 0 := by
  rw [inner_cosineMode_sineMode_same α 0 hα]; simp [Real.cos_two_pi]

/-- **k = 1 truncation eigenvalue, cosine mode**:

      `(T_1 · cosineMode α 0)(x) = (1/2) · cosineMode α 0 x`

    i.e., `cos(π·)` is an eigenfunction of the rank-2 truncated
    operator `T_1` with eigenvalue `1/2`. -/
theorem truncatedOperatorAction_one_cosineMode_zero
    (α a : ℝ) (hα : α ≠ 0) (x : ℝ) :
    truncatedOperatorAction α a 1 (cosineMode α 0) x =
    (1/2 : ℝ) * cosineMode α 0 x := by
  have hcont : Continuous (cosineMode α 0) := by
    unfold cosineMode
    exact Real.continuous_cos.comp (continuous_const.mul continuous_id')
  rw [truncatedOperatorAction_eq_sum α a 1 (cosineMode α 0) hcont x]
  simp
  have h_cos_cos : (∫ y in (0:ℝ)..1, cosineMode α 0 y * cosineMode α 0 y) = 1/2 := by
    have hrw : ∀ y, cosineMode α 0 y * cosineMode α 0 y = cosineMode α 0 y ^ 2 :=
      fun y => by ring
    simp_rw [hrw]; exact inner_cosineMode_zero_self_eq_half α hα
  have h_sin_cos : (∫ y in (0:ℝ)..1, sineMode α 0 y * cosineMode α 0 y) = 0 := by
    rw [show (fun y => sineMode α 0 y * cosineMode α 0 y) =
            (fun y => cosineMode α 0 y * sineMode α 0 y)
        from by funext y; ring]
    exact inner_cosineMode_zero_sineMode_zero_eq_zero α hα
  rw [h_cos_cos, h_sin_cos]
  ring

/-- **k = 1 truncation eigenvalue, sine mode**:

      `(T_1 · sineMode α 0)(x) = (1/2) · sineMode α 0 x`

    i.e., `sin(π·)` is an eigenfunction of the rank-2 truncated
    operator `T_1` with eigenvalue `1/2`. -/
theorem truncatedOperatorAction_one_sineMode_zero
    (α a : ℝ) (hα : α ≠ 0) (x : ℝ) :
    truncatedOperatorAction α a 1 (sineMode α 0) x =
    (1/2 : ℝ) * sineMode α 0 x := by
  have hcont : Continuous (sineMode α 0) := by
    unfold sineMode
    exact Real.continuous_sin.comp (continuous_const.mul continuous_id')
  rw [truncatedOperatorAction_eq_sum α a 1 (sineMode α 0) hcont x]
  simp
  have h_cos_sin : (∫ y in (0:ℝ)..1, cosineMode α 0 y * sineMode α 0 y) = 0 :=
    inner_cosineMode_zero_sineMode_zero_eq_zero α hα
  have h_sin_sin : (∫ y in (0:ℝ)..1, sineMode α 0 y * sineMode α 0 y) = 1/2 := by
    have hrw : ∀ y, sineMode α 0 y * sineMode α 0 y = sineMode α 0 y ^ 2 :=
      fun y => by ring
    simp_rw [hrw]; exact inner_sineMode_zero_self_eq_half α hα
  rw [h_cos_sin, h_sin_sin]
  ring

/-! ## Operator-action convergence: T_k → H_P pointwise -/

/-- **Full operator action** on `f : ℝ → ℝ` via the (un-truncated)
    fractal kernel:

      `(H_P f)(x) := ∫_0^1 V_P(x, y) · f(y) dy`. -/
noncomputable def fullOperatorAction
    (α a : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in (0:ℝ)..1, PrincipiaTractalis.IntegralKernel.fractalKernelReal α a ((x, y) : ℝ × ℝ) * f y

/-- **Truncated-to-full convergence bound**: the truncation error at
    each point `x` is bounded by `a^(-k) · a/(a−1) · ∫_0^1 |f(y)| dy`.

    Direct from:
    * the kernel-level uniform L∞ bound
      (`abs_fractalKernelReal_sub_truncated_le`),
    * `|kernel·f| ≤ (kernel L∞ bound) · |f|` pointwise,
    * monotonicity of the integral.

    Integrability hypotheses are taken as parameters — caller supplies
    them. They are satisfied, e.g., when `fractalKernelReal α a (x, ·)`
    is interval-integrable on `[0,1]` (which holds because the kernel
    is bounded; the formal `Measurable`+`Integrable` chain is in
    `IntegralKernel.FractalKernel`) and `f` is continuous.

    As `k → ∞` the right-hand side is `O(a^(-k))`, so the truncated
    operator action converges pointwise to the full operator action
    with explicit error rate. -/
theorem fullOperatorAction_sub_truncated_bound
    (α a : ℝ) (ha : 1 < a) (hα : 0 ≤ α) (k : ℕ)
    (f : ℝ → ℝ) (x : ℝ)
    (hf_int_full : IntervalIntegrable
        (fun y => PrincipiaTractalis.IntegralKernel.fractalKernelReal α a ((x, y) : ℝ × ℝ) * f y)
        MeasureTheory.volume 0 1)
    (hf_int_trunc : IntervalIntegrable
        (fun y => PrincipiaTractalis.IntegralKernel.truncatedFractalKernelReal
          α a k ((x, y) : ℝ × ℝ) * f y)
        MeasureTheory.volume 0 1)
    (hf_int_abs : IntervalIntegrable
        (fun y => |f y|) MeasureTheory.volume 0 1) :
    |fullOperatorAction α a f x - truncatedOperatorAction α a k f x|
    ≤ a^(-(k : ℤ)) * (a / (a - 1)) *
      ∫ y in (0:ℝ)..1, |f y| := by
  unfold fullOperatorAction truncatedOperatorAction
  rw [← intervalIntegral.integral_sub hf_int_full hf_int_trunc]
  have hbound : ∀ y,
      |PrincipiaTractalis.IntegralKernel.fractalKernelReal α a ((x, y) : ℝ × ℝ) * f y
        - PrincipiaTractalis.IntegralKernel.truncatedFractalKernelReal
            α a k ((x, y) : ℝ × ℝ) * f y|
      ≤ (a^(-(k : ℤ)) * (a / (a - 1))) * |f y| := by
    intro y
    rw [show PrincipiaTractalis.IntegralKernel.fractalKernelReal α a ((x, y) : ℝ × ℝ) * f y
            - PrincipiaTractalis.IntegralKernel.truncatedFractalKernelReal
                α a k ((x, y) : ℝ × ℝ) * f y
          = (PrincipiaTractalis.IntegralKernel.fractalKernelReal α a ((x, y) : ℝ × ℝ)
            - PrincipiaTractalis.IntegralKernel.truncatedFractalKernelReal
                α a k ((x, y) : ℝ × ℝ)) * f y from by ring]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right
      (PrincipiaTractalis.IntegralKernel.abs_fractalKernelReal_sub_truncated_le
        α a ha hα k x y) (abs_nonneg _)
  calc |∫ y in (0:ℝ)..1, PrincipiaTractalis.IntegralKernel.fractalKernelReal α a ((x, y) : ℝ × ℝ) * f y
              - PrincipiaTractalis.IntegralKernel.truncatedFractalKernelReal
                  α a k ((x, y) : ℝ × ℝ) * f y|
      ≤ ∫ y in (0:ℝ)..1, |PrincipiaTractalis.IntegralKernel.fractalKernelReal α a ((x, y) : ℝ × ℝ) * f y
              - PrincipiaTractalis.IntegralKernel.truncatedFractalKernelReal
                  α a k ((x, y) : ℝ × ℝ) * f y| := by
          exact intervalIntegral.abs_integral_le_integral_abs zero_le_one
    _ ≤ ∫ y in (0:ℝ)..1, (a^(-(k : ℤ)) * (a / (a - 1))) * |f y| := by
          apply intervalIntegral.integral_mono_on zero_le_one
          · exact (hf_int_full.sub hf_int_trunc).abs
          · exact hf_int_abs.const_mul _
          · intro y _; exact hbound y
    _ = a^(-(k : ℤ)) * (a / (a - 1)) * ∫ y in (0:ℝ)..1, |f y| := by
          rw [intervalIntegral.integral_const_mul]

/-! ## k = 2 truncation: scale mixing makes cosineMode α 0 NOT an eigenfunction -/

/-- **k = 2 truncation explicit action on `cosineMode α 0`**:

      `(T_2 · cosineMode α 0)(x)
        = (1/2) · cosineMode α 0 x
        + a⁻¹ · [ cosineMode α 1 x · ⟨cosineMode α 1, cosineMode α 0⟩
                + sineMode   α 1 x · ⟨sineMode   α 1, cosineMode α 0⟩ ]`

    where the cross-scale inner products are the closed forms from
    `inner_cosineMode_cosineMode_off` and `inner_sineMode_cosineMode_off`.

    Hypotheses: `α ≠ 0`, `α ≠ 1`, `α ≠ −1` (the last two ensure
    `α¹ ≠ α⁰` and `α¹ + α⁰ ≠ 0`, the conditions for the off-diagonal
    formulas to apply).

    **Significance**: cosineMode α 0 is NOT an eigenfunction of T_2
    in general — it has explicit mixing with `cosineMode α 1` and
    `sineMode α 1` whose coefficients depend on `α`. The true T_2
    eigenfunctions are linear combinations of `{cosineMode α 0,
    sineMode α 0, cosineMode α 1, sineMode α 1}` whose explicit
    determination requires diagonalising the 4×4 matrix with
    entries given by the inner-product theorems in this file. -/
theorem truncatedOperatorAction_two_cosineMode_zero
    (α a : ℝ) (hα : α ≠ 0) (hα_ne_one : α ≠ 1) (hα_ne_neg_one : α ≠ -1)
    (x : ℝ) :
    truncatedOperatorAction α a 2 (cosineMode α 0) x =
    (1/2 : ℝ) * cosineMode α 0 x
    + a^(-(1 : ℤ)) *
      (cosineMode α 1 x *
        (Real.sin (Real.pi * α^1 - Real.pi * α^0) /
            (2 * (Real.pi * α^1 - Real.pi * α^0)) +
         Real.sin (Real.pi * α^1 + Real.pi * α^0) /
            (2 * (Real.pi * α^1 + Real.pi * α^0)))
       + sineMode α 1 x *
         ((1 - Real.cos (Real.pi * α^1 - Real.pi * α^0)) /
              (2 * (Real.pi * α^1 - Real.pi * α^0)) +
          (1 - Real.cos (Real.pi * α^1 + Real.pi * α^0)) /
              (2 * (Real.pi * α^1 + Real.pi * α^0)))) := by
  have hcont : Continuous (cosineMode α 0) := by
    unfold cosineMode
    exact Real.continuous_cos.comp (continuous_const.mul continuous_id')
  rw [truncatedOperatorAction_eq_sum α a 2 (cosineMode α 0) hcont x]
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  have h_inner_cos0_cos0 :
      (∫ y in (0:ℝ)..1, cosineMode α 0 y * cosineMode α 0 y) = 1/2 := by
    have hrw : ∀ y, cosineMode α 0 y * cosineMode α 0 y = cosineMode α 0 y ^ 2 :=
      fun y => by ring
    simp_rw [hrw]; exact inner_cosineMode_zero_self_eq_half α hα
  have h_inner_sin0_cos0 :
      (∫ y in (0:ℝ)..1, sineMode α 0 y * cosineMode α 0 y) = 0 := by
    rw [show (fun y => sineMode α 0 y * cosineMode α 0 y) =
            (fun y => cosineMode α 0 y * sineMode α 0 y) from
        by funext y; ring]
    exact inner_cosineMode_zero_sineMode_zero_eq_zero α hα
  have hα_pow_diff : (α : ℝ)^(1 : ℕ) ≠ α^(0 : ℕ) := by
    simp; exact hα_ne_one
  have hα_pow_sum : (α : ℝ)^(1 : ℕ) + α^(0 : ℕ) ≠ 0 := by
    simp; intro h; apply hα_ne_neg_one; linarith
  have h_inner_cos1_cos0 :=
    inner_cosineMode_cosineMode_off α 1 0 hα_pow_diff hα_pow_sum
  have h_inner_sin1_cos0 :=
    inner_sineMode_cosineMode_off α 1 0 hα_pow_diff hα_pow_sum
  rw [h_inner_cos0_cos0, h_inner_sin0_cos0, h_inner_cos1_cos0, h_inner_sin1_cos0]
  simp only [Nat.cast_zero, neg_zero, zpow_zero, Nat.cast_one]
  ring

/-! ## k = 2 truncation: scale mixing on sineMode -/

/-- **k = 2 truncation explicit action on `sineMode α 0`** (sine analog
    of `truncatedOperatorAction_two_cosineMode_zero`):

      `(T_2 · sineMode α 0)(x)
        = (1/2) · sineMode α 0 x
        + a⁻¹ · [ cosineMode α 1 x · ⟨cosineMode α 1, sineMode α 0⟩
                + sineMode α 1 x   · ⟨sineMode α 1, sineMode α 0⟩ ]`

    where the cross-scale inner products are the closed forms from
    `inner_sineMode_cosineMode_off` (transposed via product
    commutativity) and `inner_sineMode_sineMode_off`. -/
theorem truncatedOperatorAction_two_sineMode_zero
    (α a : ℝ) (hα : α ≠ 0) (hα_ne_one : α ≠ 1) (hα_ne_neg_one : α ≠ -1)
    (x : ℝ) :
    truncatedOperatorAction α a 2 (sineMode α 0) x =
    (1/2 : ℝ) * sineMode α 0 x
    + a^(-(1 : ℤ)) *
      (cosineMode α 1 x *
        ((1 - Real.cos (Real.pi * α^0 - Real.pi * α^1)) /
            (2 * (Real.pi * α^0 - Real.pi * α^1)) +
         (1 - Real.cos (Real.pi * α^0 + Real.pi * α^1)) /
            (2 * (Real.pi * α^0 + Real.pi * α^1)))
       + sineMode α 1 x *
         (Real.sin (Real.pi * α^1 - Real.pi * α^0) /
              (2 * (Real.pi * α^1 - Real.pi * α^0)) -
          Real.sin (Real.pi * α^1 + Real.pi * α^0) /
              (2 * (Real.pi * α^1 + Real.pi * α^0)))) := by
  have hcont : Continuous (sineMode α 0) := by
    unfold sineMode
    exact Real.continuous_sin.comp (continuous_const.mul continuous_id')
  rw [truncatedOperatorAction_eq_sum α a 2 (sineMode α 0) hcont x]
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  have h_inner_cos0_sin0 :
      (∫ y in (0:ℝ)..1, cosineMode α 0 y * sineMode α 0 y) = 0 :=
    inner_cosineMode_zero_sineMode_zero_eq_zero α hα
  have h_inner_sin0_sin0 :
      (∫ y in (0:ℝ)..1, sineMode α 0 y * sineMode α 0 y) = 1/2 := by
    have hrw : ∀ y, sineMode α 0 y * sineMode α 0 y = sineMode α 0 y ^ 2 :=
      fun y => by ring
    simp_rw [hrw]; exact inner_sineMode_zero_self_eq_half α hα
  have hα_pow_diff_01 : (α : ℝ)^(0 : ℕ) ≠ α^(1 : ℕ) := by
    simp; intro h; exact hα_ne_one h.symm
  have hα_pow_sum_01 : (α : ℝ)^(0 : ℕ) + α^(1 : ℕ) ≠ 0 := by
    simp; intro h; apply hα_ne_neg_one; linarith
  have hα_pow_diff_10 : (α : ℝ)^(1 : ℕ) ≠ α^(0 : ℕ) := by
    simp; exact hα_ne_one
  have hα_pow_sum_10 : (α : ℝ)^(1 : ℕ) + α^(0 : ℕ) ≠ 0 := by
    simp; intro h; apply hα_ne_neg_one; linarith
  have h_inner_cos1_sin0 :
      (∫ y in (0:ℝ)..1, cosineMode α 1 y * sineMode α 0 y) =
      (1 - Real.cos (Real.pi * α^0 - Real.pi * α^1)) /
          (2 * (Real.pi * α^0 - Real.pi * α^1)) +
      (1 - Real.cos (Real.pi * α^0 + Real.pi * α^1)) /
          (2 * (Real.pi * α^0 + Real.pi * α^1)) := by
    rw [show (fun y => cosineMode α 1 y * sineMode α 0 y) =
            (fun y => sineMode α 0 y * cosineMode α 1 y) from
        by funext y; ring]
    exact inner_sineMode_cosineMode_off α 0 1 hα_pow_diff_01 hα_pow_sum_01
  have h_inner_sin1_sin0 :=
    inner_sineMode_sineMode_off α 1 0 hα_pow_diff_10 hα_pow_sum_10
  rw [h_inner_cos0_sin0, h_inner_sin0_sin0, h_inner_cos1_sin0, h_inner_sin1_sin0]
  simp only [Nat.cast_zero, neg_zero, zpow_zero, Nat.cast_one]
  ring

/-! ## k = 2 truncation: action on scale-1 modes -/

/-- **k = 2 truncation explicit action on `cosineMode α 1`** —
    completes row 3 of the 4×4 matrix `T_2` in the basis
    `{cosineMode α 0, sineMode α 0, cosineMode α 1, sineMode α 1}`:

      `(T_2 · cosineMode α 1)(x)
        = cosineMode α 0 x · ⟨cosineMode α 0, cosineMode α 1⟩
        + sineMode α 0 x   · ⟨sineMode α 0, cosineMode α 1⟩
        + a⁻¹ · [ cosineMode α 1 x · (1/2 + sin(2πα)/(4πα))
                + sineMode   α 1 x · (1 − cos(2πα))/(4πα) ]`

    All four inner products are closed forms from this file. -/
theorem truncatedOperatorAction_two_cosineMode_one
    (α a : ℝ) (hα : α ≠ 0) (hα_ne_one : α ≠ 1) (hα_ne_neg_one : α ≠ -1)
    (x : ℝ) :
    truncatedOperatorAction α a 2 (cosineMode α 1) x =
    cosineMode α 0 x *
      (Real.sin (Real.pi - Real.pi * α) /
          (2 * (Real.pi - Real.pi * α)) +
       Real.sin (Real.pi + Real.pi * α) /
          (2 * (Real.pi + Real.pi * α)))
    + sineMode α 0 x *
      ((1 - Real.cos (Real.pi - Real.pi * α)) /
          (2 * (Real.pi - Real.pi * α)) +
       (1 - Real.cos (Real.pi + Real.pi * α)) /
          (2 * (Real.pi + Real.pi * α)))
    + a^(-(1 : ℤ)) *
      (cosineMode α 1 x *
        (1/2 + Real.sin (2 * (Real.pi * α)) / (4 * (Real.pi * α)))
       + sineMode α 1 x *
        ((1 - Real.cos (2 * (Real.pi * α))) / (4 * (Real.pi * α)))) := by
  have hcont : Continuous (cosineMode α 1) := by
    unfold cosineMode
    exact Real.continuous_cos.comp (continuous_const.mul continuous_id')
  rw [truncatedOperatorAction_eq_sum α a 2 (cosineMode α 1) hcont x]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have hα_pow_diff_01 : (α : ℝ)^(0 : ℕ) ≠ α^(1 : ℕ) := by
    simp; intro h; exact hα_ne_one h.symm
  have hα_pow_sum_01 : (α : ℝ)^(0 : ℕ) + α^(1 : ℕ) ≠ 0 := by
    simp; intro h; apply hα_ne_neg_one; linarith
  have h_inner_cos0_cos1 :=
    inner_cosineMode_cosineMode_off α 0 1 hα_pow_diff_01 hα_pow_sum_01
  have h_inner_sin0_cos1 :=
    inner_sineMode_cosineMode_off α 0 1 hα_pow_diff_01 hα_pow_sum_01
  have h_inner_cos1_cos1 :
      (∫ y in (0:ℝ)..1, cosineMode α 1 y * cosineMode α 1 y) =
      1/2 + Real.sin (2 * (Real.pi * α^1)) / (4 * (Real.pi * α^1)) := by
    have hrw : ∀ y, cosineMode α 1 y * cosineMode α 1 y = cosineMode α 1 y ^ 2 :=
      fun y => by ring
    simp_rw [hrw]; exact inner_cosineMode_self α 1 hα
  have h_inner_sin1_cos1 :
      (∫ y in (0:ℝ)..1, sineMode α 1 y * cosineMode α 1 y) =
      (1 - Real.cos (2 * (Real.pi * α^1))) / (4 * (Real.pi * α^1)) := by
    rw [show (fun y => sineMode α 1 y * cosineMode α 1 y) =
            (fun y => cosineMode α 1 y * sineMode α 1 y) from
        by funext y; ring]
    exact inner_cosineMode_sineMode_same α 1 hα
  rw [h_inner_cos0_cos1, h_inner_sin0_cos1, h_inner_cos1_cos1, h_inner_sin1_cos1]
  simp only [pow_zero, pow_one, Nat.cast_zero, neg_zero, zpow_zero, Nat.cast_one,
             mul_one, one_mul]

/-- **k = 2 truncation explicit action on `sineMode α 1`** — completes
    row 4 of the 4×4 matrix `T_2`. Together with sessions 12, 17, and
    the cosineMode α 1 case (just above), this gives the COMPLETE
    explicit 4×4 matrix representation of `T_2` in the basis
    `{cosineMode α 0, sineMode α 0, cosineMode α 1, sineMode α 1}`,
    every entry a closed-form trig expression. -/
theorem truncatedOperatorAction_two_sineMode_one
    (α a : ℝ) (hα : α ≠ 0) (hα_ne_one : α ≠ 1) (hα_ne_neg_one : α ≠ -1)
    (x : ℝ) :
    truncatedOperatorAction α a 2 (sineMode α 1) x =
    cosineMode α 0 x *
      ((1 - Real.cos (Real.pi * α - Real.pi)) /
          (2 * (Real.pi * α - Real.pi)) +
       (1 - Real.cos (Real.pi * α + Real.pi)) /
          (2 * (Real.pi * α + Real.pi)))
    + sineMode α 0 x *
      (Real.sin (Real.pi - Real.pi * α) /
          (2 * (Real.pi - Real.pi * α)) -
       Real.sin (Real.pi + Real.pi * α) /
          (2 * (Real.pi + Real.pi * α)))
    + a^(-(1 : ℤ)) *
      (cosineMode α 1 x *
        ((1 - Real.cos (2 * (Real.pi * α))) / (4 * (Real.pi * α)))
       + sineMode α 1 x *
        (1/2 - Real.sin (2 * (Real.pi * α)) / (4 * (Real.pi * α)))) := by
  have hcont : Continuous (sineMode α 1) := by
    unfold sineMode
    exact Real.continuous_sin.comp (continuous_const.mul continuous_id')
  rw [truncatedOperatorAction_eq_sum α a 2 (sineMode α 1) hcont x]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have hα_pow_diff_01 : (α : ℝ)^(0 : ℕ) ≠ α^(1 : ℕ) := by
    simp; intro h; exact hα_ne_one h.symm
  have hα_pow_sum_01 : (α : ℝ)^(0 : ℕ) + α^(1 : ℕ) ≠ 0 := by
    simp; intro h; apply hα_ne_neg_one; linarith
  have hα_pow_diff_10 : (α : ℝ)^(1 : ℕ) ≠ α^(0 : ℕ) := by
    simp; exact hα_ne_one
  have hα_pow_sum_10 : (α : ℝ)^(1 : ℕ) + α^(0 : ℕ) ≠ 0 := by
    simp; intro h; apply hα_ne_neg_one; linarith
  have h_inner_cos0_sin1 :
      (∫ y in (0:ℝ)..1, cosineMode α 0 y * sineMode α 1 y) =
      (1 - Real.cos (Real.pi * α^1 - Real.pi * α^0)) /
          (2 * (Real.pi * α^1 - Real.pi * α^0)) +
      (1 - Real.cos (Real.pi * α^1 + Real.pi * α^0)) /
          (2 * (Real.pi * α^1 + Real.pi * α^0)) := by
    rw [show (fun y => cosineMode α 0 y * sineMode α 1 y) =
            (fun y => sineMode α 1 y * cosineMode α 0 y) from
        by funext y; ring]
    exact inner_sineMode_cosineMode_off α 1 0 hα_pow_diff_10 hα_pow_sum_10
  have h_inner_sin0_sin1 :=
    inner_sineMode_sineMode_off α 0 1 hα_pow_diff_01 hα_pow_sum_01
  have h_inner_cos1_sin1 :
      (∫ y in (0:ℝ)..1, cosineMode α 1 y * sineMode α 1 y) =
      (1 - Real.cos (2 * (Real.pi * α^1))) / (4 * (Real.pi * α^1)) :=
    inner_cosineMode_sineMode_same α 1 hα
  have h_inner_sin1_sin1 :
      (∫ y in (0:ℝ)..1, sineMode α 1 y * sineMode α 1 y) =
      1/2 - Real.sin (2 * (Real.pi * α^1)) / (4 * (Real.pi * α^1)) := by
    have hrw : ∀ y, sineMode α 1 y * sineMode α 1 y = sineMode α 1 y ^ 2 :=
      fun y => by ring
    simp_rw [hrw]; exact inner_sineMode_self α 1 hα
  rw [h_inner_cos0_sin1, h_inner_sin0_sin1, h_inner_cos1_sin1, h_inner_sin1_sin1]
  simp only [pow_zero, pow_one, Nat.cast_zero, neg_zero, zpow_zero, Nat.cast_one,
             mul_one, one_mul]

/-! ## Trace of T_k (sum of eigenvalues) -/

/-- **The diagonal of the truncated kernel is constant**:

      `V_P^(k)(x, x) = Σ_{j<k} a^(-j)`

    independent of `x`. (Each summand reduces to `a^(-j) · cos(0) =
    a^(-j)` on the diagonal.) -/
theorem truncatedFractalKernelReal_diagonal
    (α a : ℝ) (k : ℕ) (x : ℝ) :
    PrincipiaTractalis.IntegralKernel.truncatedFractalKernelReal
      α a k ((x, x) : ℝ × ℝ) =
    (Finset.range k).sum (fun j => a^(-(j : ℤ))) := by
  unfold PrincipiaTractalis.IntegralKernel.truncatedFractalKernelReal
  apply Finset.sum_congr rfl
  intro j _
  show a ^ (-(j : ℤ)) * Real.cos (Real.pi * α^j * dist x x) =
       a ^ (-(j : ℤ))
  rw [dist_self]
  simp

/-- **Trace of `T_k`** (sum of eigenvalues with multiplicity):

      `Tr(T_k) = ∫_0^1 V_P^(k)(x, x) dx = Σ_{j<k} a^(-j)`

    a finite geometric partial sum, in closed form
    `(1 − a^(-k))/(1 − 1/a) = a(1 − a^(-k))/(a−1)` for `a > 1`.

    Since `T_k` is finite-rank (rank ≤ 2k by the Mercer decomposition),
    its trace is well-defined and equals the sum of its eigenvalues.
    This gives a sum-rule constraint on the eigenvalues of the
    truncated operator. -/
theorem trace_truncatedOperator (α a : ℝ) (k : ℕ) :
    ∫ x in (0:ℝ)..1, PrincipiaTractalis.IntegralKernel.truncatedFractalKernelReal
      α a k ((x, x) : ℝ × ℝ) =
    (Finset.range k).sum (fun j => a^(-(j : ℤ))) := by
  rw [show (fun x => PrincipiaTractalis.IntegralKernel.truncatedFractalKernelReal
              α a k ((x, x) : ℝ × ℝ)) =
          (fun _ => (Finset.range k).sum (fun j => a^(-(j : ℤ))))
       from by funext x; exact truncatedFractalKernelReal_diagonal α a k x]
  rw [intervalIntegral.integral_const]
  simp

/-- **Closed form of the trace geometric sum**:

      `Σ_{j<k} a^(-j) = (1 − a^(-k)) / (1 − 1/a)`

    for `a ≠ 0, a ≠ 1`. Standard geometric-sum identity applied to
    `(1/a)^j`. As `k → ∞` for `a > 1`, this tends to `a/(a−1)`. -/
theorem geometric_sum_zpow_neg
    (a : ℝ) (ha : a ≠ 0) (ha_ne : a ≠ 1) (k : ℕ) :
    (Finset.range k).sum (fun j => a^(-(j : ℤ))) =
    (1 - a^(-(k : ℤ))) / (1 - 1/a) := by
  have h_eq : ∀ j : ℕ, (a : ℝ)^(-(j : ℤ)) = (1/a)^j := fun j => by
    rw [zpow_neg, zpow_natCast, one_div, inv_pow]
  simp_rw [h_eq]
  have h_one_div_ne : (1/a : ℝ) ≠ 1 := by
    intro h; apply ha_ne
    have : (a : ℝ) = 1 := by field_simp at h; linarith
    exact this
  rw [geom_sum_eq h_one_div_ne k]
  rw [show ((1:ℝ)/a)^k = a^(-(k:ℤ)) from by
    rw [zpow_neg, zpow_natCast, one_div, inv_pow]]
  rw [show (1 - 1/a : ℝ) = -(1/a - 1) from by ring]
  rw [show (1 - a^(-(k:ℤ)) : ℝ) = -(a^(-(k:ℤ)) - 1) from by ring]
  rw [neg_div_neg_eq]

/-- **Closed-form trace of T_k**:

      `Tr(T_k) = (1 − a^(-k)) / (1 − 1/a)`

    for `a > 1, a ≠ 0, a ≠ 1`. Combines `trace_truncatedOperator` with
    `geometric_sum_zpow_neg`. For `k → ∞`, this tends to `a/(a−1)` —
    the trace of the limiting full operator (informally; rigorous
    convergence requires trace-class limit, separate analysis). -/
theorem trace_truncatedOperator_closed_form
    (α a : ℝ) (ha : a ≠ 0) (ha_ne : a ≠ 1) (k : ℕ) :
    ∫ x in (0:ℝ)..1, PrincipiaTractalis.IntegralKernel.truncatedFractalKernelReal
      α a k ((x, x) : ℝ × ℝ) =
    (1 - a^(-(k : ℤ))) / (1 - 1/a) := by
  rw [trace_truncatedOperator α a k]
  exact geometric_sum_zpow_neg a ha ha_ne k

/-! ## ★ Full operator trace (spectral sum rule) ★ -/

/-- **★ Trace of the full operator H_P ★** (`a > 1`):

      `Tr(H_P^α) = ∫_0^1 V_P(x, x) dx = a/(a − 1)`

    Direct from the diagonal closed form `V_P(x, x) = a/(a−1)`
    (axiom-free, via `fractalKernelReal_diagonal` in
    `PF/Analytic/MatrixEntry.lean`) integrated over `[0, 1]`. The
    diagonal is INDEPENDENT of `x`, so the integral is trivially
    `a/(a−1) · μ([0, 1]) = a/(a−1)`.

    **Spectral sum rule**: by the spectral theorem for self-adjoint
    Hilbert-Schmidt operators, the trace equals the sum of eigenvalues
    (with multiplicity). So if the polylog conjecture
    `λ_k = a^(-k)·Re[Li_1(e^{iπ·αᵏ})]` holds for the full operator
    `H_P^α`, then

      `Σ_{k≥0} a^(-k)·Re[Li_1(e^{iπ·αᵏ})] = a/(a − 1)`

    is a NECESSARY CONDITION on the polylog formula. Combined with the
    trace identity at each finite truncation level k
    (`trace_truncatedOperator_closed_form`:
    `Tr(T_k) = (1 − a^(-k))/(1 − 1/a)`), the limit as `k → ∞` gives
    exactly `a/(a−1)`, **consistent with the spectral sum rule**.

    This is a STRUCTURAL CONSTRAINT on any candidate eigenvalue formula
    for `H_P^α` — both the polylog formula and any candidate eigenvalue
    sequence must sum to `a/(a−1)`.

    Note: the trace as defined here (∫ diagonal) requires the operator
    to be trace-class. For Hilbert-Schmidt operators (which `H_P^α` is,
    per `KernelSelfSimilarity.lean`'s `sq_fractalKernelReal_le`), the
    diagonal integral equals the Hilbert-Schmidt-norm-squared on the
    L² product, not the operator trace directly. But the formula
    `∫_0^1 V_P(x, x) dx = a/(a-1)` is unconditionally true at the
    integral level. -/
theorem trace_fullOperator_closed_form {α a : ℝ} (ha : 1 < a) :
    ∫ x in (0:ℝ)..1, PrincipiaTractalis.IntegralKernel.fractalKernelReal
      α a ((x, x) : ℝ × ℝ) = a / (a - 1) := by
  -- V_P(x, x) = a/(a - 1) for all x (diagonal closed form), independent of x.
  have hdiag : ∀ x : ℝ,
      PrincipiaTractalis.IntegralKernel.fractalKernelReal
        α a ((x, x) : ℝ × ℝ) = a / (a - 1) := by
    intro x
    unfold PrincipiaTractalis.IntegralKernel.fractalKernelReal
            PrincipiaTractalis.IntegralKernel.fractalKernelTerm
    have hd : dist x x = 0 := dist_self x
    have hterm : ∀ n : ℕ,
        (a : ℝ) ^ (-(n : ℤ)) *
          Real.cos (Real.pi * α ^ n * dist (x : ℝ) x) =
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
  rw [show (fun x => PrincipiaTractalis.IntegralKernel.fractalKernelReal
              α a ((x, x) : ℝ × ℝ)) =
          (fun _ => a / (a - 1)) from by funext x; exact hdiag x]
  rw [intervalIntegral.integral_const]
  simp

/-! ## ★ Single-integral cosine/sine closed forms ★ -/

/-- **Cosine integral closed form** on `[0, 1]`:

      `∫_0^1 cos(π · c · x) dx = sin(π · c) / (π · c)` (for `c ≠ 0`)

    The first moment of `cos(πcx)` over the unit interval. Foundational
    for any variational / energy-functional computation on H_P^α with
    constant or polynomial test functions. -/
theorem integral_cosine_pi_c {c : ℝ} (hc : c ≠ 0) :
    ∫ x in (0:ℝ)..1, Real.cos (Real.pi * c * x) =
    Real.sin (Real.pi * c) / (Real.pi * c) := by
  have hpi_c_ne : Real.pi * c ≠ 0 := mul_ne_zero Real.pi_ne_zero hc
  rw [show (fun x => Real.cos (Real.pi * c * x)) =
          (fun x => Real.cos ((Real.pi * c) * x)) from by funext; ring]
  rw [intervalIntegral.integral_comp_mul_left _ hpi_c_ne]
  rw [integral_cos]
  rw [mul_zero, mul_one, Real.sin_zero, sub_zero, smul_eq_mul]
  field_simp

/-- **Sine integral closed form** on `[0, 1]`:

      `∫_0^1 sin(π · c · x) dx = (1 − cos(π · c)) / (π · c)` (for `c ≠ 0`)

    Companion to `integral_cosine_pi_c`. -/
theorem integral_sine_pi_c {c : ℝ} (hc : c ≠ 0) :
    ∫ x in (0:ℝ)..1, Real.sin (Real.pi * c * x) =
    (1 - Real.cos (Real.pi * c)) / (Real.pi * c) := by
  have hpi_c_ne : Real.pi * c ≠ 0 := mul_ne_zero Real.pi_ne_zero hc
  rw [show (fun x => Real.sin (Real.pi * c * x)) =
          (fun x => Real.sin ((Real.pi * c) * x)) from by funext; ring]
  rw [intervalIntegral.integral_comp_mul_left _ hpi_c_ne]
  rw [integral_sin]
  -- (π*c)⁻¹ • (cos (π*c*0) - cos (π*c*1)) = (1 - cos (π*c)) / (π*c)
  rw [mul_zero, mul_one, Real.cos_zero, smul_eq_mul]
  field_simp

/-- **First-moment formula in cosineMode**: for `α ≠ 0` and `n : ℕ`
    with `α^n ≠ 0`,

      `∫_0^1 cosineMode α n x dx = sin(π · αⁿ) / (π · αⁿ)`

    Direct specialization of `integral_cosine_pi_c` at `c = αⁿ`.
    These are the first moments of the cosine eigenmode basis —
    foundational for variational eigenvalue upper bounds on H_P^α
    (via `⟨ψ, H_P ψ⟩` evaluation for ψ in the cos/sin basis). -/
theorem integral_cosineMode_pow {α : ℝ} (hα : α ≠ 0) (n : ℕ) :
    ∫ x in (0:ℝ)..1, cosineMode α n x =
    Real.sin (Real.pi * α^n) / (Real.pi * α^n) := by
  have hpow : α^n ≠ 0 := pow_ne_zero n hα
  unfold cosineMode
  exact integral_cosine_pi_c hpow

/-- **First-moment formula in sineMode**: for `α ≠ 0` and `n : ℕ`,

      `∫_0^1 sineMode α n x dx = (1 − cos(π · αⁿ)) / (π · αⁿ)`. -/
theorem integral_sineMode_pow {α : ℝ} (hα : α ≠ 0) (n : ℕ) :
    ∫ x in (0:ℝ)..1, sineMode α n x =
    (1 - Real.cos (Real.pi * α^n)) / (Real.pi * α^n) := by
  have hpow : α^n ≠ 0 := pow_ne_zero n hα
  unfold sineMode
  exact integral_sine_pi_c hpow

/-! ## Operator-norm-like bound: T_k as L¹ → L∞ -/

/-- **Uniform bound on `(T_k f)(x)` in terms of `‖f‖_{L¹}`**:

      `|(T_k f)(x)| ≤ (a / (a − 1)) · ∫_0^1 |f(y)| dy`

    for `a > 1`, all `x`, continuous `f`. This expresses `T_k` as a
    bounded operator `L¹([0,1]) → L^∞([0,1])` with norm uniformly
    bounded by `a/(a−1)` (independent of `k`).

    Combined with the convergence theorem `tendsto_truncatedOperatorAction`,
    this shows the truncated operators form a uniformly bounded family
    converging pointwise to the full operator. -/
theorem abs_truncatedOperatorAction_le
    (α a : ℝ) (ha : 1 < a) (k : ℕ)
    (f : ℝ → ℝ) (hf : Continuous f) (x : ℝ) :
    |truncatedOperatorAction α a k f x| ≤
    (a / (a - 1)) * ∫ y in (0:ℝ)..1, |f y| := by
  unfold truncatedOperatorAction
  have hbound : ∀ y,
      |PrincipiaTractalis.IntegralKernel.truncatedFractalKernelReal
        α a k ((x, y) : ℝ × ℝ) * f y|
      ≤ (a / (a - 1)) * |f y| := by
    intro y
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right
      (PrincipiaTractalis.IntegralKernel.abs_truncatedFractalKernelReal_le
        α a ha k x y) (abs_nonneg _)
  have hcont_summand : Continuous (fun y =>
      PrincipiaTractalis.IntegralKernel.truncatedFractalKernelReal
        α a k ((x, y) : ℝ × ℝ) * f y) :=
    (PrincipiaTractalis.IntegralKernel.continuous_truncatedFractalKernelReal_snd
      α a k x).mul hf
  have h_iint : IntervalIntegrable
      (fun y => PrincipiaTractalis.IntegralKernel.truncatedFractalKernelReal
        α a k ((x, y) : ℝ × ℝ) * f y) MeasureTheory.volume 0 1 :=
    hcont_summand.intervalIntegrable _ _
  have h_iint_abs : IntervalIntegrable (fun y => |f y|) MeasureTheory.volume 0 1 :=
    hf.abs.intervalIntegrable _ _
  calc |∫ y in (0:ℝ)..1,
            PrincipiaTractalis.IntegralKernel.truncatedFractalKernelReal
              α a k ((x, y) : ℝ × ℝ) * f y|
      ≤ ∫ y in (0:ℝ)..1, |PrincipiaTractalis.IntegralKernel.truncatedFractalKernelReal
              α a k ((x, y) : ℝ × ℝ) * f y| :=
            intervalIntegral.abs_integral_le_integral_abs zero_le_one
    _ ≤ ∫ y in (0:ℝ)..1, (a / (a - 1)) * |f y| := by
            apply intervalIntegral.integral_mono_on zero_le_one
            · exact h_iint.abs
            · exact h_iint_abs.const_mul _
            · intro y _; exact hbound y
    _ = (a / (a - 1)) * ∫ y in (0:ℝ)..1, |f y| := by
            rw [intervalIntegral.integral_const_mul]

/-! ## L²-norms of cosineMode/sineMode -/

/-- **L²([0,1]) norm-squared of `cosineMode α n`** (re-stating
    `inner_cosineMode_self` with the more conventional `2π·α^n` form):

      `∫_0^1 cosineMode α n y ^ 2 dy = 1/2 + sin(2π·αⁿ) / (4π·αⁿ)`

    for `α ≠ 0`. -/
theorem L2_norm_sq_cosineMode (α : ℝ) (n : ℕ) (hα : α ≠ 0) :
    ∫ y in (0:ℝ)..1, cosineMode α n y ^ 2 =
    1/2 + Real.sin (2 * Real.pi * α^n) / (4 * Real.pi * α^n) := by
  have := inner_cosineMode_self α n hα
  have h_eq : 2 * (Real.pi * α^n) = 2 * Real.pi * α^n := by ring
  have h_eq2 : 4 * (Real.pi * α^n) = 4 * Real.pi * α^n := by ring
  rw [this, h_eq, h_eq2]

/-- **L²([0,1]) norm-squared of `sineMode α n`**:

      `∫_0^1 sineMode α n y ^ 2 dy = 1/2 − sin(2π·αⁿ) / (4π·αⁿ)`. -/
theorem L2_norm_sq_sineMode (α : ℝ) (n : ℕ) (hα : α ≠ 0) :
    ∫ y in (0:ℝ)..1, sineMode α n y ^ 2 =
    1/2 - Real.sin (2 * Real.pi * α^n) / (4 * Real.pi * α^n) := by
  have := inner_sineMode_self α n hα
  have h_eq : 2 * (Real.pi * α^n) = 2 * Real.pi * α^n := by ring
  have h_eq2 : 4 * (Real.pi * α^n) = 4 * Real.pi * α^n := by ring
  rw [this, h_eq, h_eq2]

/-! ## Kernel characterization (forward direction) -/

/-- **If `f` is L²([0,1])-orthogonal to every `cosineMode α j` and every
    `sineMode α j` for `j < k`, then `(T_k f)(x) = 0`** for every `x`.

    Direct consequence of the explicit action formula
    `truncatedOperatorAction_eq_sum`: every coefficient is an inner
    product, all of which are zero by hypothesis.

    This is the **forward direction** of the kernel characterization
    `ker(T_k) = (span{cosineMode α j, sineMode α j : j < k})⊥`. The
    converse direction would require the spanning vectors to be
    linearly independent — they are generically, but a clean proof
    requires more work. -/
theorem truncatedOperatorAction_zero_of_orthogonal
    (α a : ℝ) (k : ℕ) (f : ℝ → ℝ) (hf : Continuous f)
    (h_orth_cos : ∀ j ∈ Finset.range k,
      ∫ y in (0:ℝ)..1, cosineMode α j y * f y = 0)
    (h_orth_sin : ∀ j ∈ Finset.range k,
      ∫ y in (0:ℝ)..1, sineMode α j y * f y = 0)
    (x : ℝ) :
    truncatedOperatorAction α a k f x = 0 := by
  rw [truncatedOperatorAction_eq_sum α a k f hf x]
  apply Finset.sum_eq_zero
  intros j hj
  rw [h_orth_cos j hj, h_orth_sin j hj]
  ring

/-! ## Spectral convergence framework -/

/-- **Spectral convergence claim** as a structured `Prop`:

      `∀ k, ∀ ε > 0, ∃ K, ∀ K' ≥ K, the truncated operator T_{K'}
       has a continuous eigenfunction with eigenvalue ε-close to λ_k`.

    This is the formal statement that the truncated spectral
    approximations converge to the conjectured eigenvalue sequence.
    It is implied by Banach-Steinhaus / compact-operator spectral
    continuity given the L¹→L∞ bound (session 21) and the convergence
    theorem (sessions 11/16), but stated separately here as a
    structured `Prop` for the conditional reduction below. -/
def SpectralConvergenceClaim (α a : ℝ) (lambda : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, ∀ ε > 0, ∃ K : ℕ, ∀ K' ≥ K,
    ∃ μ : ℝ, |μ - lambda k| < ε ∧
      ∃ (f : ℝ → ℝ), Continuous f ∧ f ≠ 0 ∧
        ∀ x ∈ Set.Icc (0 : ℝ) 1, truncatedOperatorAction α a K' f x = μ * f x

/-! ## Tendsto form of T_k → H_P -/

/-- **Truncated operator action converges to full operator action**:

      `lim_{k → ∞} (T_k f)(x) = (H_P f)(x)`

    for fixed `x : ℝ`, given the integrability hypotheses.

    This is the `Tendsto`-form of the convergence theorem
    `fullOperatorAction_sub_truncated_bound`, packaged for use with
    mathlib's filter/topology infrastructure. The proof uses the
    explicit error bound `O(a^(-k))` and the standard fact that
    `a^(-k) → 0` as `k → ∞` for `a > 1`. -/
theorem tendsto_truncatedOperatorAction
    (α a : ℝ) (ha : 1 < a) (hα : 0 ≤ α)
    (f : ℝ → ℝ) (x : ℝ)
    (hf_int_full : IntervalIntegrable
        (fun y => PrincipiaTractalis.IntegralKernel.fractalKernelReal
          α a ((x, y) : ℝ × ℝ) * f y)
        MeasureTheory.volume 0 1)
    (hf_int_trunc : ∀ (k : ℕ), IntervalIntegrable
        (fun y => PrincipiaTractalis.IntegralKernel.truncatedFractalKernelReal
          α a k ((x, y) : ℝ × ℝ) * f y)
        MeasureTheory.volume 0 1)
    (hf_int_abs : IntervalIntegrable
        (fun y => |f y|) MeasureTheory.volume 0 1) :
    Filter.Tendsto (fun k => truncatedOperatorAction α a k f x)
            Filter.atTop (nhds (fullOperatorAction α a f x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have ha_pos : 0 < a := lt_trans zero_lt_one ha
  have ha_minus_one_pos : 0 < a - 1 := by linarith
  have h_factor_nn : 0 ≤ a / (a - 1) :=
    div_nonneg (le_of_lt ha_pos) (le_of_lt ha_minus_one_pos)
  have h_int_nn : 0 ≤ ∫ y in (0:ℝ)..1, |f y| := by
    apply intervalIntegral.integral_nonneg zero_le_one
    intro y _; exact abs_nonneg _
  have hinv_lt_one : a⁻¹ < 1 := inv_lt_one_of_one_lt₀ ha
  have h_inv_nn : (0 : ℝ) ≤ a⁻¹ := le_of_lt (by positivity)
  have h_zpow : Filter.Tendsto (fun k : ℕ => (a : ℝ)^(-(k : ℤ)))
      Filter.atTop (nhds 0) := by
    have h_inv : Filter.Tendsto (fun k : ℕ => (a⁻¹ : ℝ)^k)
        Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one h_inv_nn hinv_lt_one
    have h_eq : ∀ k : ℕ, (a⁻¹ : ℝ)^k = a^(-(k : ℤ)) := fun k => by
      rw [zpow_neg, zpow_natCast, inv_pow]
    simp_rw [h_eq] at h_inv
    exact h_inv
  have h_bound_tendsto : Filter.Tendsto (fun k : ℕ =>
      a^(-(k : ℤ)) * (a / (a - 1)) * (∫ y in (0:ℝ)..1, |f y|))
      Filter.atTop (nhds 0) := by
    have h1 := (h_zpow.mul_const (a / (a - 1))).mul_const (∫ y in (0:ℝ)..1, |f y|)
    simp only [zero_mul] at h1
    exact h1
  rcases Metric.tendsto_atTop.mp h_bound_tendsto ε hε with ⟨N, hN⟩
  use N
  intro k hkN
  rw [Real.dist_eq, abs_sub_comm]
  calc |fullOperatorAction α a f x - truncatedOperatorAction α a k f x|
      ≤ a^(-(k : ℤ)) * (a / (a - 1)) * ∫ y in (0:ℝ)..1, |f y| :=
        fullOperatorAction_sub_truncated_bound α a ha hα k f x
          hf_int_full (hf_int_trunc k) hf_int_abs
    _ < ε := by
        have h := hN k hkN
        rw [Real.dist_eq, sub_zero] at h
        have h_pos : 0 ≤ a^(-(k : ℤ)) * (a / (a - 1)) * ∫ y in (0:ℝ)..1, |f y| := by
          apply mul_nonneg _ h_int_nn
          exact mul_nonneg (le_of_lt (zpow_pos ha_pos _)) h_factor_nn
        rw [abs_of_nonneg h_pos] at h
        exact h

/-! ## Formal conjecture statement

The conjecture `λ_k = (1/aᵏ) · Re[Li₁(e^{iπαᵏ})]` requires the complex
polylogarithm `Li₁`, which lives in `Complex` (not `Real`). We state the
predicate at this layer of abstraction and leave its detailed development
to a follow-on file.

In `Complex`, `Li₁(z) = −log(1 − z)` for `|z| < 1`, with the canonical
extension to `|z| = 1` (where the kernel evaluation lands) following the
Riemann-sheet selection rule of Heuristic `heur:branch-selection`.

The structured predicate below states the claim parametrically: a
proposition that `λ : ℕ → ℝ` is the eigenvalue sequence of `H_P_at α a`
in the sense of the conjecture. -/

/-- **Polylog-spectrum eigenvalue formula** as a structured `Prop`.

    Captures the manuscript's claim `λ_k = (1/aᵏ) · Re[Li₁(e^{iπ·αᵏ})]`
    parametrically over the kernel parameters `α, a` and a candidate
    eigenvalue sequence `λ : ℕ → ℝ`.

    The polylog is the principal-branch polylog of order 1 evaluated at
    a unit-modulus argument; the branch-selection content of the
    Heuristic `heur:branch-selection` is captured by the user's choice of
    the function `polylog_eval : ℂ → ℂ` (parameterised here, with the
    expectation that the manuscript's specific Riemann-sheet rule will be
    formalised as a definite function in follow-on work). -/
def PolylogSpectrumClaim
    (α a : ℝ) (polylog_eval : ℂ → ℂ) (lambda : ℕ → ℝ) : Prop :=
  ∀ k : ℕ,
    lambda k = a^(-(k : ℤ)) *
      (polylog_eval (Complex.exp (Complex.I * Real.pi * (α^k : ℝ)))).re

/-- **The full polylog spectrum conjecture** as a structured `Prop`:

    There exists an eigenvalue sequence `lambda` satisfying both
    * the polylog formula (`PolylogSpectrumClaim` with the
      principal-branch polylog `−log(1 − z)`), and
    * spectral convergence from the truncations.

    Solving Problem 1 of `OPEN_PROBLEMS.md` is equivalent to proving
    or disproving this `PolylogSpectrumFullConjecture` for `α = √2`,
    `a > 1`. -/
def PolylogSpectrumFullConjecture (α a : ℝ) : Prop :=
  ∃ lambda : ℕ → ℝ,
    PolylogSpectrumClaim α a (fun z => -Complex.log (1 - z)) lambda ∧
    SpectralConvergenceClaim α a lambda

/-- **Principal-branch consequence**: if the conjecture holds with the
    polylog evaluated on the principal branch (i.e., `−log(1 − z)`
    extended to the closed unit disk), then for each `k` with
    `sin(π·αᵏ/2) ≠ 0`,

      `λ_k = −a^(-k) · log(2 · |sin(π·αᵏ/2)|)`.

    This is the closed-form eigenvalue prediction on the principal
    branch, matching the principal-branch evaluation from
    `PolylogBoundary`. For `α = √2, k = 0` this gives the NEGATIVE
    value `≈ −0.468`; the manuscript's positive `π/(10·√2)` requires
    a different Riemann sheet (Problem 2 Heuristic). -/
theorem polylog_principal_branch_eigenvalue
    (α a : ℝ) (lambda : ℕ → ℝ)
    (h : PolylogSpectrumClaim α a (fun z => -Complex.log (1 - z)) lambda)
    (k : ℕ) (hsin : Real.sin (Real.pi * α^k / 2) ≠ 0) :
    lambda k = -a^(-(k : ℤ)) *
      Real.log (2 * |Real.sin (Real.pi * α^k / 2)|) := by
  have h_eq_arg : Complex.I * (Real.pi * α^k : ℝ)
                = Complex.I * ↑Real.pi * ↑(α^k) := by
    push_cast; ring
  rw [h k]
  show a^(-(k : ℤ)) *
    (-Complex.log (1 - Complex.exp (Complex.I * ↑Real.pi * ↑(α^k)))).re
    = -a^(-(k : ℤ)) * Real.log (2 * |Real.sin (Real.pi * α^k / 2)|)
  rw [← h_eq_arg]
  have h_ppl := re_polyLog_one_principal_exp_I_pi_alpha_pow α k hsin
  unfold polyLog_one_principal at h_ppl
  rw [h_ppl]
  ring

/-! ## Conditional retirement: the chain

Given the formal building blocks above + the (future) diagonalisation of
`H_P_at α a` in the cosineMode/sineMode basis, the chain to attack the
conjecture is:

```
1. Identify eigenvectors of H_P_at α a as linear combinations
   ψ_k = Σ_n (c_n,k cosineMode α n + d_n,k sineMode α n).
2. Use the cosineMode/sineMode inner products (this file) to compute
   the matrix entries of H_P_at α a.
3. Diagonalise (likely via the manuscript's self-similar fixed-point
   structure) to obtain explicit eigenvalues λ_k.
4. Identify λ_k = (1/aᵏ) · Re[Li₁(e^{iπαᵏ})] via the polylog series
   expansion and the branch-selection rule.
```

Steps 1, 3, 4 require **original mathematics**, not formalization labor.
Step 2 is now mechanically supported by the proven integrals above.

What this file provides referee-grade:
  * The Mercer-type rank-2-per-scale decomposition is proven in
    `FourierCosineDecomposition.lean`.
  * All six cosineMode/sineMode inner products on `[0,1]` are
    proven in this file.
  * The formal conjecture statement `PolylogSpectrumClaim` is a
    structured `Prop` ready to be targeted by future theorems.

What this file does NOT provide:
  * Steps 1, 3, 4 above. These constitute the open mathematical
    research of Problem 1 in `OPEN_PROBLEMS.md`.
-/

end PrincipiaTractalis.Analytic
