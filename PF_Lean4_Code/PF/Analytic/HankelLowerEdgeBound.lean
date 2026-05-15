/-
# Hankel Contour: Lower-Edge Integrand Modulus Bound

The bound-by-modulus piece for the lower edge. Mirrors
`HankelUpperEdgeBound.lean`, adapted to the wrapped-branch lower-edge
integrand

  `e^(2πi(s-1)) · (t - iε)^(s-1) · e^(-(t-iε))`.

Key adaptations from the upper edge:
* `(t - iε)` instead of `(t + iε)`. The modulus is the same:
  `‖t - iε‖ = √(t² + ε²) = ‖t + iε‖`.
* The real part `Re(t - iε) = t` is unchanged, so `‖exp(-(t-iε))‖ = exp(-t)`.
* The argument `arg(t - iε)` lies in `[-π/2, 0]` for `t > 0, ε > 0`,
  with `|arg(t - iε)| ≤ π/2` still (from `Re = t > 0`).
* Additional constant factor: `‖e^(2πi(s-1))‖ = exp(-2π · Im s)`.

Theorems (all axiom-clean):
* `lower_edge_ne_zero`: `(t - iε) ≠ 0` for `t > 0`.
* `abs_arg_lower_le`: `|arg(t - iε)| ≤ π/2` for `t > 0`.
* `norm_exp_neg_lower_edge`: `‖exp(-(t - iε))‖ = exp(-t)`.
* `norm_branch_factor`: `‖e^(2πi(s-1))‖ = exp(-2π · Im s)`.
* `norm_cpow_lower_edge_le`: cpow modulus bound on the lower edge.
* `norm_hankelLowerEdgeIntegrand_le`: full integrand modulus bound.

Stage L4 — Lower-edge integrand modulus bound (analytic content).
-/

import PF.Analytic.HankelUpperEdgeBound

namespace PrincipiaTractalis.Analytic

open Complex

/-! ## Basic facts about `z := t - iε` -/

/-- **z is nonzero for t > 0**: `Re(t - iε) = t > 0`. -/
theorem lower_edge_ne_zero (t ε : ℝ) (ht : 0 < t) :
    (t : ℂ) - (ε : ℂ) * I ≠ 0 := by
  intro h
  have h_re : ((t : ℂ) - (ε : ℂ) * I).re = (0 : ℂ).re := by rw [h]
  simp at h_re
  linarith

/-- **Real part is t**: `Re(t - iε) = t`. -/
theorem lower_edge_re (t ε : ℝ) :
    ((t : ℂ) - (ε : ℂ) * I).re = t := by simp

/-- **Argument bound**: `|arg(t - iε)| ≤ π/2` for `t > 0`. -/
theorem abs_arg_lower_le (t ε : ℝ) (ht : 0 < t) :
    |Complex.arg ((t : ℂ) - (ε : ℂ) * I)| ≤ Real.pi / 2 := by
  rw [Complex.abs_arg_le_pi_div_two_iff]
  rw [lower_edge_re]
  exact ht.le

/-! ## Modulus of the exp factor -/

/-- **Norm of `exp(-(t - iε))` equals `Real.exp(-t)`**. -/
theorem norm_exp_neg_lower_edge (t ε : ℝ) :
    ‖Complex.exp (-((t : ℂ) - (ε : ℂ) * I))‖ = Real.exp (-t) := by
  rw [Complex.norm_exp]
  congr 1
  simp

/-! ## Modulus of the branch factor -/

/-- **Norm of branch factor**: `‖e^(2πi(s-1))‖ = exp(-2π · Im s)`.

    Derivation:
    ```
    Re(2πi(s-1)) = Re(2πi·s − 2πi)
                 = Re(2πi·s) − Re(2πi)
                 = -2π · Im s − 0
                 = -2π · Im s.
    ```
    So `‖exp(2πi(s-1))‖ = exp(-2π · Im s)`. -/
theorem norm_branch_factor (s : ℂ) :
    ‖Complex.exp (2 * (Real.pi : ℂ) * I * (s - 1))‖ =
    Real.exp (-(2 * Real.pi * s.im)) := by
  rw [Complex.norm_exp]
  congr 1
  -- Compute Re(2π·I·(s - 1)) = -2π · Im s
  simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]

/-! ## Modulus of the cpow factor -/

/-- **Cpow modulus inequality** on the lower edge: for `t > 0` and any `ε`,

      `‖(t - iε)^(s-1)‖ ≤ ‖t - iε‖^(Re s - 1) · exp(|Im s| · π/2)`.

    Same argument as the upper edge — uses `|arg(t-iε)| ≤ π/2`. -/
theorem norm_cpow_lower_edge_le (t ε : ℝ) (ht : 0 < t) (s : ℂ) :
    ‖((t : ℂ) - (ε : ℂ) * I) ^ (s - 1)‖ ≤
    ‖(t : ℂ) - (ε : ℂ) * I‖ ^ (s.re - 1) *
      Real.exp (|s.im| * Real.pi / 2) := by
  set z : ℂ := (t : ℂ) - (ε : ℂ) * I with hz_def
  have hz_ne : z ≠ 0 := lower_edge_ne_zero t ε ht
  rw [Complex.norm_cpow_of_ne_zero hz_ne]
  have h_re : (s - 1).re = s.re - 1 := by simp
  have h_im : (s - 1).im = s.im := by simp
  rw [h_re, h_im]
  rw [div_eq_mul_inv, ← Real.exp_neg]
  have h_norm_nn : 0 ≤ ‖z‖ ^ (s.re - 1) := Real.rpow_nonneg (norm_nonneg _) _
  apply mul_le_mul_of_nonneg_left _ h_norm_nn
  apply Real.exp_le_exp.mpr
  calc -(Complex.arg z * s.im)
      ≤ |Complex.arg z * s.im| := neg_le_abs _
    _ = |Complex.arg z| * |s.im| := abs_mul _ _
    _ ≤ Real.pi / 2 * |s.im| :=
        mul_le_mul_of_nonneg_right (abs_arg_lower_le t ε ht) (abs_nonneg _)
    _ = |s.im| * Real.pi / 2 := by ring

/-! ## Modulus equivalence: `‖t - iε‖ = ‖t + iε‖` -/

/-- **Modulus equivalence**: `‖t - iε‖ = ‖t + iε‖`.
    Proof via `‖z‖² = normSq z` (= `t² + ε²` in both cases) +
    nonnegativity. -/
theorem norm_lower_eq_upper (t ε : ℝ) :
    ‖(t : ℂ) - (ε : ℂ) * I‖ = ‖(t : ℂ) + (ε : ℂ) * I‖ := by
  have h_a_nn : 0 ≤ ‖(t : ℂ) - (ε : ℂ) * I‖ := norm_nonneg _
  have h_b_nn : 0 ≤ ‖(t : ℂ) + (ε : ℂ) * I‖ := norm_nonneg _
  have h_sq : ‖(t : ℂ) - (ε : ℂ) * I‖^2 = ‖(t : ℂ) + (ε : ℂ) * I‖^2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp
  -- From ‖a‖² = ‖b‖² and both ≥ 0, conclude ‖a‖ = ‖b‖.
  rw [show ‖(t : ℂ) - (ε : ℂ) * I‖ =
        Real.sqrt (‖(t : ℂ) - (ε : ℂ) * I‖^2) from (Real.sqrt_sq h_a_nn).symm,
      show ‖(t : ℂ) + (ε : ℂ) * I‖ =
        Real.sqrt (‖(t : ℂ) + (ε : ℂ) * I‖^2) from (Real.sqrt_sq h_b_nn).symm,
      h_sq]

/-! ## Combined integrand bound -/

/-- **Full lower-edge integrand bound**:

      `‖e^(2πi(s-1)) · (t - iε)^(s-1) · e^(-(t-iε))‖
       ≤ exp(-2π·Im s) · ‖t - iε‖^(Re s - 1) · exp(|Im s|·π/2) · exp(-t)`. -/
theorem norm_hankelLowerEdgeIntegrand_le (t ε : ℝ) (ht : 0 < t) (s : ℂ) :
    ‖hankelLowerEdgeIntegrand s ε t‖ ≤
    Real.exp (-(2 * Real.pi * s.im)) *
    (‖(t : ℂ) - (ε : ℂ) * I‖ ^ (s.re - 1) *
       Real.exp (|s.im| * Real.pi / 2)) *
    Real.exp (-t) := by
  unfold hankelLowerEdgeIntegrand
  rw [norm_mul, norm_mul, norm_branch_factor, norm_exp_neg_lower_edge]
  -- Goal: exp(-2π·Im s) · ‖(t - iε)^(s-1)‖ · exp(-t) ≤
  --       exp(-2π·Im s) · (‖t - iε‖^(Re s - 1) · exp(|Im s|·π/2)) · exp(-t)
  have h_branch_pos : 0 ≤ Real.exp (-(2 * Real.pi * s.im)) := Real.exp_nonneg _
  have h_exp_pos : 0 ≤ Real.exp (-t) := Real.exp_nonneg _
  have h_cpow := norm_cpow_lower_edge_le t ε ht s
  -- Apply monotonicity
  nlinarith [mul_le_mul_of_nonneg_right h_cpow h_exp_pos,
             mul_le_mul_of_nonneg_left
               (mul_le_mul_of_nonneg_right h_cpow h_exp_pos)
               h_branch_pos]

/-! ## Open: remaining DCT-step content

With the lower-edge integrand norm bound proven above, the lower-edge
DCT reduces to the same routine mathlib invocations as the upper-edge
case:

1. **Integrability** of the dominating function (same as upper edge —
   the additional constant factor `exp(-2π·Im s)` is finite).

2. **DCT application**:
   `MeasureTheory.tendsto_integral_filter_of_dominated_convergence`
   with the pointwise convergence from `HankelLowerEdgeDCT.lean` and
   the bound proven here.

3. **Limit identification**:
   ```
   ∫_0^∞ e^(2πi(s-1)) · t^(s-1) · e^(-t) dt
     = e^(2πi(s-1)) · ∫_0^∞ t^(s-1) · e^(-t) dt
     = e^(2πi(s-1)) · Γ(s).
   ```

Each step is a focused mathlib invocation. The hard analytic content
(modulus inequalities, arg bounds, branch-factor norm) is mechanized.
-/

end PrincipiaTractalis.Analytic
