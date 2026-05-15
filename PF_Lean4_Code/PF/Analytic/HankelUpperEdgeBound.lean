/-
# Hankel Contour: Upper-Edge Integrand Modulus Bound

The integrand-bound piece of the upper-edge DCT: for `t > 0` and any
`ε ∈ ℝ`,

  `‖(t + iε)^(s-1) · e^(-(t+iε))‖ ≤
     ‖t + iε‖^(Re s - 1) · exp(|Im s|·π/2) · exp(-t)`.

This uses three exact facts (all axiom-clean):
1. `‖exp(-(t + iε))‖ = exp(-t)` — modulus of exp depends only on Re.
2. `|arg(t + iε)| ≤ π/2` — since `Re(t + iε) = t > 0`.
3. `‖z^w‖ ≤ ‖z‖^(Re w) · exp(|Im w|·π/2)` for `z = t + iε`, `w = s - 1`,
   via `Complex.norm_cpow_of_ne_zero` + the argument bound.

This file:
* Proves the modulus of the exp factor (axiom-clean).
* Proves the argument bound (axiom-clean).
* Proves `(t + iε) ≠ 0` for `t > 0` (axiom-clean).
* Proves the **cpow modulus inequality** for `(t + iε)^(s-1)` (axiom-clean).
* Proves the **full integrand modulus bound** (axiom-clean).

This completes the bound piece of the upper-edge DCT, reducing the
remaining work to: (a) integrability of `‖z‖^(Re s - 1) · exp(-t)` on
`(0, ∞)` for `Re s > 0`, and (b) the DCT-application invocation.

Stage L4 — Upper-edge integrand modulus bound (analytic content).
-/

import PF.Analytic.HankelLowerEdgeDCT
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

namespace PrincipiaTractalis.Analytic

open Complex

/-! ## Basic facts about `z := t + iε` -/

/-- **z is nonzero for t > 0**: `Re(t + iε) = t > 0` excludes 0. -/
theorem upper_edge_ne_zero (t ε : ℝ) (ht : 0 < t) :
    (t : ℂ) + (ε : ℂ) * I ≠ 0 := by
  intro h
  have h_re : ((t : ℂ) + (ε : ℂ) * I).re = (0 : ℂ).re := by rw [h]
  simp at h_re
  linarith

/-- **Real part is t**: `Re(t + iε) = t`. -/
theorem upper_edge_re (t ε : ℝ) :
    ((t : ℂ) + (ε : ℂ) * I).re = t := by simp

/-- **Argument bound**: `|arg(t + iε)| ≤ π/2` for `t > 0`. -/
theorem abs_arg_upper_le (t ε : ℝ) (ht : 0 < t) :
    |Complex.arg ((t : ℂ) + (ε : ℂ) * I)| ≤ Real.pi / 2 := by
  rw [Complex.abs_arg_le_pi_div_two_iff]
  rw [upper_edge_re]
  exact ht.le

/-! ## Modulus of the exp factor -/

/-- **Norm of `exp(-(t + iε))` equals `Real.exp(-t)`**.

    Direct consequence of `Complex.norm_exp` (modulus of exp depends
    only on the real part) and `Re(-(t + iε)) = -t`. -/
theorem norm_exp_neg_upper_edge (t ε : ℝ) :
    ‖Complex.exp (-((t : ℂ) + (ε : ℂ) * I))‖ = Real.exp (-t) := by
  rw [Complex.norm_exp]
  congr 1
  simp

/-! ## Modulus of the cpow factor -/

/-- **Cpow modulus inequality**: for `t > 0` and any `ε`,

      `‖(t + iε)^(s-1)‖ ≤ ‖t + iε‖^(Re s - 1) · exp(|Im s| · π/2)`.

    Derivation: from `Complex.norm_cpow_of_ne_zero`,
    `‖z^w‖ = ‖z‖^(Re w) · exp(-arg z · Im w)`. The bound
    `−arg z · Im w ≤ |Im w| · π/2` follows from `|arg z| ≤ π/2`
    (from `Re z > 0`) and `−x ≤ |x|`. -/
theorem norm_cpow_upper_edge_le (t ε : ℝ) (ht : 0 < t) (s : ℂ) :
    ‖((t : ℂ) + (ε : ℂ) * I) ^ (s - 1)‖ ≤
    ‖(t : ℂ) + (ε : ℂ) * I‖ ^ (s.re - 1) *
      Real.exp (|s.im| * Real.pi / 2) := by
  set z : ℂ := (t : ℂ) + (ε : ℂ) * I with hz_def
  have hz_ne : z ≠ 0 := upper_edge_ne_zero t ε ht
  rw [Complex.norm_cpow_of_ne_zero hz_ne]
  -- (s-1).re = s.re - 1; (s-1).im = s.im
  have h_re : (s - 1).re = s.re - 1 := by simp
  have h_im : (s - 1).im = s.im := by simp
  rw [h_re, h_im]
  -- Goal: ‖z‖^(s.re - 1) / exp(arg z · s.im) ≤ ‖z‖^(s.re - 1) · exp(|s.im| · π/2)
  rw [div_eq_mul_inv, ← Real.exp_neg]
  -- Goal: ‖z‖^(s.re - 1) · exp(-(arg z · s.im)) ≤ ‖z‖^(s.re - 1) · exp(|s.im| · π/2)
  have h_norm_nn : 0 ≤ ‖z‖ ^ (s.re - 1) := Real.rpow_nonneg (norm_nonneg _) _
  apply mul_le_mul_of_nonneg_left _ h_norm_nn
  apply Real.exp_le_exp.mpr
  -- Show: -(arg z · s.im) ≤ |s.im| · π/2
  calc -(Complex.arg z * s.im)
      ≤ |Complex.arg z * s.im| := neg_le_abs _
    _ = |Complex.arg z| * |s.im| := abs_mul _ _
    _ ≤ Real.pi / 2 * |s.im| :=
        mul_le_mul_of_nonneg_right (abs_arg_upper_le t ε ht) (abs_nonneg _)
    _ = |s.im| * Real.pi / 2 := by ring

/-! ## Combined integrand bound -/

/-- **Full upper-edge integrand bound**:

      `‖(t + iε)^(s-1) · e^(-(t+iε))‖ ≤
         ‖t + iε‖^(Re s - 1) · exp(|Im s| · π/2) · exp(-t)`.

    Direct combination of `norm_cpow_upper_edge_le` and
    `norm_exp_neg_upper_edge` via the multiplicativity of norms. -/
theorem norm_hankelUpperEdgeIntegrand_le (t ε : ℝ) (ht : 0 < t) (s : ℂ) :
    ‖hankelUpperEdgeIntegrand s ε t‖ ≤
    ‖(t : ℂ) + (ε : ℂ) * I‖ ^ (s.re - 1) *
      Real.exp (|s.im| * Real.pi / 2) * Real.exp (-t) := by
  unfold hankelUpperEdgeIntegrand
  rw [norm_mul, norm_exp_neg_upper_edge]
  -- Goal: ‖z^(s-1)‖ · exp(-t) ≤ ‖z‖^(s.re - 1) · exp(|s.im|·π/2) · exp(-t)
  apply mul_le_mul_of_nonneg_right (norm_cpow_upper_edge_le t ε ht s) (Real.exp_nonneg _)

/-! ## Variant bound: uniform in `ε ∈ [-1, 1]` -/

/-- **Magnitude bound for ε ∈ [-1, 1]**: `‖t + iε‖² ≤ t² + 1`. -/
theorem norm_sq_upper_edge_le (t ε : ℝ) (hε : |ε| ≤ 1) :
    ‖(t : ℂ) + (ε : ℂ) * I‖^2 ≤ t^2 + 1 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  -- normSq z = z.re * z.re + z.im * z.im
  -- For z = t + iε: re = t, im = ε
  simp
  have hε_sq : ε^2 ≤ 1 := by
    have h_abs : |ε|^2 ≤ 1^2 :=
      pow_le_pow_left₀ (abs_nonneg ε) hε 2
    rw [sq_abs] at h_abs
    linarith
  nlinarith [sq_nonneg t, sq_nonneg ε]

/-- **ε-uniform bound on the norm factor for Re s ≥ 1**: when
    `1 ≤ Re s`, the rpow `‖t + iε‖^(Re s - 1)` is bounded by
    `(t² + 1)^((Re s - 1)/2)` for `|ε| ≤ 1`.

    Proof: `‖z‖^(Re s - 1) = (‖z‖²)^((Re s - 1)/2) ≤ (t² + 1)^((Re s - 1)/2)`
    by monotonicity of `rpow` on nonneg base with nonneg exponent. -/
theorem norm_rpow_upper_edge_le_of_re_ge_one
    (t ε : ℝ) (_ht : 0 < t) (hε : |ε| ≤ 1) (s : ℂ) (hs : 1 ≤ s.re) :
    ‖(t : ℂ) + (ε : ℂ) * I‖ ^ (s.re - 1) ≤
    (t^2 + 1) ^ ((s.re - 1) / 2) := by
  set z : ℂ := (t : ℂ) + (ε : ℂ) * I
  have h_z_nn : 0 ≤ ‖z‖ := norm_nonneg _
  have h_sq_nn : 0 ≤ ‖z‖^2 := sq_nonneg _
  have h_sq_le : ‖z‖^2 ≤ t^2 + 1 := norm_sq_upper_edge_le t ε hε
  have h_exp_nn : 0 ≤ (s.re - 1) / 2 := by linarith
  -- Express ‖z‖^(s.re - 1) = (‖z‖^2)^((s.re - 1)/2) via rpow identities.
  have h_key : ‖z‖ ^ (s.re - 1) = (‖z‖^2) ^ ((s.re - 1) / 2) := by
    rw [show ‖z‖^2 = ‖z‖ ^ (2 : ℝ) from by
          rw [show ((2 : ℝ) : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
              Real.rpow_natCast]]
    rw [← Real.rpow_mul h_z_nn]
    congr 1; ring
  rw [h_key]
  exact Real.rpow_le_rpow h_sq_nn h_sq_le h_exp_nn

/-! ## Open: remaining DCT-step content

With the integrand norm bound proven above, the upper-edge DCT
reduces to:

1. **Integrability** of the dominating function
   `g(t) := M(s) · ‖t + iε‖^(Re s - 1) · exp(-t)` on `(0, ∞)`.
   - For `Re s ≥ 1`: `‖t + iε‖^(Re s - 1) ≤ (t² + 1)^((Re s - 1)/2)` (proven
     above for `|ε| ≤ 1`), and this is bounded by `(t + 1)^(Re s - 1)`,
     which is `o(e^(t/2))` so `e^(-t)` × dominates is integrable.
   - For `0 < Re s < 1`: `‖t + iε‖ ≥ t`, so `‖t + iε‖^(Re s - 1) ≤ t^(Re s - 1)`,
     and `∫_0^∞ t^(Re s - 1) e^(-t) dt = Γ(Re s) < ∞`.

2. **DCT application**:
   `MeasureTheory.tendsto_integral_filter_of_dominated_convergence`
   with the pointwise convergence from `HankelUpperEdgeDCT.lean` and
   the bound proven above.

3. **Limit identification** via `Complex.Gamma_eq_integral`.

Each step is a focused mathlib invocation. The hard analytic content
(the modulus bound) is now mechanized axiom-clean.
-/

end PrincipiaTractalis.Analytic
