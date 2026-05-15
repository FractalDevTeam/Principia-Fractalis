/-
# Hankel Contour: Integrability of the Dominating Function

The integrability piece needed to apply DCT to the upper- and
lower-edge integrals. The dominating function (from
`HankelUpperEdgeBound`, `HankelLowerEdgeBound`) takes the form

  `g(t) := M(s) · t^(Re s - 1) · e^(-t)`

where `M(s) > 0` is a constant depending on `Im s` (the exponential
factors `exp(|Im s|·π/2)` and `exp(-2π·Im s)` from the cpow and
branch bounds).

**Key result**: for `Re s > 0`, `g(t)` is integrable on `(0, ∞)`.

This follows directly from `Real.GammaIntegral_convergent`, which
gives integrability of `exp(-x) · x^(s-1)` on `Ioi 0` for real
`0 < s`. Multiplying by the constant `M(s)` preserves integrability.

This file also provides the **rpow bound for `0 < Re s < 1`**:
`‖t + iε‖^(Re s - 1) ≤ t^(Re s - 1)` (a key step in obtaining a
uniform-in-ε dominating function near the singularity at 0).

Stage L4 — Hankel-DCT integrability foundation.
-/

import PF.Analytic.HankelLowerEdgeBound
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

namespace PrincipiaTractalis.Analytic

open Complex MeasureTheory Set

/-! ## Integrability of `t ↦ t^(Re s - 1) · exp(-t)` -/

/-- **Integrability of the Γ-integrand** on `(0, ∞)` for `Re s > 0`:

      `t ↦ t^(Re s - 1) · exp(-t)`  is integrable on `Ioi 0`.

    Direct application of `Real.GammaIntegral_convergent` to the
    real number `s.re`, with order-of-multiplication adjustment. -/
theorem gammaIntegrand_real_integrable {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => t ^ (s.re - 1) * Real.exp (-t)) (Ioi 0) := by
  have h := Real.GammaIntegral_convergent hs
  -- h : IntegrableOn (fun x => Real.exp(-x) * x^(s.re - 1)) (Ioi 0)
  -- We want: IntegrableOn (fun t => t^(s.re - 1) * Real.exp(-t)) (Ioi 0)
  refine h.congr ?_
  filter_upwards with t
  ring

/-! ## Integrability of the full dominating function -/

/-- **Integrability of the constant-scaled dominating function**:

      `t ↦ C · t^(Re s - 1) · exp(-t)`  is integrable on `Ioi 0`

    for any constant `C`. Standard `Integrable.const_mul`. -/
theorem dominating_function_integrable {s : ℂ} (hs : 0 < s.re) (C : ℝ) :
    IntegrableOn (fun t : ℝ => C * (t ^ (s.re - 1) * Real.exp (-t))) (Ioi 0) :=
  (gammaIntegrand_real_integrable hs).const_mul C

/-- **Integrability of the upper-edge dominating function** with the
    full structural constant from `HankelUpperEdgeBound`:

      `t ↦ exp(|Im s|·π/2) · t^(Re s - 1) · exp(-t)`. -/
theorem upper_edge_dominating_integrable {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn
      (fun t : ℝ => Real.exp (|s.im| * Real.pi / 2) *
                     (t ^ (s.re - 1) * Real.exp (-t)))
      (Ioi 0) :=
  dominating_function_integrable hs _

/-- **Integrability of the lower-edge dominating function** with the
    full structural constant from `HankelLowerEdgeBound` (includes
    the branch factor `exp(-2π·Im s)`):

      `t ↦ exp(-2π·Im s) · exp(|Im s|·π/2) · t^(Re s - 1) · exp(-t)`. -/
theorem lower_edge_dominating_integrable {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn
      (fun t : ℝ => Real.exp (-(2 * Real.pi * s.im)) *
                    Real.exp (|s.im| * Real.pi / 2) *
                    (t ^ (s.re - 1) * Real.exp (-t)))
      (Ioi 0) :=
  dominating_function_integrable hs _

/-! ## Magnitude bound: `‖t + iε‖ ≥ t` -/

/-- **Lower bound on `‖t + iε‖`**: `‖t + iε‖ ≥ t` for `t > 0`.

    Direct from `‖t + iε‖² = t² + ε² ≥ t²` and nonnegativity. -/
theorem norm_upper_edge_ge (t ε : ℝ) (ht : 0 < t) :
    t ≤ ‖(t : ℂ) + (ε : ℂ) * I‖ := by
  have h_sq : ‖(t : ℂ) + (ε : ℂ) * I‖^2 = t^2 + ε^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp; ring
  have h_t_sq_le : t^2 ≤ ‖(t : ℂ) + (ε : ℂ) * I‖^2 := by
    rw [h_sq]; nlinarith [sq_nonneg ε]
  nlinarith [sq_nonneg (‖(t : ℂ) + (ε : ℂ) * I‖ - t),
             norm_nonneg ((t : ℂ) + (ε : ℂ) * I)]

/-- **Rpow bound for `Re s ≤ 1`**:

      `‖t + iε‖^(Re s - 1) ≤ t^(Re s - 1)`.

    Antitone behavior of `rpow` in the base for nonpositive exponent
    on positive bases. -/
theorem norm_rpow_upper_edge_le_of_re_le_one
    (t ε : ℝ) (ht : 0 < t) (s : ℂ) (hs : s.re ≤ 1) :
    ‖(t : ℂ) + (ε : ℂ) * I‖ ^ (s.re - 1) ≤ t ^ (s.re - 1) := by
  set z : ℂ := (t : ℂ) + (ε : ℂ) * I
  have h_t_le_norm : t ≤ ‖z‖ := norm_upper_edge_ge t ε ht
  have h_z_pos : 0 < ‖z‖ := lt_of_lt_of_le ht h_t_le_norm
  have h_neg_exp_nn : 0 ≤ -(s.re - 1) := by linarith
  -- Forward: t^(-(s.re-1)) ≤ ‖z‖^(-(s.re-1))
  have h_pos_exp : t ^ (-(s.re - 1)) ≤ ‖z‖ ^ (-(s.re - 1)) :=
    Real.rpow_le_rpow ht.le h_t_le_norm h_neg_exp_nn
  -- Invert: (‖z‖^(-(s.re-1)))⁻¹ ≤ (t^(-(s.re-1)))⁻¹
  have h_t_neg_pos : 0 < t ^ (-(s.re - 1)) := Real.rpow_pos_of_pos ht _
  have h_inv : (‖z‖ ^ (-(s.re - 1)))⁻¹ ≤ (t ^ (-(s.re - 1)))⁻¹ :=
    inv_anti₀ h_t_neg_pos h_pos_exp
  -- Rewrite using rpow_neg: x^(s.re - 1) = (x^(-(s.re - 1)))⁻¹
  rw [show s.re - 1 = -(-(s.re - 1)) from by ring,
      Real.rpow_neg ht.le, Real.rpow_neg (norm_nonneg _)]
  exact h_inv

/-! ## Open: lower-edge rpow bound + DCT application

The lower-edge analogue (`‖t - iε‖^(Re s - 1) ≤ t^(Re s - 1)`) follows
from `norm_lower_eq_upper` + `norm_rpow_upper_edge_le_of_re_le_one`.

The full DCT application then combines:
1. Pointwise convergence (HankelUpperEdgeDCT, HankelLowerEdgeDCT).
2. Modulus bound (HankelUpperEdgeBound, HankelLowerEdgeBound).
3. Dominating-function integrability (this file).
4. `MeasureTheory.tendsto_integral_filter_of_dominated_convergence`.

Result: the upper-edge integral → Γ(s) and lower-edge integral →
e^(2πi(s-1)) · Γ(s), both as ε → 0⁺.

The Cauchy theorem for the closed Hankel contour and the small-loop
bound-by-integration step (using HankelSmallLoop) then complete the
Γ-functional identity ∮_H t^(s-1) e^(-t) dt = 2πi/Γ(1-s).
-/

end PrincipiaTractalis.Analytic
