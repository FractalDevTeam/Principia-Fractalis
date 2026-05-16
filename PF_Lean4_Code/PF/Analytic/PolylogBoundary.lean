/-
# Polylog `Li₁` on the Boundary of the Unit Disk — Principal-Branch Closed Form

The conjectured eigenvalue formula `λ_k = (1/aᵏ) · Re[Li₁(e^{iπαᵏ})]`
(Problem 1 of `OPEN_PROBLEMS.md`) evaluates the polylogarithm at points
on the unit circle (`|z| = 1`). The `polyLog 1` series

  `Li₁(z) = Σ_{n≥1} zⁿ / n`

converges only inside the open unit disk (`|z| < 1`); on the boundary
it requires analytic continuation. Mathlib's `polyLog 1 z` equals
`−Complex.log (1 − z)` for `|z| < 1` (theorem `polyLog_one` in
`PF/Analytic/Polylog.lean`); the natural extension to `|z| = 1, z ≠ 1`
is the same formula evaluated on the principal branch of `log`.

## What this file delivers

1. **Definition** `polyLog_one_principal z := −Complex.log (1 − z)` —
   the principal-branch extension to the closed unit disk (minus
   `z = 1`).

2. **Norm formula on the unit circle**:
   `‖1 − exp(I·t)‖ = 2 · |sin(t/2)|`  for real `t`.

3. **Closed form for the real part on the unit circle**:
   `Re[polyLog_one_principal (exp(I·t))] = −log(2 · |sin(t/2)|)`
   when `sin(t/2) ≠ 0`.

4. **Specialization** to `t = π · α^k` — the manuscript's specific
   argument:
   `Re[polyLog_one_principal (exp(I·π·αᵏ))] = −log(2 · |sin(π·αᵏ/2)|)`.

5. **Numerical sanity check** at `α = √2, k = 0` confirming the
   principal-branch evaluation `≈ −0.468` matches the literature
   value (NEGATIVE — the manuscript's positive `π/(10√2)` requires a
   different Riemann sheet; see `OPEN_PROBLEMS.md` Problem 2's
   branch-selection Heuristic).

All theorems below are zero-project-axiom.

## What this file does NOT deliver

The Riemann-sheet selection that the manuscript posits (Heuristic
`heur:branch-selection`) is NOT formalized — that's exactly the
content of OPEN_PROBLEMS.md Problem 2. The principal-branch
evaluation here gives the *baseline* against which any branch-selection
rule must be measured.

Stage L4+ — `Li₁` boundary closed form (toward Problem 1 / 2).
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import PF.Analytic.Polylog

namespace PrincipiaTractalis.Analytic

open Real Complex

/-! ## Principal-branch extension of `Li₁` -/

/-- **`Li₁(z)` extended to the closed unit disk (minus `z = 1`) via the
    principal branch of `log`**: `polyLog_one_principal z := −log(1 − z)`.

    On the open unit disk (`‖z‖ < 1`), this agrees with `polyLog 1 z`
    (mathlib's `polyLog_one` theorem, proven in
    `PF/Analytic/Polylog.lean`). At the boundary `|z| = 1, z ≠ 1`,
    this is the canonical principal-branch extension. -/
noncomputable def polyLog_one_principal (z : ℂ) : ℂ :=
  -Complex.log (1 - z)

/-- Agreement with `polyLog 1 z` inside the open unit disk. -/
theorem polyLog_one_principal_eq_polyLog_one (z : ℂ) (hz : ‖z‖ < 1) :
    polyLog_one_principal z = polyLog 1 z := by
  unfold polyLog_one_principal
  rw [polyLog_one z hz]

/-! ## Norm on the unit circle -/

/-- **Norm of `1 − exp(I·t)` on the unit circle**:

      `‖1 − exp(I·t)‖² = 4 · sin²(t/2)`  for real `t`.

    Proof outline: `exp(I·t) = cos(t) + i·sin(t)`, so
    `1 − exp(I·t) = (1 − cos(t)) − i·sin(t)`, giving
    `‖1 − exp(I·t)‖² = (1 − cos(t))² + sin²(t) = 2 − 2·cos(t)
                     = 4·sin²(t/2)`  (half-angle identity). -/
theorem norm_sq_one_sub_exp_I_t (t : ℝ) :
    ‖(1 - Complex.exp (Complex.I * t) : ℂ)‖^2 = 4 * Real.sin (t/2)^2 := by
  have hexp : Complex.exp (Complex.I * t) =
      Complex.cos t + Complex.sin t * Complex.I := by
    rw [show Complex.I * (t : ℂ) = (t : ℂ) * Complex.I from by ring]
    exact Complex.exp_mul_I _
  have hcos_r : Complex.cos (t : ℂ) = (Real.cos t : ℂ) :=
    Complex.ofReal_cos t |>.symm
  have hsin_r : Complex.sin (t : ℂ) = (Real.sin t : ℂ) :=
    Complex.ofReal_sin t |>.symm
  rw [hexp, hcos_r, hsin_r]
  have h_sub : (1 - ((Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I) : ℂ) =
              ((1 - Real.cos t : ℝ) : ℂ) + ((-Real.sin t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h_sub, Complex.norm_add_mul_I]
  rw [Real.sq_sqrt
        (by positivity : (0 : ℝ) ≤ (1 - Real.cos t)^2 + (-Real.sin t)^2)]
  have hsq : (1 - Real.cos t)^2 + (-Real.sin t)^2 = 2 - 2 * Real.cos t := by
    have := Real.sin_sq_add_cos_sq t; nlinarith
  rw [hsq]
  have h := Real.cos_two_mul (t/2)
  have hpys : Real.sin (t/2)^2 + Real.cos (t/2)^2 = 1 :=
    Real.sin_sq_add_cos_sq (t/2)
  have h2t : Real.cos (2 * (t/2)) = Real.cos t := by
    rw [show 2 * (t/2) = t from by ring]
  have hcos_t : Real.cos t = 1 - 2 * Real.sin (t/2)^2 := by linarith
  linarith

/-- **`‖1 − exp(I·t)‖ = 2 · |sin(t/2)|`** (extracting the square root
    from `norm_sq_one_sub_exp_I_t`). -/
theorem norm_one_sub_exp_I_t (t : ℝ) :
    ‖(1 - Complex.exp (Complex.I * t) : ℂ)‖ = 2 * |Real.sin (t/2)| := by
  have h_sq := norm_sq_one_sub_exp_I_t t
  have h_norm_nn : 0 ≤ ‖(1 - Complex.exp (Complex.I * t) : ℂ)‖ := norm_nonneg _
  have h_rhs_nn : 0 ≤ 2 * |Real.sin (t/2)| := by positivity
  have h_sq_eq :
      ‖(1 - Complex.exp (Complex.I * t) : ℂ)‖^2 = (2 * |Real.sin (t/2)|)^2 := by
    rw [h_sq]; rw [mul_pow]; rw [sq_abs]; ring
  nlinarith [sq_nonneg (‖(1 - Complex.exp (Complex.I * t) : ℂ)‖ - 2 * |Real.sin (t/2)|),
             sq_nonneg (‖(1 - Complex.exp (Complex.I * t) : ℂ)‖ + 2 * |Real.sin (t/2)|),
             h_sq_eq, h_norm_nn, h_rhs_nn]

/-! ## Closed form for `Re[polyLog_one_principal(exp(I·t))]` -/

/-- **Closed form for the real part**: when `sin(t/2) ≠ 0` (i.e., `t`
    is not an even multiple of `π`), the principal-branch polylog
    evaluation at `exp(I·t)` has real part

      `Re[−log(1 − exp(I·t))] = −log(2 · |sin(t/2)|)`.

    Proof: `Re[log w] = log ‖w‖` for the principal-branch log when
    `w ≠ 0`; apply with `w = 1 − exp(I·t)`, whose norm is
    `2 · |sin(t/2)|` from `norm_one_sub_exp_I_t`. -/
theorem re_polyLog_one_principal_exp_I_t
    (t : ℝ) (ht : Real.sin (t/2) ≠ 0) :
    (polyLog_one_principal (Complex.exp (Complex.I * t))).re =
    -Real.log (2 * |Real.sin (t/2)|) := by
  unfold polyLog_one_principal
  -- (−log w).re = −(log w).re = −log ‖w‖
  rw [Complex.neg_re]
  -- ‖1 - exp(I·t)‖ ≠ 0  since sin(t/2) ≠ 0
  have h_norm_ne : ‖(1 - Complex.exp (Complex.I * t) : ℂ)‖ ≠ 0 := by
    rw [norm_one_sub_exp_I_t t]
    have : |Real.sin (t/2)| ≠ 0 := abs_ne_zero.mpr ht
    positivity
  have h_ne_zero : (1 - Complex.exp (Complex.I * t) : ℂ) ≠ 0 := by
    intro h; apply h_norm_ne; rw [h, norm_zero]
  rw [Complex.log_re]
  rw [norm_one_sub_exp_I_t t]

/-! ## Specialization to the manuscript's argument `t = π · α^k` -/

/-- **Specialization to `t = π · αᵏ`** (the manuscript's specific argument):

      `Re[polyLog_one_principal(exp(I·π·αᵏ))] = −log(2 · |sin(π·αᵏ/2)|)`

    whenever `sin(π·αᵏ/2) ≠ 0` (equivalently, `αᵏ` is not an even
    integer). -/
theorem re_polyLog_one_principal_exp_I_pi_alpha_pow
    (α : ℝ) (k : ℕ) (hα : Real.sin (Real.pi * α^k / 2) ≠ 0) :
    (polyLog_one_principal
      (Complex.exp (Complex.I * (Real.pi * α^k : ℝ)))).re =
    -Real.log (2 * |Real.sin (Real.pi * α^k / 2)|) := by
  exact re_polyLog_one_principal_exp_I_t (Real.pi * α^k) hα

/-! ## Documentation: principal-branch vs the manuscript's physical branch

For `α = √2, k = 0`, the principal-branch evaluation gives:

  `Re[polyLog_one_principal(exp(I·π·√2))] = −log(2 · sin(π·√2/2))`

Numerically: `π·√2/2 ≈ 2.221`, `sin(2.221) ≈ 0.7986`,
`2 · 0.7986 ≈ 1.597`, `log(1.597) ≈ 0.468`. So the principal-branch
real part is **approximately −0.468**.

The manuscript's claim is that the corresponding eigenvalue is
`π/(10√2) ≈ +0.2221441469` (POSITIVE). The principal branch
gives the *wrong sign and magnitude*. This is exactly the content of
Heuristic `heur:branch-selection`: the manuscript posits that the
operator's monodromy selects a *different* Riemann sheet of the
polylog, on which the same series-extended value is positive and
equals `π/(10√2)`.

What this file proves rigorously:
* The principal-branch closed form is `−log(2·|sin(t/2)|)`.
* This is the BASELINE against which any branch-selection rule must be
  measured.

What this file does NOT prove:
* The existence or characterization of a Riemann sheet on which the
  same series-extended value equals `π/(10√2)` for `α = √2, k = 0`.
* That such a sheet, if it exists, is the one selected by the
  operator's monodromy.

Both are part of `OPEN_PROBLEMS.md` Problem 1 + Problem 2 — original
mathematical research, multi-month at minimum. -/

end PrincipiaTractalis.Analytic
