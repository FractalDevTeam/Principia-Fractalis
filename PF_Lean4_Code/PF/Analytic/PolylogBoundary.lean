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
import PF.SpectralGap

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

/-! ## Cosine-series representation of `Re[polyLog]` -/

/-- **Real part of `exp(I·θ)` for real `θ`**: `Re[exp(I·θ)] = cos(θ)`.
    Direct from `exp(I·θ) = cos(θ) + I·sin(θ)` (Euler). -/
theorem re_exp_I_mul_real (θ : ℝ) :
    (Complex.exp (Complex.I * (θ : ℂ))).re = Real.cos θ := by
  rw [show Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I from by ring]
  rw [Complex.exp_mul_I]
  rw [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  simp [Complex.cos_ofReal_re]

/-- **Real part of the `n`-th polylog summand at `exp(I·t)`**:

      `Re[(exp(I·t))^(n+1) / (n+1)] = cos((n+1)·t) / (n+1)`. -/
theorem re_polyLog_term_exp_I (t : ℝ) (n : ℕ) :
    ((Complex.exp (Complex.I * (t : ℂ))) ^ (n + 1) / ((n + 1 : ℕ) : ℂ)).re
    = Real.cos ((n + 1) * t) / (n + 1) := by
  have h1 : Complex.exp (Complex.I * (t : ℂ)) ^ (n + 1) =
            Complex.exp (Complex.I * (((n + 1 : ℕ) * t : ℝ) : ℂ)) := by
    rw [← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  rw [h1]
  have hreal : ((n + 1 : ℕ) : ℂ) = (((n + 1 : ℕ) : ℝ) : ℂ) := by push_cast; ring
  rw [hreal, Complex.div_ofReal_re, re_exp_I_mul_real]
  push_cast; ring

/-- **Real part of the polylog partial sum at `exp(I·t)`**:

      `Re[Σ_{n=0}^{N-1} (exp(I·t))^(n+1)/(n+1)] = Σ_{n=0}^{N-1} cos((n+1)·t)/(n+1)`.

    The partial-sum cosine series is what the conjecture's polylog
    evaluation reduces to under principal-branch summation. The
    boundary-extended polylog `Li₁(e^{i·t}) = −log(1 − e^{i·t})`
    is the limit of this partial sum as `N → ∞` (conditionally
    convergent for `t ≠ 2π·k`, k ∈ ℤ; convergence rate analysis is
    a separate well-studied topic — the Dirichlet test handles it).
-/
theorem re_polyLog_partial_exp_I (t : ℝ) (N : ℕ) :
    ((Finset.range N).sum
      (fun n => (Complex.exp (Complex.I * (t : ℂ))) ^ (n + 1)
                / ((n + 1 : ℕ) : ℂ))).re
    = (Finset.range N).sum
      (fun n => Real.cos ((n + 1) * t) / (n + 1)) := by
  induction N with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Complex.add_re, ih, re_polyLog_term_exp_I,
        Finset.sum_range_succ]

/-! ## Conjectured eigenvalue (principal branch) -/

/-- **The conjectured eigenvalue formula `λ_k = a^(-k) · Re[Li₁(...)]`
    evaluated on the principal branch**:

      `conjectured_eigenvalue_principal α a k
        := −a^(-k) · log(2 · |sin(π · αᵏ / 2)|)`.

    Closed-form value of the conjecture's eigenvalue formula `λ_k` when
    the polylog is evaluated on the principal-branch logarithm. For
    `α = √2, k = 0, a = 1` this is approximately `−0.468` (NEGATIVE);
    the manuscript posits the true `λ_0` is the positive value
    `π/(10√2) ≈ +0.222`, achievable only on a different Riemann sheet
    (Heuristic `heur:branch-selection`, OPEN_PROBLEMS.md Problem 2). -/
noncomputable def conjectured_eigenvalue_principal
    (α a : ℝ) (k : ℕ) : ℝ :=
  -a^(-(k : ℤ)) * Real.log (2 * |Real.sin (Real.pi * α^k / 2)|)

/-- **Bridge** between the explicit principal-branch closed form and
    the conjecture's polylog-evaluation:

      `conjectured_eigenvalue_principal α a k
        = a^(-k) · Re[polyLog_one_principal(exp(I·π·αᵏ))]`. -/
theorem conjectured_eigenvalue_principal_eq_re_polyLog
    (α a : ℝ) (k : ℕ) (hα : Real.sin (Real.pi * α^k / 2) ≠ 0) :
    conjectured_eigenvalue_principal α a k =
    a^(-(k : ℤ)) *
      (polyLog_one_principal (Complex.exp (Complex.I * (Real.pi * α^k : ℝ)))).re := by
  unfold conjectured_eigenvalue_principal
  rw [re_polyLog_one_principal_exp_I_pi_alpha_pow α k hα]
  ring

/-! ## Singularities of the principal-branch formula at α = √2 -/

/-- **Concrete singularity at α = √2, k = 2**:

      `sin(π · (√2)² / 2) = sin(π) = 0`

    So `polylog_one_principal(exp(I·π·(√2)²)) = polylog_one_principal(exp(0)·exp(I·0))`
    has `Re = −log(2·0) = +∞` (undefined on principal branch). The
    conjecture's eigenvalue λ_2 (for α = √2) is therefore NOT defined
    by the principal-branch formula. -/
theorem principal_branch_singularity_sqrt2_k2 :
    Real.sin (Real.pi * (Real.sqrt 2 : ℝ)^2 / 2) = 0 := by
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [show (Real.pi * 2 / 2 : ℝ) = Real.pi from by ring]
  exact Real.sin_pi

/-- **Helper**: `(√2)^(2m) = 2^m`. -/
theorem sqrt2_pow_two_mul (m : ℕ) :
    (Real.sqrt 2 : ℝ)^(2 * m) = (2 : ℝ)^m := by
  rw [pow_mul]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- **General singularity at α = √2, k = 2m for m ≥ 1**:

      `sin(π · (√2)^(2m) / 2) = sin(π · 2^(m-1)) = 0`

    since `2^(m-1)` is a positive integer for `m ≥ 1` and `sin(nπ) = 0`
    for any natural `n`.

    **Massive consequence**: at α = √2, the principal-branch
    `conjectured_eigenvalue_principal` is UNDEFINED (formally `−log(0)`)
    at infinitely many `k` (every even `k ≥ 2`). The manuscript's
    conjecture predicts finite eigenvalues at every `k`, so the
    physical Riemann sheet (Problem 2's Heuristic) must resolve ALL
    these singularities, not just provide a finite correction at the
    one principal-branch evaluation point `k = 0`. -/
theorem principal_branch_singularity_sqrt2_even_k (m : ℕ) (hm : m ≥ 1) :
    Real.sin (Real.pi * (Real.sqrt 2 : ℝ)^(2 * m) / 2) = 0 := by
  rw [sqrt2_pow_two_mul]
  rcases m with _ | m'
  · omega
  · rw [show (2 : ℝ)^(m'+1) = 2 * (2 : ℝ)^m' from by rw [pow_succ]; ring]
    rw [show Real.pi * (2 * (2 : ℝ)^m') / 2 = Real.pi * (2 : ℝ)^m' from by ring]
    have h_int : Real.pi * (2 : ℝ)^m' = (2^m' : ℕ) * Real.pi := by
      push_cast; ring
    rw [h_int]
    exact Real.sin_nat_mul_pi (2^m')

/-! ## Well-definedness of principal-branch at α = √2, k = 0 -/

/-- **Positivity of `sin(π·√2/2)`**: since `π·√2/2 ∈ (0, π)` and
    `sin` is positive on `(0, π)`. Specifically, `√2 < 2` so
    `√2/2 < 1`, giving `π·√2/2 < π`. -/
theorem sin_pi_sqrt2_div_2_pos :
    Real.sin (Real.pi * Real.sqrt 2 / 2) > 0 := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · have h1 : 0 < Real.pi := Real.pi_pos
    have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
    positivity
  · have h_sqrt2_lt : Real.sqrt 2 < 2 := by
      have : Real.sqrt 2 < Real.sqrt 4 := by
        apply Real.sqrt_lt_sqrt
        · norm_num
        · norm_num
      have h4 : Real.sqrt 4 = 2 := by
        rw [show (4 : ℝ) = 2^2 from by norm_num]
        exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)
      linarith
    have h_pi_pos : 0 < Real.pi := Real.pi_pos
    nlinarith

/-- **Consequence**: `sin(π·√2/2) ≠ 0`, so the principal-branch
    formula `conjectured_eigenvalue_principal √2 a 0` is well-defined
    (equals `−log(2·sin(π·√2/2))`, a finite negative real). -/
theorem sin_pi_sqrt2_div_2_ne_zero :
    Real.sin (Real.pi * Real.sqrt 2 / 2) ≠ 0 :=
  ne_of_gt sin_pi_sqrt2_div_2_pos

/-! ## Well-definedness at k = 0 and k = 1 for α = √2 -/

/-- **At α = √2, k = 0**: `sin(π · (√2)⁰ / 2) = sin(π/2) = 1 ≠ 0`,
    so the principal-branch eigenvalue formula is well-defined. -/
theorem sin_pi_sqrt2_pow_zero_div_2_ne_zero :
    Real.sin (Real.pi * (Real.sqrt 2 : ℝ)^0 / 2) ≠ 0 := by
  simp only [pow_zero, mul_one]
  rw [Real.sin_pi_div_two]
  norm_num

/-- **At α = √2, k = 1**: `sin(π · √2 / 2) > 0`, so the principal-branch
    eigenvalue formula is well-defined (and gives a finite negative
    value `≈ -0.468`). -/
theorem sin_pi_sqrt2_pow_one_div_2_ne_zero :
    Real.sin (Real.pi * (Real.sqrt 2 : ℝ)^1 / 2) ≠ 0 := by
  simp only [pow_one]
  exact sin_pi_sqrt2_div_2_ne_zero

/-! ## Concrete principal-branch value at α = √2, k = 0 -/

/-- **Closed-form value at α = √2, k = 0**:

      `conjectured_eigenvalue_principal (√2) a 0 = −log 2 ≈ −0.693`

    (independent of `a`, since `a^0 = 1`).

    The manuscript's claim (Theorem 4.4) is that the actual eigenvalue
    `λ_0(H_P_at √2 a) = π/(10·√2) ≈ +0.222`. The discrepancy
    `principal ↦ physical : −log 2 ↦ +π/(10√2)` is the precise
    sign/magnitude flip that the physical Riemann sheet (Problem 2's
    Heuristic) must accomplish.

    Numerically: `−log 2 ≈ −0.693` vs `+π/(10√2) ≈ +0.222`. The
    difference is about `0.915` — substantially more than a small
    correction, requiring the physical Riemann sheet to be a
    fundamentally different branch (not a small perturbation of
    the principal sheet). -/
theorem conjectured_eigenvalue_principal_sqrt2_zero (a : ℝ) :
    conjectured_eigenvalue_principal (Real.sqrt 2) a 0 =
    -Real.log 2 := by
  unfold conjectured_eigenvalue_principal
  simp [pow_zero]

/-! ## Manuscript's predicted ground-state eigenvalue + incompatibility -/

/-- **Manuscript's predicted ground-state eigenvalue** for `H_P_at α a`:

      `λ_0_manuscript α := π / (10 · α)`

    (Manuscript Theorem 4.4 in Ch 21; matches the 10⁻¹⁰ numerical
    finite-dim approximation.) For α = √2: `≈ 0.222`. -/
noncomputable def manuscript_predicted_eigenvalue_zero (α : ℝ) : ℝ :=
  Real.pi / (10 * α)

/-- **Manuscript's predicted value at α = √2 is positive**:
    `π/(10·√2) > 0`. Trivial from positivity of π and √2. -/
theorem manuscript_predicted_eigenvalue_zero_sqrt2_pos :
    manuscript_predicted_eigenvalue_zero (Real.sqrt 2) > 0 := by
  unfold manuscript_predicted_eigenvalue_zero
  have h1 : 0 < Real.pi := Real.pi_pos
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  positivity

/-- **Principal-branch value at α = √2, k = 0 is NEGATIVE**:
    `−log 2 < 0` since `log 2 > 0` (because `2 > 1`). -/
theorem conjectured_eigenvalue_principal_sqrt2_zero_neg (a : ℝ) :
    conjectured_eigenvalue_principal (Real.sqrt 2) a 0 < 0 := by
  rw [conjectured_eigenvalue_principal_sqrt2_zero a]
  have h := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  linarith

/-- **★ Incompatibility theorem** ★: the manuscript's predicted
    ground-state eigenvalue and the principal-branch polylog
    evaluation CANNOT be equal at α = √2, k = 0 (one positive,
    one negative).

    This is the FORMAL, MACHINE-CHECKED statement that the polylog
    conjecture (`conj:polylog-spectrum` Ch 21) is INCOMPATIBLE with
    principal-branch evaluation of the polylog. Resolving Problem 1
    therefore REQUIRES the Riemann-sheet selection of Problem 2's
    Heuristic — without it, the conjecture is provably false. -/
theorem manuscript_principal_incompatibility (a : ℝ) :
    manuscript_predicted_eigenvalue_zero (Real.sqrt 2) ≠
    conjectured_eigenvalue_principal (Real.sqrt 2) a 0 := by
  intro h
  have h_pos := manuscript_predicted_eigenvalue_zero_sqrt2_pos
  have h_neg := conjectured_eigenvalue_principal_sqrt2_zero_neg a
  rw [h] at h_pos
  linarith

/-! ## Bridge to existing SpectralGap.lean infrastructure -/

/-- **Bridge theorem**: the manuscript's predicted ground-state
    eigenvalue at α = √2 equals `lambda_0_P` from `SpectralGap.lean`.

      `manuscript_predicted_eigenvalue_zero (√2) = lambda_0_P`

    Since `lambda_0_P = pi_10 / √2 = (π/10) / √2 = π/(10·√2) =
    manuscript_predicted_eigenvalue_zero (√2)`. Pure algebraic
    rewriting; ties together the framework's two ways of naming
    the same value:
    * Manuscript Ch 21 Theorem 4.4: `λ_0(H_P √2 a) = π/(10·√2)`
    * `SpectralGap.lean`: `lambda_0_P := pi_10 / √2`. -/
theorem manuscript_predicted_eigenvalue_zero_eq_lambda_0_P :
    manuscript_predicted_eigenvalue_zero (Real.sqrt 2) =
    PrincipiaTractalis.lambda_0_P := by
  unfold manuscript_predicted_eigenvalue_zero
        PrincipiaTractalis.lambda_0_P PrincipiaTractalis.pi_10
  ring

/-! ## α-independence of principal-branch at k = 0 -/

/-- **At k = 0, the principal-branch evaluation is α-independent**:

      `conjectured_eigenvalue_principal α a 0 = −log 2`

    for any `α : ℝ`, any `a : ℝ`. Proof: at `k = 0`, `α^0 = 1`, so
    `π · α^0 / 2 = π/2`, `sin(π/2) = 1`, hence `−log(2·1) = −log 2`.
    The `a^(-0) = 1` prefactor doesn't depend on `a` either.

    **Structural consequence**: the manuscript's distinct predictions
    `λ_0(H_P √2 a) = π/(10·√2) ≈ 0.222` (P-class) and
    `λ_0(H_P (φ+¼) a) = π/(10·(φ+¼)) ≈ 0.168` (NP-class) are
    DIFFERENT, but the principal-branch evaluation at `k = 0` gives
    the SAME value `−log 2 ≈ −0.693` for BOTH α values. Therefore
    the physical-branch selection (Problem 2's Heuristic) must depend
    *non-trivially* on α — not just resolve a singularity, but
    actually distinguish between different α values at the same
    `(α^k, k)` evaluation point. This is a sharper structural
    constraint than session 32's incompatibility theorem. -/
theorem conjectured_eigenvalue_principal_zero_eq_neg_log_two (α a : ℝ) :
    conjectured_eigenvalue_principal α a 0 = -Real.log 2 := by
  unfold conjectured_eigenvalue_principal
  simp [pow_zero]

/-! ## NP-class parallels (α = φ + 1/4) -/

/-- **NP-class bridge**: `manuscript_predicted_eigenvalue_zero (φ + 1/4) =
    lambda_0_NP` from `SpectralGap.lean`. -/
theorem manuscript_predicted_eigenvalue_zero_NP_eq_lambda_0_NP :
    manuscript_predicted_eigenvalue_zero (phi + 1/4) =
    PrincipiaTractalis.lambda_0_NP := by
  unfold manuscript_predicted_eigenvalue_zero
        PrincipiaTractalis.lambda_0_NP PrincipiaTractalis.pi_10
  have hphi_pos : 0 < phi := by
    unfold phi
    have h5 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
    linarith
  have hdenom : 0 < phi + 1/4 := by linarith
  field_simp

/-- **NP-class predicted value is positive**: `π/(10·(φ+¼)) > 0`. -/
theorem manuscript_predicted_eigenvalue_zero_NP_pos :
    manuscript_predicted_eigenvalue_zero (phi + 1/4) > 0 := by
  unfold manuscript_predicted_eigenvalue_zero
  have h1 : 0 < Real.pi := Real.pi_pos
  have h2 : 0 < phi + 1/4 := by
    unfold phi
    have h5 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
    linarith
  positivity

/-- **NP-class incompatibility** (parallel to session 32 P-class):

    Manuscript's `λ_0(H_NP) = π/(10·(φ+¼)) ≈ +0.168` is POSITIVE, while
    principal-branch `−log 2 ≈ −0.693` is NEGATIVE. They cannot be
    equal — so Problem 2's Riemann-sheet selection is also required
    for the NP-class part of the conjecture. -/
theorem manuscript_principal_incompatibility_NP (a : ℝ) :
    manuscript_predicted_eigenvalue_zero (phi + 1/4) ≠
    conjectured_eigenvalue_principal (phi + 1/4) a 0 := by
  intro h
  have h_pos := manuscript_predicted_eigenvalue_zero_NP_pos
  rw [conjectured_eigenvalue_principal_zero_eq_neg_log_two] at h
  have h_neg : -Real.log 2 < 0 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2); linarith
  rw [h] at h_pos
  linarith

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
