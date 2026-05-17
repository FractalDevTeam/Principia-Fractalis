/-
# Mellin Modes — Translation Eigenvectors in Log Coordinates (Route A, Step 1)

The natural eigenvectors of the dilation group (per GPT's Route A
diagnosis) are **Mellin modes** `x ↦ x^{−iλ} = exp(−iλ · log x)`.
Their real and imaginary parts form a 2-dimensional invariant
subspace of the dilation action.

This file defines the real-valued Mellin modes `mellinCos λ x =
cos(λ · log x)` and `mellinSin λ x = sin(λ · log x)`, proves their
log-coordinate identification with standard sine/cosine on `ℝ`,
and establishes the **rotation action** of dilation on the 2D
`{mellinCos λ, mellinSin λ}` invariant subspace.

These are the canonical eigenfunctions for the Mellin-natural
operator analysis that Route A pursues; they replace the
cosineMode/sineMode of `PolylogSpectrum.lean` (which were the
"additive" eigenfunctions natural for `[0,1]` Lebesgue).

Stage L4+ — Route A, Step 1: Mellin modes.
-/

import PF.Analytic.LogCoord
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace PrincipiaTractalis.Analytic

open Real

/-! ## Definitions -/

/-- **Mellin cosine mode**:

      `mellinCos λ x := cos(λ · log x)`  for `x > 0`.

    Real part of the complex Mellin mode `x^{−iλ} = exp(−iλ · log x) =
    cos(λ · log x) − i · sin(λ · log x)`. -/
noncomputable def mellinCos (lam : ℝ) (x : ℝ) : ℝ :=
  Real.cos (lam * Real.log x)

/-- **Mellin sine mode**:

      `mellinSin λ x := sin(λ · log x)`  for `x > 0`.

    Imaginary-part (with sign) of the complex Mellin mode. -/
noncomputable def mellinSin (lam : ℝ) (x : ℝ) : ℝ :=
  Real.sin (lam * Real.log x)

/-! ## Log-coordinate identifications -/

/-- **`mellinCos` in log coordinates is the standard cosine on `ℝ`**:

      `logCoord (mellinCos λ) (t) = cos(λ · t)`.

    Direct from `log(exp(−t)) = −t` and `cos(−x) = cos(x)`. -/
theorem logCoord_mellinCos (lam : ℝ) (t : ℝ) :
    logCoord (mellinCos lam) t = Real.cos (lam * t) := by
  unfold logCoord mellinCos
  rw [Real.log_exp]
  rw [show lam * -t = -(lam * t) from by ring]
  exact Real.cos_neg (lam * t)

/-- **`mellinSin` in log coordinates is the NEGATED standard sine on `ℝ`**:

      `logCoord (mellinSin λ) (t) = −sin(λ · t)`.

    The negation comes from `sin(−x) = −sin(x)`. -/
theorem logCoord_mellinSin (lam : ℝ) (t : ℝ) :
    logCoord (mellinSin lam) t = -Real.sin (lam * t) := by
  unfold logCoord mellinSin
  rw [Real.log_exp]
  rw [show lam * -t = -(lam * t) from by ring]
  exact Real.sin_neg (lam * t)

/-! ## ★ Dilation as a rotation on the 2D Mellin subspace ★ -/

/-- **Dilation acts as a rotation on `mellinCos`**:

      `(D_α · mellinCos λ)(x) = cos(λ · log α) · mellinCos λ x
                              + sin(λ · log α) · mellinSin λ x`

    for `x > 0, α > 0`. Direct from `cos(A − B)` subtraction formula. -/
theorem dilation_mellinCos (α : ℝ) (hα : 0 < α) (lam : ℝ) (x : ℝ) (hx : 0 < x) :
    dilation α (mellinCos lam) x =
    Real.cos (lam * Real.log α) * mellinCos lam x +
    Real.sin (lam * Real.log α) * mellinSin lam x := by
  unfold dilation mellinCos mellinSin
  rw [Real.log_div (ne_of_gt hx) (ne_of_gt hα)]
  rw [show lam * (Real.log x - Real.log α)
        = lam * Real.log x - lam * Real.log α from by ring]
  rw [Real.cos_sub (lam * Real.log x) (lam * Real.log α)]
  ring

/-- **Dilation acts as a rotation on `mellinSin`**:

      `(D_α · mellinSin λ)(x) = cos(λ · log α) · mellinSin λ x
                              − sin(λ · log α) · mellinCos λ x`. -/
theorem dilation_mellinSin (α : ℝ) (hα : 0 < α) (lam : ℝ) (x : ℝ) (hx : 0 < x) :
    dilation α (mellinSin lam) x =
    Real.cos (lam * Real.log α) * mellinSin lam x -
    Real.sin (lam * Real.log α) * mellinCos lam x := by
  unfold dilation mellinSin mellinCos
  rw [Real.log_div (ne_of_gt hx) (ne_of_gt hα)]
  rw [show lam * (Real.log x - Real.log α)
        = lam * Real.log x - lam * Real.log α from by ring]
  rw [Real.sin_sub (lam * Real.log x) (lam * Real.log α)]
  ring

/-! ## Mellin-weighted integral (toward dilation unitarity) -/

/-- **Mellin-weighted integral** on a strictly positive interval:

      `mellinIntegral a b f := ∫_a^b f(x) · (1/x) dx`

    Integration against the dilation-invariant measure `dx/x`. The
    natural integration on the multiplicative group `(0, ∞)`. -/
noncomputable def mellinIntegral (a b : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ x in a..b, f x / x

/-- **★ Change of variables under dilation ★** — the Mellin-weighted
    integral is invariant under `x = α·y`:

      `∫_{a/α}^{b/α} f(α·y) / y dy = ∫_a^b f(x) / x dx`

    for `α > 0`. The substitution `x = α·y` transforms `dx = α dy`
    and `1/x = 1/(α·y)`, so `dx/x = dy/y`. The limits transform as
    `a ↦ a/α, b ↦ b/α`, but the integrand `f(α·y)/y` is the same as
    `f(x)/x` evaluated at `x = α·y`. This is the foundational
    identity for dilation unitarity on `L²((0, ∞), dx/x)`. -/
theorem mellin_change_of_variables_dilation
    (α a b : ℝ) (hα : 0 < α) (f : ℝ → ℝ) :
    ∫ y in (a/α)..(b/α), f (α * y) / y =
    ∫ x in a..b, f x / x := by
  have h_eq : ∀ y, α * (f (α * y) / (α * y)) = f (α * y) / y := by
    intro y; field_simp
  rw [show (fun y => f (α * y) / y)
        = (fun y => α * (f (α * y) / (α * y))) from by
        funext y; rw [h_eq]]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_comp_mul_left (fun x => f x / x) (ne_of_gt hα)]
  rw [smul_eq_mul]
  have h_lim : α * (a / α) = a ∧ α * (b / α) = b := by
    constructor <;> field_simp
  rw [h_lim.1, h_lim.2]
  rw [← mul_assoc]
  rw [mul_inv_cancel₀ (ne_of_gt hα)]
  rw [one_mul]

/-- **Mellin-norm preservation under dilation on (0, ∞)** (special
    case of `mellin_change_of_variables_dilation`):

    For the full positive real line `(0, ∞)`, dilation `x ↦ α·x` is
    norm-preserving with respect to `dx/x`. The boundary terms
    `a = 0, b = ∞` give `a/α = 0, b/α = ∞`, so the limits are
    unchanged.

    On a finite interval `(a, b)` with `0 < a < b`, the dilation
    changes the interval to `(a/α, b/α)` — same integral, different
    integration region. This is the structural distinction that
    makes `(0, ∞)` (or equivalently `ℝ` in log coordinates) the
    canonical domain for the dilation group's unitary representation. -/
theorem mellin_dilation_invariance_on_finite_interval
    (α a b : ℝ) (hα : 0 < α) (f : ℝ → ℝ) :
    mellinIntegral (a/α) (b/α) (dilation α⁻¹ f) =
    mellinIntegral a b f := by
  unfold mellinIntegral
  -- (dilation α⁻¹ f) y = f(y / α⁻¹) = f(α · y)
  have hrw : ∀ y, dilation α⁻¹ f y = f (α * y) := by
    intro y
    unfold dilation
    congr 1
    field_simp
  simp_rw [hrw]
  exact mellin_change_of_variables_dilation α a b hα f

/-! ## Documentation: Mellin modes as the canonical eigen-objects

The 2D matrix representation of dilation `D_α` in the
`{mellinCos λ, mellinSin λ}` basis is the rotation by angle
`λ · log α`:

```
            [ cos(λ log α)   sin(λ log α) ]
  D_α  ↦   [                              ]
            [ −sin(λ log α)  cos(λ log α) ]
```

The complex eigenvectors are `mellinCos λ ± i · mellinSin λ`, with
eigenvalues `exp(±i · λ · log α) = α^{±iλ}`. So the COMPLEX MELLIN
MODE `x^{−iλ}` is a dilation eigenvector with eigenvalue `α^{iλ}` —
the canonical multiplicative-symmetry eigenfunction.

This is the Mellin-natural counterpart of the additive
cosineMode/sineMode used in `PolylogSpectrum.lean`. Under `logCoord`,
the Mellin modes become standard sine/cosine on `ℝ` (the
translation eigenvectors), making them the natural Fourier basis for
the translation symmetry that the kernel `V_P^log` satisfies (per
`fractalKernelReal_log_self_similarity`).

The next steps of Route A:
* Define `H_P_at α a` transported to `L²((0,1), dx/x)` (Step 2).
* On the Mellin-natural measure space, dilation becomes UNITARY.
* The eigenfunctions of the transported operator are Mellin modes
  (modulo the residual cosine-scattering term from the self-
  similarity equation).
-/

end PrincipiaTractalis.Analytic
