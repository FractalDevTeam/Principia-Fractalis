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
