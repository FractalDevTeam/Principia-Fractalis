/-
# Log-Coordinate Transform — Route A (Self-Similar / Mellin-Natural Geometry)

GPT's structural assessment identified that the framework's natural
geometry is **Mellin-natural / multiplicatively-scaling**, not the
additive (`[0,1]` with Lebesgue) embedding currently used by
`H_P_at α a`. The RH-side of the framework already uses the
Mellin-natural space `L²((0,1), dx/x)` (see `T₃^sym` in
`PF/SpectralBijection.lean`); the P-vs-NP side has been working in
the additive embedding.

This file delivers the **log-coordinate bridge** that connects the
two geometries:

* **Multiplicative side** (Mellin-natural): `x ∈ (0, ∞)` with measure
  `dx/x`. Dilation `x ↦ αx` is a UNITARY operator (preserves `dx/x`).
* **Additive side** (translation-natural): `t ∈ ℝ` with Lebesgue
  measure `dt`. Translation `t ↦ t + c` is a UNITARY operator.
* **Bridge**: `t = −log x` (so `x = exp(−t)`). Multiplicative
  dilation `x ↦ αx` ↔ additive translation `t ↦ t − log α`.

Under this bridge, the dilation group `{D_α : α > 0}` on
multiplicative coordinates becomes the translation group
`{T_c : c ∈ ℝ}` on log coordinates. The framework's fractal
self-similarity acquires the natural translation symmetry, opening
the door to Mellin transform / Fourier analysis on the translation
group.

## What this gives the framework

The kernel self-similarity `V_P(x, y) = cos(π·|x−y|) + (1/a)·V_P(αx, αy)`
becomes, in log coordinates with `s = −log x, t = −log y`:

  `V_P(e^{−s}, e^{−t}) = cos(π·|e^{−s} − e^{−t}|) +
                         (1/a)·V_P(α·e^{−s}, α·e^{−t})`

with `α·e^{−s} = e^{−(s−log α)}`, so this becomes a *translation-shifted*
identity in `s, t`. The dilation by `α` becomes a translation by
`log α` in log-coordinate space. The natural eigenvectors are the
**translation eigenvectors** — i.e., `exp(iλ·t)` for `λ ∈ ℝ` — which
in `x`-coordinates are the **Mellin modes** `x^{−iλ}`.

This is exactly the structure of the framework's `T₃^sym` operator
on `L²((0,1), dx/x)`. Route A (per GPT) is the harmonization of the
P-vs-NP-side spectral analysis with this Mellin-natural geometry.

Stage L4+ — Route A: log-coordinate / Mellin-natural framework.
-/

import PF.Analytic.Dilation
import PF.Analytic.KernelSelfSimilarity
import PF.IntegralKernel.FractalKernel

namespace PrincipiaTractalis.Analytic

open Real

/-! ## Log-coordinate transform -/

/-- **Log-coordinate transform**: maps a function on `(0, ∞)` (in `x`)
    to a function on `ℝ` (in `t`) via the substitution `x = exp(−t)`.

      `(logCoord f) t := f(exp(−t))`

    The natural setting for converting multiplicative structure to
    additive structure. -/
noncomputable def logCoord (f : ℝ → ℝ) : ℝ → ℝ :=
  fun t => f (Real.exp (-t))

/-- **Translation operator** on `ℝ`: `(T_c f) t := f(t − c)`.

    The additive analog of dilation. Forms an abelian group under
    composition, parametrised by `(ℝ, +)`. -/
noncomputable def translation (c : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun t => f (t - c)

/-! ## Basic properties of `translation` -/

/-- **Linearity (additivity)** of translation. -/
theorem translation_add (c : ℝ) (f g : ℝ → ℝ) :
    translation c (f + g) = translation c f + translation c g := by
  funext _; rfl

/-- **Linearity (scalar)** of translation. -/
theorem translation_smul (c k : ℝ) (f : ℝ → ℝ) :
    translation c (k • f) = k • translation c f := by
  funext _; rfl

/-- **Group composition**: `T_c ∘ T_d = T_(c + d)`. -/
theorem translation_comp (c d : ℝ) (f : ℝ → ℝ) :
    translation c (translation d f) = translation (c + d) f := by
  funext t
  unfold translation
  congr 1; ring

/-- **Identity**: `T_0 = id`. -/
theorem translation_zero (f : ℝ → ℝ) : translation 0 f = f := by
  funext t; unfold translation; simp

/-- **Inverse**: `T_c ∘ T_(−c) = id`. -/
theorem translation_neg_translation (c : ℝ) (f : ℝ → ℝ) :
    translation (-c) (translation c f) = f := by
  funext t
  unfold translation
  congr 1; ring

/-- **Continuity preserved** under translation. -/
theorem translation_continuous (c : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    Continuous (translation c f) := by
  unfold translation
  exact hf.comp (continuous_id'.sub continuous_const)

/-! ## ★ The bridge: dilation ↔ translation under log coordinates -/

/-- **★ Multiplicative-to-additive bridge ★**:

      `logCoord (dilation α f) (t) = logCoord f (t + log α)`

    for `α > 0`. Equivalently, in operator form:

      `logCoord ∘ dilation α = translation (−log α) ∘ logCoord`

    The dilation by `α` in `x`-coordinates corresponds EXACTLY to the
    translation by `log α` (with sign) in log coordinates. This is the
    canonical identification of the multiplicative dilation group with
    the additive translation group via Mellin / log transform. -/
theorem logCoord_dilation (α : ℝ) (hα : 0 < α) (f : ℝ → ℝ) (t : ℝ) :
    logCoord (dilation α f) t = logCoord f (t + Real.log α) := by
  unfold logCoord dilation
  congr 1
  rw [show -(t + Real.log α) = -t - Real.log α from by ring]
  rw [Real.exp_sub]
  rw [Real.exp_log hα]

/-- **Functional version** of the bridge:

      `logCoord ∘ dilation α = translation (−log α) ∘ logCoord`

    Stated as a function-level equality (composition of functions
    `ℝ → ℝ → ℝ`). -/
theorem logCoord_dilation_eq_translation_logCoord
    (α : ℝ) (hα : 0 < α) (f : ℝ → ℝ) :
    logCoord (dilation α f) =
    translation (-Real.log α) (logCoord f) := by
  funext t
  rw [logCoord_dilation α hα f t]
  unfold translation
  congr 1; ring

/-! ## Inverse transform: expCoord -/

/-- **Inverse log-coordinate transform**: maps a function on `ℝ` (in
    `t`) back to a function on `(0, ∞)` (in `x`):

      `(expCoord g) x := g(-log x)`

    Inverse of `logCoord` on `(0, ∞)`. -/
noncomputable def expCoord (g : ℝ → ℝ) : ℝ → ℝ :=
  fun x => g (-Real.log x)

/-- **Right inverse**: `expCoord (logCoord f) x = f x` for `x > 0`. -/
theorem expCoord_logCoord (f : ℝ → ℝ) (x : ℝ) (hx : 0 < x) :
    expCoord (logCoord f) x = f x := by
  unfold expCoord logCoord
  rw [neg_neg]
  rw [Real.exp_log hx]

/-- **Left inverse**: `logCoord (expCoord g) t = g t` for all `t`. -/
theorem logCoord_expCoord (g : ℝ → ℝ) (t : ℝ) :
    logCoord (expCoord g) t = g t := by
  unfold logCoord expCoord
  rw [Real.log_exp]
  rw [neg_neg]

/-! ## Log-coordinate fractal kernel -/

/-- **Fractal kernel in log coordinates**:

      `V_P^log(s, t) := V_P(e^{-s}, e^{-t})`

    The kernel of the dilation-symmetrised version of `H_P`. -/
noncomputable def fractalKernelReal_log (α a : ℝ) (s t : ℝ) : ℝ :=
  PrincipiaTractalis.IntegralKernel.fractalKernelReal
    α a ((Real.exp (-s), Real.exp (-t)) : ℝ × ℝ)

/-- **Joint translation in log coordinates corresponds to joint
    scaling in x coordinates**:

      `V_P^log(s − c, t − c) = V_P(e^c · e^{-s}, e^c · e^{-t})`

    The translation group acts on the log-coordinate kernel by
    arguments-shift, which corresponds via the bridge to dilation by
    `e^c` in the original `x`-coordinates. -/
theorem fractalKernelReal_log_joint_translation
    (α a c : ℝ) (s t : ℝ) :
    fractalKernelReal_log α a (s - c) (t - c) =
    PrincipiaTractalis.IntegralKernel.fractalKernelReal
      α a ((Real.exp c * Real.exp (-s), Real.exp c * Real.exp (-t)) : ℝ × ℝ) := by
  unfold fractalKernelReal_log
  have h1 : Real.exp (-(s - c)) = Real.exp c * Real.exp (-s) := by
    rw [show -(s - c) = c + (-s) from by ring]
    exact Real.exp_add c (-s)
  have h2 : Real.exp (-(t - c)) = Real.exp c * Real.exp (-t) := by
    rw [show -(t - c) = c + (-t) from by ring]
    exact Real.exp_add c (-t)
  rw [h1, h2]

/-- **★ Self-similarity in log coordinates ★** (the translation-shifted
    form of the kernel self-similarity equation):

      `V_P^log(s − log α, t − log α) = a · V_P^log(s, t)
                                       − a · cos(π · dist(e^{-s}, e^{-t}))`

    The dilation by `α` on `(x, y)` becomes the translation by
    `log α` on `(s, t)` (per `logCoord_dilation`). The kernel
    self-similarity (scaled form) `V_P(αx, αy) = a · V_P(x, y) − a · cos`
    therefore becomes a translation-invariance-mod-cosine equation
    in log coordinates.

    This is the structural form making the self-similarity manifest
    as a TRANSLATION SYMMETRY (Pontryagin-dual to multiplicative
    dilation) in the log-coordinate picture. -/
theorem fractalKernelReal_log_self_similarity
    (α a : ℝ) (ha : 1 < a) (hα : 0 < α) (s t : ℝ) :
    fractalKernelReal_log α a (s - Real.log α) (t - Real.log α) =
    a * fractalKernelReal_log α a s t -
    a * Real.cos (Real.pi * dist (Real.exp (-s)) (Real.exp (-t))) := by
  rw [fractalKernelReal_log_joint_translation α a (Real.log α) s t]
  rw [Real.exp_log hα]
  rw [PrincipiaTractalis.IntegralKernel.fractalKernelReal_self_similarity_scaled
        α a ha (le_of_lt hα) (Real.exp (-s)) (Real.exp (-t))]
  rfl

/-! ## Documentation: the next layer of Route A

The log-coordinate bridge above translates the **dilation group** on
`(ℝ → ℝ)` to the **translation group** on `(ℝ → ℝ)`. The natural
next pieces of Route A's infrastructure:

1. **Mellin-natural cosine modes**: in log coordinates, the
   cosineMode/sineMode (which shift scale under dilation) translate
   to functions that **shift argument** under translation:

   `cosineMode α k ↦ (logCoord ∘ cosineMode α k)(t) = cos(π·αᵏ·exp(−t))`

   Not quite the "natural" translation eigenvectors. The genuine
   translation eigenvectors on `ℝ` are `exp(iλ·t)` for `λ ∈ ℝ`,
   which in `x`-coordinates are `x^{−iλ}` — the Mellin modes.

2. **Operator transport**: `H_P_at α a` in `x`-coordinates with
   Lebesgue measure becomes an operator on log-coordinate functions
   via change of variables. The transport rules require the Jacobian
   `dx = −e^{−t} dt`, so the measure transforms as `dx ↔ e^{−t} dt`.
   The natural log-coordinate measure is `dt`; the natural
   `x`-coordinate measure for unitarity is `dx/x` (which becomes
   exactly `dt`). This is why the `L²((0,1), dx/x)` choice for
   `T₃^sym` is canonical.

3. **Mellin transform**: a unitary operator
   `M : L²((0,∞), dx/x) → L²(ℝ, dν)` for an appropriate `ν`,
   diagonalizing the dilation group. Once `H_P_at α a` is transported
   to `L²((0,∞), dx/x)`, the Mellin transform diagonalises the
   dilation part, leaving only the residual scattering structure.

These are the next layers Route A would build. Each is a real
formalization deliverable, but each requires more `MeasureTheory`
infrastructure than the kernel-level work has needed so far. -/

end PrincipiaTractalis.Analytic
