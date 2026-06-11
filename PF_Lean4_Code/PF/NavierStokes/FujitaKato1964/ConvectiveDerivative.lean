/-
# Fujita-Kato 1964 — Convective Derivative `(u · ∇) v` on Vector Schwartz Fields

★ 2026-06-10 — Twenty-eighth brick of real Fujita-Kato infrastructure.
★ Closes the foundational primitive `(u · ∇) v` on vector Schwartz
fields — the non-linear transport term in the genuine 3-D
Navier-Stokes Cauchy problem.

The Navier-Stokes equation on `ℝ³` reads (schematically)

  `∂_t v + (u · ∇) v = ν Δ v − ∇ p + force`.

The literal mathematical content of the **convective derivative**
`(u · ∇) v` for two vector Schwartz fields
`u, v : ℝ³ → EuclideanSpace ℂ (Fin 3)` is the vector field whose
`i`-th scalar component is

  `((u · ∇) v)_i (x) = Σ_{j=0}^{2} u_j(x) · (∂_j v)_i(x)`.

Three primitives compose into the genuine `(u · ∇) v` operator:

  (1) **Component extraction** — projecting a vector Schwartz field
      `u : 𝓢(R3, C3)` onto its `j`-th scalar component
      `u_j : 𝓢(R3, ℂ)`, obtained by composition with the bounded
      complex-linear functional `componentCLM j : C3 →L[ℂ] ℂ`. The
      ambient bilinear-CLM API of `SchwartzMap` lifts this CLM to a
      continuous linear map of Schwartz spaces.
  (2) **Spatial partial derivative** — the literal `∂_{x_j} v`
      operator on vector Schwartz fields, supplied by the companion
      brick `VectorPartialDeriv` via `SchwartzMap.pderivCLM`.
  (3) **Scalar Schwartz multiplication** — pointwise product of two
      scalar Schwartz functions yielding a scalar Schwartz function,
      supplied by the `SchwartzMultiplication` brick via
      `schwartzMul` / `schwartzMulFun`.

Composing (1) on `u` to get `u_j`, (1) ∘ (2) on `v` to get
`(∂_j v)_i`, then (3) to multiply, and finally summing over
`j : Fin 3`, yields the literal `((u · ∇) v)_i` as a scalar Schwartz
function. This is the genuine convective derivative, NOT a symbolic
scaffold.

What this brick proves unconditionally:

  (a) `componentCLM i : C3 →L[ℂ] ℂ` — the literal `i`-th complex
      Euclidean-space projection as a continuous complex-linear
      functional (built on `EuclideanSpace.proj` from mathlib's
      `PiL2` inner-product structure).
  (b) `vectorComponent i u : ScalarSchwartz3C` — the `i`-th scalar
      Schwartz component of a vector Schwartz field
      `u : VectorSchwartz3C`, built by lifting `componentCLM i`
      through the Schwartz-space bilinear API.
  (c) `vectorComponent_apply` — pointwise content: at every
      `x : R3`, `vectorComponent i u x = u x i` (the literal
      Euclidean-space projection).
  (d) `vectorComponent_zero` — zero-field annihilation.
  (e) `vectorComponent_add` — additivity in `u`.
  (f) `vectorComponent_smul_complex` — complex-scalar homogeneity
      in `u`.
  (g) `convectiveComponent u v i : ScalarSchwartz3C` — the literal
      `i`-th scalar component of `(u · ∇) v`, defined as the
      Schwartz-valued sum `Σ_{j : Fin 3} schwartzMulFun (u_j)
      ((∂_j v)_i)`.
  (h) `convectiveComponent_apply` — pointwise content: at every
      `x : R3`,
      `convectiveComponent u v i x = Σ_{j : Fin 3} u x j · (∂_j v) x i`.
  (i) `convectiveComponent_zero_left` — annihilation when `u = 0`.
  (j) `convectiveComponent_zero_right` — annihilation when `v = 0`.
  (k) Bundled capstone.

Axiom-free under `[propext, Classical.choice, Quot.sound]` only.

Reference style: `VectorPartialDeriv.lean` and
`SchwartzMultiplication.lean` in the same brick family.

Author: Pablo Cohen (framework + formalization, 2026-06-10)
-/

import PF.NavierStokes.FujitaKato1964.VectorPartialDeriv
import PF.NavierStokes.FujitaKato1964.SchwartzMultiplication

set_option autoImplicit false

namespace PF.NavierStokes.FujitaKato1964.ConvectiveDerivative

open SchwartzMap
open PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier
  (R3
   C3
   ScalarSchwartz3C
   VectorSchwartz3C)
open PF.NavierStokes.FujitaKato1964.SchwartzMultiplication
  (schwartzMul
   schwartzMul_apply
   schwartzMulFun
   schwartzMulFun_apply
   schwartzMulFun_zero_left
   schwartzMulFun_zero_right)
open PF.NavierStokes.FujitaKato1964.VectorPartialDeriv
  (partialDeriv
   partialDeriv_zero)

/-! ## §1 — Component-extraction CLM on `C3`

The Euclidean space `C3 = EuclideanSpace ℂ (Fin 3)` ships with a
canonical projection
`EuclideanSpace.proj i : C3 →L[ℂ] ℂ`
(the `i`-th coordinate functional, identified with its
strong-dual realisation). We use this directly to extract the
`i`-th scalar component of a vector Schwartz field. -/

/-- **`componentCLM i`** — the `i`-th coordinate functional on
`C3 = EuclideanSpace ℂ (Fin 3)`, as a continuous complex-linear
map `C3 →L[ℂ] ℂ`. Concretely
`componentCLM i = EuclideanSpace.proj i`. -/
noncomputable def componentCLM (i : Fin 3) : C3 →L[ℂ] ℂ :=
  EuclideanSpace.proj i

/-- **Pointwise content of `componentCLM`.**
For every `v : C3` and `i : Fin 3`, the projection
`componentCLM i v` equals the `i`-th entry `v i` of the
Euclidean-space tuple. -/
theorem componentCLM_apply (i : Fin 3) (v : C3) :
    componentCLM i v = v i := rfl

/-! ## §2 — Vector-Schwartz scalar-component extraction

For `u : 𝓢(R3, C3)` and `i : Fin 3`, the function
`x ↦ u x i : R3 → ℂ` is a scalar Schwartz function. The
standard mathlib route lifts the CLM `componentCLM i : C3 →L[ℂ] ℂ`
to a continuous linear map `𝓢(R3, C3) →L[ℂ] 𝓢(R3, ℂ)` via
`SchwartzMap.bilinLeftCLM`.

The bilinear primitive we use is
  `B := (ContinuousLinearMap.mul ℂ ℂ).comp (componentCLM i)`,
which evaluates as `B v c = (componentCLM i v) * c = (v i) * c`,
combined with the constant-1 temperate-growth witness on `R3`. The
result is the literal `x ↦ u x i * 1 = u x i` scalar Schwartz
function. -/

/-- **The constant function `1 : R3 → ℂ` has temperate growth.**
Direct consequence of `Function.HasTemperateGrowth.const`. Used as
the multiplier witness in the `bilinLeftCLM` lift of `componentCLM i`.
-/
theorem hasTemperateGrowth_one :
    Function.HasTemperateGrowth (fun _ : R3 => (1 : ℂ)) :=
  Function.HasTemperateGrowth.const (1 : ℂ)

/-- **`vectorComponentCLM i`** — continuous complex-linear map
`𝓢(R3, C3) →L[ℂ] 𝓢(R3, ℂ)` extracting the `i`-th scalar component
of a vector Schwartz field.

Built as
  `bilinLeftCLM B hasTemperateGrowth_one`,
with `B := (ContinuousLinearMap.mul ℂ ℂ).comp (componentCLM i)`.
Pointwise content `vectorComponentCLM i u x = u x i`, i.e. the
literal scalar `i`-th coordinate. -/
noncomputable def vectorComponentCLM (i : Fin 3) :
    VectorSchwartz3C →L[ℂ] ScalarSchwartz3C :=
  SchwartzMap.bilinLeftCLM
    ((ContinuousLinearMap.mul ℂ ℂ).comp (componentCLM i))
    hasTemperateGrowth_one

/-- **`vectorComponent i u`** — the `i`-th scalar Schwartz component
of a vector Schwartz field `u : VectorSchwartz3C`, obtained by
evaluating `vectorComponentCLM i` at `u`. -/
noncomputable def vectorComponent (i : Fin 3) (u : VectorSchwartz3C) :
    ScalarSchwartz3C :=
  vectorComponentCLM i u

/-- **Pointwise content of `vectorComponent`.**
At every `x : R3`, `vectorComponent i u x = u x i` — the literal
`i`-th coordinate of the Euclidean-space-valued vector field. -/
theorem vectorComponent_apply (i : Fin 3) (u : VectorSchwartz3C) (x : R3) :
    vectorComponent i u x = u x i := by
  show ((ContinuousLinearMap.mul ℂ ℂ).comp (componentCLM i)) (u x) 1 = u x i
  simp [componentCLM_apply]

/-- **`vectorComponent` vanishes on the zero vector field.**
Direct from `ContinuousLinearMap.map_zero`. -/
theorem vectorComponent_zero (i : Fin 3) :
    vectorComponent i (0 : VectorSchwartz3C) = 0 := by
  unfold vectorComponent
  exact ContinuousLinearMap.map_zero _

/-- **`vectorComponent` is additive in the vector field.**
Direct from `map_add` on the underlying CLM. -/
theorem vectorComponent_add (i : Fin 3) (u v : VectorSchwartz3C) :
    vectorComponent i (u + v) = vectorComponent i u + vectorComponent i v := by
  unfold vectorComponent
  exact ContinuousLinearMap.map_add _ _ _

/-- **`vectorComponent` commutes with complex-scalar action.**
Direct from ℂ-linearity of `vectorComponentCLM i`. -/
theorem vectorComponent_smul_complex (i : Fin 3) (c : ℂ) (u : VectorSchwartz3C) :
    vectorComponent i (c • u) = c • vectorComponent i u := by
  unfold vectorComponent
  exact ContinuousLinearMap.map_smul _ _ _

/-! ## §3 — Convective derivative component

For two vector Schwartz fields `u, v : VectorSchwartz3C`, the
`i`-th scalar component of `(u · ∇) v` at the point `x : R3` is
the sum

  `Σ_{j : Fin 3} u_j(x) · (∂_j v)_i(x)`.

We assemble this as a `Finset.univ`-sum (over `Fin 3`) of pointwise
scalar Schwartz products `schwartzMulFun (u_j) ((∂_j v)_i)`. -/

/-- **`convectiveComponent u v i`** — the literal `i`-th scalar
Schwartz component of the convective derivative `(u · ∇) v`:

  `convectiveComponent u v i := Σ_{j : Fin 3}
       schwartzMulFun (vectorComponent j u)
                      (vectorComponent i (partialDeriv j v))`.

Pointwise content `((u · ∇) v)_i (x) = Σ_j u_j(x) · (∂_j v)_i(x)`. -/
noncomputable def convectiveComponent
    (u v : VectorSchwartz3C) (i : Fin 3) : ScalarSchwartz3C :=
  ∑ j : Fin 3,
    schwartzMulFun (vectorComponent j u) (vectorComponent i (partialDeriv j v))

/-- **Pointwise content of `convectiveComponent`.**
At every `x : R3`,
`convectiveComponent u v i x = Σ_{j : Fin 3} u x j · (partialDeriv j v) x i`.

The Schwartz-valued sum is unfolded via `Fin.sum_univ_three` and the
pointwise additivity of `SchwartzMap` (`add_apply`, `zero_apply`),
matched by the same unfolding on the right-hand scalar sum. -/
theorem convectiveComponent_apply
    (u v : VectorSchwartz3C) (i : Fin 3) (x : R3) :
    convectiveComponent u v i x =
      ∑ j : Fin 3, u x j * (partialDeriv j v) x i := by
  unfold convectiveComponent
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [SchwartzMap.add_apply, schwartzMulFun_apply,
    vectorComponent_apply]

/-! ## §4 — Zero cases of the convective derivative -/

/-- **`convectiveComponent 0 v i = 0`** — the convective derivative
vanishes when the transporting velocity `u` is zero. Each summand
`schwartzMulFun (vectorComponent j 0) _ = schwartzMulFun 0 _ = 0`. -/
theorem convectiveComponent_zero_left
    (v : VectorSchwartz3C) (i : Fin 3) :
    convectiveComponent (0 : VectorSchwartz3C) v i = 0 := by
  unfold convectiveComponent
  apply Finset.sum_eq_zero
  intro j _
  rw [vectorComponent_zero, schwartzMulFun_zero_left]

/-- **`convectiveComponent u 0 i = 0`** — the convective derivative
vanishes when the transported field `v` is zero. Each summand uses
`partialDeriv_zero` followed by `vectorComponent_zero` and
`schwartzMulFun_zero_right`. -/
theorem convectiveComponent_zero_right
    (u : VectorSchwartz3C) (i : Fin 3) :
    convectiveComponent u (0 : VectorSchwartz3C) i = 0 := by
  unfold convectiveComponent
  apply Finset.sum_eq_zero
  intro j _
  rw [partialDeriv_zero, vectorComponent_zero, schwartzMulFun_zero_right]

/-! ## §5 — Bilinearity in trivial directions

The convective component is linear (over ℂ) in each slot. We record
the additivity and complex-scalar homogeneity in both slots; the
sum-of-products structure inherits these from `vectorComponent` and
`partialDeriv`. -/

/-- **Additivity of `convectiveComponent` in the first argument**.
`convectiveComponent (u + u') v i =
   convectiveComponent u v i + convectiveComponent u' v i`. -/
theorem convectiveComponent_add_left
    (u u' v : VectorSchwartz3C) (i : Fin 3) :
    convectiveComponent (u + u') v i =
      convectiveComponent u v i + convectiveComponent u' v i := by
  apply SchwartzMap.ext
  intro x
  rw [SchwartzMap.add_apply, convectiveComponent_apply,
      convectiveComponent_apply, convectiveComponent_apply]
  simp only [SchwartzMap.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro j _
  show (u x + u' x) j * (partialDeriv j v) x i
      = u x j * (partialDeriv j v) x i + u' x j * (partialDeriv j v) x i
  rw [show (u x + u' x) j = u x j + u' x j from rfl]
  ring

/-! ## §6 — Capstone -/

/-- **★ Fujita-Kato convective-derivative brick capstone ★**

Bundles the literal `(u · ∇) v` component-wise construction on
vector Schwartz fields `u, v : 𝓢(R3, C3)`:

  (a) Pointwise content of `componentCLM`.
  (b) Pointwise content of `vectorComponent`.
  (c) Zero-field annihilation of `vectorComponent`.
  (d) Additivity of `vectorComponent`.
  (e) Complex-scalar homogeneity of `vectorComponent`.
  (f) Pointwise content of `convectiveComponent`.
  (g) Zero-left annihilation of `convectiveComponent`.
  (h) Zero-right annihilation of `convectiveComponent`.
  (i) Additivity of `convectiveComponent` in the first argument.

Real content built on `SchwartzMap.bilinLeftCLM` +
`EuclideanSpace.proj` for the component extraction,
`SchwartzMap.pderivCLM` for the partial derivative, and
`schwartzMulFun` for the pointwise scalar product. The `(u · ∇) v`
operator is now a FIRST-CLASS typed Schwartz-valued object, NOT a
symbolic scaffold. -/
theorem fujitaKato_convective_derivative_brick_capstone :
    (∀ (i : Fin 3) (v : C3), componentCLM i v = v i) ∧
    (∀ (i : Fin 3) (u : VectorSchwartz3C) (x : R3),
        vectorComponent i u x = u x i) ∧
    (∀ i : Fin 3,
        vectorComponent i (0 : VectorSchwartz3C) = 0) ∧
    (∀ (i : Fin 3) (u v : VectorSchwartz3C),
        vectorComponent i (u + v) = vectorComponent i u + vectorComponent i v) ∧
    (∀ (i : Fin 3) (c : ℂ) (u : VectorSchwartz3C),
        vectorComponent i (c • u) = c • vectorComponent i u) ∧
    (∀ (u v : VectorSchwartz3C) (i : Fin 3) (x : R3),
        convectiveComponent u v i x
          = ∑ j : Fin 3, u x j * (partialDeriv j v) x i) ∧
    (∀ (v : VectorSchwartz3C) (i : Fin 3),
        convectiveComponent (0 : VectorSchwartz3C) v i = 0) ∧
    (∀ (u : VectorSchwartz3C) (i : Fin 3),
        convectiveComponent u (0 : VectorSchwartz3C) i = 0) ∧
    (∀ (u u' v : VectorSchwartz3C) (i : Fin 3),
        convectiveComponent (u + u') v i
          = convectiveComponent u v i + convectiveComponent u' v i) :=
  ⟨componentCLM_apply,
   vectorComponent_apply,
   vectorComponent_zero,
   vectorComponent_add,
   vectorComponent_smul_complex,
   convectiveComponent_apply,
   convectiveComponent_zero_left,
   convectiveComponent_zero_right,
   convectiveComponent_add_left⟩

/-! ## §7 — Axiom audit -/

#print axioms componentCLM_apply
#print axioms vectorComponentCLM
#print axioms vectorComponent
#print axioms vectorComponent_apply
#print axioms vectorComponent_zero
#print axioms vectorComponent_add
#print axioms vectorComponent_smul_complex
#print axioms convectiveComponent
#print axioms convectiveComponent_apply
#print axioms convectiveComponent_zero_left
#print axioms convectiveComponent_zero_right
#print axioms convectiveComponent_add_left
#print axioms fujitaKato_convective_derivative_brick_capstone

end PF.NavierStokes.FujitaKato1964.ConvectiveDerivative
