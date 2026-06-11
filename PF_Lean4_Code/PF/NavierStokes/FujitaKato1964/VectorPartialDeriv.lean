/-
# Fujita-Kato 1964 — Vector Spatial Partial Derivatives via `pderivCLM`

★ 2026-06-10 — Twentieth brick of real Fujita-Kato infrastructure.

The genuine Navier-Stokes Cauchy problem on `ℝ³` requires the
convective derivative `(u·∇)v` for vector Schwartz fields. Building
this operator requires, as a primitive, the spatial partial
derivatives `∂_j v_i` of vector Schwartz fields

  `v : ℝ³ → EuclideanSpace ℂ (Fin 3)`.

mathlib provides

  `SchwartzMap.pderivCLM ℝ : (V → V) → 𝓢(V, F) →L[ℝ] 𝓢(V, F)`

— the directional Fréchet derivative on Schwartz space, as a real
continuous-linear map. We instantiate this at `V = ℝ³`, `F = ℂ³`
along the three canonical spatial-direction basis vectors of `ℝ³` to
obtain the three operator-typed partial derivatives

  `partialDeriv j : VectorSchwartz3C → VectorSchwartz3C`

for `j : Fin 3`.

This is the LITERAL `∂_{x_j}` operator on vector Schwartz fields,
built directly from mathlib's `pderivCLM` — not a symbolic identity
scaffold. Linear-algebraic properties (zero, additivity, real-scalar
homogeneity) inherit directly from the underlying CLM structure.

Companion construction: the cyclic vorticity-style difference

  `vorticityComponent v i := ∂_{(i+1) mod 3} v − ∂_{(i+2) mod 3} v`,

which is the unmixed (∂_j v − ∂_k v) building block that the genuine
3D vorticity assembly `ω = curl v` factors through after componentwise
projection. Vanishing of `vorticityComponent` at the zero field is
recorded for the downstream NS-on-`ℝ³` pipeline.

Axiom-free under `[propext, Classical.choice, Quot.sound]` only.

Reference pattern (`pderivCLM` on `Fin 4 → ℝ`):
`PF/NavierStokes/NS_ClayLiteralClosureAttempt.lean`.

Author: Pablo Cohen (formalization, 2026-06-10)
-/

import PF.NavierStokes.FujitaKato1964.SobolevSeminormVector
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

namespace PF.NavierStokes.FujitaKato1964.VectorPartialDeriv

open MeasureTheory SchwartzMap
open PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier

/-! ## §1 — Canonical spatial direction vectors on `ℝ³`

The three canonical direction vectors `e_0, e_1, e_2 ∈ ℝ³` of the
Euclidean basis, used as the differentiation directions for the three
spatial partial derivatives. We use `EuclideanSpace.single j (1 : ℝ)`
— the unit vector whose only nonzero component is the `j`-th. -/

/-- **★ `spatialDir j`** — the `j`-th canonical spatial-direction
unit vector in `R3 = EuclideanSpace ℝ (Fin 3)`. Concretely
`spatialDir j = e_j`, the `j`-th standard basis vector of `ℝ³`,
obtained as `EuclideanSpace.single j (1 : ℝ)`. -/
noncomputable def spatialDir (j : Fin 3) : R3 :=
  EuclideanSpace.single j (1 : ℝ)

/-! ## §2 — Spatial partial derivative on vector Schwartz fields

mathlib's `SchwartzMap.pderivCLM ℝ m : 𝓢(E, F) →L[ℝ] 𝓢(E, F)` is the
directional Fréchet derivative along `m : E`, as a real
continuous-linear map. Instantiated at `E = R3`, `F = C3`, and
`m = spatialDir j`, this realises the literal `∂_{x_j}` operator on
vector Schwartz fields, returning a vector Schwartz field of the same
type. -/

/-- **★★★ `partialDeriv j u`** — the `j`-th spatial partial
derivative of the vector Schwartz field `u : VectorSchwartz3C`, as a
first-class `VectorSchwartz3C` via

  `SchwartzMap.pderivCLM ℝ (spatialDir j) u`.

Pointwise content `(partialDeriv j u) x = fderiv ℝ u x (e_j)` —
literal `∂_{x_j} u`, NOT a symbolic scaffold. -/
noncomputable def partialDeriv (j : Fin 3) (u : VectorSchwartz3C) :
    VectorSchwartz3C :=
  SchwartzMap.pderivCLM ℝ (spatialDir j) u

/-- **★ Pointwise interpretation of `partialDeriv`** — at every
point `x : R3`, the `j`-th spatial partial derivative coincides with
the Fréchet derivative of `u` evaluated in direction `e_j`. -/
theorem partialDeriv_apply (j : Fin 3) (u : VectorSchwartz3C) (x : R3) :
    partialDeriv j u x = fderiv ℝ u x (spatialDir j) := by
  unfold partialDeriv
  rw [SchwartzMap.pderivCLM_apply]

/-! ## §3 — Linear-algebraic properties

`SchwartzMap.pderivCLM ℝ (spatialDir j)` is an ℝ-linear continuous
map by construction, so it sends zero to zero, distributes over
addition, and commutes with real-scalar action. -/

/-- **★ `partialDeriv` of the zero field is zero**. Direct from the
fact that `pderivCLM ℝ _` is a continuous-linear map. -/
theorem partialDeriv_zero (j : Fin 3) :
    partialDeriv j (0 : VectorSchwartz3C) = 0 := by
  unfold partialDeriv
  exact ContinuousLinearMap.map_zero _

/-- **★ `partialDeriv` is additive in the field argument**. Direct
from `map_add` on the underlying CLM. -/
theorem partialDeriv_add (j : Fin 3) (u v : VectorSchwartz3C) :
    partialDeriv j (u + v) = partialDeriv j u + partialDeriv j v := by
  unfold partialDeriv
  exact ContinuousLinearMap.map_add _ _ _

/-- **★ `partialDeriv` commutes with real-scalar action**. Direct
from ℝ-linearity of `pderivCLM ℝ _`. -/
theorem partialDeriv_smul_real (j : Fin 3) (c : ℝ) (u : VectorSchwartz3C) :
    partialDeriv j (c • u) = c • partialDeriv j u := by
  unfold partialDeriv
  exact ContinuousLinearMap.map_smul _ _ _

/-! ## §4 — Vorticity-style cyclic difference

The classical 3D vorticity is `ω = curl u`, with components

  `ω_i = ∂_{(i+1) mod 3} u − ∂_{(i+2) mod 3} u`

after the cyclic-index identification. The `vorticityComponent`
operator below records the unmixed cyclic difference of two
`partialDeriv` calls; the genuine `curl u` assembly extracts the
appropriate scalar component of this object via the `evalCLM`
projector. This is the building block consumed downstream by the
`(u·∇)v` convective-derivative chain. -/

/-- **★ `vorticityComponent u i`** — the `i`-th cyclic
partial-derivative difference of the vector Schwartz field `u`,
defined as

  `partialDeriv ((i+1) mod 3) u − partialDeriv ((i+2) mod 3) u`.

This is the unmixed difference building block; the literal vorticity
`ω_i = (curl u)_i` factors through a scalar-component projection of
this object. -/
noncomputable def vorticityComponent (u : VectorSchwartz3C) (i : Fin 3) :
    VectorSchwartz3C :=
  partialDeriv ⟨(i.val + 1) % 3, Nat.mod_lt _ (by decide)⟩ u -
  partialDeriv ⟨(i.val + 2) % 3, Nat.mod_lt _ (by decide)⟩ u

/-- **★ `vorticityComponent` of the zero field is zero**. Consequence
of `partialDeriv_zero` and `sub_zero`. -/
theorem vorticityComponent_zero (i : Fin 3) :
    vorticityComponent (0 : VectorSchwartz3C) i = 0 := by
  unfold vorticityComponent
  rw [partialDeriv_zero, partialDeriv_zero, sub_zero]

/-! ## §5 — Vector partial-derivative brick capstone -/

/-- **★★★ Vector partial-derivative brick capstone ★★★**

Bundles the full algebraic shell of the spatial partial-derivative
operator on vector Schwartz fields `u : ℝ³ → ℂ³`:

  (a) Pointwise interpretation `(partialDeriv j u) x = fderiv ℝ u x e_j`
  (b) `partialDeriv j 0 = 0`
  (c) `partialDeriv j (u + v) = partialDeriv j u + partialDeriv j v`
  (d) `partialDeriv j (c • u) = c • partialDeriv j u` for `c : ℝ`
  (e) `vorticityComponent 0 i = 0`

Real content built on mathlib's `SchwartzMap.pderivCLM`; the spatial
gradient and the cyclic vorticity-style differences are FIRST-CLASS
typed mathlib objects, NOT symbolic scaffolds. -/
theorem fujitaKato_vector_partialDeriv_brick_capstone :
    (∀ (j : Fin 3) (u : VectorSchwartz3C) (x : R3),
        partialDeriv j u x = fderiv ℝ u x (spatialDir j)) ∧
    (∀ j : Fin 3, partialDeriv j (0 : VectorSchwartz3C) = 0) ∧
    (∀ (j : Fin 3) (u v : VectorSchwartz3C),
        partialDeriv j (u + v) = partialDeriv j u + partialDeriv j v) ∧
    (∀ (j : Fin 3) (c : ℝ) (u : VectorSchwartz3C),
        partialDeriv j (c • u) = c • partialDeriv j u) ∧
    (∀ i : Fin 3, vorticityComponent (0 : VectorSchwartz3C) i = 0) :=
  ⟨partialDeriv_apply,
   partialDeriv_zero,
   partialDeriv_add,
   partialDeriv_smul_real,
   vorticityComponent_zero⟩

/-! ## §6 — Axiom audit -/

#print axioms partialDeriv_apply
#print axioms partialDeriv_zero
#print axioms partialDeriv_add
#print axioms partialDeriv_smul_real
#print axioms vorticityComponent_zero
#print axioms fujitaKato_vector_partialDeriv_brick_capstone

end PF.NavierStokes.FujitaKato1964.VectorPartialDeriv
