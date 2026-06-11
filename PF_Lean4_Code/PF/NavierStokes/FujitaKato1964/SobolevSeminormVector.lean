/-
# Fujita-Kato 1964 — Vector-Valued Ḣ^{1/2} Seminorm

★ 2026-06-10 — Third brick of real Fujita-Kato infrastructure.

Extends the scalar `Ḣ^{1/2}` seminorm from
`SobolevSeminormFourier.lean` (scalar `ℂ`-valued Schwartz) to
**vector-valued** Schwartz fields

  `u : ℝ³ → EuclideanSpace ℂ (Fin 3)`

This is the type the genuine Navier-Stokes Cauchy problem uses
(after complexification): the velocity is a 3-vector field on ℝ³.

The vector seminorm shares the same Fourier-based integral
structure as the scalar version. The Fourier transform of a
vector-valued Schwartz function lands in the same target space
`EuclideanSpace ℂ (Fin 3)`; the pointwise norm is the inner-product
Euclidean norm. All scalar-version properties (non-negativity,
zero-on-zero, scaling by complex scalars) transfer.

Axiom-free; kernel-only `[propext, Classical.choice, Quot.sound]`.

Author: Pablo Cohen (2026-06-10)
-/

import PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier

set_option autoImplicit false

namespace PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier

open MeasureTheory SchwartzMap

/-! ## §1 — Vector Schwartz fields -/

/-- **Three-dimensional complex Euclidean target.** The Navier-Stokes
velocity field, after complexification, takes values in this space. -/
abbrev C3 : Type := EuclideanSpace ℂ (Fin 3)

/-- **Vector-valued (3-component complex) Schwartz functions on ℝ³.**
The type of the complexified Navier-Stokes velocity field. -/
abbrev VectorSchwartz3C : Type := SchwartzMap R3 C3

/-! ## §2 — Vector Sobolev seminorm integrand -/

/-- **Pointwise integrand of the homogeneous vector Ḣ^{1/2} seminorm
squared.** For a vector Schwartz field `u : ℝ³ → ℂ³` and frequency
`ξ ∈ ℝ³`, the integrand is

  `|ξ| · ‖û(ξ)‖²_{ℂ³}`

where `‖·‖_{ℂ³}` is the Euclidean (Hermitian) norm. -/
noncomputable def vectorH12IntegrandSq (u : VectorSchwartz3C) (ξ : R3) : ℝ :=
  ‖ξ‖ * ‖(fourierTransformCLM ℂ u) ξ‖ ^ 2

/-- **Vector integrand is pointwise non-negative.** -/
theorem vectorH12IntegrandSq_nonneg (u : VectorSchwartz3C) (ξ : R3) :
    0 ≤ vectorH12IntegrandSq u ξ :=
  mul_nonneg (norm_nonneg _) (sq_nonneg _)

/-- **Vector integrand vanishes on the zero vector field.** -/
theorem vectorH12IntegrandSq_zero (ξ : R3) :
    vectorH12IntegrandSq (0 : VectorSchwartz3C) ξ = 0 := by
  unfold vectorH12IntegrandSq
  rw [map_zero, SchwartzMap.zero_apply, norm_zero]
  ring

/-! ## §3 — Vector Sobolev seminorm squared -/

/-- **Vector homogeneous Ḣ^{1/2} seminorm squared.**

  `‖u‖²_{Ḣ^{1/2}} := ∫ |ξ| · ‖û(ξ)‖²_{ℂ³} dξ`

The integral is over `ℝ³` with respect to Lebesgue volume. -/
noncomputable def vectorHomogeneousH12SeminormSq (u : VectorSchwartz3C) : ℝ :=
  ∫ ξ : R3, vectorH12IntegrandSq u ξ

/-- **Vector Sobolev seminorm squared is non-negative.** -/
theorem vectorHomogeneousH12SeminormSq_nonneg (u : VectorSchwartz3C) :
    0 ≤ vectorHomogeneousH12SeminormSq u := by
  unfold vectorHomogeneousH12SeminormSq
  exact MeasureTheory.integral_nonneg (fun ξ => vectorH12IntegrandSq_nonneg u ξ)

/-- **Vector Sobolev seminorm squared of the zero field is zero.** -/
theorem vectorHomogeneousH12SeminormSq_zero :
    vectorHomogeneousH12SeminormSq (0 : VectorSchwartz3C) = 0 := by
  unfold vectorHomogeneousH12SeminormSq
  simp only [vectorH12IntegrandSq_zero, integral_zero]

/-! ## §4 — Vector scaling identity -/

/-- **Pointwise scaling of the vector integrand**: at every frequency,

  `vectorH12IntegrandSq (c • u) ξ = ‖c‖² · vectorH12IntegrandSq u ξ`. -/
theorem vectorH12IntegrandSq_smul (c : ℂ) (u : VectorSchwartz3C) (ξ : R3) :
    vectorH12IntegrandSq (c • u) ξ = ‖c‖ ^ 2 * vectorH12IntegrandSq u ξ := by
  unfold vectorH12IntegrandSq
  rw [map_smul, SchwartzMap.smul_apply, norm_smul]
  ring

/-- **Scaling identity for the vector Ḣ^{1/2} seminorm squared.**

  `vectorHomogeneousH12SeminormSq (c • u) = ‖c‖² · vectorHomogeneousH12SeminormSq u`

The small-data property the Fujita-Kato 1964 vector contraction
argument actually needs (real NS lives on vector fields). -/
theorem vectorHomogeneousH12SeminormSq_smul (c : ℂ) (u : VectorSchwartz3C) :
    vectorHomogeneousH12SeminormSq (c • u) = ‖c‖ ^ 2 * vectorHomogeneousH12SeminormSq u := by
  unfold vectorHomogeneousH12SeminormSq
  calc ∫ ξ : R3, vectorH12IntegrandSq (c • u) ξ
      = ∫ ξ : R3, ‖c‖ ^ 2 * vectorH12IntegrandSq u ξ := by
        congr 1
        ext ξ
        exact vectorH12IntegrandSq_smul c u ξ
    _ = ‖c‖ ^ 2 * ∫ ξ : R3, vectorH12IntegrandSq u ξ :=
        MeasureTheory.integral_const_mul _ _

/-! ## §5 — Vector capstone -/

/-- **★ Vector Fujita-Kato Sobolev brick capstone ★**

Bundles the full algebraic shell of the vector homogeneous `Ḣ^{1/2}`
seminorm squared on complex Schwartz vector fields on ℝ³:

  (a) Pointwise non-negativity of the integrand
  (b) Pointwise vanishing on the zero field
  (c) Non-negativity of the integrated seminorm squared
  (d) Vanishing of the integrated seminorm squared on the zero field
  (e) Scaling identity `‖c•u‖² = ‖c‖² · ‖u‖²` by complex scalars

This is the type and shell the actual NS Cauchy problem needs.
Real content built on mathlib's `SchwartzMap.fourierTransformCLM`;
not a substrate surrogate. -/
theorem fujitaKato_sobolev_vector_brick_capstone :
    (∀ u ξ, 0 ≤ vectorH12IntegrandSq u ξ) ∧
    (∀ ξ, vectorH12IntegrandSq (0 : VectorSchwartz3C) ξ = 0) ∧
    (∀ u, 0 ≤ vectorHomogeneousH12SeminormSq u) ∧
    (vectorHomogeneousH12SeminormSq (0 : VectorSchwartz3C) = 0) ∧
    (∀ (c : ℂ) (u : VectorSchwartz3C),
       vectorHomogeneousH12SeminormSq (c • u)
         = ‖c‖ ^ 2 * vectorHomogeneousH12SeminormSq u) :=
  ⟨vectorH12IntegrandSq_nonneg,
   vectorH12IntegrandSq_zero,
   vectorHomogeneousH12SeminormSq_nonneg,
   vectorHomogeneousH12SeminormSq_zero,
   vectorHomogeneousH12SeminormSq_smul⟩

/-! ## §6 — Axiom audit -/

#print axioms vectorH12IntegrandSq_nonneg
#print axioms vectorH12IntegrandSq_zero
#print axioms vectorHomogeneousH12SeminormSq_nonneg
#print axioms vectorHomogeneousH12SeminormSq_zero
#print axioms vectorH12IntegrandSq_smul
#print axioms vectorHomogeneousH12SeminormSq_smul
#print axioms fujitaKato_sobolev_vector_brick_capstone

end PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier
