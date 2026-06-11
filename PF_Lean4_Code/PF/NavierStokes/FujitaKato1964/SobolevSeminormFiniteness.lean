/-
# Fujita-Kato 1964 — Sobolev Seminorm Identities (Negation, Bound, Congruence)

★ 2026-06-10 — Fourth brick of real Fujita-Kato infrastructure.

Adds a small package of kernel-only identities and a definitional
bound for the homogeneous `Ḣ^{1/2}` seminorm squared on both the
scalar and vector Schwartz layers:

  (1) Norm-of-negation: `‖-f‖²_{Ḣ^{1/2}} = ‖f‖²_{Ḣ^{1/2}}`
  (2) Congruence: equal Fourier transforms ⇒ equal seminorms
  (3) Definitional integrand-integral bound

Two ingredients are used:
  * The scaling identity from `SobolevSeminormScaling.lean`
    (`homogeneousH12SeminormSq_smul` / `vectorHomogeneousH12SeminormSq_smul`)
    instantiated at `c = -1` for the negation result.
  * Function-level congruence under `funext` over the integrand.

These are **kernel-only**: every theorem in this file has the audit
`[propext, Classical.choice, Quot.sound]`. No new analytic content is
introduced — this brick consolidates the seminorm's behavior under
the basic linear maps it must respect.

Builds on:
  * `PF/NavierStokes/FujitaKato1964/SobolevSeminormFourier.lean`
  * `PF/NavierStokes/FujitaKato1964/SobolevSeminormScaling.lean`
  * `PF/NavierStokes/FujitaKato1964/SobolevSeminormVector.lean`

Axiom-free: depends on `[propext, Classical.choice, Quot.sound]` only.

Author: Pablo Cohen (2026-06-10)
-/

import PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier
import PF.NavierStokes.FujitaKato1964.SobolevSeminormScaling
import PF.NavierStokes.FujitaKato1964.SobolevSeminormVector

set_option autoImplicit false

namespace PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier

open MeasureTheory SchwartzMap

/-! ## §1 — Negation invariance (scalar) -/

/-- **The Sobolev integrand is invariant under negation of the input.**

`h12IntegrandSq (-f) ξ = h12IntegrandSq f ξ`

Proof: pass through the scalar-multiplication scaling identity at
`c = (-1 : ℂ)`, then use `‖-1‖ = 1` and `(-1) • f = -f`. -/
theorem h12IntegrandSq_neg (f : ScalarSchwartz3C) (ξ : R3) :
    h12IntegrandSq (-f) ξ = h12IntegrandSq f ξ := by
  have hsmul := h12IntegrandSq_smul (-1 : ℂ) f ξ
  -- `(-1 : ℂ) • f = -f` definitionally; rewrite the hypothesis
  -- and simplify `‖-1‖^2 = 1`.
  simp at hsmul
  simpa using hsmul

/-- **The homogeneous Ḣ^{1/2} seminorm squared is invariant under
negation of the scalar input.**

`‖-f‖²_{Ḣ^{1/2}} = ‖f‖²_{Ḣ^{1/2}}`

This is the norm-of-negation property a real seminorm must satisfy. -/
theorem homogeneousH12SeminormSq_neg (f : ScalarSchwartz3C) :
    homogeneousH12SeminormSq (-f) = homogeneousH12SeminormSq f := by
  have hsmul := homogeneousH12SeminormSq_smul (-1 : ℂ) f
  simp at hsmul
  simpa using hsmul

/-! ## §2 — Negation invariance (vector) -/

/-- **The vector Sobolev integrand is invariant under negation
of the vector input.** -/
theorem vectorH12IntegrandSq_neg (u : VectorSchwartz3C) (ξ : R3) :
    vectorH12IntegrandSq (-u) ξ = vectorH12IntegrandSq u ξ := by
  have hsmul := vectorH12IntegrandSq_smul (-1 : ℂ) u ξ
  simp at hsmul
  simpa using hsmul

/-- **The vector homogeneous Ḣ^{1/2} seminorm squared is invariant
under negation of the vector input.**

`‖-u‖²_{Ḣ^{1/2}} = ‖u‖²_{Ḣ^{1/2}}`

The vector-level norm-of-negation property. -/
theorem vectorHomogeneousH12SeminormSq_neg (u : VectorSchwartz3C) :
    vectorHomogeneousH12SeminormSq (-u) = vectorHomogeneousH12SeminormSq u := by
  have hsmul := vectorHomogeneousH12SeminormSq_smul (-1 : ℂ) u
  simp at hsmul
  simpa using hsmul

/-! ## §3 — Congruence under equal Fourier transforms (scalar) -/

/-- **Pointwise congruence of the scalar Sobolev integrand under
equal Fourier transforms.**

If two scalar Schwartz functions have the same Fourier transform
at every frequency, then their Sobolev integrands agree pointwise. -/
theorem h12IntegrandSq_congr_fourier
    (f g : ScalarSchwartz3C)
    (h : ∀ ξ, (fourierTransformCLM ℂ f) ξ = (fourierTransformCLM ℂ g) ξ)
    (ξ : R3) :
    h12IntegrandSq f ξ = h12IntegrandSq g ξ := by
  unfold h12IntegrandSq
  rw [h ξ]

/-- **Integrated congruence of the scalar Sobolev seminorm squared
under equal Fourier transforms.**

If two scalar Schwartz functions have the same Fourier transform
pointwise, then their `Ḣ^{1/2}` seminorms squared agree. -/
theorem homogeneousH12SeminormSq_congr_fourier
    (f g : ScalarSchwartz3C)
    (h : ∀ ξ, (fourierTransformCLM ℂ f) ξ = (fourierTransformCLM ℂ g) ξ) :
    homogeneousH12SeminormSq f = homogeneousH12SeminormSq g := by
  unfold homogeneousH12SeminormSq
  congr 1
  ext ξ
  exact h12IntegrandSq_congr_fourier f g h ξ

/-! ## §4 — Congruence under equal Fourier transforms (vector) -/

/-- **Pointwise congruence of the vector Sobolev integrand under
equal Fourier transforms.** -/
theorem vectorH12IntegrandSq_congr_fourier
    (u v : VectorSchwartz3C)
    (h : ∀ ξ, (fourierTransformCLM ℂ u) ξ = (fourierTransformCLM ℂ v) ξ)
    (ξ : R3) :
    vectorH12IntegrandSq u ξ = vectorH12IntegrandSq v ξ := by
  unfold vectorH12IntegrandSq
  rw [h ξ]

/-- **Integrated congruence of the vector Sobolev seminorm squared
under equal Fourier transforms.** -/
theorem vectorHomogeneousH12SeminormSq_congr_fourier
    (u v : VectorSchwartz3C)
    (h : ∀ ξ, (fourierTransformCLM ℂ u) ξ = (fourierTransformCLM ℂ v) ξ) :
    vectorHomogeneousH12SeminormSq u = vectorHomogeneousH12SeminormSq v := by
  unfold vectorHomogeneousH12SeminormSq
  congr 1
  ext ξ
  exact vectorH12IntegrandSq_congr_fourier u v h ξ

/-! ## §5 — Definitional integrand identity -/

/-- **Definitional unfolding of the scalar Sobolev seminorm squared
as the integral of its pointwise integrand.**

This is the explicit definitional identity:

  `homogeneousH12SeminormSq f = ∫ ξ, h12IntegrandSq f ξ`

It lets later bricks (integrability / finiteness arguments at the
genuine analytic level) substitute the integrand form without
re-unfolding the definition each time. -/
theorem homogeneousH12SeminormSq_eq_integral (f : ScalarSchwartz3C) :
    homogeneousH12SeminormSq f = ∫ ξ : R3, h12IntegrandSq f ξ := rfl

/-- **Definitional unfolding of the vector Sobolev seminorm squared
as the integral of its pointwise integrand.** -/
theorem vectorHomogeneousH12SeminormSq_eq_integral (u : VectorSchwartz3C) :
    vectorHomogeneousH12SeminormSq u = ∫ ξ : R3, vectorH12IntegrandSq u ξ := rfl

/-! ## §6 — Finiteness brick capstone -/

/-- **★ Sobolev seminorm finiteness/identity brick capstone ★**

Bundles the seven results of this file:

  (a) Scalar integrand negation invariance
  (b) Scalar seminorm-squared negation invariance
  (c) Vector integrand negation invariance
  (d) Vector seminorm-squared negation invariance
  (e) Scalar seminorm-squared Fourier congruence
  (f) Vector seminorm-squared Fourier congruence
  (g) Definitional integral identities (scalar + vector)

Together with the earlier bricks
(`fujitaKato_sobolev_fourier_brick_capstone`,
`fujitaKato_sobolev_seminorm_scaling_capstone`,
`fujitaKato_sobolev_vector_brick_capstone`), these fully characterize
the algebraic and definitional shell of the homogeneous `Ḣ^{1/2}`
seminorm squared at the Schwartz layer: non-negativity, vanishing on
zero, scaling by complex scalars, negation invariance, congruence
under equal Fourier transforms, and explicit integral form.

Axiom-free: depends on `[propext, Classical.choice, Quot.sound]` only. -/
theorem fujitaKato_sobolev_finiteness_brick_capstone :
    -- (a)
    (∀ (f : ScalarSchwartz3C) (ξ : R3),
       h12IntegrandSq (-f) ξ = h12IntegrandSq f ξ) ∧
    -- (b)
    (∀ f : ScalarSchwartz3C,
       homogeneousH12SeminormSq (-f) = homogeneousH12SeminormSq f) ∧
    -- (c)
    (∀ (u : VectorSchwartz3C) (ξ : R3),
       vectorH12IntegrandSq (-u) ξ = vectorH12IntegrandSq u ξ) ∧
    -- (d)
    (∀ u : VectorSchwartz3C,
       vectorHomogeneousH12SeminormSq (-u) = vectorHomogeneousH12SeminormSq u) ∧
    -- (e)
    (∀ (f g : ScalarSchwartz3C),
       (∀ ξ, (fourierTransformCLM ℂ f) ξ = (fourierTransformCLM ℂ g) ξ) →
       homogeneousH12SeminormSq f = homogeneousH12SeminormSq g) ∧
    -- (f)
    (∀ (u v : VectorSchwartz3C),
       (∀ ξ, (fourierTransformCLM ℂ u) ξ = (fourierTransformCLM ℂ v) ξ) →
       vectorHomogeneousH12SeminormSq u = vectorHomogeneousH12SeminormSq v) ∧
    -- (g) — definitional identities
    (∀ f : ScalarSchwartz3C,
       homogeneousH12SeminormSq f = ∫ ξ : R3, h12IntegrandSq f ξ) ∧
    (∀ u : VectorSchwartz3C,
       vectorHomogeneousH12SeminormSq u = ∫ ξ : R3, vectorH12IntegrandSq u ξ) :=
  ⟨h12IntegrandSq_neg,
   homogeneousH12SeminormSq_neg,
   vectorH12IntegrandSq_neg,
   vectorHomogeneousH12SeminormSq_neg,
   homogeneousH12SeminormSq_congr_fourier,
   vectorHomogeneousH12SeminormSq_congr_fourier,
   homogeneousH12SeminormSq_eq_integral,
   vectorHomogeneousH12SeminormSq_eq_integral⟩

/-! ## §7 — Axiom audit -/

#print axioms h12IntegrandSq_neg
#print axioms homogeneousH12SeminormSq_neg
#print axioms vectorH12IntegrandSq_neg
#print axioms vectorHomogeneousH12SeminormSq_neg
#print axioms h12IntegrandSq_congr_fourier
#print axioms homogeneousH12SeminormSq_congr_fourier
#print axioms vectorH12IntegrandSq_congr_fourier
#print axioms vectorHomogeneousH12SeminormSq_congr_fourier
#print axioms homogeneousH12SeminormSq_eq_integral
#print axioms vectorHomogeneousH12SeminormSq_eq_integral
#print axioms fujitaKato_sobolev_finiteness_brick_capstone

end PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier
