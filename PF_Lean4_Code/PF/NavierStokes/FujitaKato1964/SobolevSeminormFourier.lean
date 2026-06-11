/-
# Fujita-Kato 1964 — Real Homogeneous Sobolev Ḣ^{1/2} Seminorm via Fourier

★ 2026-06-10 — First brick of real Fujita-Kato infrastructure.
★ Wire mathlib `SchwartzMap.fourierTransformCLM` into the framework.

The Fujita-Kato 1964 theorem requires the homogeneous Sobolev space
`Ḣ^{1/2}(ℝ³)`. The genuine seminorm squared is

  ‖u‖²_{Ḣ^{1/2}} = ∫ |ξ| · |û(ξ)|² dξ

where û is the Fourier transform of u.

The existing `PF/NavierStokes/FujitaKato1964HomogeneousSobolev.lean`
defines only a structural surrogate predicate `∀ x, ‖u x‖ ≤ M`
that captures the pointwise L∞ bound, not the Sobolev seminorm.
That surrogate cannot drive a genuine Fujita-Kato proof.

This file provides the **real** Fourier-based seminorm at the scalar
complex Schwartz layer, using mathlib's `SchwartzMap.fourierTransformCLM`
directly. No surrogate. Real content.

Scope: scalar (ℂ-valued) Schwartz on `EuclideanSpace ℝ (Fin 3)`.
The vector-valued `(Fin 3 → ℂ)` case extends componentwise; the
bridge to the existing surrogate, the scaling identity
`‖c • f‖² = ‖c‖² · ‖f‖²`, and finiteness on Schwartz inputs live
in follow-on files in this directory.

Axiom-free under `[propext, Classical.choice, Quot.sound]` only.

Author: Pablo Cohen (framework + formalization, 2026-06-10)
-/

import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

namespace PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier

open MeasureTheory SchwartzMap

/-! ## §1 — Type aliases -/

/-- Three-dimensional Euclidean frequency space, used both as the
spatial domain `x ∈ ℝ³` and as the dual frequency domain `ξ ∈ ℝ³`. -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-- Complex-valued Schwartz functions on ℝ³. The Fourier transform
of such a function lives in the same space (Schwartz space is
invariant under Fourier). -/
abbrev ScalarSchwartz3C : Type := SchwartzMap R3 ℂ

/-! ## §2 — Pointwise integrand -/

/-- **Pointwise integrand of the homogeneous Ḣ^{1/2} seminorm squared.**

For a Schwartz function `f : ℝ³ → ℂ` and frequency `ξ ∈ ℝ³`, the
integrand is

  `|ξ| · |f̂(ξ)|²`

Integrating over `ξ ∈ ℝ³` against Lebesgue measure gives the
homogeneous `Ḣ^{1/2}` seminorm squared. -/
noncomputable def h12IntegrandSq (f : ScalarSchwartz3C) (ξ : R3) : ℝ :=
  ‖ξ‖ * ‖(fourierTransformCLM ℂ f) ξ‖ ^ 2

/-- **The integrand is pointwise non-negative**: `|ξ| ≥ 0` and
`|f̂(ξ)|² ≥ 0`. -/
theorem h12IntegrandSq_nonneg (f : ScalarSchwartz3C) (ξ : R3) :
    0 ≤ h12IntegrandSq f ξ :=
  mul_nonneg (norm_nonneg _) (sq_nonneg _)

/-- **For the zero Schwartz function, the integrand vanishes
identically**: the Fourier transform of zero is zero, so
`|f̂(ξ)|² = 0`. -/
theorem h12IntegrandSq_zero (ξ : R3) :
    h12IntegrandSq (0 : ScalarSchwartz3C) ξ = 0 := by
  unfold h12IntegrandSq
  rw [map_zero, SchwartzMap.zero_apply, norm_zero]
  ring

/-! ## §3 — Sobolev seminorm squared -/

/-- **Homogeneous Ḣ^{1/2} seminorm squared on scalar complex Schwartz.**

  `‖f‖²_{Ḣ^{1/2}} := ∫ |ξ| · |f̂(ξ)|² dξ`

The integral is taken over all of ℝ³ with respect to the Lebesgue
volume measure. This is the GENUINE Sobolev seminorm squared, not
a substrate surrogate. -/
noncomputable def homogeneousH12SeminormSq (f : ScalarSchwartz3C) : ℝ :=
  ∫ ξ : R3, h12IntegrandSq f ξ

/-- **The homogeneous Ḣ^{1/2} seminorm squared is non-negative**
for any scalar Schwartz function. -/
theorem homogeneousH12SeminormSq_nonneg (f : ScalarSchwartz3C) :
    0 ≤ homogeneousH12SeminormSq f := by
  unfold homogeneousH12SeminormSq
  exact MeasureTheory.integral_nonneg (fun ξ => h12IntegrandSq_nonneg f ξ)

/-- **The Sobolev seminorm squared of the zero function is zero**:
the integrand vanishes identically, so the integral vanishes. -/
theorem homogeneousH12SeminormSq_zero :
    homogeneousH12SeminormSq (0 : ScalarSchwartz3C) = 0 := by
  unfold homogeneousH12SeminormSq
  simp only [h12IntegrandSq_zero, integral_zero]

/-! ## §4 — Capstone -/

/-- **★ First Fujita-Kato real-infrastructure brick capstone ★**

Bundles the four results of this file:

  (a) Pointwise non-negativity of the Sobolev integrand
  (b) Pointwise vanishing of the integrand on the zero input
  (c) Non-negativity of the Sobolev seminorm squared
  (d) Vanishing of the Sobolev seminorm squared on the zero input

This is REAL Sobolev content built on mathlib's
`SchwartzMap.fourierTransformCLM`. The genuine homogeneous `Ḣ^{1/2}`
seminorm squared is integrated over `ℝ³`. No substrate surrogate.

Axiom-free: depends on `[propext, Classical.choice, Quot.sound]` only. -/
theorem fujitaKato_sobolev_fourier_brick_capstone :
    -- (a) Integrand non-negativity
    (∀ f ξ, 0 ≤ h12IntegrandSq f ξ) ∧
    -- (b) Integrand zero at zero input
    (∀ ξ, h12IntegrandSq (0 : ScalarSchwartz3C) ξ = 0) ∧
    -- (c) Seminorm non-negativity
    (∀ f, 0 ≤ homogeneousH12SeminormSq f) ∧
    -- (d) Seminorm zero at zero input
    (homogeneousH12SeminormSq (0 : ScalarSchwartz3C) = 0) :=
  ⟨h12IntegrandSq_nonneg,
   h12IntegrandSq_zero,
   homogeneousH12SeminormSq_nonneg,
   homogeneousH12SeminormSq_zero⟩

/-! ## §5 — Axiom audit -/

#print axioms h12IntegrandSq_nonneg
#print axioms h12IntegrandSq_zero
#print axioms homogeneousH12SeminormSq_nonneg
#print axioms homogeneousH12SeminormSq_zero
#print axioms fujitaKato_sobolev_fourier_brick_capstone

end PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier
