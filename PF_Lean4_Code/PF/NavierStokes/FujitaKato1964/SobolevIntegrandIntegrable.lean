/-
# Fujita-Kato 1964 — Integrability of the Homogeneous Ḣ^{1/2} Integrand on Schwartz Inputs

★ 2026-06-10 — Schwartz integrability brick of the Fujita-Kato Sobolev ladder.
★ Discharges the conditional `homogeneousH12SeminormSqOfHeatEvolved_le_under_integrability`
  in `HeatContractsSobolev.lean` to an unconditional contraction bound.

The brick `HeatContractsSobolev.lean` exposes the heat-semigroup
contraction of the homogeneous Sobolev `Ḣ^{1/2}` seminorm squared at
the frequency-domain image level CONDITIONAL on integrability of the
comparison RHS `h12IntegrandSq f`:

  `∫ ‖ξ‖ · ‖heatEvolveFreq t f ξ‖² dξ ≤ ∫ ‖ξ‖ · ‖(F f) ξ‖² dξ`

The integrability hypothesis is the genuine weighted-decay statement
on Schwartz inputs.  This file closes it.

Mathematical content: `F f` is itself a Schwartz function via
`SchwartzMap.fourierTransformCLM`. Schwartz functions decay faster than
any polynomial, so for any Schwartz `g`,

  `Integrable (fun ξ => ‖ξ‖ * ‖g ξ‖)`    -- `mathlib`'s `integrable_pow_mul` at k=1
  `‖g ξ‖ ≤ (seminorm 0 0) g` uniformly  -- `mathlib`'s `norm_le_seminorm`

Multiplying the two gives

  `‖ξ‖ * ‖g ξ‖² ≤ (seminorm 0 0 g) * (‖ξ‖ * ‖g ξ‖)`

which is `(integrable scalar) * (integrable function)`, hence integrable.
Applied to `g := F f` this yields integrability of `h12IntegrandSq f`.

The volume measure on `EuclideanSpace ℝ (Fin 3)` is an additive Haar
measure, so the `MeasureTheory.Measure.HasTemperateGrowth` instance fires
automatically, and `integrable_pow_mul` applies.

Scope: scalar (`ℂ`-valued) Schwartz on `EuclideanSpace ℝ (Fin 3)`.

Builds on:
  * `PF/NavierStokes/FujitaKato1964/SobolevSeminormFourier.lean`
  * `PF/NavierStokes/FujitaKato1964/HeatContractsSobolev.lean`

Axiom-free under `[propext, Classical.choice, Quot.sound]` only.

Author: Pablo Cohen (framework + formalization, 2026-06-10)
-/

import PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier
import PF.NavierStokes.FujitaKato1964.HeatContractsSobolev
import Mathlib.MeasureTheory.Function.L1Space.Integrable

set_option autoImplicit false

namespace PF.NavierStokes.FujitaKato1964.SobolevIntegrandIntegrable

open MeasureTheory SchwartzMap
open PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier
  (R3 ScalarSchwartz3C h12IntegrandSq h12IntegrandSq_nonneg
   h12IntegrandSq_zero homogeneousH12SeminormSq)
open PF.NavierStokes.FujitaKato1964.HeatContractsSobolev
  (h12IntegrandSqOfHeatEvolved homogeneousH12SeminormSqOfHeatEvolved
   homogeneousH12SeminormSqOfHeatEvolved_le_under_integrability)

/-! ## §1 — Trivial integrability at the zero Schwartz input -/

/-- **At the zero Schwartz input the Sobolev integrand is identically zero,
hence trivially integrable.**

The Fourier transform of the zero function is zero, so the integrand
`‖ξ‖ * ‖(F 0) ξ‖²` vanishes everywhere, and the constant-zero function
is integrable for any measure.

This is the unconditional zero-input case; it requires no Schwartz-decay
machinery. -/
theorem h12IntegrandSq_integrable_at_zero :
    MeasureTheory.Integrable (h12IntegrandSq (0 : ScalarSchwartz3C)) := by
  -- The integrand at zero input is the constant zero function.
  have hzero : h12IntegrandSq (0 : ScalarSchwartz3C) = fun _ => (0 : ℝ) := by
    funext ξ
    exact h12IntegrandSq_zero ξ
  rw [hzero]
  exact MeasureTheory.integrable_zero R3 ℝ _

/-! ## §2 — Transfer of integrability across equal Fourier transforms -/

/-- **Pointwise equality of Fourier transforms transfers integrability
of the Sobolev integrand.**

If `f₁` and `f₂` have the same Fourier transform pointwise, then
`h12IntegrandSq f₁ ξ = h12IntegrandSq f₂ ξ` pointwise, hence integrability
of either implies integrability of the other. -/
theorem h12IntegrandSq_integrable_congr_fourier
    (f₁ f₂ : ScalarSchwartz3C)
    (h : ∀ ξ, (fourierTransformCLM ℂ f₁) ξ = (fourierTransformCLM ℂ f₂) ξ) :
    MeasureTheory.Integrable (h12IntegrandSq f₁) ↔
      MeasureTheory.Integrable (h12IntegrandSq f₂) := by
  have hpt : h12IntegrandSq f₁ = h12IntegrandSq f₂ := by
    funext ξ
    unfold h12IntegrandSq
    rw [h ξ]
  rw [hpt]

/-! ## §3 — General Schwartz integrability of the Ḣ^{1/2} integrand -/

/-- **The Sobolev integrand `h12IntegrandSq f` is integrable for any
scalar complex Schwartz `f`.**

Proof. Let `g := fourierTransformCLM ℂ f : 𝓢(ℝ³, ℂ)` be the Fourier
transform of `f`; it is itself a Schwartz function. We show

  `∀ ξ, ‖ξ‖ * ‖g ξ‖^2 ≤ M * (‖ξ‖ * ‖g ξ‖)`         (★)

where `M := (SchwartzMap.seminorm ℝ 0 0) g`. The mathlib lemma
`SchwartzMap.norm_le_seminorm` gives `‖g ξ‖ ≤ M` pointwise, so

  `‖ξ‖ * ‖g ξ‖^2 = (‖ξ‖ * ‖g ξ‖) * ‖g ξ‖ ≤ (‖ξ‖ * ‖g ξ‖) * M`.

The RHS of (★) is integrable because

  * `(fun ξ => ‖ξ‖ * ‖g ξ‖)` is integrable: it equals
    `fun ξ => ‖ξ‖^1 * ‖g ξ‖`, and mathlib's
    `SchwartzMap.integrable_pow_mul` gives this for any Schwartz function
    `g` against any measure with temperate growth (here the volume
    measure on `EuclideanSpace ℝ (Fin 3)`, which is an additive Haar
    measure hence has temperate growth automatically).
  * Multiplying by the constant `M` preserves integrability.

The LHS of (★) is non-negative (`h12IntegrandSq_nonneg`), measurable
(continuity of `g` plus the norm and product maps), and bounded above
by an integrable function. So it is integrable by
`MeasureTheory.Integrable.mono'`. -/
theorem h12IntegrandSq_integrable_general (f : ScalarSchwartz3C) :
    MeasureTheory.Integrable (h12IntegrandSq f) := by
  -- The Fourier transform of `f` is a Schwartz function.
  set g : SchwartzMap R3 ℂ := fourierTransformCLM ℂ f with hg
  -- Uniform pointwise bound on `g`.
  set M : ℝ := (SchwartzMap.seminorm ℝ 0 0) g with hM
  -- `‖ξ‖ * ‖g ξ‖` is integrable (mathlib).
  have hweighted : MeasureTheory.Integrable
      (fun ξ : R3 => ‖ξ‖ ^ 1 * ‖g ξ‖) :=
    SchwartzMap.integrable_pow_mul (μ := (volume : Measure R3)) g 1
  -- Multiplying by the constant `M` preserves integrability.
  have hMajor : MeasureTheory.Integrable
      (fun ξ : R3 => (‖ξ‖ ^ 1 * ‖g ξ‖) * M) :=
    hweighted.mul_const M
  -- Pointwise bound: `‖ξ‖ * ‖g ξ‖^2 ≤ (‖ξ‖^1 * ‖g ξ‖) * M`.
  have hbound : ∀ ξ : R3,
      ‖h12IntegrandSq f ξ‖ ≤ (‖ξ‖ ^ 1 * ‖g ξ‖) * M := by
    intro ξ
    -- `h12IntegrandSq f ξ ≥ 0` so its norm equals itself.
    have hnn : 0 ≤ h12IntegrandSq f ξ := h12IntegrandSq_nonneg f ξ
    rw [Real.norm_of_nonneg hnn]
    -- Unfold the integrand.
    unfold h12IntegrandSq
    -- Rewrite `‖(F f) ξ‖` as `‖g ξ‖`.
    show ‖ξ‖ * ‖g ξ‖ ^ 2 ≤ (‖ξ‖ ^ 1 * ‖g ξ‖) * M
    -- Algebra: ‖ξ‖ * ‖g ξ‖^2 = (‖ξ‖^1 * ‖g ξ‖) * ‖g ξ‖.
    have hrw : ‖ξ‖ * ‖g ξ‖ ^ 2 = (‖ξ‖ ^ 1 * ‖g ξ‖) * ‖g ξ‖ := by ring
    rw [hrw]
    -- Reduce to: ‖g ξ‖ ≤ M and the prefactor is non-negative.
    have hg_le : ‖g ξ‖ ≤ M := SchwartzMap.norm_le_seminorm ℝ g ξ
    have hpre_nn : 0 ≤ ‖ξ‖ ^ 1 * ‖g ξ‖ :=
      mul_nonneg (by positivity) (norm_nonneg _)
    exact mul_le_mul_of_nonneg_left hg_le hpre_nn
  -- Strong measurability of the integrand: continuity of the squared
  -- norm composed with the continuous Schwartz `g`, times `‖ξ‖`.
  have hcont : Continuous (h12IntegrandSq f) := by
    unfold h12IntegrandSq
    have hgc : Continuous (fun ξ : R3 => (fourierTransformCLM ℂ f) ξ) :=
      g.continuous
    refine continuous_norm.mul ?_
    exact (continuous_norm.comp hgc).pow 2
  have hmeas : AEStronglyMeasurable (h12IntegrandSq f) (volume : Measure R3) :=
    hcont.aestronglyMeasurable
  -- Dominated by an integrable function ⇒ integrable.
  exact hMajor.mono' hmeas
    (Filter.Eventually.of_forall hbound)

/-! ## §4 — Unconditional heat-semigroup Ḣ^{1/2} contraction -/

/-- **Unconditional heat-semigroup contraction of the Ḣ^{1/2} seminorm
squared at the frequency-domain image level.**

For any `t ≥ 0` and any scalar Schwartz `f`,

  `homogeneousH12SeminormSqOfHeatEvolved t f ≤ homogeneousH12SeminormSq f`.

This discharges the conditional version
`homogeneousH12SeminormSqOfHeatEvolved_le_under_integrability` by
supplying the integrability hypothesis from §3.

This is the unconditional linear-propagator dissipation step of
Fujita-Kato 1964: heat is dissipative, so it cannot grow the
homogeneous Sobolev seminorm of the data, without any extra hypothesis
on the Schwartz input. -/
theorem homogeneousH12SeminormSqOfHeatEvolved_le_unconditional
    (t : ℝ) (ht : 0 ≤ t) (f : ScalarSchwartz3C) :
    homogeneousH12SeminormSqOfHeatEvolved t f
      ≤ homogeneousH12SeminormSq f :=
  homogeneousH12SeminormSqOfHeatEvolved_le_under_integrability t ht f
    (h12IntegrandSq_integrable_general f)

/-! ## §5 — Capstone -/

/-- **★ Fujita-Kato Schwartz Sobolev integrability brick capstone ★**

Bundles the four results of this file:

  (a) Trivial integrability at the zero Schwartz input
  (b) Transfer of integrability across equal Fourier transforms
  (c) General Schwartz integrability of the `Ḣ^{1/2}` integrand
  (d) Unconditional heat-semigroup `Ḣ^{1/2}` contraction at the
      frequency-domain image level

Item (c) is the genuine weighted-decay finiteness statement on Schwartz
inputs, built directly on mathlib's `SchwartzMap.integrable_pow_mul`
and `SchwartzMap.norm_le_seminorm`. Item (d) discharges the conditional
contraction bound from `HeatContractsSobolev.lean` to an unconditional
one, closing the linear-propagator dissipation step of Fujita-Kato 1964
on Schwartz data.

Axiom-free: depends on `[propext, Classical.choice, Quot.sound]` only. -/
theorem fujitaKato_sobolev_integrand_integrable_brick_capstone :
    -- (a) Trivial integrability at zero input
    MeasureTheory.Integrable (h12IntegrandSq (0 : ScalarSchwartz3C)) ∧
    -- (b) Transfer across equal Fourier transforms
    (∀ (f₁ f₂ : ScalarSchwartz3C),
       (∀ ξ, (fourierTransformCLM ℂ f₁) ξ = (fourierTransformCLM ℂ f₂) ξ) →
       (MeasureTheory.Integrable (h12IntegrandSq f₁) ↔
        MeasureTheory.Integrable (h12IntegrandSq f₂))) ∧
    -- (c) General Schwartz integrability
    (∀ f : ScalarSchwartz3C, MeasureTheory.Integrable (h12IntegrandSq f)) ∧
    -- (d) Unconditional heat-semigroup contraction
    (∀ (t : ℝ), 0 ≤ t → ∀ (f : ScalarSchwartz3C),
       homogeneousH12SeminormSqOfHeatEvolved t f
         ≤ homogeneousH12SeminormSq f) :=
  ⟨h12IntegrandSq_integrable_at_zero,
   h12IntegrandSq_integrable_congr_fourier,
   h12IntegrandSq_integrable_general,
   homogeneousH12SeminormSqOfHeatEvolved_le_unconditional⟩

/-! ## §6 — Axiom audit -/

#print axioms h12IntegrandSq_integrable_at_zero
#print axioms h12IntegrandSq_integrable_congr_fourier
#print axioms h12IntegrandSq_integrable_general
#print axioms homogeneousH12SeminormSqOfHeatEvolved_le_unconditional
#print axioms fujitaKato_sobolev_integrand_integrable_brick_capstone

end PF.NavierStokes.FujitaKato1964.SobolevIntegrandIntegrable
