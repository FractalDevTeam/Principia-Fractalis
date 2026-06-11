/-
# Fujita-Kato 1964 — Integrability of the Vector Homogeneous Ḣ^{1/2} Integrand on Vector Schwartz Inputs

★ 2026-06-10 — Vector lift of the Schwartz integrability brick of the
  Fujita-Kato Sobolev ladder.
★ Discharges the conditional
  `vectorHomogeneousH12SeminormSqOfHeatEvolved_le_under_integrability`
  in `VectorHeatContractsSobolev.lean` to an unconditional vector
  contraction bound.

The brick `VectorHeatContractsSobolev.lean` exposes the vector
heat-semigroup contraction of the homogeneous vector Sobolev `Ḣ^{1/2}`
seminorm squared at the frequency-domain image level CONDITIONAL on
integrability of the comparison RHS `vectorH12IntegrandSq u`:

  `∫ ‖ξ‖ · ‖vectorHeatEvolveFreq t u ξ‖²_{ℂ³} dξ
        ≤ ∫ ‖ξ‖ · ‖(F u) ξ‖²_{ℂ³} dξ`

The integrability hypothesis is the genuine vector weighted-decay
statement on vector Schwartz inputs. This file closes it.

Mathematical content (mechanical componentwise lift of the scalar
template `SobolevIntegrandIntegrable.lean`): `F u` is itself a Schwartz
function via `SchwartzMap.fourierTransformCLM`, now landing in the
vector target `EuclideanSpace ℂ (Fin 3)`. Schwartz functions decay
faster than any polynomial, so for any vector Schwartz `g`,

  `Integrable (fun ξ => ‖ξ‖ * ‖g ξ‖)`    -- `mathlib`'s `integrable_pow_mul` at k=1
  `‖g ξ‖ ≤ (seminorm 0 0) g` uniformly  -- `mathlib`'s `norm_le_seminorm`

Multiplying the two gives

  `‖ξ‖ * ‖g ξ‖² ≤ (seminorm 0 0 g) * (‖ξ‖ * ‖g ξ‖)`

which is `(integrable scalar) * (integrable function)`, hence integrable.
Applied to `g := F u` this yields integrability of `vectorH12IntegrandSq u`.

The volume measure on `EuclideanSpace ℝ (Fin 3)` is an additive Haar
measure, so the `MeasureTheory.Measure.HasTemperateGrowth` instance fires
automatically, and `integrable_pow_mul` applies. The Schwartz codomain
change `ℂ → EuclideanSpace ℂ (Fin 3)` does not affect the typeclass
hypotheses of `integrable_pow_mul` or `norm_le_seminorm` — both
parameterize over the codomain as a `NormedAddCommGroup` (here also
`NormedSpace ℝ`), which `EuclideanSpace ℂ (Fin 3)` satisfies.

Scope: vector (`ℂ³`-valued) Schwartz on `EuclideanSpace ℝ (Fin 3)`.
Mechanical componentwise lift of the scalar
`SobolevIntegrandIntegrable.lean`. This is the form Navier-Stokes
consumes after complexification of the velocity field.

Builds on:
  * `PF/NavierStokes/FujitaKato1964/SobolevSeminormVector.lean`
  * `PF/NavierStokes/FujitaKato1964/VectorHeatContractsSobolev.lean`

Axiom-free under `[propext, Classical.choice, Quot.sound]` only.

Author: Pablo Cohen (framework + formalization, 2026-06-10)
-/

import PF.NavierStokes.FujitaKato1964.SobolevSeminormVector
import PF.NavierStokes.FujitaKato1964.VectorHeatContractsSobolev
import Mathlib.MeasureTheory.Function.L1Space.Integrable

set_option autoImplicit false

namespace PF.NavierStokes.FujitaKato1964.VectorSobolevIntegrandIntegrable

open MeasureTheory SchwartzMap
open PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier
  (R3 C3 VectorSchwartz3C vectorH12IntegrandSq vectorH12IntegrandSq_nonneg
   vectorH12IntegrandSq_zero vectorHomogeneousH12SeminormSq)
open PF.NavierStokes.FujitaKato1964.VectorHeatContractsSobolev
  (vectorH12IntegrandSqOfHeatEvolved vectorHomogeneousH12SeminormSqOfHeatEvolved
   vectorHomogeneousH12SeminormSqOfHeatEvolved_le_under_integrability)

/-! ## §1 — Trivial integrability at the zero vector Schwartz input -/

/-- **At the zero vector Schwartz input the vector Sobolev integrand is
identically zero, hence trivially integrable.**

The Fourier transform of the zero vector field is zero, so the integrand
`‖ξ‖ * ‖(F 0) ξ‖²_{ℂ³}` vanishes everywhere, and the constant-zero
function is integrable for any measure.

This is the unconditional zero-input case; it requires no Schwartz-decay
machinery. Mechanical componentwise lift of the scalar
`h12IntegrandSq_integrable_at_zero`. -/
theorem vectorH12IntegrandSq_integrable_at_zero :
    MeasureTheory.Integrable (vectorH12IntegrandSq (0 : VectorSchwartz3C)) := by
  -- The integrand at zero input is the constant zero function.
  have hzero : vectorH12IntegrandSq (0 : VectorSchwartz3C) = fun _ => (0 : ℝ) := by
    funext ξ
    exact vectorH12IntegrandSq_zero ξ
  rw [hzero]
  exact MeasureTheory.integrable_zero R3 ℝ _

/-! ## §2 — Transfer of integrability across equal Fourier transforms -/

/-- **Pointwise equality of vector Fourier transforms transfers
integrability of the vector Sobolev integrand.**

If `u₁` and `u₂` have the same Fourier transform pointwise, then
`vectorH12IntegrandSq u₁ ξ = vectorH12IntegrandSq u₂ ξ` pointwise, hence
integrability of either implies integrability of the other. Mechanical
componentwise lift of the scalar
`h12IntegrandSq_integrable_congr_fourier`. -/
theorem vectorH12IntegrandSq_integrable_congr_fourier
    (u₁ u₂ : VectorSchwartz3C)
    (h : ∀ ξ, (fourierTransformCLM ℂ u₁) ξ = (fourierTransformCLM ℂ u₂) ξ) :
    MeasureTheory.Integrable (vectorH12IntegrandSq u₁) ↔
      MeasureTheory.Integrable (vectorH12IntegrandSq u₂) := by
  have hpt : vectorH12IntegrandSq u₁ = vectorH12IntegrandSq u₂ := by
    funext ξ
    unfold vectorH12IntegrandSq
    rw [h ξ]
  rw [hpt]

/-! ## §3 — General vector Schwartz integrability of the Ḣ^{1/2} integrand -/

/-- **The vector Sobolev integrand `vectorH12IntegrandSq u` is integrable
for any vector complex Schwartz `u`.**

Proof. Let `g := fourierTransformCLM ℂ u : 𝓢(ℝ³, ℂ³)` be the Fourier
transform of `u`; it is itself a Schwartz function (now landing in the
vector codomain `EuclideanSpace ℂ (Fin 3)`). We show

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
    measure hence has temperate growth automatically). The lemma
    parameterizes over the Schwartz codomain as a `NormedAddCommGroup`
    plus `NormedSpace ℝ`; `EuclideanSpace ℂ (Fin 3)` satisfies both.
  * Multiplying by the constant `M` preserves integrability.

The LHS of (★) is non-negative (`vectorH12IntegrandSq_nonneg`),
measurable (continuity of `g` plus the norm and product maps), and
bounded above by an integrable function. So it is integrable by
`MeasureTheory.Integrable.mono'`. Mechanical componentwise lift of the
scalar `h12IntegrandSq_integrable_general`. -/
theorem vectorH12IntegrandSq_integrable_general (u : VectorSchwartz3C) :
    MeasureTheory.Integrable (vectorH12IntegrandSq u) := by
  -- The Fourier transform of `u` is a vector Schwartz function.
  set g : SchwartzMap R3 C3 := fourierTransformCLM ℂ u with hg
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
      ‖vectorH12IntegrandSq u ξ‖ ≤ (‖ξ‖ ^ 1 * ‖g ξ‖) * M := by
    intro ξ
    -- `vectorH12IntegrandSq u ξ ≥ 0` so its norm equals itself.
    have hnn : 0 ≤ vectorH12IntegrandSq u ξ := vectorH12IntegrandSq_nonneg u ξ
    rw [Real.norm_of_nonneg hnn]
    -- Unfold the integrand.
    unfold vectorH12IntegrandSq
    -- Rewrite `‖(F u) ξ‖` as `‖g ξ‖`.
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
  -- norm composed with the continuous vector Schwartz `g`, times `‖ξ‖`.
  have hcont : Continuous (vectorH12IntegrandSq u) := by
    unfold vectorH12IntegrandSq
    have hgc : Continuous (fun ξ : R3 => (fourierTransformCLM ℂ u) ξ) :=
      g.continuous
    refine continuous_norm.mul ?_
    exact (continuous_norm.comp hgc).pow 2
  have hmeas : AEStronglyMeasurable (vectorH12IntegrandSq u) (volume : Measure R3) :=
    hcont.aestronglyMeasurable
  -- Dominated by an integrable function ⇒ integrable.
  exact hMajor.mono' hmeas
    (Filter.Eventually.of_forall hbound)

/-! ## §4 — Unconditional vector heat-semigroup Ḣ^{1/2} contraction -/

/-- **Unconditional vector heat-semigroup contraction of the Ḣ^{1/2}
seminorm squared at the frequency-domain image level.**

For any `t ≥ 0` and any vector Schwartz `u`,

  `vectorHomogeneousH12SeminormSqOfHeatEvolved t u
        ≤ vectorHomogeneousH12SeminormSq u`.

This discharges the conditional version
`vectorHomogeneousH12SeminormSqOfHeatEvolved_le_under_integrability` by
supplying the integrability hypothesis from §3.

This is the unconditional vector linear-propagator dissipation step of
Fujita-Kato 1964 — the version Navier-Stokes actually consumes after
complexification of the velocity field: heat is dissipative, so it
cannot grow the homogeneous vector Sobolev seminorm of the data, without
any extra hypothesis on the vector Schwartz input. Mechanical
componentwise lift of the scalar
`homogeneousH12SeminormSqOfHeatEvolved_le_unconditional`. -/
theorem vectorHomogeneousH12SeminormSqOfHeatEvolved_le_unconditional
    (t : ℝ) (ht : 0 ≤ t) (u : VectorSchwartz3C) :
    vectorHomogeneousH12SeminormSqOfHeatEvolved t u
      ≤ vectorHomogeneousH12SeminormSq u :=
  vectorHomogeneousH12SeminormSqOfHeatEvolved_le_under_integrability t ht u
    (vectorH12IntegrandSq_integrable_general u)

/-! ## §5 — Capstone -/

/-- **★ Fujita-Kato vector Schwartz Sobolev integrability brick capstone ★**

Bundles the four results of this file:

  (a) Trivial integrability at the zero vector Schwartz input
  (b) Transfer of integrability across equal vector Fourier transforms
  (c) General vector Schwartz integrability of the `Ḣ^{1/2}` integrand
  (d) Unconditional vector heat-semigroup `Ḣ^{1/2}` contraction at the
      frequency-domain image level

Item (c) is the genuine vector weighted-decay finiteness statement on
vector Schwartz inputs, built directly on mathlib's
`SchwartzMap.integrable_pow_mul` and `SchwartzMap.norm_le_seminorm`
applied to the vector-codomain Schwartz space. Item (d) discharges the
conditional contraction bound from `VectorHeatContractsSobolev.lean` to
an unconditional one, closing the vector linear-propagator dissipation
step of Fujita-Kato 1964 on vector Schwartz data — the version
Navier-Stokes consumes.

Mechanical componentwise lift of the scalar
`fujitaKato_sobolev_integrand_integrable_brick_capstone` of
`SobolevIntegrandIntegrable.lean`.

Axiom-free: depends on `[propext, Classical.choice, Quot.sound]` only. -/
theorem fujitaKato_vector_sobolev_integrand_integrable_brick_capstone :
    -- (a) Trivial integrability at zero input
    MeasureTheory.Integrable (vectorH12IntegrandSq (0 : VectorSchwartz3C)) ∧
    -- (b) Transfer across equal Fourier transforms
    (∀ (u₁ u₂ : VectorSchwartz3C),
       (∀ ξ, (fourierTransformCLM ℂ u₁) ξ = (fourierTransformCLM ℂ u₂) ξ) →
       (MeasureTheory.Integrable (vectorH12IntegrandSq u₁) ↔
        MeasureTheory.Integrable (vectorH12IntegrandSq u₂))) ∧
    -- (c) General vector Schwartz integrability
    (∀ u : VectorSchwartz3C, MeasureTheory.Integrable (vectorH12IntegrandSq u)) ∧
    -- (d) Unconditional vector heat-semigroup contraction
    (∀ (t : ℝ), 0 ≤ t → ∀ (u : VectorSchwartz3C),
       vectorHomogeneousH12SeminormSqOfHeatEvolved t u
         ≤ vectorHomogeneousH12SeminormSq u) :=
  ⟨vectorH12IntegrandSq_integrable_at_zero,
   vectorH12IntegrandSq_integrable_congr_fourier,
   vectorH12IntegrandSq_integrable_general,
   vectorHomogeneousH12SeminormSqOfHeatEvolved_le_unconditional⟩

/-! ## §6 — Axiom audit -/

#print axioms vectorH12IntegrandSq_integrable_at_zero
#print axioms vectorH12IntegrandSq_integrable_congr_fourier
#print axioms vectorH12IntegrandSq_integrable_general
#print axioms vectorHomogeneousH12SeminormSqOfHeatEvolved_le_unconditional
#print axioms fujitaKato_vector_sobolev_integrand_integrable_brick_capstone

end PF.NavierStokes.FujitaKato1964.VectorSobolevIntegrandIntegrable
