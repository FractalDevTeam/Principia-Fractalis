/-
# Fujita-Kato 1964 — Linearity of Heat Evolution in the Input

★ 2026-06-11 — Adds linearity properties of the frequency-domain
heat-evolution operators in the Schwartz input.

The Fujita-Kato 1964 Picard contraction argument requires the heat
semigroup `e^{tΔ}` to be **linear** in the initial data: for any
scalars `a, b` and inputs `f, g`,

  `e^{tΔ}(a f + b g) = a · e^{tΔ} f + b · e^{tΔ} g`.

At the frequency level this reduces to linearity of
`fourierTransformCLM ℂ` (which is built-in as a continuous linear
map) composed with pointwise multiplication by the heat multiplier,
which preserves both addition and scalar multiplication.

Both scalar and vector versions land here:
  - `heatEvolveFreq` on `ScalarSchwartz3C` (codomain ℂ)
  - `vectorHeatEvolveFreq` on `VectorSchwartz3C` (codomain ℂ³)

Axiom-free; kernel-only `[propext, Classical.choice, Quot.sound]`.

Author: Pablo Cohen (2026-06-11)
-/

import PF.NavierStokes.FujitaKato1964.HeatSemigroupOperator
import PF.NavierStokes.FujitaKato1964.HeatSemigroupVector
import PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier

set_option autoImplicit false

namespace PF.NavierStokes.FujitaKato1964.HeatEvolveLinear

open MeasureTheory SchwartzMap
open PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier
  (R3 C3 VectorSchwartz3C ScalarSchwartz3C)
open PF.NavierStokes.FujitaKato1964.HeatSemigroupFourier (heatMultiplier)
open PF.NavierStokes.FujitaKato1964.HeatSemigroupOperator (heatEvolveFreq)
open PF.NavierStokes.FujitaKato1964.HeatSemigroupVector (vectorHeatEvolveFreq)

/-! ## §1 — Scalar heat-evolve linearity -/

/-- **Heat evolution is additive in the input** (scalar version). -/
theorem heatEvolveFreq_add (t : ℝ) (f g : ScalarSchwartz3C) (ξ : R3) :
    heatEvolveFreq t (f + g) ξ = heatEvolveFreq t f ξ + heatEvolveFreq t g ξ := by
  show (heatMultiplier t ξ : ℂ) * (fourierTransformCLM ℂ (f + g)) ξ
       = (heatMultiplier t ξ : ℂ) * (fourierTransformCLM ℂ f) ξ
       + (heatMultiplier t ξ : ℂ) * (fourierTransformCLM ℂ g) ξ
  rw [map_add]
  show (heatMultiplier t ξ : ℂ) * ((fourierTransformCLM ℂ f) ξ + (fourierTransformCLM ℂ g) ξ)
       = _
  ring

/-- **Heat evolution is ℂ-scalar-linear in the input** (scalar version). -/
theorem heatEvolveFreq_smul (c : ℂ) (t : ℝ) (f : ScalarSchwartz3C) (ξ : R3) :
    heatEvolveFreq t (c • f) ξ = c * heatEvolveFreq t f ξ := by
  show (heatMultiplier t ξ : ℂ) * (fourierTransformCLM ℂ (c • f)) ξ
       = c * ((heatMultiplier t ξ : ℂ) * (fourierTransformCLM ℂ f) ξ)
  rw [map_smul]
  show (heatMultiplier t ξ : ℂ) * (c • (fourierTransformCLM ℂ f)) ξ = _
  rw [SchwartzMap.smul_apply, smul_eq_mul]
  ring

/-! ## §2 — Vector heat-evolve linearity -/

/-- **Vector heat evolution is additive in the input.** -/
theorem vectorHeatEvolveFreq_add
    (t : ℝ) (u v : VectorSchwartz3C) (ξ : R3) :
    vectorHeatEvolveFreq t (u + v) ξ
      = vectorHeatEvolveFreq t u ξ + vectorHeatEvolveFreq t v ξ := by
  show (heatMultiplier t ξ : ℂ) • (fourierTransformCLM ℂ (u + v)) ξ
       = (heatMultiplier t ξ : ℂ) • (fourierTransformCLM ℂ u) ξ
       + (heatMultiplier t ξ : ℂ) • (fourierTransformCLM ℂ v) ξ
  rw [map_add]
  show (heatMultiplier t ξ : ℂ) • ((fourierTransformCLM ℂ u) ξ + (fourierTransformCLM ℂ v) ξ)
       = _
  rw [smul_add]

/-- **Vector heat evolution is ℂ-scalar-linear in the input.** -/
theorem vectorHeatEvolveFreq_smul
    (c : ℂ) (t : ℝ) (u : VectorSchwartz3C) (ξ : R3) :
    vectorHeatEvolveFreq t (c • u) ξ = c • vectorHeatEvolveFreq t u ξ := by
  show (heatMultiplier t ξ : ℂ) • (fourierTransformCLM ℂ (c • u)) ξ
       = c • ((heatMultiplier t ξ : ℂ) • (fourierTransformCLM ℂ u) ξ)
  rw [map_smul]
  show (heatMultiplier t ξ : ℂ) • (c • (fourierTransformCLM ℂ u)) ξ = _
  rw [SchwartzMap.smul_apply]
  rw [smul_comm]

/-! ## §3 — Capstone -/

/-- **★ Heat-evolve linearity brick capstone ★**

Bundles the additivity and scalar-multiplication compatibility of
`heatEvolveFreq` and `vectorHeatEvolveFreq` in the Schwartz input:

  (a) Scalar additive
  (b) Scalar ℂ-linear
  (c) Vector additive
  (d) Vector ℂ-linear

Together: both operators are ℂ-linear maps in their input variable.
This is the linearity the Picard contraction uses to identify the
mild solution as a fixed point of a contraction in the small-data
ball. -/
theorem fujitaKato_heat_evolve_linear_brick_capstone :
    (∀ (t : ℝ) (f g : ScalarSchwartz3C) (ξ : R3),
       heatEvolveFreq t (f + g) ξ = heatEvolveFreq t f ξ + heatEvolveFreq t g ξ) ∧
    (∀ (c : ℂ) (t : ℝ) (f : ScalarSchwartz3C) (ξ : R3),
       heatEvolveFreq t (c • f) ξ = c * heatEvolveFreq t f ξ) ∧
    (∀ (t : ℝ) (u v : VectorSchwartz3C) (ξ : R3),
       vectorHeatEvolveFreq t (u + v) ξ
         = vectorHeatEvolveFreq t u ξ + vectorHeatEvolveFreq t v ξ) ∧
    (∀ (c : ℂ) (t : ℝ) (u : VectorSchwartz3C) (ξ : R3),
       vectorHeatEvolveFreq t (c • u) ξ = c • vectorHeatEvolveFreq t u ξ) :=
  ⟨heatEvolveFreq_add,
   heatEvolveFreq_smul,
   vectorHeatEvolveFreq_add,
   vectorHeatEvolveFreq_smul⟩

/-! ## §4 — Axiom audit -/

#print axioms heatEvolveFreq_add
#print axioms heatEvolveFreq_smul
#print axioms vectorHeatEvolveFreq_add
#print axioms vectorHeatEvolveFreq_smul
#print axioms fujitaKato_heat_evolve_linear_brick_capstone

end PF.NavierStokes.FujitaKato1964.HeatEvolveLinear
