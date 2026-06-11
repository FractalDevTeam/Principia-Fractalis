/-
# Fujita-Kato 1964 — Heat Evolution Preserves Fourier-Divergence-Freeness

★ 2026-06-11 — Bridge between the vector heat-evolution operator
and the Fourier-side divergence-free predicate.

For a vector Schwartz field `u : VectorSchwartz3C` whose Fourier
transform is divergence-free in the Fourier-side sense
(`IsFourierDivFree (fun ξ => (SchwartzMap.fourierTransformCLM ℂ u) ξ)`),
the heat-evolved frequency-domain image `vectorHeatEvolveFreq t u`
is also divergence-free at every time `t : ℝ`.

The reason: heat evolution at the frequency level is **pointwise
scalar multiplication** by the heat multiplier `heatMultiplier t ξ`
(a real coerced to complex). Divergence-freeness in the Fourier
sense is the perpendicularity of `w ξ` to `complexifyVec ξ` (under
the Hermitian inner product), which is preserved under scalar
multiplication on the right by `inner_smul_right`.

This bridge connects three previously-landed bricks:
  - `HeatSemigroupVector.vectorHeatEvolveFreq` (the operator)
  - `FourierDivFree.IsFourierDivFree` (the predicate)
  - `LerayProjectorOperator.complexifyVec` (the embedding)

Physical interpretation: the heat semigroup respects the
divergence-free subspace. This is the property the Fujita-Kato 1964
contraction argument uses to keep the velocity field
divergence-free for all time once the initial datum is.

Axiom-free under `[propext, Classical.choice, Quot.sound]` only.

Author: Pablo Cohen (2026-06-11)
-/

import PF.NavierStokes.FujitaKato1964.HeatSemigroupVector
import PF.NavierStokes.FujitaKato1964.FourierDivFree

set_option autoImplicit false

namespace PF.NavierStokes.FujitaKato1964.HeatPreservesDivFree

open MeasureTheory SchwartzMap
open PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier (R3 C3 VectorSchwartz3C)
open PF.NavierStokes.FujitaKato1964.LerayProjectorOperator (complexifyVec)
open PF.NavierStokes.FujitaKato1964.HeatSemigroupVector (vectorHeatEvolveFreq)
open PF.NavierStokes.FujitaKato1964.FourierDivFree (IsFourierDivFree)

/-! ## §1 — Heat evolution preserves Fourier-divergence-freeness -/

/-- **★ Heat evolution preserves Fourier-divergence-freeness.**

If the Fourier transform of `u` is Fourier-divergence-free, then
the heat-evolved frequency-domain image `vectorHeatEvolveFreq t u`
is also Fourier-divergence-free for every time `t`. -/
theorem vectorHeatEvolveFreq_preserves_isFourierDivFree
    (t : ℝ) (u : VectorSchwartz3C)
    (h : IsFourierDivFree (fun ξ => (fourierTransformCLM ℂ u) ξ)) :
    IsFourierDivFree (vectorHeatEvolveFreq t u) := by
  intro ξ hξ
  have h1 : inner ℂ (complexifyVec ξ) ((fourierTransformCLM ℂ u) ξ) = 0 := h ξ hξ
  show inner ℂ (complexifyVec ξ)
       ((HeatSemigroupFourier.heatMultiplier t ξ : ℂ) • (fourierTransformCLM ℂ u) ξ) = 0
  rw [inner_smul_right, h1, mul_zero]

/-! ## §2 — Zero input case -/

/-- **Zero input remains divergence-free under heat evolution.**

A consequence/sanity check: starting from the zero vector Schwartz
field, the heat-evolved frequency-domain image is identically zero
and hence trivially divergence-free at every time. -/
theorem vectorHeatEvolveFreq_zero_isFourierDivFree (t : ℝ) :
    IsFourierDivFree (vectorHeatEvolveFreq t (0 : VectorSchwartz3C)) := by
  intro ξ _hξ
  rw [HeatSemigroupVector.vectorHeatEvolveFreq_zero_input]
  exact inner_zero_right _

/-! ## §3 — Initial-time identity -/

/-- **At `t = 0` the heat-evolved field is Fourier-div-free iff the
Fourier transform is** — direct consequence of the initial-time
identity for `vectorHeatEvolveFreq`. -/
theorem vectorHeatEvolveFreq_isFourierDivFree_at_zero
    (u : VectorSchwartz3C)
    (h : IsFourierDivFree (fun ξ => (fourierTransformCLM ℂ u) ξ)) :
    IsFourierDivFree (vectorHeatEvolveFreq 0 u) :=
  vectorHeatEvolveFreq_preserves_isFourierDivFree 0 u h

/-! ## §4 — Capstone -/

/-- **★ Heat-preserves-divergence-free brick capstone ★**

Bundles:
  (a) Universal: heat evolution preserves Fourier-divergence-freeness
      at every time, given the initial Fourier transform is div-free.
  (b) Zero input is trivially div-free after heat evolution.
  (c) Initial-time consistency: at `t = 0`, divergence-freeness
      transfers directly from the Fourier transform. -/
theorem fujitaKato_heat_preserves_div_free_brick_capstone :
    (∀ (t : ℝ) (u : VectorSchwartz3C),
       IsFourierDivFree (fun ξ => (fourierTransformCLM ℂ u) ξ) →
       IsFourierDivFree (vectorHeatEvolveFreq t u)) ∧
    (∀ t : ℝ,
       IsFourierDivFree (vectorHeatEvolveFreq t (0 : VectorSchwartz3C))) ∧
    (∀ u : VectorSchwartz3C,
       IsFourierDivFree (fun ξ => (fourierTransformCLM ℂ u) ξ) →
       IsFourierDivFree (vectorHeatEvolveFreq 0 u)) :=
  ⟨vectorHeatEvolveFreq_preserves_isFourierDivFree,
   vectorHeatEvolveFreq_zero_isFourierDivFree,
   vectorHeatEvolveFreq_isFourierDivFree_at_zero⟩

/-! ## §5 — Axiom audit -/

#print axioms vectorHeatEvolveFreq_preserves_isFourierDivFree
#print axioms vectorHeatEvolveFreq_zero_isFourierDivFree
#print axioms vectorHeatEvolveFreq_isFourierDivFree_at_zero
#print axioms fujitaKato_heat_preserves_div_free_brick_capstone

end PF.NavierStokes.FujitaKato1964.HeatPreservesDivFree
