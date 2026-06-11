/-
# Fujita-Kato 1964 — Composite `Leray ∘ Heat` Operator at the Frequency Level

★ 2026-06-10 — Composite-operator brick of real Fujita-Kato infrastructure.
★ Composes the vector heat-semigroup frequency image
  `vectorHeatEvolveFreq` (from `HeatSemigroupVector.lean`) with the
  complex Leray Fourier symbol `lerayFourierSymbolC` (from
  `LerayProjectorOperator.lean`) into the single composite

    `heatLerayCompose t u ξ := lerayFourierSymbolC ξ (vectorHeatEvolveFreq t u ξ)`.

This is the operator that appears inside the Fujita-Kato mild-formulation
bilinear integrand: heat-evolve a vector Schwartz field, then project to
the divergence-free subspace. After Fourier inversion, this is exactly
`e^{(t-s)Δ} ∘ P` acting on the convective term.

The headline content of this brick is that the result is itself
divergence-free at every nonzero frequency — i.e. the composite lands
in the Fourier-divergence-free subspace of `R3 → C3`. This follows
without any algebraic effort from the perpendicularity lemma
`lerayFourierSymbolC_inner_eq_zero` of `LerayImageIsDivFree.lean`:
the Leray symbol kills the parallel-to-ξ part of *every* complex
vector, so it kills it for the particular vector
`vectorHeatEvolveFreq t u ξ` as well.

Bricks landed here:

  §1 — Composite operator `heatLerayCompose`.
  §2 — Pointwise properties at zero frequency / zero input.
  §3 — HEADLINE: composite image is `IsFourierDivFree`.
  §4 — Initial-time identity: at `t = 0`, the composite equals the
       frequency-domain Leray projection `lerayProjectFreq`.
  §5 — Capstone bundling §2-§4.
  §6 — `#print axioms` audit (kernel-only).

Axiom-free; depends only on `[propext, Classical.choice, Quot.sound]`.

Author: Pablo Cohen (2026-06-10)
-/

import PF.NavierStokes.FujitaKato1964.HeatSemigroupVector
import PF.NavierStokes.FujitaKato1964.LerayProjectorOperator
import PF.NavierStokes.FujitaKato1964.LerayImageIsDivFree
import PF.NavierStokes.FujitaKato1964.FourierDivFree

set_option autoImplicit false

namespace PF.NavierStokes.FujitaKato1964.HeatLerayCompose

open PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier
  (R3 C3 VectorSchwartz3C)
open PF.NavierStokes.FujitaKato1964.HeatSemigroupVector
  (vectorHeatEvolveFreq
   vectorHeatEvolveFreq_at_zero_time
   vectorHeatEvolveFreq_at_zero_freq
   vectorHeatEvolveFreq_zero_input)
open PF.NavierStokes.FujitaKato1964.LerayProjectorOperator
  (lerayFourierSymbolC
   lerayProjectFreq
   lerayFourierSymbolC_zero_freq
   lerayFourierSymbolC_zero_field)
open PF.NavierStokes.FujitaKato1964.LerayImageIsDivFree
  (lerayFourierSymbolC_inner_eq_zero)
open PF.NavierStokes.FujitaKato1964.FourierDivFree
  (IsFourierDivFree)

/-! ## §1 — The composite operator -/

/-- **★ Composite frequency-domain operator `Leray ∘ Heat` ★.**

For a vector Schwartz field `u : ℝ³ → ℂ³`, a time `t ∈ ℝ`, and a
frequency `ξ ∈ ℝ³`, the composite operator at the frequency level is

  `heatLerayCompose t u ξ := lerayFourierSymbolC ξ (vectorHeatEvolveFreq t u ξ)`.

In words: first apply the vector heat-semigroup multiplier in
frequency to get `(m_t(ξ) : ℂ) • (F u)(ξ)`, then apply the complex
Leray symbol `P̂_ℂ(ξ)` to project out the parallel-to-ξ part.

Under Fourier inversion this is the frequency-side avatar of the
physical-space composite `e^{tΔ} ∘ P`, which is the operator that
acts on the convective term inside the Fujita-Kato mild-formulation
bilinear integrand

  `B(u, v)(t) := -∫₀ᵗ e^{(t-s)Δ} P (u(s) ⊗ ∇ · v(s)) ds`.

We stay at the frequency level — both `vectorHeatEvolveFreq` and
`lerayFourierSymbolC` are defined there, and the Leray symbol does
not preserve Schwartz space, so the physical-space lift lives in a
separate brick. -/
noncomputable def heatLerayCompose
    (t : ℝ) (u : VectorSchwartz3C) (ξ : R3) : C3 :=
  lerayFourierSymbolC ξ (vectorHeatEvolveFreq t u ξ)

/-! ## §2 — Pointwise properties -/

/-- **At zero frequency, the composite collapses to the heat image.**
The complex Leray symbol at `ξ = 0` is the identity
(`lerayFourierSymbolC_zero_freq`), so the composite at the zero
mode is just `vectorHeatEvolveFreq t u 0`. This reflects the fact
that the Leray projector leaves the spatial-average mode alone —
the heat semigroup already preserves the mean by
`vectorHeatEvolveFreq_at_zero_freq`. -/
theorem heatLerayCompose_at_zero_freq
    (t : ℝ) (u : VectorSchwartz3C) :
    heatLerayCompose t u (0 : R3) = vectorHeatEvolveFreq t u (0 : R3) := by
  unfold heatLerayCompose
  exact lerayFourierSymbolC_zero_freq _

/-- **Zero input gives zero composite output.** Computational chain:
the vector heat-semigroup image of the zero field is zero
(`vectorHeatEvolveFreq_zero_input`); the complex Leray symbol
annihilates the zero vector (`lerayFourierSymbolC_zero_field`). So
the composite of the zero field is the zero function on `R3`. This
is the linearity of `Leray ∘ Heat` at the zero vector field, on the
Fourier side. -/
theorem heatLerayCompose_zero_input (t : ℝ) (ξ : R3) :
    heatLerayCompose t (0 : VectorSchwartz3C) ξ = 0 := by
  unfold heatLerayCompose
  rw [vectorHeatEvolveFreq_zero_input t ξ]
  exact lerayFourierSymbolC_zero_field ξ

/-! ## §3 — HEADLINE: composite image is Fourier-divergence-free -/

/-- **★★★ THE HEADLINE THEOREM ★★★**

For every vector Schwartz field `u : ℝ³ → ℂ³` and every time `t ∈ ℝ`,
the composite frequency-domain image `heatLerayCompose t u : R3 → C3`
is Fourier-divergence-free:

  `∀ ξ ≠ 0,   ⟨complexifyVec ξ, heatLerayCompose t u ξ⟩_ℂ = 0`.

This is the literal Fourier-side encoding of
`div (e^{tΔ} P (·)) = 0`: the Leray projector kills the
gradient (parallel-to-ξ) part of every mode, and applying it AFTER
the heat semigroup preserves this property since the Leray symbol
acts on the full vector `vectorHeatEvolveFreq t u ξ` independently
of how that vector was constructed.

Proof: unfold the composite to `lerayFourierSymbolC ξ (·)` and apply
the perpendicularity lemma `lerayFourierSymbolC_inner_eq_zero` from
`LerayImageIsDivFree.lean` to the specific complex vector
`w := vectorHeatEvolveFreq t u ξ`. The Leray symbol's
perpendicularity is the entire mathematical content — heat-evolution
is irrelevant to divergence-freeness of the OUTPUT, only to its
magnitude. -/
theorem heatLerayCompose_isFourierDivFree
    (t : ℝ) (u : VectorSchwartz3C) :
    IsFourierDivFree (heatLerayCompose t u) := by
  intro ξ hξ
  unfold heatLerayCompose
  exact lerayFourierSymbolC_inner_eq_zero ξ hξ (vectorHeatEvolveFreq t u ξ)

/-! ## §4 — Initial-time identity (`t = 0`) -/

/-- **At `t = 0`, the composite reduces to the frequency-domain
Leray projection.** Computational chain: the heat-semigroup image
at `t = 0` is the Fourier transform itself
(`vectorHeatEvolveFreq_at_zero_time`), so applying the Leray symbol
afterwards gives exactly `lerayProjectFreq u ξ` by definition.

This is the consistency check that the composite restricts to the
pure Leray projector at the initial time, before any heat-diffusion
has occurred. Physically: at `t = 0`, `e^{0·Δ} = I` and the
composite `Leray ∘ Heat` becomes just `Leray`. -/
theorem heatLerayCompose_at_zero_time_eq_lerayProjectFreq
    (u : VectorSchwartz3C) (ξ : R3) :
    heatLerayCompose 0 u ξ = lerayProjectFreq u ξ := by
  unfold heatLerayCompose lerayProjectFreq
  rw [vectorHeatEvolveFreq_at_zero_time u ξ]

/-! ## §5 — Capstone -/

/-- **★★★ `Leray ∘ Heat` composite brick capstone ★★★**

Bundles the pointwise algebraic properties of the composite
frequency-domain operator
`heatLerayCompose t u ξ := lerayFourierSymbolC ξ (vectorHeatEvolveFreq t u ξ)`:

  (a) Zero-frequency collapse: at `ξ = 0`, the composite equals the
      heat-semigroup image, i.e.
      `heatLerayCompose t u 0 = vectorHeatEvolveFreq t u 0`.

  (b) Zero-input annihilation: applied to the zero vector field, the
      composite is identically zero.

  (c) **HEADLINE — divergence-free image**: for every `u` and every
      `t`, the composite image `heatLerayCompose t u : R3 → C3` is
      Fourier-divergence-free. This is the load-bearing fact: the
      Fujita-Kato bilinear integrand `e^{(t-s)Δ} ∘ P` lands in the
      divergence-free subspace, automatically and exactly.

  (d) Initial-time identity: at `t = 0`, the composite reduces to
      the pure Leray projection `lerayProjectFreq u ξ`.

Together: `heatLerayCompose` is the correctly-typed Fourier-side
composite operator for the Fujita-Kato mild integrand, and its
range is the Fourier-divergence-free subspace at every time.

Axiom-free: depends on `[propext, Classical.choice, Quot.sound]`
only. -/
theorem fujitaKato_heat_leray_compose_brick_capstone :
    -- (a) Zero-frequency collapse to the heat image
    (∀ (t : ℝ) (u : VectorSchwartz3C),
       heatLerayCompose t u (0 : R3) = vectorHeatEvolveFreq t u (0 : R3)) ∧
    -- (b) Zero-input annihilation
    (∀ (t : ℝ) (ξ : R3),
       heatLerayCompose t (0 : VectorSchwartz3C) ξ = 0) ∧
    -- (c) HEADLINE — divergence-free image
    (∀ (t : ℝ) (u : VectorSchwartz3C),
       IsFourierDivFree (heatLerayCompose t u)) ∧
    -- (d) Initial-time identity
    (∀ (u : VectorSchwartz3C) (ξ : R3),
       heatLerayCompose 0 u ξ = lerayProjectFreq u ξ) :=
  ⟨heatLerayCompose_at_zero_freq,
   heatLerayCompose_zero_input,
   heatLerayCompose_isFourierDivFree,
   heatLerayCompose_at_zero_time_eq_lerayProjectFreq⟩

/-! ## §6 — Axiom audit -/

#print axioms heatLerayCompose_at_zero_freq
#print axioms heatLerayCompose_zero_input
#print axioms heatLerayCompose_isFourierDivFree
#print axioms heatLerayCompose_at_zero_time_eq_lerayProjectFreq
#print axioms fujitaKato_heat_leray_compose_brick_capstone

end PF.NavierStokes.FujitaKato1964.HeatLerayCompose
