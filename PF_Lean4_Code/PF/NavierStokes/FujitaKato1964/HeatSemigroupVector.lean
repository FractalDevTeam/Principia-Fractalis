/-
# Fujita-Kato 1964 — Vector Heat Semigroup Operator (Frequency-Domain Image)

★ 2026-06-10 — Tenth brick of real Fujita-Kato infrastructure.
★ Mechanical lift of the scalar `heatEvolveFreq` operator from
  `HeatSemigroupOperator.lean` to the vector codomain
  `EuclideanSpace ℂ (Fin 3)` actually used by Navier-Stokes (the
  complexified velocity field is a 3-vector).

The vector heat semigroup `e^{tΔ}` acts componentwise on a vector
Schwartz field `u : ℝ³ → ℂ³` by

  `e^{tΔ} u = F^{-1} (m_t · F u)`,

where `F = fourierTransformCLM ℂ` is mathlib's Fourier transform on
vector Schwartz space and `m_t(ξ) = e^{-t · ‖ξ‖²}` is the scalar
heat Fourier multiplier from `HeatSemigroupFourier.lean`. The
multiplier acts on the vector Fourier transform via the canonical
`ℂ`-scalar action on `EuclideanSpace ℂ (Fin 3)` (i.e. componentwise
multiplication).

The frequency-domain image

  `vectorHeatEvolveFreq t u ξ := (m_t(ξ) : ℂ) • (F u)(ξ)`

is the load-bearing object for the vector Fujita-Kato estimates:
after Plancherel, the vector `Ḣ^{1/2}` seminorm reduces to integrals
against `‖vectorHeatEvolveFreq t u ξ‖²_{ℂ³}`.

This file lands the function-of-frequency form for the vector
case and verifies its core algebraic properties:

  (a) initial-time identity: `vectorHeatEvolveFreq 0 u ξ = (F u) ξ`
  (b) mean-mode preservation: `vectorHeatEvolveFreq t u 0 = (F u) 0`
  (c) zero input gives zero output
  (d) `‖·‖` contraction at non-negative times: bounded above by `‖(F u) ξ‖`
  (e) multiplier-level semigroup compatibility

These are exactly the algebraic facts the Fujita-Kato contraction
argument invokes for the vector linear propagator bound on
`Ḣ^{1/2}(ℝ³; ℂ³)`.

Scope: vector (`ℂ³`-valued) Schwartz on `EuclideanSpace ℝ (Fin 3)`.
Mechanical componentwise lift of the scalar version; physical-space
lift via Fourier inversion is a separate brick.

Imports: scalar operator (for naming consistency / reference) and
vector seminorm shell (for the `VectorSchwartz3C` / `C3` type
aliases).

Axiom-free under `[propext, Classical.choice, Quot.sound]` only.

Author: Pablo Cohen (framework + formalization, 2026-06-10)
-/

import PF.NavierStokes.FujitaKato1964.HeatSemigroupFourier
import PF.NavierStokes.FujitaKato1964.HeatSemigroupOperator
import PF.NavierStokes.FujitaKato1964.SobolevSeminormVector

set_option autoImplicit false

namespace PF.NavierStokes.FujitaKato1964.HeatSemigroupVector

open SchwartzMap
open PF.NavierStokes.FujitaKato1964.HeatSemigroupFourier
  (heatMultiplier
   heatMultiplier_at_zero_time
   heatMultiplier_at_zero_freq
   heatMultiplier_le_one
   heatMultiplier_nonneg
   heatMultiplier_add)
open PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier
  (R3 C3 VectorSchwartz3C)

/-! ## §1 — Vector frequency-domain heat evolution image -/

/-- **Frequency-domain image of the heat semigroup applied to a
vector-valued Schwartz field.**

For a vector Schwartz field `u : ℝ³ → ℂ³`, time `t ∈ ℝ`, and
frequency `ξ ∈ ℝ³`, the frequency-side image is

  `vectorHeatEvolveFreq t u ξ := (m_t(ξ) : ℂ) • (F u)(ξ)`

where `m_t(ξ) = e^{-t · ‖ξ‖²}` is the scalar heat Fourier multiplier
from `HeatSemigroupFourier.lean` and `F = fourierTransformCLM ℂ` is
mathlib's Fourier transform on vector Schwartz space. The real
multiplier is coerced into `ℂ` and acts on the vector Fourier image
via the canonical `ℂ`-scalar action on `EuclideanSpace ℂ (Fin 3)`
(componentwise multiplication, supplied by `PiLp` / `EuclideanSpace`
module structure).

Mechanical componentwise lift of the scalar `heatEvolveFreq` from
`HeatSemigroupOperator.lean`. The vector form is the one Navier-Stokes
actually needs: the velocity field is `ℂ³`-valued after
complexification. Applying `F^{-1}` to this would yield `e^{tΔ} u`
in physical space; that step (Schwartz round-trip on the vector
side) lives in a follow-on brick. -/
noncomputable def vectorHeatEvolveFreq
    (t : ℝ) (u : VectorSchwartz3C) (ξ : R3) : C3 :=
  (heatMultiplier t ξ : ℂ) • (fourierTransformCLM ℂ u) ξ

/-! ## §2 — Pointwise properties -/

/-- **Initial-time identity in vector frequency space.** At `t = 0`
the multiplier collapses to `1`, so the frequency-domain image of
the vector heat semigroup reduces to the Fourier transform of the
input. This is the multiplier-level avatar of `e^{0·Δ} = I` on the
vector Fourier side. -/
theorem vectorHeatEvolveFreq_at_zero_time
    (u : VectorSchwartz3C) (ξ : R3) :
    vectorHeatEvolveFreq 0 u ξ = (fourierTransformCLM ℂ u) ξ := by
  unfold vectorHeatEvolveFreq
  rw [heatMultiplier_at_zero_time]
  push_cast
  rw [one_smul]

/-- **Mean-mode preservation in vector frequency space.** At zero
frequency `ξ = 0` the multiplier collapses to `1` for every time,
so the zero-frequency mode of `vectorHeatEvolveFreq t u` agrees with
that of `F u`. This is the conservation of the mean value of the
vector field under the heat flow, expressed on the Fourier side. -/
theorem vectorHeatEvolveFreq_at_zero_freq
    (t : ℝ) (u : VectorSchwartz3C) :
    vectorHeatEvolveFreq t u (0 : R3) = (fourierTransformCLM ℂ u) (0 : R3) := by
  unfold vectorHeatEvolveFreq
  rw [heatMultiplier_at_zero_freq]
  push_cast
  rw [one_smul]

/-- **Zero input produces zero vector frequency-domain image.** The
Fourier transform of the zero vector field is the zero vector field,
so scalar multiplication by any factor (the heat multiplier in
particular) yields zero. This is the linearity of `e^{tΔ}` at the
zero vector field, on the Fourier side. -/
theorem vectorHeatEvolveFreq_zero_input (t : ℝ) (ξ : R3) :
    vectorHeatEvolveFreq t (0 : VectorSchwartz3C) ξ = 0 := by
  unfold vectorHeatEvolveFreq
  rw [map_zero, SchwartzMap.zero_apply, smul_zero]

/-- **Pointwise contraction in vector frequency space at non-negative
times.** For `t ≥ 0` the multiplier is bounded in `[0, 1]`, so the
vector frequency-domain image is bounded above in `ℂ³`-norm by the
Fourier transform of the input pointwise:

  `‖vectorHeatEvolveFreq t u ξ‖ ≤ ‖(F u) ξ‖`.

After Plancherel, integrating the squared inequality against `|ξ|`
gives the vector `Ḣ^{1/2}` contraction estimate

  `‖e^{tΔ} u₀‖_{Ḣ^{1/2}} ≤ ‖u₀‖_{Ḣ^{1/2}}`

that the vector Fujita-Kato fixed-point argument relies on for the
linear-propagator bound. -/
theorem norm_vectorHeatEvolveFreq_le
    (t : ℝ) (ht : 0 ≤ t) (u : VectorSchwartz3C) (ξ : R3) :
    ‖vectorHeatEvolveFreq t u ξ‖ ≤ ‖(fourierTransformCLM ℂ u) ξ‖ := by
  unfold vectorHeatEvolveFreq
  rw [norm_smul, Complex.norm_real,
      Real.norm_of_nonneg (heatMultiplier_nonneg t ξ)]
  have h_one : heatMultiplier t ξ ≤ 1 := heatMultiplier_le_one t ht ξ
  have h_nn : 0 ≤ ‖(fourierTransformCLM ℂ u) ξ‖ := norm_nonneg _
  calc heatMultiplier t ξ * ‖(fourierTransformCLM ℂ u) ξ‖
      ≤ 1 * ‖(fourierTransformCLM ℂ u) ξ‖ := by
        exact mul_le_mul_of_nonneg_right h_one h_nn
    _ = ‖(fourierTransformCLM ℂ u) ξ‖ := one_mul _

/-! ## §3 — Multiplier-level semigroup compatibility -/

/-- **Multiplier-level semigroup compatibility in vector frequency
space.** The semigroup law `m_{s+t}(ξ) = m_s(ξ) · m_t(ξ)` for the
scalar heat multiplier lifts pointwise to a frequency-domain
factorization of `vectorHeatEvolveFreq`:

  `vectorHeatEvolveFreq (s + t) u ξ = m_s(ξ) • vectorHeatEvolveFreq t u ξ`.

This is the multiplier-side avatar of the semigroup composition
`e^{(s+t)Δ} = e^{sΔ} ∘ e^{tΔ}` on the vector side, before Fourier
inversion is applied to recover the physical-space operator
composition. The proof unfolds both sides, applies
`heatMultiplier_add`, and reassociates the scalar action using
`mul_smul`. -/
theorem vectorHeatEvolveFreq_semigroup
    (s t : ℝ) (u : VectorSchwartz3C) (ξ : R3) :
    vectorHeatEvolveFreq (s + t) u ξ
      = (heatMultiplier s ξ : ℂ) • vectorHeatEvolveFreq t u ξ := by
  unfold vectorHeatEvolveFreq
  rw [heatMultiplier_add]
  push_cast
  rw [mul_smul]

/-! ## §4 — Capstone -/

/-- **★ Fujita-Kato vector heat-semigroup operator (frequency-domain)
brick capstone ★**

Bundles the five algebraic properties of the frequency-domain image
`vectorHeatEvolveFreq t u ξ := (m_t(ξ) : ℂ) • (F u)(ξ)` of the heat
semigroup `e^{tΔ}` on vector complex Schwartz fields on `ℝ³`:

  (a) Initial-time identity: `vectorHeatEvolveFreq 0 u ξ = (F u) ξ`
  (b) Mean-mode preservation: `vectorHeatEvolveFreq t u 0 = (F u) 0`
  (c) Zero input gives zero output
  (d) Pointwise contraction at non-negative times:
      `‖vectorHeatEvolveFreq t u ξ‖ ≤ ‖(F u) ξ‖` for `t ≥ 0`
  (e) Multiplier-level semigroup compatibility:
      `vectorHeatEvolveFreq (s+t) u ξ = m_s(ξ) • vectorHeatEvolveFreq t u ξ`

These are the algebraic facts the Fujita-Kato 1964 vector contraction
argument invokes when bounding the linear propagator `e^{tΔ} u₀` on
the Fourier side, before Plancherel transports the estimates into the
vector `Ḣ^{1/2}(ℝ³; ℂ³)` Sobolev seminorm of
`SobolevSeminormVector.lean`. Promoting `vectorHeatEvolveFreq` to a
genuine physical-space operator
`vectorHeatSemigroup : ℝ → VectorSchwartz3C → VectorSchwartz3C` via
Fourier inversion (which requires the pointwise Gaussian multiplier
to preserve vector Schwartz decay) lives in a follow-on brick.

Mechanical componentwise lift of the scalar capstone
`fujitaKato_heat_evolve_freq_brick_capstone` of
`HeatSemigroupOperator.lean`. This is the version Navier-Stokes
actually uses.

Axiom-free: depends on `[propext, Classical.choice, Quot.sound]`
only. -/
theorem fujitaKato_vector_heat_evolve_freq_brick_capstone :
    -- (a) Initial-time identity
    (∀ (u : VectorSchwartz3C) (ξ : R3),
       vectorHeatEvolveFreq 0 u ξ = (fourierTransformCLM ℂ u) ξ) ∧
    -- (b) Mean-mode preservation
    (∀ (t : ℝ) (u : VectorSchwartz3C),
       vectorHeatEvolveFreq t u (0 : R3) = (fourierTransformCLM ℂ u) (0 : R3)) ∧
    -- (c) Zero input gives zero output
    (∀ (t : ℝ) (ξ : R3),
       vectorHeatEvolveFreq t (0 : VectorSchwartz3C) ξ = 0) ∧
    -- (d) Pointwise contraction at non-negative times
    (∀ (t : ℝ), 0 ≤ t → ∀ (u : VectorSchwartz3C) (ξ : R3),
       ‖vectorHeatEvolveFreq t u ξ‖ ≤ ‖(fourierTransformCLM ℂ u) ξ‖) ∧
    -- (e) Multiplier-level semigroup compatibility
    (∀ (s t : ℝ) (u : VectorSchwartz3C) (ξ : R3),
       vectorHeatEvolveFreq (s + t) u ξ
         = (heatMultiplier s ξ : ℂ) • vectorHeatEvolveFreq t u ξ) :=
  ⟨vectorHeatEvolveFreq_at_zero_time,
   vectorHeatEvolveFreq_at_zero_freq,
   vectorHeatEvolveFreq_zero_input,
   norm_vectorHeatEvolveFreq_le,
   vectorHeatEvolveFreq_semigroup⟩

/-! ## §5 — Axiom audit -/

#print axioms vectorHeatEvolveFreq_at_zero_time
#print axioms vectorHeatEvolveFreq_at_zero_freq
#print axioms vectorHeatEvolveFreq_zero_input
#print axioms norm_vectorHeatEvolveFreq_le
#print axioms vectorHeatEvolveFreq_semigroup
#print axioms fujitaKato_vector_heat_evolve_freq_brick_capstone

end PF.NavierStokes.FujitaKato1964.HeatSemigroupVector
