/-
# Fujita-Kato 1964 — Heat Semigroup Operator (Frequency-Domain Image)

★ 2026-06-10 — Fifth brick of real Fujita-Kato infrastructure.
★ Promotes the pointwise multiplier `m_t(ξ) = e^{-t · ‖ξ‖²}` of
  `HeatSemigroupFourier.lean` to a function-of-frequency operator
  acting on scalar complex Schwartz on `ℝ³` via the Fourier round-trip.

The heat semigroup `e^{tΔ}` acts on a Schwartz function `f : ℝ³ → ℂ`
by

  `e^{tΔ} f = F^{-1} (m_t · F f)`,

where `F = fourierTransformCLM ℂ` is the mathlib Fourier transform
on scalar Schwartz space. The intermediate quantity

  `heatEvolveFreq t f ξ := m_t(ξ) · (F f)(ξ)`

is the **frequency-domain image** of `e^{tΔ} f`: the pointwise
product of the Fourier multiplier with the Fourier transform of the
input. Applying `F^{-1}` recovers the physical-space heat evolution,
but that step requires proving that pointwise multiplication by a
Gaussian preserves Schwartz decay — a substantial standalone result
that lives in a follow-on brick.

This file lands the function-of-frequency form and verifies its
core algebraic properties:

  (a) initial-time identity: `heatEvolveFreq 0 f ξ = (F f) ξ`
  (b) mean-mode preservation: `heatEvolveFreq t f 0 = (F f) 0`
  (c) zero input gives zero output
  (d) `‖·‖` contraction at non-negative times: bounded above by `‖(F f) ξ‖`
  (e) multiplier-level semigroup compatibility

These are exactly the algebraic facts the Fujita-Kato contraction
argument invokes when bounding `‖e^{tΔ} u₀‖_{Ḣ^{1/2}}` and the
Duhamel term in the mild formulation.

Scope: scalar (`ℂ`-valued) Schwartz on `EuclideanSpace ℝ (Fin 3)`.
The vector version reduces componentwise; the physical-space lift
via Fourier inversion is a separate brick.

Imports: the just-landed multiplier shell and seminorm shell, which
together supply `R3`, `ScalarSchwartz3C`, `heatMultiplier`, and
mathlib's `SchwartzMap.fourierTransformCLM`.

Axiom-free under `[propext, Classical.choice, Quot.sound]` only.

Author: Pablo Cohen (framework + formalization, 2026-06-10)
-/

import PF.NavierStokes.FujitaKato1964.HeatSemigroupFourier
import PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier

set_option autoImplicit false

namespace PF.NavierStokes.FujitaKato1964.HeatSemigroupOperator

open SchwartzMap
open PF.NavierStokes.FujitaKato1964.HeatSemigroupFourier
  (heatMultiplier
   heatMultiplier_at_zero_time
   heatMultiplier_at_zero_freq
   heatMultiplier_le_one
   heatMultiplier_nonneg
   heatMultiplier_add)
open PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier
  (R3 ScalarSchwartz3C)

/-! ## §1 — Frequency-domain heat evolution image -/

/-- **Frequency-domain image of the heat semigroup applied to a
scalar Schwartz function.**

For a scalar Schwartz function `f : ℝ³ → ℂ`, time `t ∈ ℝ`, and
frequency `ξ ∈ ℝ³`, the frequency-side image is

  `heatEvolveFreq t f ξ := m_t(ξ) · (F f)(ξ)`

where `m_t(ξ) = e^{-t · ‖ξ‖²}` is the heat Fourier multiplier from
`HeatSemigroupFourier.lean` and `F = fourierTransformCLM ℂ` is
mathlib's Fourier transform on scalar Schwartz space. The real
multiplier is coerced into `ℂ` to multiply the complex Fourier image.

Applying `F^{-1}` to this would yield `e^{tΔ} f` in physical space;
that step (proving the round-trip stays inside Schwartz) lives in
a follow-on brick. The frequency-side image is itself the
load-bearing object for the contraction estimates of Fujita-Kato:
the Plancherel theorem moves all Sobolev seminorms to integrals
against `|heatEvolveFreq t f ξ|²`. -/
noncomputable def heatEvolveFreq
    (t : ℝ) (f : ScalarSchwartz3C) (ξ : R3) : ℂ :=
  (heatMultiplier t ξ : ℂ) * (fourierTransformCLM ℂ f) ξ

/-! ## §2 — Pointwise properties -/

/-- **Initial-time identity in frequency space.** At `t = 0` the
multiplier collapses to `1`, so the frequency-domain image of the
heat semigroup reduces to the Fourier transform of the input. This
is the multiplier-level avatar of `e^{0·Δ} = I` on the Fourier
side. -/
theorem heatEvolveFreq_at_zero_time (f : ScalarSchwartz3C) (ξ : R3) :
    heatEvolveFreq 0 f ξ = (fourierTransformCLM ℂ f) ξ := by
  unfold heatEvolveFreq
  rw [heatMultiplier_at_zero_time]
  push_cast
  ring

/-- **Mean-mode preservation in frequency space.** At zero frequency
`ξ = 0` the multiplier collapses to `1` for every time, so the
zero-frequency mode of `heatEvolveFreq t f` agrees with that of
`F f`. This is the conservation of the mean value under the heat
flow, expressed on the Fourier side. -/
theorem heatEvolveFreq_at_zero_freq (t : ℝ) (f : ScalarSchwartz3C) :
    heatEvolveFreq t f (0 : R3) = (fourierTransformCLM ℂ f) (0 : R3) := by
  unfold heatEvolveFreq
  rw [heatMultiplier_at_zero_freq]
  push_cast
  ring

/-- **Zero input produces zero frequency-domain image.** Fourier
transform of zero is zero, so multiplication by any factor (the
heat multiplier in particular) yields zero. This is the linearity
of `e^{tΔ}` at the zero vector, on the Fourier side. -/
theorem heatEvolveFreq_zero_input (t : ℝ) (ξ : R3) :
    heatEvolveFreq t (0 : ScalarSchwartz3C) ξ = 0 := by
  unfold heatEvolveFreq
  rw [map_zero, SchwartzMap.zero_apply, mul_zero]

/-- **Pointwise contraction in frequency space at non-negative times.**
For `t ≥ 0` the multiplier is bounded in `[0, 1]`, so the
frequency-domain image is bounded above in norm by the Fourier
transform of the input pointwise:

  `‖heatEvolveFreq t f ξ‖ ≤ ‖(F f) ξ‖`.

After Plancherel, integrating the squared inequality against `|ξ|`
gives the `Ḣ^{1/2}` contraction estimate

  `‖e^{tΔ} u₀‖_{Ḣ^{1/2}} ≤ ‖u₀‖_{Ḣ^{1/2}}`

that the Fujita-Kato fixed-point argument relies on for the
linear-propagator bound. -/
theorem norm_heatEvolveFreq_le
    (t : ℝ) (ht : 0 ≤ t) (f : ScalarSchwartz3C) (ξ : R3) :
    ‖heatEvolveFreq t f ξ‖ ≤ ‖(fourierTransformCLM ℂ f) ξ‖ := by
  unfold heatEvolveFreq
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (heatMultiplier_nonneg t ξ)]
  have h_one : heatMultiplier t ξ ≤ 1 := heatMultiplier_le_one t ht ξ
  have h_nn : 0 ≤ ‖(fourierTransformCLM ℂ f) ξ‖ := norm_nonneg _
  calc heatMultiplier t ξ * ‖(fourierTransformCLM ℂ f) ξ‖
      ≤ 1 * ‖(fourierTransformCLM ℂ f) ξ‖ := by
        exact mul_le_mul_of_nonneg_right h_one h_nn
    _ = ‖(fourierTransformCLM ℂ f) ξ‖ := one_mul _

/-! ## §3 — Multiplier-level semigroup compatibility -/

/-- **Multiplier-level semigroup compatibility in frequency space.**
The semigroup law `m_{s+t}(ξ) = m_s(ξ) · m_t(ξ)` for the heat
multiplier lifts pointwise to a frequency-domain factorization of
`heatEvolveFreq`:

  `heatEvolveFreq (s + t) f ξ = m_s(ξ) · heatEvolveFreq t f ξ`.

This is the multiplier-side avatar of the semigroup composition
`e^{(s+t)Δ} = e^{sΔ} ∘ e^{tΔ}`, before Fourier inversion is
applied to recover the physical-space operator composition. The
proof unfolds both sides, applies `heatMultiplier_add`, and
reassociates the product. -/
theorem heatEvolveFreq_semigroup
    (s t : ℝ) (f : ScalarSchwartz3C) (ξ : R3) :
    heatEvolveFreq (s + t) f ξ
      = (heatMultiplier s ξ : ℂ) * heatEvolveFreq t f ξ := by
  unfold heatEvolveFreq
  rw [heatMultiplier_add]
  push_cast
  ring

/-! ## §4 — Capstone -/

/-- **★ Fujita-Kato heat-semigroup operator (frequency-domain) brick capstone ★**

Bundles the five algebraic properties of the frequency-domain image
`heatEvolveFreq t f ξ := m_t(ξ) · (F f)(ξ)` of the heat semigroup
`e^{tΔ}` on scalar complex Schwartz on `ℝ³`:

  (a) Initial-time identity: `heatEvolveFreq 0 f ξ = (F f) ξ`
  (b) Mean-mode preservation: `heatEvolveFreq t f 0 = (F f) 0`
  (c) Zero input gives zero output
  (d) Pointwise contraction at non-negative times:
      `‖heatEvolveFreq t f ξ‖ ≤ ‖(F f) ξ‖` for `t ≥ 0`
  (e) Multiplier-level semigroup compatibility:
      `heatEvolveFreq (s+t) f ξ = m_s(ξ) · heatEvolveFreq t f ξ`

These are the algebraic facts the Fujita-Kato 1964 contraction
argument invokes when bounding the linear propagator `e^{tΔ} u₀`
on the Fourier side, before Plancherel transports the estimates
into the `Ḣ^{1/2}` Sobolev seminorm. Promoting `heatEvolveFreq` to
a genuine physical-space operator
`heatSemigroup : ℝ → ScalarSchwartz3C → ScalarSchwartz3C` via Fourier
inversion (which requires the pointwise Gaussian multiplier to
preserve Schwartz decay) lives in a follow-on brick.

Axiom-free: depends on `[propext, Classical.choice, Quot.sound]`
only. -/
theorem fujitaKato_heat_evolve_freq_brick_capstone :
    -- (a) Initial-time identity
    (∀ (f : ScalarSchwartz3C) (ξ : R3),
       heatEvolveFreq 0 f ξ = (fourierTransformCLM ℂ f) ξ) ∧
    -- (b) Mean-mode preservation
    (∀ (t : ℝ) (f : ScalarSchwartz3C),
       heatEvolveFreq t f (0 : R3) = (fourierTransformCLM ℂ f) (0 : R3)) ∧
    -- (c) Zero input gives zero output
    (∀ (t : ℝ) (ξ : R3),
       heatEvolveFreq t (0 : ScalarSchwartz3C) ξ = 0) ∧
    -- (d) Pointwise contraction at non-negative times
    (∀ (t : ℝ), 0 ≤ t → ∀ (f : ScalarSchwartz3C) (ξ : R3),
       ‖heatEvolveFreq t f ξ‖ ≤ ‖(fourierTransformCLM ℂ f) ξ‖) ∧
    -- (e) Multiplier-level semigroup compatibility
    (∀ (s t : ℝ) (f : ScalarSchwartz3C) (ξ : R3),
       heatEvolveFreq (s + t) f ξ
         = (heatMultiplier s ξ : ℂ) * heatEvolveFreq t f ξ) :=
  ⟨heatEvolveFreq_at_zero_time,
   heatEvolveFreq_at_zero_freq,
   heatEvolveFreq_zero_input,
   norm_heatEvolveFreq_le,
   heatEvolveFreq_semigroup⟩

/-! ## §5 — Axiom audit -/

#print axioms heatEvolveFreq_at_zero_time
#print axioms heatEvolveFreq_at_zero_freq
#print axioms heatEvolveFreq_zero_input
#print axioms norm_heatEvolveFreq_le
#print axioms heatEvolveFreq_semigroup
#print axioms fujitaKato_heat_evolve_freq_brick_capstone

end PF.NavierStokes.FujitaKato1964.HeatSemigroupOperator
