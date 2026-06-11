/-
# Fujita-Kato 1964 — Leray Projector Operator at the Frequency Level

★ 2026-06-10 — Seventh brick of real Fujita-Kato infrastructure.
★ Lifts the **real** Leray Fourier symbol (from
  `LerayProjectorFourier.lean`) to act on the **complex** Fourier
  transform of a vector Schwartz field on ℝ³.

The Fourier transform of a vector Schwartz field
`u : ℝ³ → EuclideanSpace ℂ (Fin 3)` is itself a function from `ℝ³`
to `EuclideanSpace ℂ (Fin 3)`. To apply the Leray projector at the
frequency level we therefore need a **complex** version of the
symbol acting on complex vectors, using the (still real) frequency
`ξ ∈ ℝ³`.

The Leray symbol is real-linear: it makes sense to apply it
componentwise to the real and imaginary parts of a complex vector
(equivalently, to embed `ξ` into `ℂ³` and run the same formula
with the complex inner product). We take the embed-and-run route:

  `complexifyVec ξ` sends `ξ ∈ ℝ³` to the obvious vector in `ℂ³`
  whose components are `(ξ i : ℂ)`.

  `lerayFourierSymbolC ξ w := w - (⟨complexifyVec ξ, w⟩_ℂ / ‖ξ‖²) • complexifyVec ξ`
  for `ξ ≠ 0`, and `lerayFourierSymbolC 0 w := w`.

⚠ DESIGN: We do **not** attempt to define a physical-space
operator on `VectorSchwartz3C`: the Leray symbol has a
discontinuous derivative at `ξ = 0`, so pointwise multiplication
by the symbol does not preserve Schwartz space. We stay at the
**frequency** level only.

Bricks landed here:

  §1 — Componentwise complexification `complexifyVec : R3 → C3`.
  §2 — Complex Leray Fourier symbol `lerayFourierSymbolC`.
  §3 — Pointwise properties of the complex symbol.
  §4 — Frequency-domain Leray image `lerayProjectFreq`.
  §5 — Pointwise properties of `lerayProjectFreq`.
  §6 — Capstone bundling §3 and §5.
  §7 — `#print axioms` audit (kernel-only).

Axiom-free; depends only on `[propext, Classical.choice, Quot.sound]`.

Author: Pablo Cohen (2026-06-10)
-/

import PF.NavierStokes.FujitaKato1964.LerayProjectorFourier
import PF.NavierStokes.FujitaKato1964.SobolevSeminormVector

set_option autoImplicit false

namespace PF.NavierStokes.FujitaKato1964.LerayProjectorOperator

open MeasureTheory SchwartzMap
open PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier
  (R3 C3 VectorSchwartz3C)

/-! ## §1 — Componentwise complexification `ℝ³ → ℂ³` -/

/-- **Componentwise complexification of a real frequency vector.**
Sends `ξ ∈ ℝ³` to the obvious `ℂ³` vector whose `i`-th component
is `(ξ i : ℂ)`. This is the bridge between the real frequency
domain and the complex codomain of the vector Fourier transform. -/
noncomputable def complexifyVec (ξ : R3) : C3 :=
  WithLp.toLp 2 (fun i : Fin 3 => ((ξ i : ℝ) : ℂ))

/-- **Complexification of the zero frequency is the zero vector.** -/
theorem complexifyVec_zero : complexifyVec (0 : R3) = 0 := by
  unfold complexifyVec
  ext i
  simp

/-! ## §2 — Complex Leray Fourier symbol -/

/-- **★ Complex Leray projector at the Fourier symbol level.**

For a real frequency `ξ ∈ ℝ³` and a complex velocity Fourier mode
`w ∈ ℂ³`,

  `lerayFourierSymbolC ξ w := w - (⟨complexifyVec ξ, w⟩_ℂ / ‖ξ‖²) • complexifyVec ξ`
  for `ξ ≠ 0`,
  `lerayFourierSymbolC 0 w := w`.

This is the complex-codomain analogue of `lerayFourierSymbol` from
`LerayProjectorFourier.lean`. Acting componentwise on the real and
imaginary parts of `w` it reproduces the real symbol on each part;
written in this embedded form it is well-typed against the complex
codomain `C3` of the vector Fourier transform. -/
noncomputable def lerayFourierSymbolC
    (ξ : R3) (w : C3) : C3 :=
  if ξ = 0 then w
  else w - (inner ℂ (complexifyVec ξ) w / ((‖ξ‖ ^ 2 : ℝ) : ℂ)) • complexifyVec ξ

/-! ## §3 — Pointwise properties of the complex symbol -/

/-- **Zero-frequency identity (complex):** `P̂_ℂ(0) w = w`. The
spatial-average mode is already divergence-free by convention. -/
theorem lerayFourierSymbolC_zero_freq (w : C3) :
    lerayFourierSymbolC 0 w = w := by
  unfold lerayFourierSymbolC
  rw [if_pos rfl]

/-- **Zero-data is annihilated (complex):** `P̂_ℂ(ξ) 0 = 0` for any
frequency `ξ`. -/
theorem lerayFourierSymbolC_zero_field (ξ : R3) :
    lerayFourierSymbolC ξ 0 = 0 := by
  unfold lerayFourierSymbolC
  by_cases h : ξ = 0
  · rw [if_pos h]
  · rw [if_neg h]
    simp

/-! ## §4 — Frequency-domain Leray image of a vector Schwartz field -/

/-- **★ Frequency-domain Leray image of a vector Schwartz field.**

Given a vector Schwartz field
`u : ℝ³ → EuclideanSpace ℂ (Fin 3)`, the Leray projection at
frequency `ξ` is

  `lerayProjectFreq u ξ := lerayFourierSymbolC ξ (û(ξ))`

where `û = fourierTransformCLM ℂ u` is the mathlib Fourier transform.
This is a function `R3 → C3` — the **frequency-side** image of the
Leray projector applied to `u`. We do **not** invert the Fourier
transform back to physical space here: the symbol does not preserve
Schwartz space, so the physical-space operator must be built at a
different layer (e.g. on `L²`). -/
noncomputable def lerayProjectFreq
    (u : VectorSchwartz3C) (ξ : R3) : C3 :=
  lerayFourierSymbolC ξ ((fourierTransformCLM ℂ u) ξ)

/-! ## §5 — Pointwise properties of `lerayProjectFreq` -/

/-- **The Leray image of the zero field is the zero function.**

Computational chain: the Fourier transform of zero is zero
(`map_zero`); the complex Leray symbol applied to zero gives zero
(`lerayFourierSymbolC_zero_field`). -/
theorem lerayProjectFreq_zero (ξ : R3) :
    lerayProjectFreq (0 : VectorSchwartz3C) ξ = 0 := by
  unfold lerayProjectFreq
  rw [map_zero, SchwartzMap.zero_apply]
  exact lerayFourierSymbolC_zero_field ξ

/-- **At zero frequency, the Leray image equals the Fourier
transform**: the spatial-average mode is left untouched. -/
theorem lerayProjectFreq_at_zero_freq (u : VectorSchwartz3C) :
    lerayProjectFreq u 0 = (fourierTransformCLM ℂ u) 0 := by
  unfold lerayProjectFreq
  exact lerayFourierSymbolC_zero_freq _

/-! ## §6 — Capstone -/

/-- **★★★ Leray projector operator brick capstone ★★★**

Bundles the algebraic shell of the complex-codomain Leray projector
at the Fourier symbol level, together with its action on the
Fourier transform of a vector Schwartz field on ℝ³:

  (a) Complexification of zero frequency is zero
  (b) Complex symbol zero-frequency identity: `P̂_ℂ(0) w = w`
  (c) Complex symbol zero-data annihilation: `P̂_ℂ(ξ) 0 = 0`
  (d) Leray image of the zero field is zero
  (e) Leray image at zero frequency equals the Fourier transform there

These are the pointwise algebraic facts a Fujita-Kato divergence-
free decomposition uses at the frequency-symbol level. The
companion Lp / operator-norm content for the lift to a bounded
operator on `L²(ℝ³; ℂ³)` lives in follow-on bricks.

Axiom-free: `[propext, Classical.choice, Quot.sound]` only. -/
theorem lerayProjectorOperator_capstone :
    -- (a) Complexification of zero is zero
    (complexifyVec (0 : R3) = 0) ∧
    -- (b) Complex symbol identity on ξ = 0
    (∀ w : C3, lerayFourierSymbolC 0 w = w) ∧
    -- (c) Complex symbol annihilates zero data
    (∀ ξ : R3, lerayFourierSymbolC ξ 0 = 0) ∧
    -- (d) Leray image of zero field is zero
    (∀ ξ : R3, lerayProjectFreq (0 : VectorSchwartz3C) ξ = 0) ∧
    -- (e) Leray image at zero frequency equals the Fourier transform there
    (∀ u : VectorSchwartz3C,
       lerayProjectFreq u 0 = (fourierTransformCLM ℂ u) 0) :=
  ⟨complexifyVec_zero,
   lerayFourierSymbolC_zero_freq,
   lerayFourierSymbolC_zero_field,
   lerayProjectFreq_zero,
   lerayProjectFreq_at_zero_freq⟩

/-! ## §7 — Axiom audit -/

#print axioms complexifyVec_zero
#print axioms lerayFourierSymbolC_zero_freq
#print axioms lerayFourierSymbolC_zero_field
#print axioms lerayProjectFreq_zero
#print axioms lerayProjectFreq_at_zero_freq
#print axioms lerayProjectorOperator_capstone

end PF.NavierStokes.FujitaKato1964.LerayProjectorOperator
