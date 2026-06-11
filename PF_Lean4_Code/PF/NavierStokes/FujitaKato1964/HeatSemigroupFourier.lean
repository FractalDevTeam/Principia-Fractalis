/-
# Fujita-Kato 1964 — Heat Semigroup Fourier Multiplier

★ 2026-06-10 — Fourth brick of real Fujita-Kato infrastructure.

The Fujita-Kato 1964 mild-solution formula for the Navier-Stokes
Cauchy problem uses the heat semigroup `e^{tΔ}` as the linear
propagator and Duhamel integration against the nonlinearity. On the
Fourier side the heat semigroup acts as multiplication by the
Gaussian decay symbol

  `m_t(ξ) := e^{-t |ξ|²}`

This is the SOLID first heat-semigroup brick: the pointwise
multiplier as a real-valued function on `ℝ³`, with its core
algebraic properties (non-negativity, contraction at `t ≥ 0`,
boundary values at `t = 0` and `ξ = 0`, and the semigroup law
`m_{s+t}(ξ) = m_s(ξ) · m_t(ξ)`). These are precisely the
algebraic facts the Fujita-Kato contraction argument invokes
when bounding `e^{tΔ} u₀` and the Duhamel term in Sobolev
norms.

The follow-on brick — promoting the multiplier to a genuine
operator `heatSemigroup : ℝ → SchwartzMap → SchwartzMap` via
Fourier inversion and verifying that pointwise multiplication
by `e^{-t|ξ|²}` preserves Schwartz decay — lives in a separate
file.

Scope: scalar multiplier on `EuclideanSpace ℝ (Fin 3)`. The
vector version reduces to the scalar one applied componentwise.

Imports: only mathlib's real exponential and Euclidean inner-product
infrastructure. No dependency on the existing
`SobolevSeminorm*.lean` bricks; this file is independent.

Axiom-free under `[propext, Classical.choice, Quot.sound]` only.

Author: Pablo Cohen (framework + formalization, 2026-06-10)
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

namespace PF.NavierStokes.FujitaKato1964.HeatSemigroupFourier

/-! ## §1 — Pointwise Fourier multiplier -/

/-- **Three-dimensional Euclidean frequency space.** The dual
domain `ξ ∈ ℝ³` on which the heat-semigroup symbol acts. -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-- **Heat-semigroup Fourier multiplier symbol.** At time `t ∈ ℝ`
and frequency `ξ ∈ ℝ³`,

  `m_t(ξ) := e^{-t · ‖ξ‖²}`

is the symbol of `e^{tΔ}` on the Fourier side. For physical times
`t ≥ 0` the symbol is a contraction in `[0, 1]`, decaying like a
Gaussian in `|ξ|`. The multiplier is defined for all real `t`;
positivity and boundedness above by `1` require the physical sign
`t ≥ 0`. -/
noncomputable def heatMultiplier (t : ℝ) (ξ : R3) : ℝ :=
  Real.exp (-t * ‖ξ‖ ^ 2)

/-! ## §2 — Pointwise properties -/

/-- **The heat multiplier is strictly positive.** The real
exponential is strictly positive everywhere, so `m_t(ξ) > 0`,
and in particular `m_t(ξ) ≥ 0`, for every time `t` and every
frequency `ξ`. -/
theorem heatMultiplier_nonneg (t : ℝ) (ξ : R3) :
    0 ≤ heatMultiplier t ξ := by
  unfold heatMultiplier
  exact (Real.exp_pos _).le

/-- **The heat multiplier is a contraction at non-negative times.**
For `t ≥ 0`, the exponent `-t · ‖ξ‖² ≤ 0`, so the multiplier is
bounded above by `1 = e^0`. This is the algebraic source of the
`L²` contraction estimate

  `‖e^{tΔ} u‖_{L²} ≤ ‖u‖_{L²}`

on the Fourier side. -/
theorem heatMultiplier_le_one (t : ℝ) (ht : 0 ≤ t) (ξ : R3) :
    heatMultiplier t ξ ≤ 1 := by
  unfold heatMultiplier
  have hexp_nonneg : 0 ≤ t * ‖ξ‖ ^ 2 := mul_nonneg ht (sq_nonneg _)
  have hexp_neg : -t * ‖ξ‖ ^ 2 ≤ 0 := by
    have : -(t * ‖ξ‖ ^ 2) ≤ 0 := neg_nonpos_of_nonneg hexp_nonneg
    linarith
  calc Real.exp (-t * ‖ξ‖ ^ 2) ≤ Real.exp 0 := Real.exp_le_exp.mpr hexp_neg
    _ = 1 := Real.exp_zero

/-- **Heat multiplier at the initial time.** At `t = 0` the
exponent vanishes, so `m_0(ξ) = e^0 = 1`. This is the identity
property of the heat semigroup at `t = 0` on the Fourier side:
`e^{0·Δ} = I` corresponds to multiplication by the constant
function `1`. -/
theorem heatMultiplier_at_zero_time (ξ : R3) :
    heatMultiplier 0 ξ = 1 := by
  unfold heatMultiplier
  simp [Real.exp_zero]

/-- **Heat multiplier at zero frequency.** At `ξ = 0` the squared
norm vanishes, so the exponent vanishes and `m_t(0) = 1`. This
is the constant-mode preservation property: the zero-frequency
mode (mean value) is preserved by the heat semigroup for all
times. -/
theorem heatMultiplier_at_zero_freq (t : ℝ) :
    heatMultiplier t (0 : R3) = 1 := by
  unfold heatMultiplier
  simp [Real.exp_zero]

/-! ## §3 — Semigroup additivity -/

/-- **Semigroup law for the heat multiplier.** At every frequency,

  `m_{s+t}(ξ) = m_s(ξ) · m_t(ξ)`

This is the multiplier-level avatar of the semigroup identity

  `e^{(s+t)Δ} = e^{sΔ} ∘ e^{tΔ}`

The proof reduces, after distributing the exponent
`-(s+t) · ‖ξ‖² = (-s · ‖ξ‖²) + (-t · ‖ξ‖²)`, to `Real.exp_add`. -/
theorem heatMultiplier_add (s t : ℝ) (ξ : R3) :
    heatMultiplier (s + t) ξ = heatMultiplier s ξ * heatMultiplier t ξ := by
  unfold heatMultiplier
  have hexp_eq : -(s + t) * ‖ξ‖ ^ 2 = (-s * ‖ξ‖ ^ 2) + (-t * ‖ξ‖ ^ 2) := by
    ring
  rw [hexp_eq, Real.exp_add]

/-! ## §4 — Capstone -/

/-- **★ Fujita-Kato heat-semigroup multiplier brick capstone ★**

Bundles the five core algebraic properties of the Fourier
multiplier symbol `m_t(ξ) = e^{-t · ‖ξ‖²}` of the heat semigroup
`e^{tΔ}` on the frequency side:

  (a) Pointwise non-negativity: `0 ≤ m_t(ξ)` for all `t, ξ`
  (b) Contraction at physical times: `m_t(ξ) ≤ 1` for `t ≥ 0`
  (c) Identity at `t = 0`: `m_0(ξ) = 1`
  (d) Mean-preservation at `ξ = 0`: `m_t(0) = 1`
  (e) Semigroup law: `m_{s+t}(ξ) = m_s(ξ) · m_t(ξ)`

These are the multiplier-level facts the Fujita-Kato 1964
contraction argument uses to bound `e^{tΔ} u₀` and the Duhamel
integral in Sobolev norms. Promoting the multiplier to a genuine
`SchwartzMap → SchwartzMap` operator via Fourier inversion lives
in a follow-on file.

Axiom-free: depends on `[propext, Classical.choice, Quot.sound]`
only. -/
theorem fujitaKato_heat_multiplier_brick_capstone :
    -- (a) Non-negativity
    (∀ (t : ℝ) (ξ : R3), 0 ≤ heatMultiplier t ξ) ∧
    -- (b) Contraction at non-negative times
    (∀ (t : ℝ), 0 ≤ t → ∀ (ξ : R3), heatMultiplier t ξ ≤ 1) ∧
    -- (c) Identity at the initial time
    (∀ (ξ : R3), heatMultiplier 0 ξ = 1) ∧
    -- (d) Mean-mode preservation at zero frequency
    (∀ (t : ℝ), heatMultiplier t (0 : R3) = 1) ∧
    -- (e) Semigroup law
    (∀ (s t : ℝ) (ξ : R3),
       heatMultiplier (s + t) ξ = heatMultiplier s ξ * heatMultiplier t ξ) :=
  ⟨heatMultiplier_nonneg,
   heatMultiplier_le_one,
   heatMultiplier_at_zero_time,
   heatMultiplier_at_zero_freq,
   heatMultiplier_add⟩

/-! ## §5 — Axiom audit -/

#print axioms heatMultiplier_nonneg
#print axioms heatMultiplier_le_one
#print axioms heatMultiplier_at_zero_time
#print axioms heatMultiplier_at_zero_freq
#print axioms heatMultiplier_add
#print axioms fujitaKato_heat_multiplier_brick_capstone

end PF.NavierStokes.FujitaKato1964.HeatSemigroupFourier
