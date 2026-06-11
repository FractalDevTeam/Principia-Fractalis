/-
# Fujita-Kato 1964 — Heat Semigroup Contracts the Ḣ^{1/2} Seminorm (Frequency-Domain Image)

★ 2026-06-10 — Bridge result combining the SobolevSeminormFourier shell
  with the HeatSemigroupOperator shell.

This is one of the key ingredients of the Fujita-Kato 1964 contraction
argument: the heat semigroup `e^{tΔ}` is dissipative at the
frequency-domain level, hence cannot grow the homogeneous Sobolev
`Ḣ^{1/2}` seminorm.

At the frequency-domain image layer (no Fourier inversion required),
the statement is

  `∫ ‖ξ‖ · ‖heatEvolveFreq t f ξ‖² dξ ≤ ‖f‖²_{Ḣ^{1/2}}`     (★)

for `t ≥ 0` and any scalar Schwartz `f`. The proof outline is:

  (1) Pointwise: `‖heatEvolveFreq t f ξ‖² = m_t(ξ)² · ‖(F f) ξ‖²`
  (2) Pointwise: `0 ≤ m_t(ξ) ≤ 1` for `t ≥ 0`, so `m_t(ξ)² ≤ 1`
  (3) Pointwise: `‖ξ‖ · ‖heatEvolveFreq t f ξ‖² ≤ ‖ξ‖ · ‖(F f) ξ‖² = h12IntegrandSq f ξ`
  (4) Integrating gives (★)

Step (4) requires integrability of the comparison RHS to invoke the
mathlib monotonicity lemma `integral_mono_of_nonneg`. The integrability
of `h12IntegrandSq f` on Schwartz inputs is the genuine Plancherel +
weighted-decay finiteness statement that lives in its own brick
(`SobolevSeminormFiniteness.lean` ladder). To keep this brick
kernel-only and not block on that orthogonal piece, the integrated
contraction bound is stated CONDITIONAL on integrability of
`h12IntegrandSq f`. The unconditional pointwise contraction (§2) and
the unconditional zero-time identity (§5) hold without any integrability
assumption.

For the zero Schwartz input the integrated bound holds unconditionally
because both sides vanish — landed in §4 as a sanity check.

Scope: scalar (`ℂ`-valued) Schwartz on `EuclideanSpace ℝ (Fin 3)`.

Imports: the seminorm shell, the heat multiplier shell, and the
heat-evolved frequency-domain image shell.

Axiom-free under `[propext, Classical.choice, Quot.sound]` only.

Author: Pablo Cohen (framework + formalization, 2026-06-10)
-/

import PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier
import PF.NavierStokes.FujitaKato1964.HeatSemigroupFourier
import PF.NavierStokes.FujitaKato1964.HeatSemigroupOperator

set_option autoImplicit false

namespace PF.NavierStokes.FujitaKato1964.HeatContractsSobolev

open MeasureTheory SchwartzMap
open PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier
  (R3 ScalarSchwartz3C h12IntegrandSq h12IntegrandSq_nonneg
   h12IntegrandSq_zero homogeneousH12SeminormSq
   homogeneousH12SeminormSq_zero)
open PF.NavierStokes.FujitaKato1964.HeatSemigroupFourier
  (heatMultiplier heatMultiplier_le_one heatMultiplier_nonneg)
open PF.NavierStokes.FujitaKato1964.HeatSemigroupOperator
  (heatEvolveFreq heatEvolveFreq_at_zero_time heatEvolveFreq_zero_input
   norm_heatEvolveFreq_le)

/-! ## §1 — Heat-evolved Sobolev integrand -/

/-- **Pointwise integrand of the heat-evolved homogeneous Ḣ^{1/2}
seminorm squared.**

For a scalar Schwartz function `f`, a time `t ∈ ℝ`, and a frequency
`ξ ∈ ℝ³`, the integrand is

  `‖ξ‖ · ‖heatEvolveFreq t f ξ‖²`.

Integrating over `ξ ∈ ℝ³` gives the heat-evolved `Ḣ^{1/2}` seminorm
squared, the load-bearing quantity for the linear-propagator contraction
estimate of Fujita-Kato. -/
noncomputable def h12IntegrandSqOfHeatEvolved
    (t : ℝ) (f : ScalarSchwartz3C) (ξ : R3) : ℝ :=
  ‖ξ‖ * ‖heatEvolveFreq t f ξ‖ ^ 2

/-! ## §2 — Pointwise contraction of the integrand -/

/-- **The heat-evolved Sobolev integrand is pointwise non-negative.**
The factor `‖ξ‖` is non-negative and the squared norm `‖·‖²` is
non-negative. -/
theorem h12IntegrandSqOfHeatEvolved_nonneg
    (t : ℝ) (f : ScalarSchwartz3C) (ξ : R3) :
    0 ≤ h12IntegrandSqOfHeatEvolved t f ξ :=
  mul_nonneg (norm_nonneg _) (sq_nonneg _)

/-- **Pointwise contraction of the heat-evolved Sobolev integrand
at non-negative times.**

For `t ≥ 0` the frequency-domain heat image is bounded in norm by the
Fourier transform of the input (the operator-shell theorem
`norm_heatEvolveFreq_le`). Squaring and multiplying by `‖ξ‖ ≥ 0`
preserves the inequality, yielding

  `‖ξ‖ · ‖heatEvolveFreq t f ξ‖² ≤ ‖ξ‖ · ‖(F f) ξ‖² = h12IntegrandSq f ξ`.

This is the pointwise form of the heat-semigroup `Ḣ^{1/2}` contraction
estimate, before any integration. -/
theorem h12IntegrandSqOfHeatEvolved_le
    (t : ℝ) (ht : 0 ≤ t) (f : ScalarSchwartz3C) (ξ : R3) :
    h12IntegrandSqOfHeatEvolved t f ξ ≤ h12IntegrandSq f ξ := by
  unfold h12IntegrandSqOfHeatEvolved h12IntegrandSq
  have h_norm_le : ‖heatEvolveFreq t f ξ‖
      ≤ ‖(fourierTransformCLM ℂ f) ξ‖ :=
    norm_heatEvolveFreq_le t ht f ξ
  have h_norm_nn : 0 ≤ ‖heatEvolveFreq t f ξ‖ := norm_nonneg _
  have h_sq_le : ‖heatEvolveFreq t f ξ‖ ^ 2
      ≤ ‖(fourierTransformCLM ℂ f) ξ‖ ^ 2 :=
    pow_le_pow_left₀ h_norm_nn h_norm_le 2
  have h_xi_nn : 0 ≤ ‖ξ‖ := norm_nonneg _
  exact mul_le_mul_of_nonneg_left h_sq_le h_xi_nn

/-- **For the zero Schwartz input the heat-evolved integrand
vanishes identically.** The frequency-domain image of zero is zero
(`heatEvolveFreq_zero_input`), so its squared norm is zero. -/
theorem h12IntegrandSqOfHeatEvolved_zero
    (t : ℝ) (ξ : R3) :
    h12IntegrandSqOfHeatEvolved t (0 : ScalarSchwartz3C) ξ = 0 := by
  unfold h12IntegrandSqOfHeatEvolved
  rw [heatEvolveFreq_zero_input]
  simp

/-! ## §3 — Integrated heat-evolved seminorm -/

/-- **Integrated heat-evolved homogeneous Ḣ^{1/2} seminorm squared.**

  `∫ ξ ∈ ℝ³, ‖ξ‖ · ‖heatEvolveFreq t f ξ‖² dξ`

This is the frequency-domain image of the squared `Ḣ^{1/2}` seminorm
of the heat-evolved Schwartz function. Plancherel transports it to
the physical-space heat-evolved Sobolev seminorm; the Plancherel /
Fourier-inversion bridge to physical space is a separate brick. -/
noncomputable def homogeneousH12SeminormSqOfHeatEvolved
    (t : ℝ) (f : ScalarSchwartz3C) : ℝ :=
  ∫ ξ : R3, h12IntegrandSqOfHeatEvolved t f ξ

/-- **The heat-evolved Ḣ^{1/2} seminorm squared is non-negative.**
Follows from pointwise non-negativity of the integrand and monotonicity
of the Bochner integral. -/
theorem homogeneousH12SeminormSqOfHeatEvolved_nonneg
    (t : ℝ) (f : ScalarSchwartz3C) :
    0 ≤ homogeneousH12SeminormSqOfHeatEvolved t f := by
  unfold homogeneousH12SeminormSqOfHeatEvolved
  exact MeasureTheory.integral_nonneg
    (fun ξ => h12IntegrandSqOfHeatEvolved_nonneg t f ξ)

/-- **For the zero Schwartz input the heat-evolved seminorm squared
is zero.** The integrand vanishes identically. -/
theorem homogeneousH12SeminormSqOfHeatEvolved_zero (t : ℝ) :
    homogeneousH12SeminormSqOfHeatEvolved t (0 : ScalarSchwartz3C) = 0 := by
  unfold homogeneousH12SeminormSqOfHeatEvolved
  simp only [h12IntegrandSqOfHeatEvolved_zero, integral_zero]

/-! ## §4 — The bridge contraction bound -/

/-- **Heat-semigroup contraction of the Ḣ^{1/2} seminorm squared at the
frequency-domain image level, conditional on integrability of the
comparison RHS.**

For any `t ≥ 0` and any scalar Schwartz `f` such that the comparison
integrand `h12IntegrandSq f` is integrable,

  `∫ ‖ξ‖ · ‖heatEvolveFreq t f ξ‖² dξ ≤ ∫ ‖ξ‖ · ‖(F f) ξ‖² dξ`,

i.e., the heat-evolved `Ḣ^{1/2}` seminorm squared at the frequency-domain
image level is bounded above by the Sobolev seminorm squared of `f`.

This is the linear-propagator dissipation step of Fujita-Kato 1964:
heat is dissipative, so it cannot grow the homogeneous Sobolev seminorm
of the data. The integrability hypothesis on `h12IntegrandSq f` is the
genuine Plancherel / weighted-decay finiteness statement; it lives in
its own brick (`SobolevSeminormFiniteness.lean` ladder). The pointwise
contraction (§2) and the algebraic identities (§3, §5) hold
unconditionally.

Proof: from the pointwise contraction (§2) plus integral monotonicity
via `MeasureTheory.integral_mono_of_nonneg`, using non-negativity of
the heat-evolved integrand on the LHS and integrability of the comparison
integrand on the RHS. -/
theorem homogeneousH12SeminormSqOfHeatEvolved_le_under_integrability
    (t : ℝ) (ht : 0 ≤ t) (f : ScalarSchwartz3C)
    (hIntegrable : MeasureTheory.Integrable (h12IntegrandSq f)) :
    homogeneousH12SeminormSqOfHeatEvolved t f
      ≤ homogeneousH12SeminormSq f := by
  unfold homogeneousH12SeminormSqOfHeatEvolved homogeneousH12SeminormSq
  refine MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall
      (fun ξ => h12IntegrandSqOfHeatEvolved_nonneg t f ξ))
    hIntegrable
    (Filter.Eventually.of_forall
      (fun ξ => h12IntegrandSqOfHeatEvolved_le t ht f ξ))

/-- **Unconditional zero-input case of the contraction bound.**
For the zero Schwartz function both sides vanish, so the contraction
bound holds trivially without any integrability hypothesis. This serves
as a sanity check on the statement. -/
theorem homogeneousH12SeminormSqOfHeatEvolved_le_zero_input
    (t : ℝ) :
    homogeneousH12SeminormSqOfHeatEvolved t (0 : ScalarSchwartz3C)
      ≤ homogeneousH12SeminormSq (0 : ScalarSchwartz3C) := by
  rw [homogeneousH12SeminormSqOfHeatEvolved_zero,
      homogeneousH12SeminormSq_zero]

/-! ## §5 — Initial-time identity -/

/-- **At `t = 0` the heat-evolved Ḣ^{1/2} seminorm squared equals the
original.** At zero time the heat multiplier collapses to `1`, so
`heatEvolveFreq 0 f ξ = (F f) ξ` (the operator-shell theorem
`heatEvolveFreq_at_zero_time`). Therefore the integrand
`‖ξ‖ · ‖heatEvolveFreq 0 f ξ‖²` matches the original Sobolev integrand
`h12IntegrandSq f ξ` pointwise, and the integrals coincide.

This is the avatar of `e^{0·Δ} = I` at the level of the squared `Ḣ^{1/2}`
seminorm: dissipation has not yet acted, so no contraction has yet
occurred. -/
theorem homogeneousH12SeminormSqOfHeatEvolved_at_zero
    (f : ScalarSchwartz3C) :
    homogeneousH12SeminormSqOfHeatEvolved 0 f = homogeneousH12SeminormSq f := by
  unfold homogeneousH12SeminormSqOfHeatEvolved homogeneousH12SeminormSq
  congr 1
  funext ξ
  unfold h12IntegrandSqOfHeatEvolved h12IntegrandSq
  rw [heatEvolveFreq_at_zero_time]

/-! ## §6 — Capstone -/

/-- **★ Fujita-Kato heat-contracts-Sobolev brick capstone ★**

Bundles the six results of this file:

  (a) Pointwise non-negativity of the heat-evolved Sobolev integrand
  (b) Pointwise contraction of the heat-evolved Sobolev integrand at
      non-negative times: `‖ξ‖ · ‖heatEvolveFreq t f ξ‖² ≤ h12IntegrandSq f ξ`
  (c) Pointwise vanishing on the zero input
  (d) Non-negativity of the integrated heat-evolved seminorm squared
  (e) Conditional contraction bound at the integrated level:
      under integrability of `h12IntegrandSq f`, the heat-evolved
      `Ḣ^{1/2}` seminorm squared is bounded above by the original
  (f) Initial-time identity:
      `homogeneousH12SeminormSqOfHeatEvolved 0 f = homogeneousH12SeminormSq f`

This is the linear-propagator dissipation step of Fujita-Kato 1964 at
the frequency-domain image level: heat cannot grow the homogeneous
`Ḣ^{1/2}` seminorm. The integrability hypothesis in (e) is the genuine
Plancherel / weighted-decay finiteness statement for the Sobolev
integrand on Schwartz inputs, which lives in the
`SobolevSeminormFiniteness.lean` ladder. The pointwise contraction
(a)-(c) and the initial-time identity (f) hold unconditionally.

Axiom-free: depends on `[propext, Classical.choice, Quot.sound]`
only. -/
theorem fujitaKato_heat_contracts_sobolev_brick_capstone :
    -- (a) Integrand non-negativity
    (∀ (t : ℝ) (f : ScalarSchwartz3C) (ξ : R3),
       0 ≤ h12IntegrandSqOfHeatEvolved t f ξ) ∧
    -- (b) Pointwise contraction at non-negative times
    (∀ (t : ℝ), 0 ≤ t → ∀ (f : ScalarSchwartz3C) (ξ : R3),
       h12IntegrandSqOfHeatEvolved t f ξ ≤ h12IntegrandSq f ξ) ∧
    -- (c) Pointwise vanishing on zero input
    (∀ (t : ℝ) (ξ : R3),
       h12IntegrandSqOfHeatEvolved t (0 : ScalarSchwartz3C) ξ = 0) ∧
    -- (d) Integrated non-negativity
    (∀ (t : ℝ) (f : ScalarSchwartz3C),
       0 ≤ homogeneousH12SeminormSqOfHeatEvolved t f) ∧
    -- (e) Conditional integrated contraction bound
    (∀ (t : ℝ), 0 ≤ t → ∀ (f : ScalarSchwartz3C),
       MeasureTheory.Integrable (h12IntegrandSq f) →
       homogeneousH12SeminormSqOfHeatEvolved t f
         ≤ homogeneousH12SeminormSq f) ∧
    -- (f) Initial-time identity
    (∀ (f : ScalarSchwartz3C),
       homogeneousH12SeminormSqOfHeatEvolved 0 f
         = homogeneousH12SeminormSq f) :=
  ⟨h12IntegrandSqOfHeatEvolved_nonneg,
   h12IntegrandSqOfHeatEvolved_le,
   h12IntegrandSqOfHeatEvolved_zero,
   homogeneousH12SeminormSqOfHeatEvolved_nonneg,
   homogeneousH12SeminormSqOfHeatEvolved_le_under_integrability,
   homogeneousH12SeminormSqOfHeatEvolved_at_zero⟩

/-! ## §7 — Axiom audit -/

#print axioms h12IntegrandSqOfHeatEvolved_nonneg
#print axioms h12IntegrandSqOfHeatEvolved_le
#print axioms h12IntegrandSqOfHeatEvolved_zero
#print axioms homogeneousH12SeminormSqOfHeatEvolved_nonneg
#print axioms homogeneousH12SeminormSqOfHeatEvolved_zero
#print axioms homogeneousH12SeminormSqOfHeatEvolved_le_under_integrability
#print axioms homogeneousH12SeminormSqOfHeatEvolved_le_zero_input
#print axioms homogeneousH12SeminormSqOfHeatEvolved_at_zero
#print axioms fujitaKato_heat_contracts_sobolev_brick_capstone

end PF.NavierStokes.FujitaKato1964.HeatContractsSobolev
