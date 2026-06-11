/-
# Fujita-Kato 1964 — Composite `Leray ∘ Heat` Contracts the Ḣ^{1/2} Seminorm

★ 2026-06-10 — Composite contraction brick of the Fujita-Kato Sobolev ladder.
★ Combines the two unconditional `Ḣ^{1/2}` contraction bricks:

    * `LerayContractsSobolev.lean`        — Leray operator-norm ≤ 1
    * `VectorHeatContractsSobolev.lean`   — vector heat-semigroup contraction
    * `VectorSobolevIntegrandIntegrable.lean` — unconditional integrability

into the single composite

    `heatLerayCompose t u ξ := lerayFourierSymbolC ξ (vectorHeatEvolveFreq t u ξ)`.

This is the operator that appears inside the Fujita-Kato mild-formulation
linear propagator `e^{tΔ} ∘ P`. Its frequency-side avatar inherits the
`Ḣ^{1/2}` contraction by composing the two factor-side contractions: the
Leray symbol is a contraction at every frequency (operator norm ≤ 1), and
the heat multiplier is bounded above by 1 at every non-negative time. So

    `‖heatLerayCompose t u ξ‖_{ℂ³}
       ≤ ‖vectorHeatEvolveFreq t u ξ‖_{ℂ³}
       ≤ ‖(F u) ξ‖_{ℂ³}`,

pointwise at every ξ. Squaring, multiplying by `‖ξ‖ ≥ 0`, and integrating
over `ξ ∈ ℝ³` against the unconditional vector Schwartz integrability of
`vectorH12IntegrandSq u` (from `VectorSobolevIntegrandIntegrable.lean`)
yields

    `∫ ‖ξ‖ · ‖heatLerayCompose t u ξ‖²_{ℂ³} dξ ≤ ‖u‖²_{Ḣ^{1/2}}`     (★)

for any `t ≥ 0` and any vector Schwartz `u`. This is the unconditional
contraction of the Fujita-Kato linear propagator on the homogeneous
vector `Ḣ^{1/2}` seminorm at the frequency-domain image level — the
key linear-side ingredient of the small-data global-existence theorem.

Bricks landed here:

  §1 — Pointwise composite integrand bound.
  §2 — Integrated composite contraction bound.
  §3 — Trivial cases (zero input, initial time).
  §4 — Capstone bundling §1-§3.
  §5 — `#print axioms` audit (kernel-only).

Axiom-free; depends only on `[propext, Classical.choice, Quot.sound]`.

Author: Pablo Cohen (framework + formalization, 2026-06-10)
-/

import PF.NavierStokes.FujitaKato1964.HeatLerayCompose
import PF.NavierStokes.FujitaKato1964.LerayContractsSobolev
import PF.NavierStokes.FujitaKato1964.VectorHeatContractsSobolev
import PF.NavierStokes.FujitaKato1964.VectorSobolevIntegrandIntegrable

set_option autoImplicit false

namespace PF.NavierStokes.FujitaKato1964.HeatLerayContractsSobolev

open MeasureTheory SchwartzMap
open PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier
  (R3 C3 VectorSchwartz3C vectorH12IntegrandSq vectorH12IntegrandSq_nonneg
   vectorH12IntegrandSq_zero vectorHomogeneousH12SeminormSq
   vectorHomogeneousH12SeminormSq_zero)
open PF.NavierStokes.FujitaKato1964.HeatSemigroupVector
  (vectorHeatEvolveFreq vectorHeatEvolveFreq_at_zero_time
   vectorHeatEvolveFreq_zero_input norm_vectorHeatEvolveFreq_le)
open PF.NavierStokes.FujitaKato1964.LerayProjectorOperator
  (lerayFourierSymbolC lerayProjectFreq
   lerayFourierSymbolC_zero_field)
open PF.NavierStokes.FujitaKato1964.HeatLerayCompose
  (heatLerayCompose heatLerayCompose_zero_input
   heatLerayCompose_at_zero_time_eq_lerayProjectFreq)
open PF.NavierStokes.FujitaKato1964.LerayContractsSobolev
  (norm_lerayFourierSymbolC_le vectorH12IntegrandSqOfLeray)
open PF.NavierStokes.FujitaKato1964.VectorSobolevIntegrandIntegrable
  (vectorH12IntegrandSq_integrable_general)

/-! ## §1 — Pointwise composite integrand bound -/

/-- **Pointwise integrand of the composite `Leray ∘ Heat` Ḣ^{1/2} seminorm
squared.**

For a vector Schwartz field `u`, a time `t ∈ ℝ`, and a frequency `ξ ∈ ℝ³`,
the integrand is

  `‖ξ‖ · ‖heatLerayCompose t u ξ‖²_{ℂ³}`.

Integrating over `ξ ∈ ℝ³` gives the squared `Ḣ^{1/2}` seminorm of the
composite frequency-domain image. This is the load-bearing quantity for
the unconditional Fujita-Kato linear-propagator contraction estimate
on the vector velocity field after complexification. -/
noncomputable def vectorH12IntegrandSqOfHeatLeray
    (t : ℝ) (u : VectorSchwartz3C) (ξ : R3) : ℝ :=
  ‖ξ‖ * ‖heatLerayCompose t u ξ‖ ^ 2

/-- **The composite Sobolev integrand is pointwise non-negative.** The
factor `‖ξ‖` is non-negative and the squared norm `‖·‖²` is non-negative. -/
theorem vectorH12IntegrandSqOfHeatLeray_nonneg
    (t : ℝ) (u : VectorSchwartz3C) (ξ : R3) :
    0 ≤ vectorH12IntegrandSqOfHeatLeray t u ξ :=
  mul_nonneg (norm_nonneg _) (sq_nonneg _)

/-- **★ Pointwise contraction of the composite `Leray ∘ Heat` Sobolev
integrand at non-negative times.**

Two factor-side operator-norm bounds chain:

  * Leray operator-norm bound at frequency `ξ`:
    `‖lerayFourierSymbolC ξ w‖ ≤ ‖w‖` (`norm_lerayFourierSymbolC_le`,
    from `LerayContractsSobolev.lean`).
  * Vector heat-semigroup bound at non-negative time `t`:
    `‖vectorHeatEvolveFreq t u ξ‖ ≤ ‖(F u) ξ‖` (`norm_vectorHeatEvolveFreq_le`,
    from `HeatSemigroupVector.lean`).

Composing them at the specific complex vector
`w := vectorHeatEvolveFreq t u ξ` yields

  `‖heatLerayCompose t u ξ‖
       = ‖lerayFourierSymbolC ξ (vectorHeatEvolveFreq t u ξ)‖
       ≤ ‖vectorHeatEvolveFreq t u ξ‖
       ≤ ‖(F u) ξ‖`.

Squaring (all sides non-negative) and multiplying by `‖ξ‖ ≥ 0` preserves
the inequality, giving

  `‖ξ‖ · ‖heatLerayCompose t u ξ‖² ≤ ‖ξ‖ · ‖(F u) ξ‖² = vectorH12IntegrandSq u ξ`.

This is the pointwise form of the composite `Leray ∘ Heat` contraction
estimate, before any integration. -/
theorem vectorH12IntegrandSqOfHeatLeray_le
    (t : ℝ) (ht : 0 ≤ t) (u : VectorSchwartz3C) (ξ : R3) :
    vectorH12IntegrandSqOfHeatLeray t u ξ ≤ vectorH12IntegrandSq u ξ := by
  unfold vectorH12IntegrandSqOfHeatLeray vectorH12IntegrandSq
  -- Step 1: composite norm bound via the two factor-side operator-norm bounds.
  have h_leray : ‖heatLerayCompose t u ξ‖
      ≤ ‖vectorHeatEvolveFreq t u ξ‖ := by
    unfold heatLerayCompose
    exact norm_lerayFourierSymbolC_le ξ _
  have h_heat : ‖vectorHeatEvolveFreq t u ξ‖
      ≤ ‖(fourierTransformCLM ℂ u) ξ‖ :=
    norm_vectorHeatEvolveFreq_le t ht u ξ
  have h_norm_le : ‖heatLerayCompose t u ξ‖
      ≤ ‖(fourierTransformCLM ℂ u) ξ‖ :=
    le_trans h_leray h_heat
  -- Step 2: square the chained bound.
  have h_norm_nn : 0 ≤ ‖heatLerayCompose t u ξ‖ := norm_nonneg _
  have h_sq_le : ‖heatLerayCompose t u ξ‖ ^ 2
      ≤ ‖(fourierTransformCLM ℂ u) ξ‖ ^ 2 :=
    pow_le_pow_left₀ h_norm_nn h_norm_le 2
  -- Step 3: multiply by ‖ξ‖ ≥ 0.
  have h_xi_nn : 0 ≤ ‖ξ‖ := norm_nonneg _
  exact mul_le_mul_of_nonneg_left h_sq_le h_xi_nn

/-- **For the zero vector Schwartz input the composite integrand vanishes
identically.** The composite of the zero field is the zero function on
`R3` (`heatLerayCompose_zero_input`), so its squared norm is zero. -/
theorem vectorH12IntegrandSqOfHeatLeray_zero
    (t : ℝ) (ξ : R3) :
    vectorH12IntegrandSqOfHeatLeray t (0 : VectorSchwartz3C) ξ = 0 := by
  unfold vectorH12IntegrandSqOfHeatLeray
  rw [heatLerayCompose_zero_input]
  simp

/-! ## §2 — Integrated composite contraction bound -/

/-- **Integrated composite `Leray ∘ Heat` homogeneous Ḣ^{1/2} seminorm
squared.**

  `∫ ξ ∈ ℝ³, ‖ξ‖ · ‖heatLerayCompose t u ξ‖²_{ℂ³} dξ`

This is the frequency-domain image of the squared `Ḣ^{1/2}` seminorm of
the composite linear propagator `e^{tΔ} ∘ P` applied to the vector
Schwartz field `u`. Plancherel transports it to the physical-space
composite Sobolev seminorm; the Plancherel / Fourier-inversion bridge to
physical space is a separate brick. -/
noncomputable def vectorHomogeneousH12SeminormSqOfHeatLeray
    (t : ℝ) (u : VectorSchwartz3C) : ℝ :=
  ∫ ξ : R3, vectorH12IntegrandSqOfHeatLeray t u ξ

/-- **The composite Ḣ^{1/2} seminorm squared is non-negative.** Follows
from pointwise non-negativity of the integrand and monotonicity of the
Bochner integral. -/
theorem vectorHomogeneousH12SeminormSqOfHeatLeray_nonneg
    (t : ℝ) (u : VectorSchwartz3C) :
    0 ≤ vectorHomogeneousH12SeminormSqOfHeatLeray t u := by
  unfold vectorHomogeneousH12SeminormSqOfHeatLeray
  exact MeasureTheory.integral_nonneg
    (fun ξ => vectorH12IntegrandSqOfHeatLeray_nonneg t u ξ)

/-- **For the zero vector Schwartz input the composite seminorm squared
is zero.** The integrand vanishes identically. -/
theorem vectorHomogeneousH12SeminormSqOfHeatLeray_zero (t : ℝ) :
    vectorHomogeneousH12SeminormSqOfHeatLeray t (0 : VectorSchwartz3C) = 0 := by
  unfold vectorHomogeneousH12SeminormSqOfHeatLeray
  simp only [vectorH12IntegrandSqOfHeatLeray_zero, integral_zero]

/-- **★★★ THE HEADLINE THEOREM: composite `Leray ∘ Heat` contraction of
the homogeneous vector Ḣ^{1/2} seminorm squared at the frequency-domain
image level.** ★★★

For any `t ≥ 0` and any vector Schwartz `u`,

  `∫ ‖ξ‖ · ‖heatLerayCompose t u ξ‖² dξ
        ≤ ∫ ‖ξ‖ · ‖(F u) ξ‖² dξ = ‖u‖²_{Ḣ^{1/2}}`.

This is the unconditional composite linear-propagator dissipation step
of Fujita-Kato 1964 at the frequency-domain image level: the operator
`e^{tΔ} ∘ P` cannot grow the homogeneous vector Sobolev seminorm of the
data, without any extra hypothesis on the vector Schwartz input.

Proof: from the pointwise contraction (§1) plus integral monotonicity
via `MeasureTheory.integral_mono_of_nonneg`, using non-negativity of
the composite integrand on the LHS and the unconditional integrability
of the comparison integrand on the RHS
(`vectorH12IntegrandSq_integrable_general` from
`VectorSobolevIntegrandIntegrable.lean`). -/
theorem vectorHomogeneousH12SeminormSqOfHeatLeray_le
    (t : ℝ) (ht : 0 ≤ t) (u : VectorSchwartz3C) :
    vectorHomogeneousH12SeminormSqOfHeatLeray t u
      ≤ vectorHomogeneousH12SeminormSq u := by
  unfold vectorHomogeneousH12SeminormSqOfHeatLeray vectorHomogeneousH12SeminormSq
  refine MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall
      (fun ξ => vectorH12IntegrandSqOfHeatLeray_nonneg t u ξ))
    (vectorH12IntegrandSq_integrable_general u)
    (Filter.Eventually.of_forall
      (fun ξ => vectorH12IntegrandSqOfHeatLeray_le t ht u ξ))

/-! ## §3 — Trivial cases -/

/-- **Unconditional zero-input case of the composite contraction bound.**
For the zero vector Schwartz field both sides vanish, so the contraction
bound holds trivially without any hypothesis on `t`. This serves as a
sanity check on the statement. -/
theorem vectorHomogeneousH12SeminormSqOfHeatLeray_le_zero_input
    (t : ℝ) :
    vectorHomogeneousH12SeminormSqOfHeatLeray t (0 : VectorSchwartz3C)
      ≤ vectorHomogeneousH12SeminormSq (0 : VectorSchwartz3C) := by
  rw [vectorHomogeneousH12SeminormSqOfHeatLeray_zero,
      vectorHomogeneousH12SeminormSq_zero]

/-- **At `t = 0` the composite `Leray ∘ Heat` Ḣ^{1/2} seminorm squared
equals the Leray-projected Ḣ^{1/2} seminorm squared.** At zero time the
heat factor is the identity and the composite reduces to the pure Leray
projection (`heatLerayCompose_at_zero_time_eq_lerayProjectFreq`), so the
integrand `‖ξ‖ · ‖heatLerayCompose 0 u ξ‖²` matches the Leray-projected
integrand `vectorH12IntegrandSqOfLeray u ξ` pointwise, and the integrals
coincide.

This is the avatar of `e^{0·Δ} = I` at the composite-seminorm level:
dissipation has not yet acted, only the Leray projection. Combined with
the Leray contraction (§3 of `LerayContractsSobolev.lean`), this gives
the unconditional bound at `t = 0` directly. -/
theorem vectorHomogeneousH12SeminormSqOfHeatLeray_at_zero
    (u : VectorSchwartz3C) :
    vectorHomogeneousH12SeminormSqOfHeatLeray 0 u
      = PF.NavierStokes.FujitaKato1964.LerayContractsSobolev.vectorHomogeneousH12SeminormSqOfLeray u := by
  unfold vectorHomogeneousH12SeminormSqOfHeatLeray
    PF.NavierStokes.FujitaKato1964.LerayContractsSobolev.vectorHomogeneousH12SeminormSqOfLeray
  congr 1
  funext ξ
  unfold vectorH12IntegrandSqOfHeatLeray vectorH12IntegrandSqOfLeray
  rw [heatLerayCompose_at_zero_time_eq_lerayProjectFreq]

/-! ## §4 — Capstone -/

/-- **★ Fujita-Kato `Leray ∘ Heat` contracts-Sobolev brick capstone ★**

Bundles the seven results of this file:

  (a) Pointwise non-negativity of the composite Sobolev integrand
  (b) Pointwise contraction of the composite Sobolev integrand at
      non-negative times:
      `‖ξ‖ · ‖heatLerayCompose t u ξ‖² ≤ vectorH12IntegrandSq u ξ`
  (c) Pointwise vanishing on the zero vector input
  (d) Non-negativity of the integrated composite seminorm squared
  (e) Vanishing of the integrated composite seminorm squared on zero input
  (f) **HEADLINE — unconditional integrated contraction bound**:
      `vectorHomogeneousH12SeminormSqOfHeatLeray t u
          ≤ vectorHomogeneousH12SeminormSq u`
      for any `t ≥ 0` and any vector Schwartz `u`.
  (g) Initial-time identity to the Leray-projected Ḣ^{1/2} seminorm
      squared.

This is the unconditional composite linear-propagator dissipation step
of Fujita-Kato 1964 at the frequency-domain image level — the version
Navier-Stokes consumes after complexification of the velocity field.
The operator `e^{tΔ} ∘ P` cannot grow the homogeneous vector `Ḣ^{1/2}`
seminorm of the data: both factors are contractions, and composition
preserves this property.

Axiom-free: depends on `[propext, Classical.choice, Quot.sound]`
only. -/
theorem fujitaKato_heat_leray_contracts_sobolev_brick_capstone :
    -- (a) Integrand non-negativity
    (∀ (t : ℝ) (u : VectorSchwartz3C) (ξ : R3),
       0 ≤ vectorH12IntegrandSqOfHeatLeray t u ξ) ∧
    -- (b) Pointwise contraction at non-negative times
    (∀ (t : ℝ), 0 ≤ t → ∀ (u : VectorSchwartz3C) (ξ : R3),
       vectorH12IntegrandSqOfHeatLeray t u ξ ≤ vectorH12IntegrandSq u ξ) ∧
    -- (c) Pointwise vanishing on zero input
    (∀ (t : ℝ) (ξ : R3),
       vectorH12IntegrandSqOfHeatLeray t (0 : VectorSchwartz3C) ξ = 0) ∧
    -- (d) Integrated non-negativity
    (∀ (t : ℝ) (u : VectorSchwartz3C),
       0 ≤ vectorHomogeneousH12SeminormSqOfHeatLeray t u) ∧
    -- (e) Integrated vanishing on zero input
    (∀ (t : ℝ),
       vectorHomogeneousH12SeminormSqOfHeatLeray t (0 : VectorSchwartz3C) = 0) ∧
    -- (f) HEADLINE — unconditional integrated contraction bound
    (∀ (t : ℝ), 0 ≤ t → ∀ (u : VectorSchwartz3C),
       vectorHomogeneousH12SeminormSqOfHeatLeray t u
         ≤ vectorHomogeneousH12SeminormSq u) ∧
    -- (g) Initial-time identity
    (∀ (u : VectorSchwartz3C),
       vectorHomogeneousH12SeminormSqOfHeatLeray 0 u
         = PF.NavierStokes.FujitaKato1964.LerayContractsSobolev.vectorHomogeneousH12SeminormSqOfLeray u) :=
  ⟨vectorH12IntegrandSqOfHeatLeray_nonneg,
   vectorH12IntegrandSqOfHeatLeray_le,
   vectorH12IntegrandSqOfHeatLeray_zero,
   vectorHomogeneousH12SeminormSqOfHeatLeray_nonneg,
   vectorHomogeneousH12SeminormSqOfHeatLeray_zero,
   vectorHomogeneousH12SeminormSqOfHeatLeray_le,
   vectorHomogeneousH12SeminormSqOfHeatLeray_at_zero⟩

/-! ## §5 — Axiom audit -/

#print axioms vectorH12IntegrandSqOfHeatLeray_nonneg
#print axioms vectorH12IntegrandSqOfHeatLeray_le
#print axioms vectorH12IntegrandSqOfHeatLeray_zero
#print axioms vectorHomogeneousH12SeminormSqOfHeatLeray_nonneg
#print axioms vectorHomogeneousH12SeminormSqOfHeatLeray_zero
#print axioms vectorHomogeneousH12SeminormSqOfHeatLeray_le
#print axioms vectorHomogeneousH12SeminormSqOfHeatLeray_le_zero_input
#print axioms vectorHomogeneousH12SeminormSqOfHeatLeray_at_zero
#print axioms fujitaKato_heat_leray_contracts_sobolev_brick_capstone

end PF.NavierStokes.FujitaKato1964.HeatLerayContractsSobolev
