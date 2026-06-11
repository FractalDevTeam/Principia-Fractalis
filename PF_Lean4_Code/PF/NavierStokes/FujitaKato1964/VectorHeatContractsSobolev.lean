/-
# Fujita-Kato 1964 — Vector Heat Semigroup Contracts the Vector Ḣ^{1/2} Seminorm (Frequency-Domain Image)

★ 2026-06-10 — Vector extension of `HeatContractsSobolev.lean` combining the
  `SobolevSeminormVector` shell with the `HeatSemigroupVector` shell.

This is the version Navier-Stokes actually uses: the velocity field is a
`ℂ³`-valued 3-vector after complexification, so the load-bearing
dissipativity statement of Fujita-Kato 1964 is the **vector** heat
semigroup contraction of the vector `Ḣ^{1/2}` seminorm.

At the frequency-domain image layer (no Fourier inversion required),
the statement is

  `∫ ‖ξ‖ · ‖vectorHeatEvolveFreq t u ξ‖²_{ℂ³} dξ ≤ ‖u‖²_{Ḣ^{1/2}(ℝ³; ℂ³)}`     (★)

for `t ≥ 0` and any vector Schwartz `u : ℝ³ → ℂ³`. The proof outline
mechanically mirrors the scalar version of `HeatContractsSobolev.lean`:

  (1) Pointwise: `‖vectorHeatEvolveFreq t u ξ‖² = m_t(ξ)² · ‖(F u) ξ‖²_{ℂ³}`
  (2) Pointwise: `0 ≤ m_t(ξ) ≤ 1` for `t ≥ 0`, so `m_t(ξ)² ≤ 1`
  (3) Pointwise: `‖ξ‖ · ‖vectorHeatEvolveFreq t u ξ‖² ≤ ‖ξ‖ · ‖(F u) ξ‖²
                 = vectorH12IntegrandSq u ξ`
  (4) Integrating gives (★)

Step (4) requires integrability of the comparison RHS to invoke the
mathlib monotonicity lemma `integral_mono_of_nonneg`. The integrability
of `vectorH12IntegrandSq u` on vector Schwartz inputs is the genuine
Plancherel + weighted-decay finiteness statement that lives in its own
brick (the vector analogue of `SobolevSeminormFiniteness.lean`). To
keep this brick kernel-only and not block on that orthogonal piece,
the integrated contraction bound is stated CONDITIONAL on integrability
of `vectorH12IntegrandSq u`. The unconditional pointwise contraction
(§2) and the unconditional zero-time identity (§5) hold without any
integrability assumption.

For the zero vector Schwartz input the integrated bound holds
unconditionally because both sides vanish — landed in §4 as a sanity
check.

Scope: vector (`ℂ³`-valued) Schwartz on `EuclideanSpace ℝ (Fin 3)`.
Mechanical componentwise lift of the scalar version of
`HeatContractsSobolev.lean`. This is the form Navier-Stokes consumes.

Imports: the vector seminorm shell, the vector heat operator shell, and
the scalar `HeatContractsSobolev` brick (for naming consistency /
reference).

Axiom-free under `[propext, Classical.choice, Quot.sound]` only.

Author: Pablo Cohen (framework + formalization, 2026-06-10)
-/

import PF.NavierStokes.FujitaKato1964.SobolevSeminormVector
import PF.NavierStokes.FujitaKato1964.HeatSemigroupVector
import PF.NavierStokes.FujitaKato1964.HeatContractsSobolev

set_option autoImplicit false

namespace PF.NavierStokes.FujitaKato1964.VectorHeatContractsSobolev

open MeasureTheory SchwartzMap
open PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier
  (R3 C3 VectorSchwartz3C vectorH12IntegrandSq vectorH12IntegrandSq_nonneg
   vectorH12IntegrandSq_zero vectorHomogeneousH12SeminormSq
   vectorHomogeneousH12SeminormSq_zero)
open PF.NavierStokes.FujitaKato1964.HeatSemigroupVector
  (vectorHeatEvolveFreq vectorHeatEvolveFreq_at_zero_time
   vectorHeatEvolveFreq_zero_input norm_vectorHeatEvolveFreq_le)

/-! ## §1 — Vector heat-evolved Sobolev integrand -/

/-- **Pointwise integrand of the vector heat-evolved homogeneous Ḣ^{1/2}
seminorm squared.**

For a vector Schwartz field `u : ℝ³ → ℂ³`, a time `t ∈ ℝ`, and a
frequency `ξ ∈ ℝ³`, the integrand is

  `‖ξ‖ · ‖vectorHeatEvolveFreq t u ξ‖²_{ℂ³}`.

Integrating over `ξ ∈ ℝ³` gives the heat-evolved vector `Ḣ^{1/2}`
seminorm squared, the load-bearing quantity for the vector
linear-propagator contraction estimate of Fujita-Kato. This is the
version the real Navier-Stokes Cauchy problem consumes after
complexification of the velocity field. -/
noncomputable def vectorH12IntegrandSqOfHeatEvolved
    (t : ℝ) (u : VectorSchwartz3C) (ξ : R3) : ℝ :=
  ‖ξ‖ * ‖vectorHeatEvolveFreq t u ξ‖ ^ 2

/-! ## §2 — Pointwise properties -/

/-- **The vector heat-evolved Sobolev integrand is pointwise
non-negative.** The factor `‖ξ‖` is non-negative and the squared norm
`‖·‖²` is non-negative. -/
theorem vectorH12IntegrandSqOfHeatEvolved_nonneg
    (t : ℝ) (u : VectorSchwartz3C) (ξ : R3) :
    0 ≤ vectorH12IntegrandSqOfHeatEvolved t u ξ :=
  mul_nonneg (norm_nonneg _) (sq_nonneg _)

/-- **Pointwise contraction of the vector heat-evolved Sobolev integrand
at non-negative times.**

For `t ≥ 0` the frequency-domain vector heat image is bounded in
`ℂ³`-norm by the Fourier transform of the input (the vector
operator-shell theorem `norm_vectorHeatEvolveFreq_le`). Squaring and
multiplying by `‖ξ‖ ≥ 0` preserves the inequality, yielding

  `‖ξ‖ · ‖vectorHeatEvolveFreq t u ξ‖² ≤ ‖ξ‖ · ‖(F u) ξ‖²
        = vectorH12IntegrandSq u ξ`.

This is the pointwise form of the vector heat-semigroup `Ḣ^{1/2}`
contraction estimate, before any integration. Mechanical componentwise
lift of the scalar `h12IntegrandSqOfHeatEvolved_le`. -/
theorem vectorH12IntegrandSqOfHeatEvolved_le
    (t : ℝ) (ht : 0 ≤ t) (u : VectorSchwartz3C) (ξ : R3) :
    vectorH12IntegrandSqOfHeatEvolved t u ξ ≤ vectorH12IntegrandSq u ξ := by
  unfold vectorH12IntegrandSqOfHeatEvolved vectorH12IntegrandSq
  have h_norm_le : ‖vectorHeatEvolveFreq t u ξ‖
      ≤ ‖(fourierTransformCLM ℂ u) ξ‖ :=
    norm_vectorHeatEvolveFreq_le t ht u ξ
  have h_norm_nn : 0 ≤ ‖vectorHeatEvolveFreq t u ξ‖ := norm_nonneg _
  have h_sq_le : ‖vectorHeatEvolveFreq t u ξ‖ ^ 2
      ≤ ‖(fourierTransformCLM ℂ u) ξ‖ ^ 2 :=
    pow_le_pow_left₀ h_norm_nn h_norm_le 2
  have h_xi_nn : 0 ≤ ‖ξ‖ := norm_nonneg _
  exact mul_le_mul_of_nonneg_left h_sq_le h_xi_nn

/-- **For the zero vector Schwartz input the heat-evolved integrand
vanishes identically.** The frequency-domain image of the zero vector
field is zero (`vectorHeatEvolveFreq_zero_input`), so its squared norm
is zero. -/
theorem vectorH12IntegrandSqOfHeatEvolved_zero
    (t : ℝ) (ξ : R3) :
    vectorH12IntegrandSqOfHeatEvolved t (0 : VectorSchwartz3C) ξ = 0 := by
  unfold vectorH12IntegrandSqOfHeatEvolved
  rw [vectorHeatEvolveFreq_zero_input]
  simp

/-! ## §3 — Integrated vector heat-evolved seminorm -/

/-- **Integrated vector heat-evolved homogeneous Ḣ^{1/2} seminorm
squared.**

  `∫ ξ ∈ ℝ³, ‖ξ‖ · ‖vectorHeatEvolveFreq t u ξ‖²_{ℂ³} dξ`

This is the frequency-domain image of the squared vector `Ḣ^{1/2}`
seminorm of the heat-evolved vector Schwartz field. Plancherel
transports it to the physical-space heat-evolved vector Sobolev
seminorm; the Plancherel / Fourier-inversion bridge to physical space
is a separate brick. -/
noncomputable def vectorHomogeneousH12SeminormSqOfHeatEvolved
    (t : ℝ) (u : VectorSchwartz3C) : ℝ :=
  ∫ ξ : R3, vectorH12IntegrandSqOfHeatEvolved t u ξ

/-- **The vector heat-evolved Ḣ^{1/2} seminorm squared is non-negative.**
Follows from pointwise non-negativity of the integrand and monotonicity
of the Bochner integral. -/
theorem vectorHomogeneousH12SeminormSqOfHeatEvolved_nonneg
    (t : ℝ) (u : VectorSchwartz3C) :
    0 ≤ vectorHomogeneousH12SeminormSqOfHeatEvolved t u := by
  unfold vectorHomogeneousH12SeminormSqOfHeatEvolved
  exact MeasureTheory.integral_nonneg
    (fun ξ => vectorH12IntegrandSqOfHeatEvolved_nonneg t u ξ)

/-- **For the zero vector Schwartz input the heat-evolved seminorm
squared is zero.** The integrand vanishes identically. -/
theorem vectorHomogeneousH12SeminormSqOfHeatEvolved_zero (t : ℝ) :
    vectorHomogeneousH12SeminormSqOfHeatEvolved t (0 : VectorSchwartz3C) = 0 := by
  unfold vectorHomogeneousH12SeminormSqOfHeatEvolved
  simp only [vectorH12IntegrandSqOfHeatEvolved_zero, integral_zero]

/-! ## §4 — The bridge contraction bound -/

/-- **Heat-semigroup contraction of the vector Ḣ^{1/2} seminorm squared
at the frequency-domain image level, conditional on integrability of the
comparison RHS.**

For any `t ≥ 0` and any vector Schwartz `u` such that the comparison
integrand `vectorH12IntegrandSq u` is integrable,

  `∫ ‖ξ‖ · ‖vectorHeatEvolveFreq t u ξ‖² dξ ≤ ∫ ‖ξ‖ · ‖(F u) ξ‖² dξ`,

i.e., the heat-evolved vector `Ḣ^{1/2}` seminorm squared at the
frequency-domain image level is bounded above by the vector Sobolev
seminorm squared of `u`.

This is the vector linear-propagator dissipation step of Fujita-Kato
1964: heat is dissipative, so it cannot grow the homogeneous vector
Sobolev seminorm of the data. The integrability hypothesis on
`vectorH12IntegrandSq u` is the genuine vector Plancherel /
weighted-decay finiteness statement; it lives in its own brick (the
vector analogue of the `SobolevSeminormFiniteness.lean` ladder). The
pointwise contraction (§2) and the algebraic identities (§3, §5) hold
unconditionally.

Proof: from the pointwise contraction (§2) plus integral monotonicity
via `MeasureTheory.integral_mono_of_nonneg`, using non-negativity of
the heat-evolved integrand on the LHS and integrability of the
comparison integrand on the RHS. Mechanical componentwise lift of the
scalar `homogeneousH12SeminormSqOfHeatEvolved_le_under_integrability`. -/
theorem vectorHomogeneousH12SeminormSqOfHeatEvolved_le_under_integrability
    (t : ℝ) (ht : 0 ≤ t) (u : VectorSchwartz3C)
    (hIntegrable : MeasureTheory.Integrable (vectorH12IntegrandSq u)) :
    vectorHomogeneousH12SeminormSqOfHeatEvolved t u
      ≤ vectorHomogeneousH12SeminormSq u := by
  unfold vectorHomogeneousH12SeminormSqOfHeatEvolved vectorHomogeneousH12SeminormSq
  refine MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall
      (fun ξ => vectorH12IntegrandSqOfHeatEvolved_nonneg t u ξ))
    hIntegrable
    (Filter.Eventually.of_forall
      (fun ξ => vectorH12IntegrandSqOfHeatEvolved_le t ht u ξ))

/-- **Unconditional zero-input case of the vector contraction bound.**
For the zero vector Schwartz field both sides vanish, so the contraction
bound holds trivially without any integrability hypothesis. This serves
as a sanity check on the statement. -/
theorem vectorHomogeneousH12SeminormSqOfHeatEvolved_le_zero_input
    (t : ℝ) :
    vectorHomogeneousH12SeminormSqOfHeatEvolved t (0 : VectorSchwartz3C)
      ≤ vectorHomogeneousH12SeminormSq (0 : VectorSchwartz3C) := by
  rw [vectorHomogeneousH12SeminormSqOfHeatEvolved_zero,
      vectorHomogeneousH12SeminormSq_zero]

/-! ## §5 — Initial-time identity -/

/-- **At `t = 0` the vector heat-evolved Ḣ^{1/2} seminorm squared equals
the original.** At zero time the heat multiplier collapses to `1`, so
`vectorHeatEvolveFreq 0 u ξ = (F u) ξ` (the vector operator-shell theorem
`vectorHeatEvolveFreq_at_zero_time`). Therefore the integrand
`‖ξ‖ · ‖vectorHeatEvolveFreq 0 u ξ‖²` matches the original vector
Sobolev integrand `vectorH12IntegrandSq u ξ` pointwise, and the
integrals coincide.

This is the avatar of `e^{0·Δ} = I` at the level of the squared vector
`Ḣ^{1/2}` seminorm: dissipation has not yet acted, so no contraction
has yet occurred. Mechanical componentwise lift of the scalar
`homogeneousH12SeminormSqOfHeatEvolved_at_zero`. -/
theorem vectorHomogeneousH12SeminormSqOfHeatEvolved_at_zero
    (u : VectorSchwartz3C) :
    vectorHomogeneousH12SeminormSqOfHeatEvolved 0 u
      = vectorHomogeneousH12SeminormSq u := by
  unfold vectorHomogeneousH12SeminormSqOfHeatEvolved vectorHomogeneousH12SeminormSq
  congr 1
  funext ξ
  unfold vectorH12IntegrandSqOfHeatEvolved vectorH12IntegrandSq
  rw [vectorHeatEvolveFreq_at_zero_time]

/-! ## §6 — Capstone -/

/-- **★ Fujita-Kato vector heat-contracts-Sobolev brick capstone ★**

Bundles the six results of this file:

  (a) Pointwise non-negativity of the vector heat-evolved Sobolev
      integrand
  (b) Pointwise contraction of the vector heat-evolved Sobolev integrand
      at non-negative times:
      `‖ξ‖ · ‖vectorHeatEvolveFreq t u ξ‖² ≤ vectorH12IntegrandSq u ξ`
  (c) Pointwise vanishing on the zero vector input
  (d) Non-negativity of the integrated vector heat-evolved seminorm
      squared
  (e) Conditional contraction bound at the integrated level:
      under integrability of `vectorH12IntegrandSq u`, the heat-evolved
      vector `Ḣ^{1/2}` seminorm squared is bounded above by the
      original
  (f) Initial-time identity:
      `vectorHomogeneousH12SeminormSqOfHeatEvolved 0 u
         = vectorHomogeneousH12SeminormSq u`

This is the vector linear-propagator dissipation step of Fujita-Kato
1964 at the frequency-domain image level — the version Navier-Stokes
actually consumes after complexification of the velocity field: heat
cannot grow the homogeneous vector `Ḣ^{1/2}` seminorm. The integrability
hypothesis in (e) is the genuine vector Plancherel / weighted-decay
finiteness statement for the vector Sobolev integrand on vector
Schwartz inputs, which lives in the vector analogue of the
`SobolevSeminormFiniteness.lean` ladder. The pointwise contraction
(a)-(c) and the initial-time identity (f) hold unconditionally.

Mechanical componentwise lift of the scalar capstone
`fujitaKato_heat_contracts_sobolev_brick_capstone` of
`HeatContractsSobolev.lean`.

Axiom-free: depends on `[propext, Classical.choice, Quot.sound]`
only. -/
theorem fujitaKato_vector_heat_contracts_sobolev_brick_capstone :
    -- (a) Integrand non-negativity
    (∀ (t : ℝ) (u : VectorSchwartz3C) (ξ : R3),
       0 ≤ vectorH12IntegrandSqOfHeatEvolved t u ξ) ∧
    -- (b) Pointwise contraction at non-negative times
    (∀ (t : ℝ), 0 ≤ t → ∀ (u : VectorSchwartz3C) (ξ : R3),
       vectorH12IntegrandSqOfHeatEvolved t u ξ ≤ vectorH12IntegrandSq u ξ) ∧
    -- (c) Pointwise vanishing on zero input
    (∀ (t : ℝ) (ξ : R3),
       vectorH12IntegrandSqOfHeatEvolved t (0 : VectorSchwartz3C) ξ = 0) ∧
    -- (d) Integrated non-negativity
    (∀ (t : ℝ) (u : VectorSchwartz3C),
       0 ≤ vectorHomogeneousH12SeminormSqOfHeatEvolved t u) ∧
    -- (e) Conditional integrated contraction bound
    (∀ (t : ℝ), 0 ≤ t → ∀ (u : VectorSchwartz3C),
       MeasureTheory.Integrable (vectorH12IntegrandSq u) →
       vectorHomogeneousH12SeminormSqOfHeatEvolved t u
         ≤ vectorHomogeneousH12SeminormSq u) ∧
    -- (f) Initial-time identity
    (∀ (u : VectorSchwartz3C),
       vectorHomogeneousH12SeminormSqOfHeatEvolved 0 u
         = vectorHomogeneousH12SeminormSq u) :=
  ⟨vectorH12IntegrandSqOfHeatEvolved_nonneg,
   vectorH12IntegrandSqOfHeatEvolved_le,
   vectorH12IntegrandSqOfHeatEvolved_zero,
   vectorHomogeneousH12SeminormSqOfHeatEvolved_nonneg,
   vectorHomogeneousH12SeminormSqOfHeatEvolved_le_under_integrability,
   vectorHomogeneousH12SeminormSqOfHeatEvolved_at_zero⟩

/-! ## §7 — Axiom audit -/

#print axioms vectorH12IntegrandSqOfHeatEvolved_nonneg
#print axioms vectorH12IntegrandSqOfHeatEvolved_le
#print axioms vectorH12IntegrandSqOfHeatEvolved_zero
#print axioms vectorHomogeneousH12SeminormSqOfHeatEvolved_nonneg
#print axioms vectorHomogeneousH12SeminormSqOfHeatEvolved_zero
#print axioms vectorHomogeneousH12SeminormSqOfHeatEvolved_le_under_integrability
#print axioms vectorHomogeneousH12SeminormSqOfHeatEvolved_le_zero_input
#print axioms vectorHomogeneousH12SeminormSqOfHeatEvolved_at_zero
#print axioms fujitaKato_vector_heat_contracts_sobolev_brick_capstone

end PF.NavierStokes.FujitaKato1964.VectorHeatContractsSobolev
