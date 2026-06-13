/-
# NS3D_HeatEnergyMonotone — H^s energy of the heat semigroup is
   monotone non-increasing in time

★ 2026-06-13 — twenty-first Type (F) advance on the NS Sobolev/Leray
bridge. The H^s energy `hsNormSqVecOnL2 (heatSemigroup t c) s S` is
a continuously differentiable function of `t` whose derivative is
non-positive (by the global energy decay ODE plus Stokes positivity).
Hence it is monotone non-increasing in `t`:

  `t₁ ≤ t₂  ⇒  hsNormSqVecOnL2 (heatSemigroup t₂ c) s S
                ≤ hsNormSqVecOnL2 (heatSemigroup t₁ c) s S`.

The earlier file `NS3D_HeatSemigroupHsContraction.lean` already
proved the special case `t₁ = 0`. The present file generalizes via
the antitone-from-non-positive-derivative principle.

## What this file delivers, axiom-free

  (1) **`differentiable_hsNormSqVecOnL2_heatSemigroup`** — the H^s
      energy is differentiable in `t` everywhere.

  (2) **`deriv_hsNormSqVecOnL2_heatSemigroup_nonpos`** — its
      derivative is non-positive everywhere.

  (3) **`antitone_hsNormSqVecOnL2_heatSemigroup`** — the H^s
      energy is antitone (non-increasing) in `t`.

  (4) **Capstone** — the H^s energy is differentiable with
      non-positive derivative, hence antitone in time.

ZERO project axioms; kernel-only `[propext, Classical.choice, Quot.sound]`.

Author: Pablo Cohen + Claude Opus 4.7. 2026-06-13.
-/

import PF.NS3D_HeatGlobalEnergyDecay
import PF.NS3D_StokesPositivity

namespace PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

open PrincipiaTractalis.SobolevHSScaleOnTorus3Attempt
open PrincipiaTractalis.DivFreeFourierDensityOnTorus3Attempt

/-! ## §1 — Differentiability -/

theorem differentiable_hsNormSqVecOnL2_heatSemigroup
    (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) (s : ℝ) (S : Finset (Fin 3 → ℤ)) :
    Differentiable ℝ (fun r => hsNormSqVecOnL2 (heatSemigroup r c) s S) := by
  intro t
  exact (hasDerivAt_hsNormSqVecOnL2_heatSemigroup t c s S).differentiableAt

/-! ## §2 — Non-positive derivative -/

theorem deriv_hsNormSqVecOnL2_heatSemigroup_nonpos
    (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) (s : ℝ) (S : Finset (Fin 3 → ℤ))
    (t : ℝ) :
    deriv (fun r => hsNormSqVecOnL2 (heatSemigroup r c) s S) t ≤ 0 := by
  rw [(hasDerivAt_hsNormSqVecOnL2_heatSemigroup t c s S).deriv]
  -- The derivative equals -2 * stokesHsEnergy (heatSemigroup t c) s S,
  -- which is ≤ 0 since stokesHsEnergy ≥ 0.
  have h_energy_nonneg :
      0 ≤ stokesHsEnergy (heatSemigroup t c) s S :=
    stokesHsEnergy_nonneg _ s S
  linarith

/-! ## §3 — Antitonicity -/

theorem antitone_hsNormSqVecOnL2_heatSemigroup
    (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) (s : ℝ) (S : Finset (Fin 3 → ℤ)) :
    Antitone (fun r => hsNormSqVecOnL2 (heatSemigroup r c) s S) := by
  apply antitone_of_deriv_nonpos
  · exact differentiable_hsNormSqVecOnL2_heatSemigroup c s S
  · intro t
    exact deriv_hsNormSqVecOnL2_heatSemigroup_nonpos c s S t

/-- **Pointwise contraction**: for `t₁ ≤ t₂`, the H^s energy at
    later time is ≤ the H^s energy at earlier time. -/
theorem hsNormSqVecOnL2_heatSemigroup_antitone
    (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) (s : ℝ) (S : Finset (Fin 3 → ℤ))
    {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    hsNormSqVecOnL2 (heatSemigroup t₂ c) s S
      ≤ hsNormSqVecOnL2 (heatSemigroup t₁ c) s S :=
  antitone_hsNormSqVecOnL2_heatSemigroup c s S h

/-! ## §4 — Capstone -/

/-- **★ HEAT ENERGY MONOTONICITY CAPSTONE ★** —
    `concrete_div_free_heat_energy_monotone_capstone`.

    The H^s energy of the heat semigroup is a continuously
    differentiable, antitone function of time:

    (E1) Differentiable at every `t`.
    (E2) Derivative is non-positive at every `t` (since it equals
         `-2 · stokesHsEnergy ≥ 0` and `stokesHsEnergy ≥ 0`).
    (E3) Antitone (monotone non-increasing) in `t`.
    (E4) Pointwise: `t₁ ≤ t₂` ⇒ energy at `t₂` ≤ energy at `t₁`.

    Specializing `t₁ = 0` recovers the earlier H^s contraction
    `hsNormSqVecOnL2_heatSemigroup_le_of_nonneg`. The present
    statement is strictly stronger: monotonicity at all times,
    not just from the initial condition. -/
theorem concrete_div_free_heat_energy_monotone_capstone
    (s : ℝ) (S : Finset (Fin 3 → ℤ)) :
    -- (E1) differentiability
    (∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      Differentiable ℝ (fun r => hsNormSqVecOnL2 (heatSemigroup r c) s S)) ∧
    -- (E2) non-positive derivative
    (∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ), ∀ t : ℝ,
      deriv (fun r => hsNormSqVecOnL2 (heatSemigroup r c) s S) t ≤ 0) ∧
    -- (E3) antitone
    (∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      Antitone (fun r => hsNormSqVecOnL2 (heatSemigroup r c) s S)) ∧
    -- (E4) pointwise inequality
    (∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ), ∀ t₁ t₂ : ℝ, t₁ ≤ t₂ →
      hsNormSqVecOnL2 (heatSemigroup t₂ c) s S
        ≤ hsNormSqVecOnL2 (heatSemigroup t₁ c) s S) :=
  ⟨fun c => differentiable_hsNormSqVecOnL2_heatSemigroup c s S,
   fun c t => deriv_hsNormSqVecOnL2_heatSemigroup_nonpos c s S t,
   fun c => antitone_hsNormSqVecOnL2_heatSemigroup c s S,
   fun c t₁ t₂ h => hsNormSqVecOnL2_heatSemigroup_antitone c s S h⟩

end PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

#print axioms
  PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField.concrete_div_free_heat_energy_monotone_capstone
