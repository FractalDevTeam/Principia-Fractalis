/-
# NS3D_HeatExpFormula — explicit exponential formula for per-mode
   heat-semigroup energy

★ 2026-06-13 — twenty-fifth Type (F) advance on the NS Sobolev/Leray
bridge. Records the explicit closed-form formula for the per-mode
L²-energy of the heat semigroup:

  `vecL2NormSq (heatSemigroup t c k) = exp(-2 t ‖k‖²) · vecL2NormSq (c k)`

This unwinds the factorization `(heatMultiplier t k)² · vecL2NormSq (c k)`
using `heatMultiplier t k = exp(-t ‖k‖²)`, so the square is
`exp(-2 t ‖k‖²)`.

## What this file delivers, axiom-free

  (1) **`heatMultiplier_sq`** — `(heatMultiplier t k)² = exp(-2 t ‖k‖²)`.

  (2) **`vecL2NormSq_heatSemigroup_exp_formula`** — the explicit
      exponential energy formula at every mode.

  (3) **Capstone** — explicit exponential decay of per-mode
      L²-energy.

ZERO project axioms; kernel-only `[propext, Classical.choice, Quot.sound]`.

Author: Pablo Cohen + Claude Opus 4.7. 2026-06-13.
-/

import PF.NS3D_HeatEnergyDecay

namespace PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

open PrincipiaTractalis.SobolevHSScaleOnTorus3Attempt
open PrincipiaTractalis.DivFreeFourierDensityOnTorus3Attempt

/-! ## §1 — Squared heat multiplier -/

theorem heatMultiplier_sq (t : ℝ) (k : Fin 3 → ℤ) :
    (heatMultiplier t k)^2 = Real.exp (-(2 * t * kNormSqReal k)) := by
  unfold heatMultiplier
  rw [show (Real.exp (-(t * kNormSqReal k)))^2
      = Real.exp (-(t * kNormSqReal k)) * Real.exp (-(t * kNormSqReal k)) from
    sq _]
  rw [← Real.exp_add]
  rw [show -(t * kNormSqReal k) + -(t * kNormSqReal k)
      = -(2 * t * kNormSqReal k) from by ring]

/-! ## §2 — Exponential energy formula -/

theorem vecL2NormSq_heatSemigroup_exp_formula
    (t : ℝ) (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) (k : Fin 3 → ℤ) :
    vecL2NormSq (heatSemigroup t c k)
      = Real.exp (-(2 * t * kNormSqReal k)) * vecL2NormSq (c k) := by
  rw [vecL2NormSq_heatSemigroup_eq, heatMultiplier_sq]

/-! ## §3 — Capstone -/

/-- **★ HEAT EXPONENTIAL FORMULA CAPSTONE ★** —
    `concrete_div_free_heat_exp_formula_capstone`.

    The per-mode L²-energy of the heat semigroup admits the
    explicit exponential closed form:

    (EF1) `(heatMultiplier t k)² = exp(-2 t ‖k‖²)`.
    (EF2) `vecL2NormSq (heatSemigroup t c k)
            = exp(-2 t ‖k‖²) · vecL2NormSq (c k)`.

    This is the explicit decay-rate formula: at every mode `k`,
    the per-mode L²-energy decays exponentially at rate `2 ‖k‖²`.
    For `k = 0` the rate is zero (the 0-mode is conserved), and
    for higher modes the decay is faster, giving the spectral
    smoothing characteristic of the linear heat equation. -/
theorem concrete_div_free_heat_exp_formula_capstone :
    (∀ t : ℝ, ∀ k : Fin 3 → ℤ,
      (heatMultiplier t k)^2 = Real.exp (-(2 * t * kNormSqReal k))) ∧
    (∀ t : ℝ, ∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ), ∀ k : Fin 3 → ℤ,
      vecL2NormSq (heatSemigroup t c k)
        = Real.exp (-(2 * t * kNormSqReal k)) * vecL2NormSq (c k)) :=
  ⟨heatMultiplier_sq,
   vecL2NormSq_heatSemigroup_exp_formula⟩

end PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

#print axioms
  PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField.concrete_div_free_heat_exp_formula_capstone
