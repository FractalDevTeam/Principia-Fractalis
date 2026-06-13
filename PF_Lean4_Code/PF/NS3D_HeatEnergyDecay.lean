/-
# NS3D_HeatEnergyDecay — per-mode L²-energy decay identity for
   the heat semigroup

★ 2026-06-13 — eighteenth Type (F) advance on the NS Sobolev/Leray
bridge (Wave 51B residual gap). The per-mode L²-energy of the
heat semigroup satisfies the exact ODE:

  `d/dt vecL2NormSq (heatSemigroup t c k) = -2 ‖k‖² · vecL2NormSq (heatSemigroup t c k)`

This is the standard NS a priori energy decay identity, here at the
per-mode Fourier level, derived directly from the multiplier ODE
`d/dt heatMultiplier t k = -‖k‖² · heatMultiplier t k`.

## Strategy

`vecL2NormSq (heatSemigroup t c k) = (heatMultiplier t k)² · vecL2NormSq (c k)`.
Differentiating in `t`:
  `d/dt [(heatMultiplier t k)² · vecL2NormSq (c k)]`
    `= 2 · (heatMultiplier t k) · (d/dt heatMultiplier t k) · vecL2NormSq (c k)`
    `= 2 · (heatMultiplier t k) · (-‖k‖²) · heatMultiplier t k · vecL2NormSq (c k)`
    `= -2 ‖k‖² · (heatMultiplier t k)² · vecL2NormSq (c k)`
    `= -2 ‖k‖² · vecL2NormSq (heatSemigroup t c k)`.

## What this file delivers, axiom-free

  (1) **`vecL2NormSq_heatSemigroup_eq`** — explicit identity:
      `vecL2NormSq (heatSemigroup t c k)
         = (heatMultiplier t k)² · vecL2NormSq (c k)`.

  (2) **`hasDerivAt_vecL2NormSq_heatSemigroup`** — the per-mode
      L²-energy has the expected derivative.

  (3) **Capstone** — the per-mode L²-energy of the heat semigroup
      satisfies the exact a priori decay ODE, valid at every mode,
      every time, every input sequence.

ZERO project axioms; kernel-only `[propext, Classical.choice, Quot.sound]`.

Author: Pablo Cohen + Claude Opus 4.7. 2026-06-13.
-/

import PF.NS3D_HeatEquationPerMode

namespace PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

open PrincipiaTractalis.SobolevHSScaleOnTorus3Attempt
open PrincipiaTractalis.DivFreeFourierDensityOnTorus3Attempt

/-! ## §1 — Explicit factorization of the per-mode L²-energy -/

/-- **Per-mode L²-energy factorization**:
    `vecL2NormSq (heatSemigroup t c k) = (heatMultiplier t k)² · vecL2NormSq (c k)`. -/
theorem vecL2NormSq_heatSemigroup_eq
    (t : ℝ) (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) (k : Fin 3 → ℤ) :
    vecL2NormSq (heatSemigroup t c k)
      = (heatMultiplier t k)^2 * vecL2NormSq (c k) := by
  unfold vecL2NormSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  show ‖heatSemigroup t c k j‖^2
      = (heatMultiplier t k)^2 * ‖c k j‖^2
  show ‖((heatMultiplier t k : ℂ) • c k) j‖^2
      = (heatMultiplier t k)^2 * ‖c k j‖^2
  show ‖(heatMultiplier t k : ℂ) * c k j‖^2
      = (heatMultiplier t k)^2 * ‖c k j‖^2
  rw [norm_mul]
  rw [show ‖((heatMultiplier t k : ℂ))‖ = heatMultiplier t k from
    by rw [Complex.norm_real]; exact abs_of_pos (heatMultiplier_pos t k)]
  ring

/-! ## §2 — Per-mode L²-energy decay ODE -/

/-- **Per-mode L²-energy decay identity**:
    `d/dt vecL2NormSq (heatSemigroup t c k)
       = -2 ‖k‖² · vecL2NormSq (heatSemigroup t c k)`. -/
theorem hasDerivAt_vecL2NormSq_heatSemigroup
    (t : ℝ) (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) (k : Fin 3 → ℤ) :
    HasDerivAt (fun s => vecL2NormSq (heatSemigroup s c k))
      (-2 * kNormSqReal k * vecL2NormSq (heatSemigroup t c k)) t := by
  -- Rewrite the differentiand using the factorization.
  have h_eq : (fun s => vecL2NormSq (heatSemigroup s c k))
      = (fun s => (heatMultiplier s k)^2 * vecL2NormSq (c k)) := by
    funext s
    exact vecL2NormSq_heatSemigroup_eq s c k
  rw [h_eq]
  -- d/ds (f s)^2 * const = 2 * f s * f' s * const
  -- with f s = heatMultiplier s k, f'(t) = -‖k‖² · heatMultiplier t k
  have h_mult : HasDerivAt (fun s => heatMultiplier s k)
      (-(kNormSqReal k) * heatMultiplier t k) t :=
    hasDerivAt_heatMultiplier t k
  have h_sq : HasDerivAt (fun s => (heatMultiplier s k)^2)
      (2 * heatMultiplier t k * (-(kNormSqReal k) * heatMultiplier t k)) t := by
    have := h_mult.pow 2
    convert this using 1
    ring
  have h_final : HasDerivAt
      (fun s => (heatMultiplier s k)^2 * vecL2NormSq (c k))
      ((2 * heatMultiplier t k * (-(kNormSqReal k) * heatMultiplier t k))
        * vecL2NormSq (c k)) t :=
    h_sq.mul_const _
  convert h_final using 1
  -- Show:
  --   -2 * ‖k‖² * vecL2NormSq (heatSemigroup t c k)
  -- = 2 * heatMultiplier t k * (-‖k‖² * heatMultiplier t k) * vecL2NormSq (c k)
  rw [vecL2NormSq_heatSemigroup_eq]
  ring

/-! ## §3 — Capstone -/

/-- **★ HEAT ENERGY DECAY CAPSTONE ★** —
    `concrete_div_free_heat_energy_decay_capstone`.

    The per-mode L²-energy of the heat semigroup satisfies the
    exact a priori decay ODE at every mode, every time, every input:

    (D1) Factorization:
         `vecL2NormSq (heatSemigroup t c k)
            = (heatMultiplier t k)² · vecL2NormSq (c k)`.

    (D2) Per-mode energy decay ODE:
         `d/dt vecL2NormSq (heatSemigroup t c k)
            = -2 ‖k‖² · vecL2NormSq (heatSemigroup t c k)`.

    Identity (D2) is the per-mode form of the classical NS energy
    decay estimate. Summing over `k ∈ S` would give the full
    H^s energy decay; the present per-mode statement is the
    foundational ingredient. -/
theorem concrete_div_free_heat_energy_decay_capstone :
    -- (D1) factorization
    (∀ t : ℝ, ∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ), ∀ k : Fin 3 → ℤ,
      vecL2NormSq (heatSemigroup t c k)
        = (heatMultiplier t k)^2 * vecL2NormSq (c k)) ∧
    -- (D2) decay ODE
    (∀ t : ℝ, ∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ), ∀ k : Fin 3 → ℤ,
      HasDerivAt (fun s => vecL2NormSq (heatSemigroup s c k))
        (-2 * kNormSqReal k * vecL2NormSq (heatSemigroup t c k)) t) :=
  ⟨vecL2NormSq_heatSemigroup_eq,
   hasDerivAt_vecL2NormSq_heatSemigroup⟩

end PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

#print axioms
  PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField.concrete_div_free_heat_energy_decay_capstone
