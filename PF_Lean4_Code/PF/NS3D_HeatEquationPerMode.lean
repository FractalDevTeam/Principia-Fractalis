/-
# NS3D_HeatEquationPerMode — per-mode differential heat equation
   `∂_t (heatSemigroup t c)(k) j = -‖k‖² · (heatSemigroup t c)(k) j`

★ 2026-06-13 — seventeenth Type (F) advance on the NS Sobolev/Leray
bridge (Wave 51B residual gap). Lifts the multiplier-level
differential generator identity to the full per-mode semigroup
statement:

  `HasDerivAt (fun s => (heatSemigroup s c)(k) j)
              (-(kNormSqReal k) · (heatSemigroup t c)(k) j) t`

This is the per-mode form of the linear heat equation
`∂_t u = -A u` (in Fourier: `∂_t u_k = -‖k‖²·u_k`), at every
mode and every component, valid for every fixed `c, k, j`.

## What this file delivers, axiom-free

  (1) **`hasDerivAt_heatSemigroup_apply`** — for every `c`, `k`, `j`,
      the map `s ↦ (heatSemigroup s c)(k) j` has derivative
      `-(kNormSqReal k) * (heatSemigroup t c)(k) j` at `t`.

  (2) **`heatSemigroup_apply_satisfies_heat_eqn`** — packaged form:
      the per-mode component satisfies `∂_t u_k j = -‖k‖² · u_k j`.

  (3) **Capstone** — the heat semigroup solves the per-mode heat
      equation, the per-mode form of `∂_t u = -A u`.

ZERO project axioms; kernel-only `[propext, Classical.choice, Quot.sound]`.

Author: Pablo Cohen + Claude Opus 4.7. 2026-06-13.
-/

import PF.NS3D_HeatLerayCommutation

namespace PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

open PrincipiaTractalis.SobolevHSScaleOnTorus3Attempt
open PrincipiaTractalis.DivFreeFourierDensityOnTorus3Attempt

/-! ## §1 — Per-mode derivative -/

/-- **Per-mode differential generator at the semigroup level**:
    `s ↦ (heatSemigroup s c)(k) j` has derivative
    `-(kNormSqReal k) * (heatSemigroup t c)(k) j` at every `t`. -/
theorem hasDerivAt_heatSemigroup_apply
    (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) (k : Fin 3 → ℤ) (j : Fin 3) (t : ℝ) :
    HasDerivAt (fun s => heatSemigroup s c k j)
      (-(kNormSqReal k) * heatSemigroup t c k j) t := by
  -- (heatSemigroup s c)(k) j = (heatMultiplier s k : ℂ) * c k j
  -- so d/ds at t = (d/ds heatMultiplier s k at t : ℂ) * c k j
  --              = -‖k‖² · heatMultiplier t k * c k j
  --              = -‖k‖² · (heatSemigroup t c)(k) j
  have h_eq : (fun s => heatSemigroup s c k j)
      = (fun s => ((heatMultiplier s k : ℂ)) * c k j) := by
    funext s
    rfl
  rw [h_eq]
  -- HasDerivAt of (real-to-complex composition) * constant
  have h_mult : HasDerivAt (fun s => heatMultiplier s k)
      (-(kNormSqReal k) * heatMultiplier t k) t :=
    hasDerivAt_heatMultiplier t k
  -- Lift to ℂ via HasDerivAt.ofReal_comp; rhs comes back as a real,
  -- which is what we want (will be cast via convert in h_final).
  have h_mult_C : HasDerivAt (fun s => ((heatMultiplier s k : ℂ)))
      (-(kNormSqReal k) * heatMultiplier t k : ℝ) t :=
    h_mult.ofReal_comp
  -- Multiply by the constant c k j
  have h_final : HasDerivAt (fun s => ((heatMultiplier s k : ℂ)) * (c k j))
      (((-(kNormSqReal k) * heatMultiplier t k : ℝ) : ℂ) * (c k j)) t :=
    h_mult_C.mul_const (c k j)
  convert h_final using 1
  push_cast
  show -(kNormSqReal k : ℂ) * ((heatMultiplier t k : ℂ) * c k j)
      = (-(kNormSqReal k : ℂ) * (heatMultiplier t k : ℂ)) * c k j
  ring

/-! ## §2 — Per-mode heat equation -/

/-- **Per-mode form of the linear heat equation**:
    for every mode `k` and every component `j`,
    `s ↦ (heatSemigroup s c)(k) j` solves the ODE
    `u'(t) = -‖k‖²·u(t)`. -/
theorem heatSemigroup_apply_satisfies_heat_eqn
    (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) (k : Fin 3 → ℤ) (j : Fin 3) (t : ℝ) :
    deriv (fun s => heatSemigroup s c k j) t
      = -(kNormSqReal k) * heatSemigroup t c k j :=
  (hasDerivAt_heatSemigroup_apply c k j t).deriv

/-- **Per-mode initial-value identity at `t = 0`**:
    `(heatSemigroup 0 c)(k) j = (c k) j`. -/
theorem heatSemigroup_apply_at_zero
    (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) (k : Fin 3 → ℤ) (j : Fin 3) :
    heatSemigroup 0 c k j = c k j := by
  rw [heatSemigroup_zero_time]

/-! ## §3 — Capstone -/

/-- **★ PER-MODE HEAT EQUATION CAPSTONE ★** —
    `concrete_div_free_heat_equation_per_mode_capstone`.

    The heat semigroup `heatSemigroup` solves the per-mode form of
    the linear heat equation `∂_t u = -A u` at every mode and every
    component:

    (HE1) Per-mode differential identity:
          `HasDerivAt (fun s => (heatSemigroup s c)(k) j)
                     (-‖k‖² · (heatSemigroup t c)(k) j) t`.

    (HE2) Initial value at `t = 0`:
          `(heatSemigroup 0 c)(k) j = (c k) j`.

    Together with the H^s contraction, semigroup composition, and
    operator commutations established in the 16-advance ledger,
    this completes the substrate-level solution of the linear heat
    equation on the divergence-free subspace of `𝕋³`. -/
theorem concrete_div_free_heat_equation_per_mode_capstone :
    (∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ), ∀ k : Fin 3 → ℤ, ∀ j : Fin 3, ∀ t : ℝ,
      HasDerivAt (fun s => heatSemigroup s c k j)
        (-(kNormSqReal k) * heatSemigroup t c k j) t) ∧
    (∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ), ∀ k : Fin 3 → ℤ, ∀ j : Fin 3,
      heatSemigroup 0 c k j = c k j) :=
  ⟨hasDerivAt_heatSemigroup_apply,
   heatSemigroup_apply_at_zero⟩

end PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

#print axioms
  PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField.concrete_div_free_heat_equation_per_mode_capstone
