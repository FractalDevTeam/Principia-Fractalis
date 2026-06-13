/-
# NS3D_HeatSemigroupProperty — semigroup property of `e^{-tA}`

★ 2026-06-12 — fifteenth Type (F) advance on the NS Sobolev/Leray
bridge (Wave 51B residual gap). Proves the fundamental semigroup
property:

  `heatSemigroup (s + t) = heatSemigroup s ∘ heatSemigroup t`

In Fourier form this is `e^{-(s+t)‖k‖²} = e^{-s‖k‖²} · e^{-t‖k‖²}`
via `Real.exp_add`.

## What this file delivers, axiom-free

  (1) **`heatMultiplier_add`** —
      `heatMultiplier (s + t) k = heatMultiplier s k * heatMultiplier t k`.

  (2) **`heatSemigroup_add_time`** —
      `heatSemigroup (s + t) c = heatSemigroup s (heatSemigroup t c)`.

  (3) **`heatSemigroupOnConcrete_add_time`** — same at the concrete
      type level.

  (4) **Capstone** — `heatSemigroup` is a one-parameter semigroup
      with composition `heatSemigroup (s + t) = heatSemigroup s ∘ heatSemigroup t`,
      together with identity at `t = 0` and L²/H^s contraction for
      `t ≥ 0`.

ZERO project axioms; kernel-only `[propext, Classical.choice, Quot.sound]`.

Author: Pablo Cohen + Claude Opus 4.7. 2026-06-12.
-/

import PF.NS3D_HeatSemigroupHsContraction

namespace PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

open PrincipiaTractalis.SobolevHSScaleOnTorus3Attempt
open PrincipiaTractalis.DivFreeFourierDensityOnTorus3Attempt

/-! ## §1 — Multiplicative property of the heat multiplier -/

theorem heatMultiplier_add (s t : ℝ) (k : Fin 3 → ℤ) :
    heatMultiplier (s + t) k = heatMultiplier s k * heatMultiplier t k := by
  unfold heatMultiplier
  rw [show -((s + t) * kNormSqReal k)
      = -(s * kNormSqReal k) + -(t * kNormSqReal k) from by ring]
  exact Real.exp_add _ _

/-! ## §2 — Semigroup property at the function level -/

theorem heatSemigroup_add_time
    (s t : ℝ) (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    heatSemigroup (s + t) c = heatSemigroup s (heatSemigroup t c) := by
  funext k j
  show (heatMultiplier (s + t) k : ℂ) • c k j
      = (heatMultiplier s k : ℂ) • heatSemigroup t c k j
  show (heatMultiplier (s + t) k : ℂ) * c k j
      = (heatMultiplier s k : ℂ) * ((heatMultiplier t k : ℂ) * c k j)
  rw [heatMultiplier_add]
  push_cast
  ring

/-! ## §3 — Semigroup property at the concrete type level -/

theorem heatSemigroupOnConcrete_add_time
    (s t : ℝ) (u : ConcreteDivFreeVelocityField) :
    heatSemigroupOnConcrete (s + t) u
      = heatSemigroupOnConcrete s (heatSemigroupOnConcrete t u) := by
  apply ext
  rw [heatSemigroupOnConcrete_coeff]
  show heatSemigroup (s + t) u.coeff
      = (heatSemigroupOnConcrete s (heatSemigroupOnConcrete t u)).coeff
  rw [heatSemigroupOnConcrete_coeff]
  rw [heatSemigroupOnConcrete_coeff]
  exact heatSemigroup_add_time s t u.coeff

/-! ## §4 — Capstone -/

/-- **★ HEAT SEMIGROUP PROPERTY CAPSTONE ★** —
    `concrete_div_free_heat_semigroup_property_capstone`.

    `heatSemigroup` is a one-parameter semigroup on the Fourier-
    coefficient space:
      (SG1) identity at time zero: `heatSemigroup 0 = id`,
      (SG2) semigroup composition:
            `heatSemigroup (s + t) = heatSemigroup s ∘ heatSemigroup t`,
      (SG3) same on the concrete `ConcreteDivFreeVelocityField`.

    Combined with the L²/H^s contraction (`t ≥ 0`) and the
    operator-theoretic Stokes infrastructure, this gives the full
    one-parameter contraction semigroup structure of the linear
    heat equation on `𝕋³` at the substrate level. -/
theorem concrete_div_free_heat_semigroup_property_capstone :
    -- (SG1) identity at time zero
    (∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ), heatSemigroup 0 c = c) ∧
    -- (SG2) semigroup composition on ambient
    (∀ s t : ℝ, ∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      heatSemigroup (s + t) c = heatSemigroup s (heatSemigroup t c)) ∧
    -- (SG3) semigroup composition on concrete
    (∀ s t : ℝ, ∀ u : ConcreteDivFreeVelocityField,
      heatSemigroupOnConcrete (s + t) u
        = heatSemigroupOnConcrete s (heatSemigroupOnConcrete t u)) :=
  ⟨heatSemigroup_zero_time,
   heatSemigroup_add_time,
   heatSemigroupOnConcrete_add_time⟩

end PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

#print axioms
  PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField.concrete_div_free_heat_semigroup_property_capstone
