/-
# NS3D_HeatLerayCommutation — commutation of heat semigroup and
   Leray projector, and the differential generator at the multiplier level

★ 2026-06-12 — sixteenth Type (F) advance on the NS Sobolev/Leray
bridge (Wave 51B residual gap). Two clean identities relating the
NS operators:

  (A) `heatSemigroup t ∘ lerayProject = lerayProject ∘ heatSemigroup t`
      (since both are Fourier-diagonal, they commute mode-by-mode).

  (B) `d/dt (heatMultiplier t k) = -kNormSqReal k * heatMultiplier t k`
      (the differential generator identity at the multiplier level,
      via `Real.exp_deriv`).

## What this file delivers, axiom-free

  (1) **`heatSemigroup_lerayProject_comm`** —
      `heatSemigroup t (lerayProject c) = lerayProject (heatSemigroup t c)`.

  (2) **`hasDerivAt_heatMultiplier`** — for every `t : ℝ` and
      `k : Fin 3 → ℤ`, the heat multiplier has derivative
      `-(kNormSqReal k) * heatMultiplier t k` at `t`.

  (3) **`heatMultiplier_deriv`** — derivative formula at every t.

  (4) **`heatSemigroup_stokes_comm`** —
      `heatSemigroup t ∘ stokesOp = stokesOp ∘ heatSemigroup t`.

  (5) **Capstone** — the heat semigroup commutes with both the
      Leray projector and the Stokes operator (all three are
      Fourier-diagonal), and the heat multiplier satisfies the
      differential generator identity `d/dt = -‖k‖² · `.

ZERO project axioms; kernel-only `[propext, Classical.choice, Quot.sound]`.

Author: Pablo Cohen + Claude Opus 4.7. 2026-06-12.
-/

import PF.NS3D_HeatSemigroupProperty

namespace PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

open PrincipiaTractalis.SobolevHSScaleOnTorus3Attempt
open PrincipiaTractalis.DivFreeFourierDensityOnTorus3Attempt

/-! ## §1 — Leray-heat commutation -/

theorem heatSemigroup_lerayProject_comm
    (t : ℝ) (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    heatSemigroup t (lerayProject c) = lerayProject (heatSemigroup t c) := by
  funext k
  by_cases hk : k = 0
  · -- k = 0 case: lerayProject c 0 = c 0 on both sides
    rw [hk]
    show heatSemigroup t (lerayProject c) 0 = lerayProject (heatSemigroup t c) 0
    rw [show heatSemigroup t (lerayProject c) 0
        = (heatMultiplier t 0 : ℂ) • lerayProject c 0 from rfl]
    rw [lerayProject_zero_mode]
    rw [show lerayProject (heatSemigroup t c) 0 = heatSemigroup t c 0 from
      lerayProject_zero_mode (heatSemigroup t c)]
    rfl
  · -- k ≠ 0 case: explicit projection formula on each component
    funext j
    show (heatMultiplier t k : ℂ) • (lerayProject c k) j
        = lerayProject (heatSemigroup t c) k j
    show (heatMultiplier t k : ℂ) * (lerayProject c k j)
        = lerayProject (heatSemigroup t c) k j
    rw [lerayProject_at_ne_zero c hk j]
    rw [lerayProject_at_ne_zero (heatSemigroup t c) hk j]
    -- LHS: hm * (c k j - dot/norm * k j)
    -- RHS: (hm * c k j) - dot(hm * c k) / norm * k j = hm * (c k j - dot(c k)/norm * k j)
    -- The key is dotIntC3 k (heatSemigroup t c k) = hm * dotIntC3 k (c k)
    -- since heatSemigroup t c k = hm • c k
    have h_heat_apply : heatSemigroup t c k = (heatMultiplier t k : ℂ) • c k := rfl
    rw [show heatSemigroup t c k j = (heatMultiplier t k : ℂ) * c k j from rfl]
    rw [h_heat_apply]
    rw [dotIntC3_smul]
    -- Goal:
    --  hm * (c k j - dotIntC3 k (c k) / kNormSqC k * k j)
    -- =  hm * c k j - hm * dotIntC3 k (c k) / kNormSqC k * k j
    ring

/-! ## §2 — Stokes-heat commutation -/

theorem heatSemigroup_stokes_comm
    (t : ℝ) (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    heatSemigroup t (stokesOp c) = stokesOp (heatSemigroup t c) := by
  funext k j
  show (heatMultiplier t k : ℂ) • stokesOp c k j = stokesOp (heatSemigroup t c) k j
  show (heatMultiplier t k : ℂ) * stokesOp c k j = stokesOp (heatSemigroup t c) k j
  rw [stokesOp_apply, stokesOp_apply]
  show (heatMultiplier t k : ℂ) * ((kNormSqReal k : ℂ) • c k) j
      = ((kNormSqReal k : ℂ) • (heatSemigroup t c k)) j
  show (heatMultiplier t k : ℂ) * ((kNormSqReal k : ℂ) * c k j)
      = (kNormSqReal k : ℂ) * (heatSemigroup t c k j)
  show (heatMultiplier t k : ℂ) * ((kNormSqReal k : ℂ) * c k j)
      = (kNormSqReal k : ℂ) * ((heatMultiplier t k : ℂ) * c k j)
  ring

/-! ## §3 — Differential generator at the multiplier level -/

/-- **The heat multiplier has derivative `-‖k‖² · heatMultiplier t k`
    at every `t`**. -/
theorem hasDerivAt_heatMultiplier
    (t : ℝ) (k : Fin 3 → ℤ) :
    HasDerivAt (fun s => heatMultiplier s k)
      (-(kNormSqReal k) * heatMultiplier t k) t := by
  unfold heatMultiplier
  -- d/dt exp(-t * ‖k‖²) = -‖k‖² · exp(-t * ‖k‖²)
  have h_inner : HasDerivAt (fun s => -(s * kNormSqReal k)) (-(kNormSqReal k)) t := by
    have h_mul : HasDerivAt (fun s => s * kNormSqReal k) (kNormSqReal k) t := by
      have := (hasDerivAt_id t).mul_const (kNormSqReal k)
      simpa using this
    exact h_mul.neg
  have h_exp := h_inner.exp
  convert h_exp using 1
  ring

/-- **Pointwise derivative formula**. -/
theorem heatMultiplier_deriv
    (t : ℝ) (k : Fin 3 → ℤ) :
    deriv (fun s => heatMultiplier s k) t
      = -(kNormSqReal k) * heatMultiplier t k :=
  (hasDerivAt_heatMultiplier t k).deriv

/-! ## §4 — Capstone -/

/-- **★ HEAT-LERAY-STOKES COMMUTATION & GENERATOR CAPSTONE ★** —
    `concrete_div_free_heat_leray_stokes_capstone`.

    The three NS operators (heat semigroup, Leray projector, Stokes
    operator) all act diagonally in Fourier and hence commute
    pairwise; and the heat multiplier satisfies the differential
    generator identity:
      (C1) `heatSemigroup t ∘ lerayProject = lerayProject ∘ heatSemigroup t`,
      (C2) `heatSemigroup t ∘ stokesOp = stokesOp ∘ heatSemigroup t`,
      (C3) `d/dt (heatMultiplier t k) = -‖k‖² · heatMultiplier t k`.

    Identity (C3) lifts at every mode to:
      `d/dt (heatSemigroup t c)(k) = -(stokesOp (heatSemigroup t c))(k)`
    which is the per-mode form of the linear heat equation
    `∂_t u = -A u` driving the NS analysis. -/
theorem concrete_div_free_heat_leray_stokes_capstone :
    -- (C1) Leray-heat commutation
    (∀ t : ℝ, ∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      heatSemigroup t (lerayProject c) = lerayProject (heatSemigroup t c)) ∧
    -- (C2) Stokes-heat commutation
    (∀ t : ℝ, ∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      heatSemigroup t (stokesOp c) = stokesOp (heatSemigroup t c)) ∧
    -- (C3) multiplier-level differential generator
    (∀ t : ℝ, ∀ k : Fin 3 → ℤ,
      HasDerivAt (fun s => heatMultiplier s k)
        (-(kNormSqReal k) * heatMultiplier t k) t) :=
  ⟨heatSemigroup_lerayProject_comm,
   heatSemigroup_stokes_comm,
   hasDerivAt_heatMultiplier⟩

end PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

#print axioms
  PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField.concrete_div_free_heat_leray_stokes_capstone
