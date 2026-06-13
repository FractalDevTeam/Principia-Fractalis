/-
# NS3D_LerayProjectorLinear — linearity of the Leray projector

★ 2026-06-12 — sixth Type (F) advance on the NS Sobolev/Leray
bridge (Wave 51B residual gap). Proves that the concrete Leray
projector `lerayProject` is ℂ-linear in its input
Fourier-coefficient sequence.

## What this file delivers, axiom-free

  (1) **`lerayProject_add`** — additivity:
      `lerayProject (c + d) = lerayProject c + lerayProject d`.

  (2) **`lerayProject_smul`** — scalar homogeneity:
      `lerayProject (lam • c) = lam • lerayProject c`.

  (3) **`lerayProject_zero`** — `lerayProject 0 = 0`.

  (4) **Capstone** — the Leray projector is a ℂ-linear operator on
      `(Fin 3 → ℤ) → (Fin 3 → ℂ)` whose image lies in the
      divergence-free subspace, with the fixed-point property
      on already-div-free inputs (so it is a genuine idempotent
      projection in the operator-theoretic sense).

ZERO project axioms; kernel-only `[propext, Classical.choice, Quot.sound]`.

Author: Pablo Cohen + Claude Opus 4.7. 2026-06-12.
-/

import PF.NS3D_LerayProjector

namespace PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

open PrincipiaTractalis.DivFreeFourierDensityOnTorus3Attempt

/-! ## §1 — Pointwise additivity at a single mode -/

theorem lerayProject_add_at
    (c d : (Fin 3 → ℤ) → (Fin 3 → ℂ)) (k : Fin 3 → ℤ) :
    lerayProject (c + d) k = lerayProject c k + lerayProject d k := by
  by_cases hk : k = 0
  · rw [hk]
    show lerayProject (c + d) 0 = lerayProject c 0 + lerayProject d 0
    rw [lerayProject_zero_mode, lerayProject_zero_mode, lerayProject_zero_mode]
    rfl
  · funext j
    rw [lerayProject_at_ne_zero (c + d) hk j]
    show (c + d) k j - dotIntC3 k ((c + d) k) / kNormSqC k * (k j : ℂ)
        = lerayProject c k j + lerayProject d k j
    rw [lerayProject_at_ne_zero c hk j,
        lerayProject_at_ne_zero d hk j]
    have h_ck : (c + d) k = c k + d k := rfl
    rw [h_ck, dotIntC3_add]
    show c k j + d k j - (dotIntC3 k (c k) + dotIntC3 k (d k))
        / kNormSqC k * (k j : ℂ)
        = c k j - dotIntC3 k (c k) / kNormSqC k * (k j : ℂ)
        + (d k j - dotIntC3 k (d k) / kNormSqC k * (k j : ℂ))
    field_simp
    ring

/-! ## §2 — Pointwise scalar homogeneity at a single mode -/

theorem lerayProject_smul_at
    (lam : ℂ) (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) (k : Fin 3 → ℤ) :
    lerayProject (lam • c) k = lam • lerayProject c k := by
  by_cases hk : k = 0
  · rw [hk]
    show lerayProject (lam • c) 0 = lam • lerayProject c 0
    rw [lerayProject_zero_mode, lerayProject_zero_mode]
    rfl
  · funext j
    rw [lerayProject_at_ne_zero (lam • c) hk j]
    show (lam • c) k j - dotIntC3 k ((lam • c) k) / kNormSqC k * (k j : ℂ)
        = (lam • lerayProject c k) j
    have h_smul_app : (lam • lerayProject c k) j = lam * (lerayProject c k j) := rfl
    rw [h_smul_app, lerayProject_at_ne_zero c hk j]
    have h_ck : (lam • c) k = lam • c k := rfl
    have h_jk : (lam • c) k j = lam * c k j := rfl
    rw [h_ck, dotIntC3_smul]
    show (lam • c k) j - lam * dotIntC3 k (c k) / kNormSqC k * (k j : ℂ)
        = lam * (c k j - dotIntC3 k (c k) / kNormSqC k * (k j : ℂ))
    have h_app : (lam • c k) j = lam * c k j := rfl
    rw [h_app]
    ring

/-! ## §3 — Functional linearity -/

theorem lerayProject_add
    (c d : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    lerayProject (c + d) = lerayProject c + lerayProject d := by
  funext k
  exact lerayProject_add_at c d k

theorem lerayProject_smul
    (lam : ℂ) (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    lerayProject (lam • c) = lam • lerayProject c := by
  funext k
  exact lerayProject_smul_at lam c k

theorem lerayProject_zero :
    lerayProject (fun _ _ => (0 : ℂ)) = (fun _ _ => (0 : ℂ)) := by
  funext k j
  by_cases hk : k = 0
  · rw [hk]
    show lerayProject (fun _ _ => (0 : ℂ)) 0 j = 0
    rw [lerayProject_zero_mode]
  · rw [lerayProject_at_ne_zero _ hk j]
    have h_dot : dotIntC3 k (fun _ => (0 : ℂ)) = 0 := dotIntC3_zero k
    rw [h_dot]
    simp

/-! ## §4 — Capstone -/

/-- **★ LERAY PROJECTOR LINEARITY CAPSTONE ★** —
    `concrete_div_free_leray_projector_linearity_capstone`.

    The Leray projector is a ℂ-linear idempotent operator with image
    in the divergence-free subspace:
      (L1) additivity
      (L2) scalar homogeneity
      (L3) preserves zero
      (L4) image in divergence-free subspace
      (L5) fixes already-div-free inputs
      (L6) idempotence

    The combination of (L4)-(L6) makes `lerayProject` a genuine
    operator-theoretic projection. Combined with (L1)-(L3), it is
    the canonical Leray projector of NS theory, here realized
    concretely at the Fourier-coefficient level. -/
theorem concrete_div_free_leray_projector_linearity_capstone :
    (∀ c d : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      lerayProject (c + d) = lerayProject c + lerayProject d) ∧
    (∀ lam : ℂ, ∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      lerayProject (lam • c) = lam • lerayProject c) ∧
    (lerayProject (fun _ _ => (0 : ℂ)) = (fun _ _ => (0 : ℂ))) ∧
    (∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ), ∀ k : Fin 3 → ℤ,
      dotIntC3 k (lerayProject c k) = 0) ∧
    (∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      (∀ k : Fin 3 → ℤ, dotIntC3 k (c k) = 0) → lerayProject c = c) ∧
    (∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      lerayProject (lerayProject c) = lerayProject c) :=
  ⟨lerayProject_add,
   lerayProject_smul,
   lerayProject_zero,
   lerayProject_div_free,
   lerayProject_fixes_div_free,
   lerayProject_idempotent⟩

end PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

#print axioms
  PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField.concrete_div_free_leray_projector_linearity_capstone
