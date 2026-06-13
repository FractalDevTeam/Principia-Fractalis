/-
# NS3D_DivFreeSubmodule — divergence-free subspace as a `Submodule ℂ`
   of the ambient Fourier-coefficient space

★ 2026-06-12 — seventh Type (F) advance on the NS Sobolev/Leray bridge
(Wave 51B residual gap). Packages the strong-form divergence-free
constraint as a `Submodule ℂ` of the ambient Fourier-coefficient
space `(Fin 3 → ℤ) → (Fin 3 → ℂ)`. This is the canonical algebraic
form the mathlib SobolevSpace bridge consumes.

## What this file delivers, axiom-free

  (1) **`divFreeSubmodule`** — the `Submodule ℂ` of
      `(Fin 3 → ℤ) → (Fin 3 → ℂ)` whose elements satisfy
      `∀ k, dotIntC3 k (c k) = 0`.

  (2) **`lerayProject_mem`** — for every ambient sequence `c`,
      `lerayProject c ∈ divFreeSubmodule`.

  (3) **`lerayProjectLinear`** — the Leray projector packaged as a
      ℂ-linear map `(Fin 3 → ℤ) → (Fin 3 → ℂ)` → `(Fin 3 → ℤ) → (Fin 3 → ℂ)`,
      with image in `divFreeSubmodule`.

  (4) **`divFreeRange`** — the range of `lerayProjectLinear` equals
      `divFreeSubmodule` (since the projector fixes any div-free
      input).

  (5) **Capstone** — the divergence-free subspace is a `Submodule ℂ`,
      the Leray projector is a ℂ-linear projection onto it, and
      restriction to this subspace recovers the divergence-free
      coefficient structure.

ZERO project axioms; kernel-only `[propext, Classical.choice, Quot.sound]`.

Author: Pablo Cohen + Claude Opus 4.7. 2026-06-12.
-/

import PF.NS3D_LerayProjectorLinear

namespace PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

open PrincipiaTractalis.DivFreeFourierDensityOnTorus3Attempt

/-! ## §1 — The divergence-free subspace -/

/-- **Divergence-free subspace** of `(Fin 3 → ℤ) → (Fin 3 → ℂ)` —
    Fourier-coefficient sequences whose discrete divergence vanishes
    at every wave-vector. -/
def divFreeSubmodule : Submodule ℂ ((Fin 3 → ℤ) → (Fin 3 → ℂ)) where
  carrier := { c | ∀ k : Fin 3 → ℤ, dotIntC3 k (c k) = 0 }
  zero_mem' := by
    intro k
    show dotIntC3 k ((0 : (Fin 3 → ℤ) → (Fin 3 → ℂ)) k) = 0
    have : ((0 : (Fin 3 → ℤ) → (Fin 3 → ℂ)) k) = (0 : Fin 3 → ℂ) := rfl
    rw [this]
    exact dotIntC3_zero k
  add_mem' := by
    intro c d hc hd k
    have h_add : ((c + d) k) = c k + d k := rfl
    rw [h_add, dotIntC3_add, hc k, hd k, add_zero]
  smul_mem' := by
    intro lam c hc k
    have h_smul : ((lam • c) k) = lam • c k := rfl
    rw [h_smul, dotIntC3_smul, hc k, mul_zero]

theorem mem_divFreeSubmodule_iff
    (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    c ∈ divFreeSubmodule ↔ ∀ k : Fin 3 → ℤ, dotIntC3 k (c k) = 0 :=
  Iff.rfl

/-! ## §2 — Leray projector membership -/

/-- **The Leray projection lands in the divergence-free subspace**. -/
theorem lerayProject_mem
    (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    lerayProject c ∈ divFreeSubmodule :=
  lerayProject_div_free c

/-! ## §3 — Leray projector as a ℂ-linear map -/

/-- **The Leray projector packaged as a ℂ-linear map**. -/
noncomputable def lerayProjectLinear :
    ((Fin 3 → ℤ) → (Fin 3 → ℂ)) →ₗ[ℂ] ((Fin 3 → ℤ) → (Fin 3 → ℂ)) where
  toFun := lerayProject
  map_add' := lerayProject_add
  map_smul' := by
    intro lam c
    show lerayProject (lam • c) = lam • lerayProject c
    exact lerayProject_smul lam c

theorem lerayProjectLinear_apply
    (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    lerayProjectLinear c = lerayProject c := rfl

/-- **Image of `lerayProjectLinear` is contained in `divFreeSubmodule`**. -/
theorem lerayProjectLinear_range_le :
    LinearMap.range lerayProjectLinear ≤ divFreeSubmodule := by
  intro v hv
  rcases hv with ⟨c, hc⟩
  rw [← hc]
  exact lerayProject_mem c

/-- **Reverse inclusion**: every div-free sequence is in the range
    (it is fixed by the projector). -/
theorem divFreeSubmodule_le_lerayProjectLinear_range :
    divFreeSubmodule ≤ LinearMap.range lerayProjectLinear := by
  intro c hc
  -- c is fixed by lerayProject, so c is in the range.
  exact ⟨c, lerayProject_fixes_div_free c hc⟩

/-- **The range of `lerayProjectLinear` equals `divFreeSubmodule`**. -/
theorem lerayProjectLinear_range_eq :
    LinearMap.range lerayProjectLinear = divFreeSubmodule :=
  le_antisymm lerayProjectLinear_range_le
    divFreeSubmodule_le_lerayProjectLinear_range

/-! ## §4 — Idempotence at the LinearMap level -/

theorem lerayProjectLinear_idem (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    lerayProjectLinear (lerayProjectLinear c) = lerayProjectLinear c := by
  show lerayProject (lerayProject c) = lerayProject c
  exact lerayProject_idempotent c

/-! ## §5 — Bridge: ConcreteDivFreeVelocityField → divFreeSubmodule -/

/-- **The inclusion `ConcreteDivFreeVelocityField → divFreeSubmodule`**:
    every concrete div-free velocity field gives an element of the
    div-free submodule via its coefficient sequence. -/
def concreteToSubmoduleElement
    (u : ConcreteDivFreeVelocityField) :
    { c : (Fin 3 → ℤ) → (Fin 3 → ℂ) // c ∈ divFreeSubmodule } :=
  ⟨u.coeff, u.div_free⟩

theorem concreteToSubmoduleElement_coeff
    (u : ConcreteDivFreeVelocityField) :
    (concreteToSubmoduleElement u).val = u.coeff := rfl

/-! ## §6 — Capstone -/

/-- **★ DIVERGENCE-FREE SUBMODULE CAPSTONE ★** —
    `concrete_div_free_submodule_capstone`.

    The divergence-free constraint forms a `Submodule ℂ` of the
    ambient Fourier-coefficient space, with:
      (S1) the Leray projector lifts to a ℂ-linear map,
      (S2) its image equals the divergence-free submodule,
      (S3) it is idempotent,
      (S4) every concrete div-free velocity field embeds as an
           element of the submodule.

    This is the algebraic packaging the mathlib SobolevSpace bridge
    consumes: a quotient/embedding via a submodule with an explicit
    canonical orthogonal projector. -/
theorem concrete_div_free_submodule_capstone :
    -- (S1) divergence-free is a Submodule ℂ
    (∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      c ∈ divFreeSubmodule ↔ ∀ k : Fin 3 → ℤ, dotIntC3 k (c k) = 0) ∧
    -- (S2) Leray projector range equals divergence-free submodule
    (LinearMap.range lerayProjectLinear = divFreeSubmodule) ∧
    -- (S3) idempotent
    (∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      lerayProjectLinear (lerayProjectLinear c) = lerayProjectLinear c) ∧
    -- (S4) concrete type embeds
    (∀ u : ConcreteDivFreeVelocityField,
      u.coeff ∈ divFreeSubmodule) :=
  ⟨mem_divFreeSubmodule_iff,
   lerayProjectLinear_range_eq,
   lerayProjectLinear_idem,
   fun u => u.div_free⟩

end PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

#print axioms
  PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField.concrete_div_free_submodule_capstone
