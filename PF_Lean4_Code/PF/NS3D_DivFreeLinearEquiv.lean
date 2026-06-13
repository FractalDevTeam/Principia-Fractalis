/-
# NS3D_DivFreeLinearEquiv — canonical ℂ-linear equivalence
   `ConcreteDivFreeVelocityField ≃ₗ[ℂ] divFreeSubmodule`

★ 2026-06-12 — eighth Type (F) advance on the NS Sobolev/Leray
bridge (Wave 51B residual gap). Establishes that the concrete
divergence-free velocity field type is canonically ℂ-linearly
equivalent to the divergence-free `Submodule ℂ` of the ambient
Fourier-coefficient space.

This is the equivalence under which any mathlib theorem about
`Submodule ℂ`s transfers verbatim to `ConcreteDivFreeVelocityField`
— the structural step needed for the mathlib SobolevSpace bridge.

## What this file delivers, axiom-free

  (1) **`fromSubmodule`** — the inverse map
      `↥divFreeSubmodule → ConcreteDivFreeVelocityField` taking a
      submodule element to its underlying coefficient sequence.

  (2) **`concreteEquivSubmodule`** — the ℂ-linear equivalence
      `ConcreteDivFreeVelocityField ≃ₗ[ℂ] ↥divFreeSubmodule`.

  (3) **Round-trip identities** — both compositions are the identity.

  (4) **Capstone** — the equivalence transports the concrete type's
      module structure to the submodule and vice versa, with all
      linear operations commuting under the equivalence.

ZERO project axioms; kernel-only `[propext, Classical.choice, Quot.sound]`.

Author: Pablo Cohen + Claude Opus 4.7. 2026-06-12.
-/

import PF.NS3D_DivFreeSubmodule

namespace PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

open PrincipiaTractalis.DivFreeFourierDensityOnTorus3Attempt

/-! ## §1 — Forward map: `ConcreteDivFreeVelocityField → divFreeSubmodule` -/

/-- **Forward map as a Subtype.element**. -/
def toSubmodule (u : ConcreteDivFreeVelocityField) :
    ↥divFreeSubmodule :=
  ⟨u.coeff, u.div_free⟩

theorem toSubmodule_val (u : ConcreteDivFreeVelocityField) :
    (toSubmodule u).val = u.coeff := rfl

/-! ## §2 — Inverse map: `divFreeSubmodule → ConcreteDivFreeVelocityField` -/

/-- **Inverse map**: a div-free submodule element is precisely a
    coefficient sequence with the divergence-free property. -/
def fromSubmodule (c : ↥divFreeSubmodule) : ConcreteDivFreeVelocityField where
  coeff := c.val
  div_free := c.property

theorem fromSubmodule_coeff (c : ↥divFreeSubmodule) :
    (fromSubmodule c).coeff = c.val := rfl

/-! ## §3 — Round-trip identities -/

theorem fromSubmodule_toSubmodule (u : ConcreteDivFreeVelocityField) :
    fromSubmodule (toSubmodule u) = u := by
  apply ext
  rfl

theorem toSubmodule_fromSubmodule (c : ↥divFreeSubmodule) :
    toSubmodule (fromSubmodule c) = c := by
  apply Subtype.ext
  rfl

/-! ## §4 — Linearity of the forward map -/

theorem toSubmodule_add
    (u v : ConcreteDivFreeVelocityField) :
    toSubmodule (u + v) = toSubmodule u + toSubmodule v := by
  apply Subtype.ext
  show (u + v).coeff = u.coeff + v.coeff
  funext k
  exact add_coeff u v k

theorem toSubmodule_smul
    (lam : ℂ) (u : ConcreteDivFreeVelocityField) :
    toSubmodule (lam • u) = lam • toSubmodule u := by
  apply Subtype.ext
  show (lam • u).coeff = lam • u.coeff
  funext k
  exact smul_coeff lam u k

/-! ## §5 — The ℂ-linear equivalence -/

/-- **The canonical ℂ-linear equivalence**:
    `ConcreteDivFreeVelocityField ≃ₗ[ℂ] ↥divFreeSubmodule`. -/
noncomputable def concreteEquivSubmodule :
    ConcreteDivFreeVelocityField ≃ₗ[ℂ] ↥divFreeSubmodule where
  toFun := toSubmodule
  invFun := fromSubmodule
  left_inv := fromSubmodule_toSubmodule
  right_inv := toSubmodule_fromSubmodule
  map_add' := toSubmodule_add
  map_smul' := by
    intro lam u
    show toSubmodule (lam • u) = lam • toSubmodule u
    exact toSubmodule_smul lam u

theorem concreteEquivSubmodule_apply
    (u : ConcreteDivFreeVelocityField) :
    concreteEquivSubmodule u = toSubmodule u := rfl

theorem concreteEquivSubmodule_symm_apply
    (c : ↥divFreeSubmodule) :
    concreteEquivSubmodule.symm c = fromSubmodule c := rfl

/-! ## §6 — Capstone -/

/-- **★ DIV-FREE LINEAR EQUIV CAPSTONE ★** —
    `concrete_div_free_linear_equiv_capstone`.

    The concrete divergence-free velocity field type is ℂ-linearly
    equivalent to the divergence-free `Submodule ℂ` of the ambient
    Fourier-coefficient space:

      (E1) `concreteEquivSubmodule : ConcreteDivFreeVelocityField ≃ₗ[ℂ] ↥divFreeSubmodule`
           is a ℂ-linear isomorphism,
      (E2) forward map preserves zero, addition, and scalar action,
      (E3) inverse round-trip is the identity on both sides,
      (E4) the equivalence transports `ConcreteDivFreeVelocityField`'s
           module structure to the submodule and vice versa.

    Under this equivalence, any mathlib theorem about the
    `Submodule ℂ` transfers verbatim to `ConcreteDivFreeVelocityField`.
    This is the structural bridge to the mathlib SobolevSpace
    machinery. -/
theorem concrete_div_free_linear_equiv_capstone :
    -- (E1) round-trip identities
    (∀ u : ConcreteDivFreeVelocityField,
      concreteEquivSubmodule.symm (concreteEquivSubmodule u) = u) ∧
    (∀ c : ↥divFreeSubmodule,
      concreteEquivSubmodule (concreteEquivSubmodule.symm c) = c) ∧
    -- (E2) forward map preserves addition
    (∀ u v : ConcreteDivFreeVelocityField,
      concreteEquivSubmodule (u + v)
        = concreteEquivSubmodule u + concreteEquivSubmodule v) ∧
    -- (E3) forward map preserves scalar action
    (∀ lam : ℂ, ∀ u : ConcreteDivFreeVelocityField,
      concreteEquivSubmodule (lam • u) = lam • concreteEquivSubmodule u) ∧
    -- (E4) the underlying coefficient sequence is preserved
    (∀ u : ConcreteDivFreeVelocityField,
      (concreteEquivSubmodule u).val = u.coeff) :=
  ⟨concreteEquivSubmodule.left_inv,
   concreteEquivSubmodule.right_inv,
   concreteEquivSubmodule.map_add,
   concreteEquivSubmodule.map_smul,
   fun u => toSubmodule_val u⟩

end PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

#print axioms
  PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField.concrete_div_free_linear_equiv_capstone
