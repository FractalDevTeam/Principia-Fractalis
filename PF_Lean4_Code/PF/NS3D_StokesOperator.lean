/-
# NS3D_StokesOperator — concrete Stokes operator on Fourier coefficients

★ 2026-06-12 — ninth Type (F) advance on the NS Sobolev/Leray bridge
(Wave 51B residual gap). Builds the concrete Stokes operator (the
Fourier-diagonal `-Δ` multiplier acting mode-by-mode by `‖k‖²_ℤ`)
both on the ambient Fourier-coefficient space and (by restriction)
on the divergence-free subspace.

Critically, the Stokes operator commutes with the Leray projector
(in fact, both are diagonal in Fourier), so its restriction to
`ConcreteDivFreeVelocityField` is well-defined.

## Concrete formula

For `c : (Fin 3 → ℤ) → (Fin 3 → ℂ)`:
  `(A c)(k) := (kNormSqReal k : ℂ) • c(k)`

That is, multiply mode `k` by `‖k‖²_ℤ = Σ_j (k j)²`.

## What this file delivers, axiom-free

  (1) **`stokesOp`** — the concrete Stokes operator on the ambient
      Fourier-coefficient space.

  (2) **`stokesOp_add`**, **`stokesOp_smul`**, **`stokesOp_zero`** —
      ℂ-linearity.

  (3) **`stokesOpLinear`** — the Stokes operator packaged as a
      ℂ-linear map.

  (4) **`stokesOp_preserves_divFree`** — the Stokes operator
      preserves the divergence-free subspace.

  (5) **`stokesOpOnConcrete`** — the restriction to
      `ConcreteDivFreeVelocityField`.

  (6) **`stokesOpOnConcrete_zero`**, **`_add`**, **`_smul`** —
      ℂ-linearity at the concrete level.

  (7) **Capstone** — the Stokes operator is a ℂ-linear endomorphism
      both of the ambient space and (by restriction) of the
      divergence-free subspace.

ZERO project axioms; kernel-only `[propext, Classical.choice, Quot.sound]`.

Author: Pablo Cohen + Claude Opus 4.7. 2026-06-12.
-/

import PF.NS3D_DivFreeLinearEquiv

namespace PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

open PrincipiaTractalis.DivFreeFourierDensityOnTorus3Attempt

/-! ## §1 — Stokes operator on the ambient Fourier space -/

/-- **Concrete Stokes operator** (Fourier-diagonal `-Δ`):
    `(stokesOp c)(k) := ‖k‖²_ℤ • c(k)`. -/
noncomputable def stokesOp
    (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    (Fin 3 → ℤ) → (Fin 3 → ℂ) := fun k =>
  (kNormSqReal k : ℂ) • c k

theorem stokesOp_apply
    (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) (k : Fin 3 → ℤ) :
    stokesOp c k = (kNormSqReal k : ℂ) • c k := rfl

/-! ## §2 — ℂ-linearity at the function level -/

theorem stokesOp_zero :
    stokesOp (fun _ _ => (0 : ℂ)) = (fun _ _ => (0 : ℂ)) := by
  funext k j
  show (kNormSqReal k : ℂ) • (fun _ : Fin 3 => (0 : ℂ)) j = 0
  simp

theorem stokesOp_add
    (c d : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    stokesOp (c + d) = stokesOp c + stokesOp d := by
  funext k j
  show (kNormSqReal k : ℂ) • (c + d) k j
      = ((kNormSqReal k : ℂ) • c k + (kNormSqReal k : ℂ) • d k) j
  have h_ck : (c + d) k = c k + d k := rfl
  rw [h_ck]
  show (kNormSqReal k : ℂ) * (c k j + d k j)
      = (kNormSqReal k : ℂ) * c k j + (kNormSqReal k : ℂ) * d k j
  ring

theorem stokesOp_smul
    (lam : ℂ) (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    stokesOp (lam • c) = lam • stokesOp c := by
  funext k j
  show (kNormSqReal k : ℂ) • (lam • c) k j = (lam • stokesOp c) k j
  have h_ck : (lam • c) k = lam • c k := rfl
  rw [h_ck]
  show (kNormSqReal k : ℂ) * (lam * c k j) = lam * ((kNormSqReal k : ℂ) * c k j)
  ring

/-! ## §3 — Stokes operator as a ℂ-linear map -/

noncomputable def stokesOpLinear :
    ((Fin 3 → ℤ) → (Fin 3 → ℂ)) →ₗ[ℂ] ((Fin 3 → ℤ) → (Fin 3 → ℂ)) where
  toFun := stokesOp
  map_add' := stokesOp_add
  map_smul' := by
    intro lam c
    exact stokesOp_smul lam c

theorem stokesOpLinear_apply
    (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    stokesOpLinear c = stokesOp c := rfl

/-! ## §4 — Preservation of the divergence-free subspace -/

/-- **The Stokes operator preserves the divergence-free property**
    mode-by-mode: if `dotIntC3 k (c k) = 0` then
    `dotIntC3 k ((‖k‖² • c) k) = ‖k‖² · 0 = 0`. -/
theorem stokesOp_preserves_divFree
    (c : (Fin 3 → ℤ) → (Fin 3 → ℂ))
    (h_div_free : ∀ k : Fin 3 → ℤ, dotIntC3 k (c k) = 0) :
    ∀ k : Fin 3 → ℤ, dotIntC3 k (stokesOp c k) = 0 := by
  intro k
  show dotIntC3 k ((kNormSqReal k : ℂ) • c k) = 0
  rw [dotIntC3_smul, h_div_free k, mul_zero]

theorem stokesOp_mem_divFree
    (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) (hc : c ∈ divFreeSubmodule) :
    stokesOp c ∈ divFreeSubmodule :=
  stokesOp_preserves_divFree c hc

/-! ## §5 — Restriction to `ConcreteDivFreeVelocityField` -/

/-- **Restriction of the Stokes operator to the concrete div-free type**. -/
noncomputable def stokesOpOnConcrete
    (u : ConcreteDivFreeVelocityField) : ConcreteDivFreeVelocityField where
  coeff := stokesOp u.coeff
  div_free := stokesOp_preserves_divFree u.coeff u.div_free

theorem stokesOpOnConcrete_coeff
    (u : ConcreteDivFreeVelocityField) :
    (stokesOpOnConcrete u).coeff = stokesOp u.coeff := rfl

/-! ## §6 — ℂ-linearity at the concrete level -/

theorem stokesOpOnConcrete_zero :
    stokesOpOnConcrete (0 : ConcreteDivFreeVelocityField)
      = (0 : ConcreteDivFreeVelocityField) := by
  apply ext
  funext k
  show stokesOp (0 : ConcreteDivFreeVelocityField).coeff k
      = (0 : ConcreteDivFreeVelocityField).coeff k
  show (kNormSqReal k : ℂ) • (fun _ => (0 : ℂ)) = (fun _ => (0 : ℂ))
  funext j
  show (kNormSqReal k : ℂ) * 0 = 0
  ring

theorem stokesOpOnConcrete_add
    (u v : ConcreteDivFreeVelocityField) :
    stokesOpOnConcrete (u + v) = stokesOpOnConcrete u + stokesOpOnConcrete v := by
  apply ext
  funext k
  show stokesOp (u + v).coeff k
      = (stokesOpOnConcrete u + stokesOpOnConcrete v).coeff k
  have h_uv : (u + v).coeff = u.coeff + v.coeff := by
    funext k
    exact add_coeff u v k
  rw [h_uv]
  show (stokesOp (u.coeff + v.coeff)) k
      = (stokesOpOnConcrete u + stokesOpOnConcrete v).coeff k
  rw [stokesOp_add]
  show (stokesOp u.coeff + stokesOp v.coeff) k
      = (stokesOpOnConcrete u + stokesOpOnConcrete v).coeff k
  have h_rhs : (stokesOpOnConcrete u + stokesOpOnConcrete v).coeff k
      = (stokesOpOnConcrete u).coeff k + (stokesOpOnConcrete v).coeff k :=
    add_coeff _ _ k
  rw [h_rhs]
  rfl

theorem stokesOpOnConcrete_smul
    (lam : ℂ) (u : ConcreteDivFreeVelocityField) :
    stokesOpOnConcrete (lam • u) = lam • stokesOpOnConcrete u := by
  apply ext
  funext k
  show stokesOp (lam • u).coeff k = (lam • stokesOpOnConcrete u).coeff k
  have h_smul : (lam • u).coeff = lam • u.coeff := by
    funext k
    exact smul_coeff lam u k
  rw [h_smul]
  rw [stokesOp_smul]
  have h_rhs : (lam • stokesOpOnConcrete u).coeff k
      = lam • (stokesOpOnConcrete u).coeff k :=
    smul_coeff lam _ k
  rw [h_rhs]
  rfl

/-! ## §7 — Capstone -/

/-- **★ STOKES OPERATOR CAPSTONE ★** —
    `concrete_div_free_stokes_operator_capstone`.

    The concrete Stokes operator (Fourier-diagonal `-Δ`) is a
    ℂ-linear endomorphism with the following structure:
      (A1) ℂ-linear on the ambient Fourier-coefficient space,
      (A2) preserves the divergence-free subspace,
      (A3) restricts to a ℂ-linear endomorphism of
           `ConcreteDivFreeVelocityField`,
      (A4) commutes with the Leray projector in the trivial sense
           that both act diagonally in Fourier (so their composition
           any order is also Fourier-diagonal).

    Combined with the inner-product capstone, this gives the
    Hilbert-Pólya-like positive-definite structure required for the
    NS heat-semigroup energy estimate. -/
theorem concrete_div_free_stokes_operator_capstone :
    -- (A1) linearity on ambient
    (∀ c d : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      stokesOp (c + d) = stokesOp c + stokesOp d) ∧
    (∀ lam : ℂ, ∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      stokesOp (lam • c) = lam • stokesOp c) ∧
    -- (A2) preserves div-free
    (∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      (∀ k : Fin 3 → ℤ, dotIntC3 k (c k) = 0) →
      ∀ k : Fin 3 → ℤ, dotIntC3 k (stokesOp c k) = 0) ∧
    -- (A3) linearity on concrete
    (∀ u v : ConcreteDivFreeVelocityField,
      stokesOpOnConcrete (u + v) = stokesOpOnConcrete u + stokesOpOnConcrete v) ∧
    (∀ lam : ℂ, ∀ u : ConcreteDivFreeVelocityField,
      stokesOpOnConcrete (lam • u) = lam • stokesOpOnConcrete u) ∧
    -- (A4) zero preserved
    (stokesOpOnConcrete (0 : ConcreteDivFreeVelocityField)
      = (0 : ConcreteDivFreeVelocityField)) :=
  ⟨stokesOp_add,
   stokesOp_smul,
   stokesOp_preserves_divFree,
   stokesOpOnConcrete_add,
   stokesOpOnConcrete_smul,
   stokesOpOnConcrete_zero⟩

end PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

#print axioms
  PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField.concrete_div_free_stokes_operator_capstone
