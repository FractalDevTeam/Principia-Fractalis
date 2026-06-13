/-
# NS3D_SupportedSubmodule — finite-mode-supported subspace as a
   `Submodule ℂ`

★ 2026-06-13 — twenty-seventh Type (F) advance on the NS Sobolev/Leray
bridge. Packages the finite-mode-supported subspace
`supportedSubmodule S := { c | ∀ k ∉ S, c k = 0 }` as a `Submodule ℂ`
of `(Fin 3 → ℤ) → (Fin 3 → ℂ)`.

This is the finite-dimensional ambient space underlying the
NS-Galerkin truncation: a coefficient sequence supported on the
finite mode set `S`.

## What this file delivers, axiom-free

  (1) **`supportedSubmodule`** — the `Submodule ℂ`.

  (2) **`galerkinTrunc_mem_supportedSubmodule`** — image of
      `galerkinTrunc S` lies in `supportedSubmodule S`.

  (3) **`supportedSubmodule_galerkinTrunc_fixed`** — `galerkinTrunc S`
      fixes sequences already supported on `S`.

  (4) **`finiteDimDivFreeSubmodule`** — the intersection
      `supportedSubmodule S ⊓ divFreeSubmodule`, the
      finite-dim divergence-free subspace.

  (5) **Capstone** — finite-mode-supported sequences form a
      `Submodule ℂ` with `galerkinTrunc S` as its canonical
      projection; intersecting with `divFreeSubmodule` gives
      the NS-Galerkin invariant subspace.

ZERO project axioms; kernel-only `[propext, Classical.choice, Quot.sound]`.

Author: Pablo Cohen + Claude Opus 4.7. 2026-06-13.
-/

import PF.NS3D_GalerkinTruncation

namespace PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

open PrincipiaTractalis.SobolevHSScaleOnTorus3Attempt
open PrincipiaTractalis.DivFreeFourierDensityOnTorus3Attempt

/-! ## §1 — Finite-mode-supported subspace -/

/-- **Finite-mode-supported subspace**: sequences vanishing outside `S`. -/
def supportedSubmodule (S : Finset (Fin 3 → ℤ)) :
    Submodule ℂ ((Fin 3 → ℤ) → (Fin 3 → ℂ)) where
  carrier := { c | ∀ k : Fin 3 → ℤ, k ∉ S → c k = 0 }
  zero_mem' := by
    intro k _
    rfl
  add_mem' := by
    intro c d hc hd k hk
    have h_add : (c + d) k = c k + d k := rfl
    rw [h_add, hc k hk, hd k hk, add_zero]
  smul_mem' := by
    intro lam c hc k hk
    have h_smul : (lam • c) k = lam • c k := rfl
    rw [h_smul, hc k hk, smul_zero]

theorem mem_supportedSubmodule_iff
    (S : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    c ∈ supportedSubmodule S ↔ ∀ k : Fin 3 → ℤ, k ∉ S → c k = 0 :=
  Iff.rfl

/-! ## §2 — Galerkin truncation as projector -/

theorem galerkinTrunc_mem_supportedSubmodule
    (S : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    galerkinTrunc S c ∈ supportedSubmodule S := by
  intro k hk
  exact galerkinTrunc_not_mem S c hk

theorem galerkinTrunc_fixes_supportedSubmodule
    (S : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → (Fin 3 → ℂ))
    (hc : c ∈ supportedSubmodule S) :
    galerkinTrunc S c = c := by
  funext k
  by_cases hk : k ∈ S
  · exact galerkinTrunc_mem S c hk
  · rw [galerkinTrunc_not_mem S c hk, hc k hk]
    rfl

/-! ## §3 — Finite-dim divergence-free subspace -/

/-- **Finite-dim divergence-free subspace**: supported on `S` AND
    divergence-free. -/
def finiteDimDivFreeSubmodule (S : Finset (Fin 3 → ℤ)) :
    Submodule ℂ ((Fin 3 → ℤ) → (Fin 3 → ℂ)) :=
  supportedSubmodule S ⊓ divFreeSubmodule

theorem mem_finiteDimDivFreeSubmodule_iff
    (S : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    c ∈ finiteDimDivFreeSubmodule S
      ↔ (∀ k : Fin 3 → ℤ, k ∉ S → c k = 0)
         ∧ (∀ k : Fin 3 → ℤ, dotIntC3 k (c k) = 0) :=
  Iff.rfl

theorem galerkinTrunc_div_free_mem_finiteDimDivFreeSubmodule
    (S : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → (Fin 3 → ℂ))
    (h_div_free : ∀ k : Fin 3 → ℤ, dotIntC3 k (c k) = 0) :
    galerkinTrunc S c ∈ finiteDimDivFreeSubmodule S := by
  refine ⟨?_, ?_⟩
  · exact galerkinTrunc_mem_supportedSubmodule S c
  · exact galerkinTrunc_preserves_divFree S c h_div_free

/-! ## §4 — Invariance under NS operators -/

theorem stokesOp_mem_finiteDimDivFreeSubmodule
    (S : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → (Fin 3 → ℂ))
    (hc : c ∈ finiteDimDivFreeSubmodule S) :
    stokesOp c ∈ finiteDimDivFreeSubmodule S := by
  refine ⟨?_, ?_⟩
  · intro k hk
    show stokesOp c k = 0
    rw [stokesOp_apply, hc.1 k hk]
    funext j
    simp
  · exact stokesOp_preserves_divFree c hc.2

theorem heatSemigroup_mem_finiteDimDivFreeSubmodule
    (S : Finset (Fin 3 → ℤ)) (t : ℝ) (c : (Fin 3 → ℤ) → (Fin 3 → ℂ))
    (hc : c ∈ finiteDimDivFreeSubmodule S) :
    heatSemigroup t c ∈ finiteDimDivFreeSubmodule S := by
  refine ⟨?_, ?_⟩
  · intro k hk
    show heatSemigroup t c k = 0
    show (heatMultiplier t k : ℂ) • c k = 0
    rw [hc.1 k hk]
    simp
  · exact heatSemigroup_preserves_divFree t c hc.2

/-! ## §5 — Capstone -/

/-- **★ FINITE-DIM DIV-FREE SUBMODULE CAPSTONE ★** —
    `concrete_div_free_finite_dim_submodule_capstone`.

    The finite-mode-supported divergence-free subspace
    `finiteDimDivFreeSubmodule S = supportedSubmodule S ⊓ divFreeSubmodule`
    is a `Submodule ℂ` invariant under the diagonal NS operators:

    (F1) Characterization: `c ∈ finiteDimDivFreeSubmodule S` iff
         `c` is supported on `S` and divergence-free.
    (F2) `galerkinTrunc S` maps any divergence-free sequence into
         `finiteDimDivFreeSubmodule S`.
    (F3) `stokesOp` preserves `finiteDimDivFreeSubmodule S`.
    (F4) `heatSemigroup t` preserves `finiteDimDivFreeSubmodule S`
         at every time `t`.
    (F5) `supportedSubmodule S` is a `Submodule ℂ` and `galerkinTrunc S`
         is its canonical projection.

    Combined with the bilinear NS advective term (which mixes modes
    via convolution, so does NOT generally preserve `supportedSubmodule S`
    unless `S` is closed under the convolution `k_1 + k_2 ∈ S`),
    this gives the finite-dim invariant subspace structure for the
    linear part of the NS-Galerkin equation. -/
theorem concrete_div_free_finite_dim_submodule_capstone
    (S : Finset (Fin 3 → ℤ)) :
    -- (F1) characterization
    (∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      c ∈ finiteDimDivFreeSubmodule S
        ↔ (∀ k : Fin 3 → ℤ, k ∉ S → c k = 0)
           ∧ (∀ k : Fin 3 → ℤ, dotIntC3 k (c k) = 0)) ∧
    -- (F2) Galerkin truncation lands in finite-dim div-free subspace
    (∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      (∀ k : Fin 3 → ℤ, dotIntC3 k (c k) = 0) →
      galerkinTrunc S c ∈ finiteDimDivFreeSubmodule S) ∧
    -- (F3) Stokes operator preserves finite-dim div-free
    (∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      c ∈ finiteDimDivFreeSubmodule S → stokesOp c ∈ finiteDimDivFreeSubmodule S) ∧
    -- (F4) heat semigroup preserves finite-dim div-free
    (∀ t : ℝ, ∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      c ∈ finiteDimDivFreeSubmodule S →
      heatSemigroup t c ∈ finiteDimDivFreeSubmodule S) ∧
    -- (F5) galerkinTrunc fixes elements of supportedSubmodule
    (∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      c ∈ supportedSubmodule S → galerkinTrunc S c = c) :=
  ⟨mem_finiteDimDivFreeSubmodule_iff S,
   galerkinTrunc_div_free_mem_finiteDimDivFreeSubmodule S,
   stokesOp_mem_finiteDimDivFreeSubmodule S,
   heatSemigroup_mem_finiteDimDivFreeSubmodule S,
   galerkinTrunc_fixes_supportedSubmodule S⟩

end PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

#print axioms
  PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField.concrete_div_free_finite_dim_submodule_capstone
