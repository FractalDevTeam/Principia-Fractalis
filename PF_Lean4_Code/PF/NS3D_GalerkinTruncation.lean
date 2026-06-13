/-
# NS3D_GalerkinTruncation — Galerkin truncation operator on a finite
   mode set

★ 2026-06-13 — twenty-sixth Type (F) advance on the NS Sobolev/Leray
bridge. Defines the Galerkin truncation operator
`galerkinTrunc S : ((Fin 3 → ℤ) → (Fin 3 → ℂ)) → ((Fin 3 → ℤ) → (Fin 3 → ℂ))`
that zeros out all modes `k ∉ S`. This is the standard NS Galerkin
mode-truncation, the first step in any finite-dimensional approximation.

## What this file delivers, axiom-free

  (1) **`galerkinTrunc`** — the operator.

  (2) **`galerkinTrunc_idempotent`** — `galerkinTrunc S ∘ galerkinTrunc S = galerkinTrunc S`.

  (3) **`galerkinTrunc_add`**, **`_smul`** — ℂ-linearity.

  (4) **`galerkinTrunc_preserves_divFree`** — preserves the
      divergence-free subspace.

  (5) **`galerkinTrunc_commutes_stokesOp`**, **`_heatSemigroup`** —
      the truncation commutes with the diagonal NS operators.

  (6) **Capstone** — the Galerkin truncation is a ℂ-linear
      idempotent projection commuting with the diagonal NS operators
      and preserving the div-free subspace.

ZERO project axioms; kernel-only `[propext, Classical.choice, Quot.sound]`.

Author: Pablo Cohen + Claude Opus 4.7. 2026-06-13.
-/

import PF.NS3D_HeatExpFormula

namespace PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

open PrincipiaTractalis.SobolevHSScaleOnTorus3Attempt
open PrincipiaTractalis.DivFreeFourierDensityOnTorus3Attempt

open Classical in
/-! ## §1 — The Galerkin truncation -/

/-- **Galerkin truncation**: zeros out all modes `k ∉ S`. -/
noncomputable def galerkinTrunc
    (S : Finset (Fin 3 → ℤ))
    (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    (Fin 3 → ℤ) → (Fin 3 → ℂ) := fun k =>
  if k ∈ S then c k else fun _ => 0

theorem galerkinTrunc_mem
    (S : Finset (Fin 3 → ℤ))
    (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) {k : Fin 3 → ℤ} (hk : k ∈ S) :
    galerkinTrunc S c k = c k := by
  unfold galerkinTrunc
  rw [if_pos hk]

theorem galerkinTrunc_not_mem
    (S : Finset (Fin 3 → ℤ))
    (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) {k : Fin 3 → ℤ} (hk : k ∉ S) :
    galerkinTrunc S c k = fun _ => 0 := by
  unfold galerkinTrunc
  rw [if_neg hk]

/-! ## §2 — Idempotence -/

theorem galerkinTrunc_idempotent
    (S : Finset (Fin 3 → ℤ))
    (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    galerkinTrunc S (galerkinTrunc S c) = galerkinTrunc S c := by
  funext k
  by_cases hk : k ∈ S
  · rw [galerkinTrunc_mem S _ hk, galerkinTrunc_mem S c hk]
  · rw [galerkinTrunc_not_mem S _ hk, galerkinTrunc_not_mem S c hk]

/-! ## §3 — ℂ-linearity -/

theorem galerkinTrunc_add
    (S : Finset (Fin 3 → ℤ))
    (c d : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    galerkinTrunc S (c + d) = galerkinTrunc S c + galerkinTrunc S d := by
  funext k
  by_cases hk : k ∈ S
  · rw [galerkinTrunc_mem S _ hk]
    show (c + d) k = (galerkinTrunc S c + galerkinTrunc S d) k
    rw [show (galerkinTrunc S c + galerkinTrunc S d) k
            = galerkinTrunc S c k + galerkinTrunc S d k from rfl]
    rw [galerkinTrunc_mem S c hk, galerkinTrunc_mem S d hk]
    rfl
  · rw [galerkinTrunc_not_mem S _ hk]
    show (fun _ : Fin 3 => (0 : ℂ))
        = (galerkinTrunc S c + galerkinTrunc S d) k
    rw [show (galerkinTrunc S c + galerkinTrunc S d) k
            = galerkinTrunc S c k + galerkinTrunc S d k from rfl]
    rw [galerkinTrunc_not_mem S c hk, galerkinTrunc_not_mem S d hk]
    funext j
    simp

theorem galerkinTrunc_smul
    (S : Finset (Fin 3 → ℤ))
    (lam : ℂ) (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    galerkinTrunc S (lam • c) = lam • galerkinTrunc S c := by
  funext k
  by_cases hk : k ∈ S
  · rw [galerkinTrunc_mem S _ hk]
    show (lam • c) k = (lam • galerkinTrunc S c) k
    rw [show (lam • galerkinTrunc S c) k = lam • (galerkinTrunc S c k) from rfl]
    rw [galerkinTrunc_mem S c hk]
    rfl
  · rw [galerkinTrunc_not_mem S _ hk]
    show (fun _ : Fin 3 => (0 : ℂ)) = (lam • galerkinTrunc S c) k
    rw [show (lam • galerkinTrunc S c) k = lam • (galerkinTrunc S c k) from rfl]
    rw [galerkinTrunc_not_mem S c hk]
    funext j
    simp

/-! ## §4 — Preservation of divergence-free -/

theorem galerkinTrunc_preserves_divFree
    (S : Finset (Fin 3 → ℤ))
    (c : (Fin 3 → ℤ) → (Fin 3 → ℂ))
    (h_div_free : ∀ k : Fin 3 → ℤ, dotIntC3 k (c k) = 0) :
    ∀ k : Fin 3 → ℤ, dotIntC3 k (galerkinTrunc S c k) = 0 := by
  intro k
  by_cases hk : k ∈ S
  · rw [galerkinTrunc_mem S c hk]
    exact h_div_free k
  · rw [galerkinTrunc_not_mem S c hk]
    exact dotIntC3_zero k

/-! ## §5 — Commutation with diagonal NS operators -/

theorem galerkinTrunc_commutes_stokesOp
    (S : Finset (Fin 3 → ℤ))
    (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    galerkinTrunc S (stokesOp c) = stokesOp (galerkinTrunc S c) := by
  funext k j
  by_cases hk : k ∈ S
  · rw [galerkinTrunc_mem S _ hk]
    show stokesOp c k j = stokesOp (galerkinTrunc S c) k j
    rw [stokesOp_apply, stokesOp_apply]
    rw [galerkinTrunc_mem S c hk]
  · rw [galerkinTrunc_not_mem S _ hk]
    show (fun _ : Fin 3 => (0 : ℂ)) j = stokesOp (galerkinTrunc S c) k j
    rw [stokesOp_apply]
    rw [galerkinTrunc_not_mem S c hk]
    show (0 : ℂ) = ((kNormSqReal k : ℂ) • (fun _ : Fin 3 => (0 : ℂ))) j
    simp

theorem galerkinTrunc_commutes_heatSemigroup
    (S : Finset (Fin 3 → ℤ)) (t : ℝ)
    (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    galerkinTrunc S (heatSemigroup t c) = heatSemigroup t (galerkinTrunc S c) := by
  funext k j
  by_cases hk : k ∈ S
  · rw [galerkinTrunc_mem S _ hk]
    show heatSemigroup t c k j = heatSemigroup t (galerkinTrunc S c) k j
    show ((heatMultiplier t k : ℂ) • c k) j
        = ((heatMultiplier t k : ℂ) • galerkinTrunc S c k) j
    rw [galerkinTrunc_mem S c hk]
  · rw [galerkinTrunc_not_mem S _ hk]
    show (fun _ : Fin 3 => (0 : ℂ)) j = heatSemigroup t (galerkinTrunc S c) k j
    show (0 : ℂ) = ((heatMultiplier t k : ℂ) • galerkinTrunc S c k) j
    rw [galerkinTrunc_not_mem S c hk]
    show (0 : ℂ) = ((heatMultiplier t k : ℂ) • (fun _ : Fin 3 => (0 : ℂ))) j
    simp

/-! ## §6 — Capstone -/

/-- **★ GALERKIN TRUNCATION CAPSTONE ★** —
    `concrete_div_free_galerkin_truncation_capstone`.

    The Galerkin truncation `galerkinTrunc S` zeros out modes
    outside the finite set `S`, providing a clean cutoff projection:

    (T1) Idempotent.
    (T2) ℂ-linear (additivity + scalar homogeneity).
    (T3) Preserves divergence-free subspace.
    (T4) Commutes with the Stokes operator and heat semigroup
         (both diagonal in Fourier).

    This is the operator that enables NS-Galerkin finite-dimensional
    approximation: restricting to modes `k ∈ S` gives a finite-dim
    invariant subspace under all the diagonal NS operators.
    Combined with the bilinear advective term (which mixes modes
    via convolution), this gives the NS-Galerkin truncated equation
    `du/dt = -A u - B(u, u)|_S` on a finite-dim space. -/
theorem concrete_div_free_galerkin_truncation_capstone
    (S : Finset (Fin 3 → ℤ)) :
    -- (T1) idempotent
    (∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      galerkinTrunc S (galerkinTrunc S c) = galerkinTrunc S c) ∧
    -- (T2) linear
    (∀ c d : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      galerkinTrunc S (c + d) = galerkinTrunc S c + galerkinTrunc S d) ∧
    (∀ lam : ℂ, ∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      galerkinTrunc S (lam • c) = lam • galerkinTrunc S c) ∧
    -- (T3) preserves div-free
    (∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      (∀ k : Fin 3 → ℤ, dotIntC3 k (c k) = 0) →
      ∀ k : Fin 3 → ℤ, dotIntC3 k (galerkinTrunc S c k) = 0) ∧
    -- (T4) commutes with Stokes
    (∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      galerkinTrunc S (stokesOp c) = stokesOp (galerkinTrunc S c)) ∧
    -- (T4) commutes with heat semigroup
    (∀ t : ℝ, ∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      galerkinTrunc S (heatSemigroup t c) = heatSemigroup t (galerkinTrunc S c)) :=
  ⟨galerkinTrunc_idempotent S,
   galerkinTrunc_add S,
   galerkinTrunc_smul S,
   galerkinTrunc_preserves_divFree S,
   galerkinTrunc_commutes_stokesOp S,
   fun t c => galerkinTrunc_commutes_heatSemigroup S t c⟩

end PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

#print axioms
  PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField.concrete_div_free_galerkin_truncation_capstone
