/-
# NS3D_EvolutionRHS — NS evolution right-hand side operator
   on the divergence-free subspace

★ 2026-06-13 — twenty-third Type (F) advance on the NS Sobolev/Leray
bridge. Packages the right-hand side of the periodic NS equation:

  `∂_t u = -A u - B(u, u)`

as a single operator `nsEvolutionRHS S u := -stokesOp u - nsBilinear S u u`,
acting on Fourier-coefficient sequences. When the input is div-free,
the output is mean-zero div-free.

## What this file delivers, axiom-free

  (1) **`nsEvolutionRHS`** — the explicit operator.

  (2) **`nsEvolutionRHS_div_free`** — image in the divergence-free
      subspace.

  (3) **`nsEvolutionRHS_mean_zero_div_free`** — image in the
      mean-zero divergence-free subspace, when the input is div-free.

  (4) **Capstone** — `nsEvolutionRHS S` is a (nonlinear, quadratic)
      operator with image in the mean-zero divergence-free subspace
      whenever its input is divergence-free.

ZERO project axioms; kernel-only `[propext, Classical.choice, Quot.sound]`.

Author: Pablo Cohen + Claude Opus 4.7. 2026-06-13.
-/

import PF.NS3D_NonlinearZeroMode

namespace PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

open PrincipiaTractalis.SobolevHSScaleOnTorus3Attempt
open PrincipiaTractalis.DivFreeFourierDensityOnTorus3Attempt

/-! ## §1 — The NS evolution RHS -/

/-- **NS evolution right-hand side operator** on a finite mode set:
    `nsEvolutionRHS S u := -stokesOp u - nsBilinear S u u`. -/
noncomputable def nsEvolutionRHS
    (S : Finset (Fin 3 → ℤ))
    (u : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    (Fin 3 → ℤ) → (Fin 3 → ℂ) :=
  -stokesOp u - nsBilinear S u u

theorem nsEvolutionRHS_def
    (S : Finset (Fin 3 → ℤ))
    (u : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    nsEvolutionRHS S u = -stokesOp u - nsBilinear S u u := rfl

/-! ## §2 — Output is divergence-free -/

theorem nsEvolutionRHS_div_free_of_div_free
    (S : Finset (Fin 3 → ℤ))
    (u : (Fin 3 → ℤ) → (Fin 3 → ℂ))
    (h_div_free : ∀ k : Fin 3 → ℤ, dotIntC3 k (u k) = 0) :
    ∀ k : Fin 3 → ℤ, dotIntC3 k (nsEvolutionRHS S u k) = 0 := by
  intro k
  show dotIntC3 k ((-stokesOp u - nsBilinear S u u) k) = 0
  have h_app : ((-stokesOp u - nsBilinear S u u) k)
      = -(stokesOp u k) - (nsBilinear S u u k) := rfl
  rw [h_app]
  rw [show -(stokesOp u k) - (nsBilinear S u u k)
      = -(stokesOp u k) + -(nsBilinear S u u k) from by ring]
  rw [dotIntC3_add, dotIntC3_neg, dotIntC3_neg]
  rw [stokesOp_preserves_divFree u h_div_free k]
  rw [nsBilinear_div_free S u u k]
  ring

/-! ## §3 — Output is mean-zero when input is div-free -/

theorem nsEvolutionRHS_zero_mode_of_div_free
    (S : Finset (Fin 3 → ℤ))
    (u : (Fin 3 → ℤ) → (Fin 3 → ℂ))
    (h_div_free : ∀ k : Fin 3 → ℤ, dotIntC3 k (u k) = 0) :
    nsEvolutionRHS S u 0 = 0 := by
  show (-stokesOp u - nsBilinear S u u) 0 = 0
  have h_app : ((-stokesOp u - nsBilinear S u u) 0)
      = -(stokesOp u 0) - (nsBilinear S u u 0) := rfl
  rw [h_app]
  rw [stokesOp_at_zero, nsBilinear_zero_mode_of_div_free S u u h_div_free]
  simp

theorem nsEvolutionRHS_mem_meanZeroDivFree_of_div_free
    (S : Finset (Fin 3 → ℤ))
    (u : (Fin 3 → ℤ) → (Fin 3 → ℂ))
    (h_div_free : ∀ k : Fin 3 → ℤ, dotIntC3 k (u k) = 0) :
    nsEvolutionRHS S u ∈ meanZeroDivFreeSubmodule := by
  refine ⟨?_, ?_⟩
  · exact nsEvolutionRHS_div_free_of_div_free S u h_div_free
  · exact nsEvolutionRHS_zero_mode_of_div_free S u h_div_free

/-- **Specialization to concrete div-free type**. -/
theorem nsEvolutionRHS_concrete_mem_meanZeroDivFree
    (S : Finset (Fin 3 → ℤ))
    (u : ConcreteDivFreeVelocityField) :
    nsEvolutionRHS S u.coeff ∈ meanZeroDivFreeSubmodule :=
  nsEvolutionRHS_mem_meanZeroDivFree_of_div_free S u.coeff u.div_free

/-! ## §4 — Restriction to `ConcreteDivFreeVelocityField` -/

/-- **NS evolution RHS lifted to a concrete div-free output**.
    Input: a concrete div-free velocity field. Output: a concrete
    div-free velocity field giving the RHS of the NS ODE. -/
noncomputable def nsEvolutionRHSOnConcrete
    (S : Finset (Fin 3 → ℤ))
    (u : ConcreteDivFreeVelocityField) : ConcreteDivFreeVelocityField where
  coeff := nsEvolutionRHS S u.coeff
  div_free := nsEvolutionRHS_div_free_of_div_free S u.coeff u.div_free

theorem nsEvolutionRHSOnConcrete_coeff
    (S : Finset (Fin 3 → ℤ))
    (u : ConcreteDivFreeVelocityField) :
    (nsEvolutionRHSOnConcrete S u).coeff = nsEvolutionRHS S u.coeff := rfl

/-! ## §5 — Capstone -/

/-- **★ NS EVOLUTION RHS CAPSTONE ★** —
    `concrete_div_free_ns_evolution_RHS_capstone`.

    The NS evolution right-hand side operator
    `nsEvolutionRHS S u := -stokesOp u - nsBilinear S u u`
    has the following structural properties when applied to a
    divergence-free input:

    (R1) Image is divergence-free at every mode.
    (R2) Image is mean-zero (zero at the 0-mode).
    (R3) Image is in the `meanZeroDivFreeSubmodule`.
    (R4) Restriction to `ConcreteDivFreeVelocityField` is
         well-defined as `nsEvolutionRHSOnConcrete`.

    This packages the substrate-level NS dynamics as the operator
    that drives the periodic NS ODE `du/dt = nsEvolutionRHS S u`
    on the mean-zero divergence-free subspace. Combined with the
    heat semigroup linear infrastructure (advance ledger), this
    gives the NS-Galerkin mild-solution formulation:

      `u(t) = e^{-tA} u_0 - ∫_0^t e^{-(t-s)A} B(u(s), u(s)) ds`. -/
theorem concrete_div_free_ns_evolution_RHS_capstone
    (S : Finset (Fin 3 → ℤ)) :
    -- (R1) divergence-free output
    (∀ u : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      (∀ k : Fin 3 → ℤ, dotIntC3 k (u k) = 0) →
      ∀ k : Fin 3 → ℤ, dotIntC3 k (nsEvolutionRHS S u k) = 0) ∧
    -- (R2) mean-zero output
    (∀ u : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      (∀ k : Fin 3 → ℤ, dotIntC3 k (u k) = 0) →
      nsEvolutionRHS S u 0 = 0) ∧
    -- (R3) mean-zero div-free submodule membership
    (∀ u : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      (∀ k : Fin 3 → ℤ, dotIntC3 k (u k) = 0) →
      nsEvolutionRHS S u ∈ meanZeroDivFreeSubmodule) ∧
    -- (R4) concrete type restriction is well-defined
    (∀ u : ConcreteDivFreeVelocityField,
      (nsEvolutionRHSOnConcrete S u).coeff = nsEvolutionRHS S u.coeff) :=
  ⟨nsEvolutionRHS_div_free_of_div_free S,
   nsEvolutionRHS_zero_mode_of_div_free S,
   nsEvolutionRHS_mem_meanZeroDivFree_of_div_free S,
   fun u => nsEvolutionRHSOnConcrete_coeff S u⟩

end PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

#print axioms
  PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField.concrete_div_free_ns_evolution_RHS_capstone
