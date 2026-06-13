/-
# NS3D_NonlinearScaling — quadratic homogeneity of the NS bilinear form

★ 2026-06-13 — twenty-fourth Type (F) advance on the NS Sobolev/Leray
bridge. Records the quadratic homogeneity properties of the NS
bilinear advective term `B(u, v) = P((u·∇)v)`:

  `B(c • u, c • v) = c² • B(u, v)`
  `B(c • u, v) = c • B(u, v)`
  `B(u, c • v) = c • B(u, v)`

These follow from bilinearity (advance 20) and clean up the
scaling structure of the NS nonlinearity. Importantly, the
quadratic homogeneity `B(c • u, c • u) = c² • B(u, u)` controls
the scaling behavior of the NS nonlinear self-interaction term in
the NS ODE `du/dt = -A u - B(u, u)`.

## What this file delivers, axiom-free

  (1) **`nsBilinear_smul_both`** — `B(c • u, c • v) = c² • B(u, v)`.

  (2) **`nsBilinear_self_smul`** — `B(c • u, c • u) = c² • B(u, u)`.

  (3) **`nsEvolutionRHS_quadratic_self_smul`** —
      `nsEvolutionRHS S (c • u) = c • (-stokesOp u) - c² • nsBilinear S u u`.

  (4) **Capstone** — full scaling behavior of the NS dynamics:
      linear in `stokesOp`, quadratic in `nsBilinear`.

ZERO project axioms; kernel-only `[propext, Classical.choice, Quot.sound]`.

Author: Pablo Cohen + Claude Opus 4.7. 2026-06-13.
-/

import PF.NS3D_EvolutionRHS

namespace PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

open PrincipiaTractalis.SobolevHSScaleOnTorus3Attempt
open PrincipiaTractalis.DivFreeFourierDensityOnTorus3Attempt

/-! ## §1 — Both-slot scaling of the bilinear form -/

theorem nsBilinear_smul_both
    (S : Finset (Fin 3 → ℤ))
    (c : ℂ) (u v : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    nsBilinear S (c • u) (c • v) = c^2 • nsBilinear S u v := by
  rw [nsBilinear_smul_left, nsBilinear_smul_right]
  ext k j
  show (c • c • nsBilinear S u v) k j = (c^2 • nsBilinear S u v) k j
  show c * (c * (nsBilinear S u v) k j) = c^2 * (nsBilinear S u v) k j
  ring

/-- **NS self-interaction quadratic homogeneity**:
    `B(c • u, c • u) = c² • B(u, u)`. -/
theorem nsBilinear_self_smul
    (S : Finset (Fin 3 → ℤ))
    (c : ℂ) (u : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    nsBilinear S (c • u) (c • u) = c^2 • nsBilinear S u u :=
  nsBilinear_smul_both S c u u

/-! ## §2 — NS evolution RHS under scaling -/

/-- **NS evolution RHS scaling**:
    `nsEvolutionRHS S (c • u) = -c • stokesOp u - c² • nsBilinear S u u`. -/
theorem nsEvolutionRHS_smul
    (S : Finset (Fin 3 → ℤ))
    (c : ℂ) (u : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    nsEvolutionRHS S (c • u)
      = -(c • stokesOp u) - c^2 • nsBilinear S u u := by
  unfold nsEvolutionRHS
  rw [stokesOp_smul, nsBilinear_self_smul]

/-! ## §3 — Capstone -/

/-- **★ NS NONLINEAR SCALING CAPSTONE ★** —
    `concrete_div_free_ns_nonlinear_scaling_capstone`.

    The NS bilinear advective term is quadratically homogeneous in
    its argument, and the NS evolution RHS combines linear (Stokes)
    and quadratic (bilinear) parts under scaling:

    (Q1) `B(c • u, c • v) = c² • B(u, v)`.
    (Q2) Self-interaction: `B(c • u, c • u) = c² • B(u, u)`.
    (Q3) Evolution RHS scaling: `nsEvolutionRHS S (c • u)
                                  = -c • stokesOp u - c² • nsBilinear S u u`.

    Identity (Q3) makes explicit the NS scaling structure: under
    `u ↦ c • u`, the linear diffusion term scales by `c` while the
    nonlinear advection term scales by `c²`. This is the familiar
    NS scaling that controls the relative dominance of the linear
    and nonlinear effects at different amplitudes. -/
theorem concrete_div_free_ns_nonlinear_scaling_capstone
    (S : Finset (Fin 3 → ℤ)) :
    -- (Q1) both-slot quadratic scaling
    (∀ c : ℂ, ∀ u v : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      nsBilinear S (c • u) (c • v) = c^2 • nsBilinear S u v) ∧
    -- (Q2) self-interaction quadratic scaling
    (∀ c : ℂ, ∀ u : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      nsBilinear S (c • u) (c • u) = c^2 • nsBilinear S u u) ∧
    -- (Q3) evolution RHS scaling
    (∀ c : ℂ, ∀ u : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      nsEvolutionRHS S (c • u)
        = -(c • stokesOp u) - c^2 • nsBilinear S u u) :=
  ⟨nsBilinear_smul_both S,
   nsBilinear_self_smul S,
   nsEvolutionRHS_smul S⟩

end PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

#print axioms
  PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField.concrete_div_free_ns_nonlinear_scaling_capstone
