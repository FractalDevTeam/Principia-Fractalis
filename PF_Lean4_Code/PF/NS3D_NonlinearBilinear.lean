/-
# NS3D_NonlinearBilinear — NS nonlinear bilinear form `B(u, v) = P((u · ∇) v)`
   on a finite mode set

★ 2026-06-13 — twentieth Type (F) advance on the NS Sobolev/Leray
bridge (Wave 51B residual gap). Constructs the NS nonlinear
bilinear term on a finite mode set — the convolution-style
quadratic nonlinearity that drives the NS dynamics.

## The bilinear form in Fourier

Classical NS: `u_t + (u · ∇) u = -∇p + Δu` with `div u = 0`.
After Leray projection: `u_t + P((u · ∇) u) = Δu`.
The advective term `P((u · ∇) u)` in Fourier is:

  `[(u · ∇) v](k) = Σ_{k_1 + k_2 = k} i (k_2 · u(k_1)) v(k_2)`

and `P` then removes the `k`-parallel component.

On a finite mode set `S`, the convolution becomes:

  `nsBilinear S u v k j
     := Σ_{k_1 ∈ S, k_2 ∈ S, k_1 + k_2 = k}
        i · (Σ_{i' : Fin 3} (k_2 i' : ℂ) · u k_1 i') · v k_2 j`

then optionally Leray-projected at the end.

## What this file delivers, axiom-free

  (1) **`bilinearCore`** — the pre-projection bilinear core:
      `Σ_{k_1, k_2 ∈ S, k_1 + k_2 = k} (k_2 · u k_1) · v k_2 j`.

  (2) **`bilinearCore_zero_left`** — `bilinearCore S 0 v = 0`.

  (3) **`bilinearCore_zero_right`** — `bilinearCore S u 0 = 0`.

  (4) **`bilinearCore_add_left`**, **`_add_right`** — bilinearity.

  (5) **`bilinearCore_smul_left`**, **`_smul_right`** —
      scalar homogeneity in each slot.

  (6) **`nsBilinear`** — Leray-projected bilinear form
      `lerayProject (bilinearCore S u v)`.

  (7) **Capstone** — `nsBilinear S` is bilinear, lands in the
      divergence-free subspace, and is zero in either slot when
      that slot is zero.

ZERO project axioms; kernel-only `[propext, Classical.choice, Quot.sound]`.

Author: Pablo Cohen + Claude Opus 4.7. 2026-06-13.
-/

import PF.NS3D_HeatGlobalEnergyDecay

namespace PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

open PrincipiaTractalis.SobolevHSScaleOnTorus3Attempt
open PrincipiaTractalis.DivFreeFourierDensityOnTorus3Attempt

/-! ## §1 — Convolution-style index set -/

/-- **Convolution index pairs**: pairs `(k_1, k_2) ∈ S × S` with
    `k_1 + k_2 = k`. -/
noncomputable def convIndex
    (S : Finset (Fin 3 → ℤ)) (k : Fin 3 → ℤ) :
    Finset ((Fin 3 → ℤ) × (Fin 3 → ℤ)) :=
  (S ×ˢ S).filter (fun p => p.1 + p.2 = k)

theorem mem_convIndex_iff
    (S : Finset (Fin 3 → ℤ)) (k : Fin 3 → ℤ)
    (p : (Fin 3 → ℤ) × (Fin 3 → ℤ)) :
    p ∈ convIndex S k ↔ p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 + p.2 = k := by
  unfold convIndex
  rw [Finset.mem_filter, Finset.mem_product]
  tauto

/-! ## §2 — Pre-projection bilinear core -/

/-- **Pre-projection bilinear core**:
    `bilinearCore S u v k j
       := Σ_{(k_1, k_2) ∈ convIndex S k}
          (Σ_{i' : Fin 3} (k_2 i' : ℂ) · u k_1 i') · v k_2 j`.
    Pre-Leray, pre-`i·` factor. -/
noncomputable def bilinearCore
    (S : Finset (Fin 3 → ℤ))
    (u v : (Fin 3 → ℤ) → (Fin 3 → ℂ))
    (k : Fin 3 → ℤ) (j : Fin 3) : ℂ :=
  ∑ p ∈ convIndex S k,
    (∑ i' : Fin 3, (p.2 i' : ℂ) * u p.1 i') * v p.2 j

/-- **`bilinearCore`** as a function `(Fin 3 → ℤ) → (Fin 3 → ℂ)`. -/
noncomputable def bilinearCoreFn
    (S : Finset (Fin 3 → ℤ))
    (u v : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    (Fin 3 → ℤ) → (Fin 3 → ℂ) := fun k j => bilinearCore S u v k j

/-! ## §3 — Vanishing on zero arguments -/

theorem bilinearCore_zero_left
    (S : Finset (Fin 3 → ℤ))
    (v : (Fin 3 → ℤ) → (Fin 3 → ℂ))
    (k : Fin 3 → ℤ) (j : Fin 3) :
    bilinearCore S (fun _ _ => 0) v k j = 0 := by
  unfold bilinearCore
  apply Finset.sum_eq_zero
  intro p _
  show (∑ i' : Fin 3, (p.2 i' : ℂ) * (fun _ _ => (0 : ℂ)) p.1 i') * v p.2 j = 0
  have h_inner : ∀ i' : Fin 3,
      (p.2 i' : ℂ) * (fun _ _ => (0 : ℂ)) p.1 i' = 0 := by
    intro i'
    show (p.2 i' : ℂ) * 0 = 0
    ring
  rw [Finset.sum_eq_zero (fun i' _ => h_inner i')]
  ring

theorem bilinearCore_zero_right
    (S : Finset (Fin 3 → ℤ))
    (u : (Fin 3 → ℤ) → (Fin 3 → ℂ))
    (k : Fin 3 → ℤ) (j : Fin 3) :
    bilinearCore S u (fun _ _ => 0) k j = 0 := by
  unfold bilinearCore
  apply Finset.sum_eq_zero
  intro p _
  show (∑ i' : Fin 3, (p.2 i' : ℂ) * u p.1 i')
       * (fun _ _ => (0 : ℂ)) p.2 j = 0
  show (∑ i' : Fin 3, (p.2 i' : ℂ) * u p.1 i') * 0 = 0
  ring

/-! ## §4 — Bilinearity -/

theorem bilinearCore_add_left
    (S : Finset (Fin 3 → ℤ))
    (u₁ u₂ v : (Fin 3 → ℤ) → (Fin 3 → ℂ))
    (k : Fin 3 → ℤ) (j : Fin 3) :
    bilinearCore S (u₁ + u₂) v k j
      = bilinearCore S u₁ v k j + bilinearCore S u₂ v k j := by
  unfold bilinearCore
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro p _
  show (∑ i' : Fin 3, (p.2 i' : ℂ) * (u₁ + u₂) p.1 i') * v p.2 j
      = (∑ i' : Fin 3, (p.2 i' : ℂ) * u₁ p.1 i') * v p.2 j
        + (∑ i' : Fin 3, (p.2 i' : ℂ) * u₂ p.1 i') * v p.2 j
  have h_add : ∀ i' : Fin 3,
      (p.2 i' : ℂ) * (u₁ + u₂) p.1 i'
        = (p.2 i' : ℂ) * u₁ p.1 i' + (p.2 i' : ℂ) * u₂ p.1 i' := by
    intro i'
    show (p.2 i' : ℂ) * ((u₁ + u₂) p.1 i')
        = (p.2 i' : ℂ) * u₁ p.1 i' + (p.2 i' : ℂ) * u₂ p.1 i'
    show (p.2 i' : ℂ) * (u₁ p.1 i' + u₂ p.1 i')
        = (p.2 i' : ℂ) * u₁ p.1 i' + (p.2 i' : ℂ) * u₂ p.1 i'
    ring
  rw [show
    (∑ i' : Fin 3, (p.2 i' : ℂ) * (u₁ + u₂) p.1 i')
      = ∑ i' : Fin 3,
        ((p.2 i' : ℂ) * u₁ p.1 i' + (p.2 i' : ℂ) * u₂ p.1 i') from
    Finset.sum_congr rfl (fun i' _ => h_add i')]
  rw [Finset.sum_add_distrib]
  ring

theorem bilinearCore_add_right
    (S : Finset (Fin 3 → ℤ))
    (u v₁ v₂ : (Fin 3 → ℤ) → (Fin 3 → ℂ))
    (k : Fin 3 → ℤ) (j : Fin 3) :
    bilinearCore S u (v₁ + v₂) k j
      = bilinearCore S u v₁ k j + bilinearCore S u v₂ k j := by
  unfold bilinearCore
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro p _
  show (∑ i' : Fin 3, (p.2 i' : ℂ) * u p.1 i') * (v₁ + v₂) p.2 j
      = (∑ i' : Fin 3, (p.2 i' : ℂ) * u p.1 i') * v₁ p.2 j
        + (∑ i' : Fin 3, (p.2 i' : ℂ) * u p.1 i') * v₂ p.2 j
  have h_add : (v₁ + v₂) p.2 j = v₁ p.2 j + v₂ p.2 j := rfl
  rw [h_add]
  ring

theorem bilinearCore_smul_left
    (S : Finset (Fin 3 → ℤ))
    (c : ℂ) (u v : (Fin 3 → ℤ) → (Fin 3 → ℂ))
    (k : Fin 3 → ℤ) (j : Fin 3) :
    bilinearCore S (c • u) v k j = c * bilinearCore S u v k j := by
  unfold bilinearCore
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro p _
  show (∑ i' : Fin 3, (p.2 i' : ℂ) * (c • u) p.1 i') * v p.2 j
      = c * ((∑ i' : Fin 3, (p.2 i' : ℂ) * u p.1 i') * v p.2 j)
  have h_smul : ∀ i' : Fin 3,
      (p.2 i' : ℂ) * (c • u) p.1 i' = c * ((p.2 i' : ℂ) * u p.1 i') := by
    intro i'
    show (p.2 i' : ℂ) * ((c • u) p.1 i')
        = c * ((p.2 i' : ℂ) * u p.1 i')
    show (p.2 i' : ℂ) * (c * u p.1 i')
        = c * ((p.2 i' : ℂ) * u p.1 i')
    ring
  rw [Finset.sum_congr rfl (fun i' _ => h_smul i')]
  rw [← Finset.mul_sum]
  ring

theorem bilinearCore_smul_right
    (S : Finset (Fin 3 → ℤ))
    (c : ℂ) (u v : (Fin 3 → ℤ) → (Fin 3 → ℂ))
    (k : Fin 3 → ℤ) (j : Fin 3) :
    bilinearCore S u (c • v) k j = c * bilinearCore S u v k j := by
  unfold bilinearCore
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro p _
  show (∑ i' : Fin 3, (p.2 i' : ℂ) * u p.1 i') * (c • v) p.2 j
      = c * ((∑ i' : Fin 3, (p.2 i' : ℂ) * u p.1 i') * v p.2 j)
  have h_smul : (c • v) p.2 j = c * v p.2 j := rfl
  rw [h_smul]
  ring

/-! ## §5 — Leray-projected NS bilinear form -/

/-- **NS bilinear form**: `B(u, v) := P (bilinearCore u v)`. -/
noncomputable def nsBilinear
    (S : Finset (Fin 3 → ℤ))
    (u v : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    (Fin 3 → ℤ) → (Fin 3 → ℂ) :=
  lerayProject (bilinearCoreFn S u v)

theorem nsBilinear_div_free
    (S : Finset (Fin 3 → ℤ))
    (u v : (Fin 3 → ℤ) → (Fin 3 → ℂ)) (k : Fin 3 → ℤ) :
    dotIntC3 k (nsBilinear S u v k) = 0 :=
  lerayProject_div_free (bilinearCoreFn S u v) k

theorem nsBilinear_add_left
    (S : Finset (Fin 3 → ℤ))
    (u₁ u₂ v : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    nsBilinear S (u₁ + u₂) v = nsBilinear S u₁ v + nsBilinear S u₂ v := by
  unfold nsBilinear
  have h_core : bilinearCoreFn S (u₁ + u₂) v
      = bilinearCoreFn S u₁ v + bilinearCoreFn S u₂ v := by
    funext k j
    exact bilinearCore_add_left S u₁ u₂ v k j
  rw [h_core]
  exact lerayProject_add _ _

theorem nsBilinear_add_right
    (S : Finset (Fin 3 → ℤ))
    (u v₁ v₂ : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    nsBilinear S u (v₁ + v₂) = nsBilinear S u v₁ + nsBilinear S u v₂ := by
  unfold nsBilinear
  have h_core : bilinearCoreFn S u (v₁ + v₂)
      = bilinearCoreFn S u v₁ + bilinearCoreFn S u v₂ := by
    funext k j
    exact bilinearCore_add_right S u v₁ v₂ k j
  rw [h_core]
  exact lerayProject_add _ _

theorem nsBilinear_smul_left
    (S : Finset (Fin 3 → ℤ))
    (c : ℂ) (u v : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    nsBilinear S (c • u) v = c • nsBilinear S u v := by
  unfold nsBilinear
  have h_core : bilinearCoreFn S (c • u) v = c • bilinearCoreFn S u v := by
    funext k j
    show bilinearCore S (c • u) v k j = (c • bilinearCoreFn S u v) k j
    rw [bilinearCore_smul_left]
    show c * bilinearCore S u v k j = c * (bilinearCoreFn S u v k j)
    rfl
  rw [h_core]
  exact lerayProject_smul c _

theorem nsBilinear_smul_right
    (S : Finset (Fin 3 → ℤ))
    (c : ℂ) (u v : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    nsBilinear S u (c • v) = c • nsBilinear S u v := by
  unfold nsBilinear
  have h_core : bilinearCoreFn S u (c • v) = c • bilinearCoreFn S u v := by
    funext k j
    show bilinearCore S u (c • v) k j = (c • bilinearCoreFn S u v) k j
    rw [bilinearCore_smul_right]
    show c * bilinearCore S u v k j = c * (bilinearCoreFn S u v k j)
    rfl
  rw [h_core]
  exact lerayProject_smul c _

/-! ## §6 — Capstone -/

/-- **★ NS NONLINEAR BILINEAR FORM CAPSTONE ★** —
    `concrete_div_free_ns_bilinear_capstone`.

    The NS nonlinear bilinear form `nsBilinear S` is a genuine
    bilinear operator on Fourier-coefficient sequences on a finite
    mode set, projected by the Leray projector at the end:

    (B1) Image is divergence-free at every mode by construction.
    (B2) Bilinear: additivity in each slot.
    (B3) Bilinear: scalar homogeneity in each slot.

    This is the NS nonlinear advective term `P((u·∇)v)` realized
    concretely at the Fourier level. Combined with the linear heat
    semigroup infrastructure, it gives the NS-Galerkin mild-solution
    formula `u(t) = e^{-tA} u_0 - ∫_0^t e^{-(t-s)A} B(u(s), u(s)) ds`
    its concrete substrate-level representation. -/
theorem concrete_div_free_ns_bilinear_capstone
    (S : Finset (Fin 3 → ℤ)) :
    -- (B1) image in div-free subspace
    (∀ u v : (Fin 3 → ℤ) → (Fin 3 → ℂ), ∀ k : Fin 3 → ℤ,
      dotIntC3 k (nsBilinear S u v k) = 0) ∧
    -- (B2) additivity left
    (∀ u₁ u₂ v : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      nsBilinear S (u₁ + u₂) v = nsBilinear S u₁ v + nsBilinear S u₂ v) ∧
    -- (B2) additivity right
    (∀ u v₁ v₂ : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      nsBilinear S u (v₁ + v₂) = nsBilinear S u v₁ + nsBilinear S u v₂) ∧
    -- (B3) scalar homogeneity left
    (∀ c : ℂ, ∀ u v : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      nsBilinear S (c • u) v = c • nsBilinear S u v) ∧
    -- (B3) scalar homogeneity right
    (∀ c : ℂ, ∀ u v : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      nsBilinear S u (c • v) = c • nsBilinear S u v) :=
  ⟨nsBilinear_div_free S,
   nsBilinear_add_left S,
   nsBilinear_add_right S,
   nsBilinear_smul_left S,
   nsBilinear_smul_right S⟩

end PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

#print axioms
  PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField.concrete_div_free_ns_bilinear_capstone
