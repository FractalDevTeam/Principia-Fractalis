/-
# NS3D_NonlinearZeroMode — zero-mode vanishing of the NS bilinear
   core when the first argument is divergence-free

★ 2026-06-13 — twenty-second Type (F) advance on the NS Sobolev/Leray
bridge. Proves the clean structural identity:

  if `u` is divergence-free at every wave-vector, then
  `bilinearCore S u v 0 j = 0` for every `S`, `v`, `j`.

The argument is direct: at `k = 0`, the convolution constraint
`k_1 + k_2 = 0` forces `k_2 = -k_1`. Then the inner sum
`Σ_{i'} (k_2 i' : ℂ) · u k_1 i' = -Σ_{i'} (k_1 i' : ℂ) · u k_1 i'
                                = -dotIntC3 k_1 (u k_1)`,
which is zero by the divergence-free hypothesis on `u`.

This sharpens the Leray-projection-based vanishing
`nsBilinear S u v ∈ divFreeSubmodule` by giving a structural
pre-projection identity at the zero mode.

## What this file delivers, axiom-free

  (1) **`bilinearCore_zero_mode_of_div_free`** — at `k = 0`,
      `bilinearCore S u v 0 j = 0` when `u` is divergence-free.

  (2) **`bilinearCoreFn_zero_mode_of_div_free`** — function-level
      form: `bilinearCoreFn S u v 0 = 0`.

  (3) **`nsBilinear_div_free_mean_zero_of_div_free`** — the NS
      bilinear form lands in the mean-zero divergence-free
      subspace when its first argument is div-free.

  (4) **Capstone** — divergence-free first argument forces the
      NS bilinear form to be mean-zero and divergence-free.

ZERO project axioms; kernel-only `[propext, Classical.choice, Quot.sound]`.

Author: Pablo Cohen + Claude Opus 4.7. 2026-06-13.
-/

import PF.NS3D_NonlinearBilinear
import PF.NS3D_MeanZeroDivFree

namespace PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

open PrincipiaTractalis.SobolevHSScaleOnTorus3Attempt
open PrincipiaTractalis.DivFreeFourierDensityOnTorus3Attempt

/-! ## §1 — Zero-mode vanishing of the bilinear core -/

/-- **Inner sum identity**: `Σ_{i'} ((-k_1) i' : ℂ) * u k_1 i'
    = -Σ_{i'} (k_1 i' : ℂ) * u k_1 i'`. -/
theorem inner_sum_neg
    (k_1 : Fin 3 → ℤ) (u : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    ∑ i' : Fin 3, ((-k_1) i' : ℂ) * u k_1 i'
      = -∑ i' : Fin 3, (k_1 i' : ℂ) * u k_1 i' := by
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro i' _
  show ((-k_1) i' : ℂ) * u k_1 i' = -((k_1 i' : ℂ) * u k_1 i')
  have h_neg : (-k_1) i' = -(k_1 i') := rfl
  rw [h_neg]
  push_cast
  ring

/-- **Zero-mode vanishing**: when `u` is divergence-free at every
    wave-vector, the NS bilinear core at the zero mode vanishes
    component-wise. -/
theorem bilinearCore_zero_mode_of_div_free
    (S : Finset (Fin 3 → ℤ))
    (u v : (Fin 3 → ℤ) → (Fin 3 → ℂ))
    (h_div_free : ∀ k : Fin 3 → ℤ, dotIntC3 k (u k) = 0)
    (j : Fin 3) :
    bilinearCore S u v 0 j = 0 := by
  unfold bilinearCore
  apply Finset.sum_eq_zero
  intro p hp
  rw [mem_convIndex_iff] at hp
  obtain ⟨_hp1, _hp2, hp_sum⟩ := hp
  -- hp_sum : p.1 + p.2 = 0, so p.2 = -p.1
  have hp_2_eq : p.2 = -p.1 := by
    have : p.1 + p.2 = 0 := hp_sum
    have : p.2 = -p.1 := by
      have h := this
      linear_combination h
    exact this
  -- Substitute p.2 = -p.1
  rw [hp_2_eq]
  -- Inner sum at p.2 = -p.1 picks up a negation, becoming -dotIntC3 p.1 (u p.1)
  rw [inner_sum_neg]
  -- u is div-free at p.1
  have h_u_div : dotIntC3 p.1 (u p.1) = 0 := h_div_free p.1
  unfold dotIntC3 at h_u_div
  rw [h_u_div]
  ring

theorem bilinearCoreFn_zero_mode_of_div_free
    (S : Finset (Fin 3 → ℤ))
    (u v : (Fin 3 → ℤ) → (Fin 3 → ℂ))
    (h_div_free : ∀ k : Fin 3 → ℤ, dotIntC3 k (u k) = 0) :
    bilinearCoreFn S u v 0 = 0 := by
  funext j
  show bilinearCore S u v 0 j = 0
  exact bilinearCore_zero_mode_of_div_free S u v h_div_free j

/-! ## §2 — Mean-zero output -/

theorem nsBilinear_zero_mode_of_div_free
    (S : Finset (Fin 3 → ℤ))
    (u v : (Fin 3 → ℤ) → (Fin 3 → ℂ))
    (h_div_free : ∀ k : Fin 3 → ℤ, dotIntC3 k (u k) = 0) :
    nsBilinear S u v 0 = 0 := by
  unfold nsBilinear
  rw [lerayProject_zero_mode]
  exact bilinearCoreFn_zero_mode_of_div_free S u v h_div_free

theorem nsBilinear_mem_meanZeroDivFree_of_div_free
    (S : Finset (Fin 3 → ℤ))
    (u v : (Fin 3 → ℤ) → (Fin 3 → ℂ))
    (h_div_free : ∀ k : Fin 3 → ℤ, dotIntC3 k (u k) = 0) :
    nsBilinear S u v ∈ meanZeroDivFreeSubmodule := by
  refine ⟨?_, ?_⟩
  · exact nsBilinear_div_free S u v
  · exact nsBilinear_zero_mode_of_div_free S u v h_div_free

/-- **Specialization to concrete div-free type**: when `u` is a
    `ConcreteDivFreeVelocityField`, `nsBilinear S u.coeff v` is
    mean-zero and divergence-free. -/
theorem nsBilinear_concrete_left_mem_meanZeroDivFree
    (S : Finset (Fin 3 → ℤ))
    (u : ConcreteDivFreeVelocityField)
    (v : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    nsBilinear S u.coeff v ∈ meanZeroDivFreeSubmodule :=
  nsBilinear_mem_meanZeroDivFree_of_div_free S u.coeff v u.div_free

/-! ## §3 — Capstone -/

/-- **★ NS BILINEAR ZERO-MODE CAPSTONE ★** —
    `concrete_div_free_ns_bilinear_zero_mode_capstone`.

    Divergence-free first argument forces the NS bilinear form to
    be mean-zero and divergence-free, sharpening the post-Leray
    div-free property by giving a structural pre-projection
    vanishing identity at the zero mode:

    (Z1) `bilinearCore S u v 0 = 0` when `u` is div-free.
    (Z2) `nsBilinear S u v 0 = 0` when `u` is div-free.
    (Z3) `nsBilinear S u v ∈ meanZeroDivFreeSubmodule` when `u`
         is div-free.

    Specializing `u` to a `ConcreteDivFreeVelocityField` gives the
    canonical NS evolution dynamics: the bilinear advective term
    automatically lands in the mean-zero div-free configuration
    space of the periodic NS equations on `𝕋³`. -/
theorem concrete_div_free_ns_bilinear_zero_mode_capstone
    (S : Finset (Fin 3 → ℤ)) :
    -- (Z1) bilinearCore vanishes at zero-mode when u is div-free
    (∀ u v : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      (∀ k : Fin 3 → ℤ, dotIntC3 k (u k) = 0) →
      bilinearCoreFn S u v 0 = 0) ∧
    -- (Z2) nsBilinear vanishes at zero-mode when u is div-free
    (∀ u v : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      (∀ k : Fin 3 → ℤ, dotIntC3 k (u k) = 0) →
      nsBilinear S u v 0 = 0) ∧
    -- (Z3) nsBilinear is mean-zero div-free when u is div-free
    (∀ u v : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      (∀ k : Fin 3 → ℤ, dotIntC3 k (u k) = 0) →
      nsBilinear S u v ∈ meanZeroDivFreeSubmodule) ∧
    -- specialization to concrete div-free type
    (∀ u : ConcreteDivFreeVelocityField, ∀ v : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      nsBilinear S u.coeff v ∈ meanZeroDivFreeSubmodule) :=
  ⟨bilinearCoreFn_zero_mode_of_div_free S,
   nsBilinear_zero_mode_of_div_free S,
   nsBilinear_mem_meanZeroDivFree_of_div_free S,
   nsBilinear_concrete_left_mem_meanZeroDivFree S⟩

end PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

#print axioms
  PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField.concrete_div_free_ns_bilinear_zero_mode_capstone
