/-
# NS3D_MeanZeroDivFree — mean-zero divergence-free subspace

★ 2026-06-12 — thirteenth Type (F) advance on the NS Sobolev/Leray
bridge (Wave 51B residual gap). Defines and characterizes the
*mean-zero* divergence-free subspace, which is the natural
configuration space for the periodic NS equations on `𝕋³`.

A divergence-free Fourier-coefficient sequence is *mean-zero*
when its 0-mode vanishes: `c 0 = 0` (i.e. the spatial mean is
zero, equivalently the total momentum vanishes).

The mean-zero div-free subspace is preserved by:
  - the Leray projector (since `lerayProject c 0 = c 0`),
  - the Stokes operator (since `kNormSqReal 0 = 0` so the 0-mode
    is zeroed out automatically, hence "preserved at 0"),
  - the heat semigroup (since `heatMultiplier t 0 = 1` so the
    0-mode is unchanged, and starting at 0 stays at 0).

## What this file delivers, axiom-free

  (1) **`meanZeroDivFreeSubmodule`** — the sub-`Submodule ℂ` of
      `divFreeSubmodule` consisting of sequences `c` with `c 0 = 0`.

  (2) **`stokesOp_meanZero_mode`** — the Stokes operator sends the
      0-mode to 0 unconditionally (`kNormSqReal 0 = 0`).

  (3) **`heatSemigroup_preserves_meanZero`** — the heat semigroup
      preserves the mean-zero subspace.

  (4) **`lerayProject_preserves_meanZero`** — the Leray projector
      preserves the mean-zero subspace.

  (5) **Capstone** — the mean-zero div-free subspace is invariant
      under all three NS operators (Leray, Stokes, heat semigroup).

ZERO project axioms; kernel-only `[propext, Classical.choice, Quot.sound]`.

Author: Pablo Cohen + Claude Opus 4.7. 2026-06-12.
-/

import PF.NS3D_Wave51BResidualClosed

namespace PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

open PrincipiaTractalis.SobolevHSScaleOnTorus3Attempt
open PrincipiaTractalis.DivFreeFourierDensityOnTorus3Attempt

/-! ## §1 — The mean-zero divergence-free submodule -/

/-- **Mean-zero divergence-free subspace** of
    `(Fin 3 → ℤ) → (Fin 3 → ℂ)`: divergence-free at every wave-vector
    AND zero spatial mean (`c 0 = 0`). -/
def meanZeroDivFreeSubmodule : Submodule ℂ ((Fin 3 → ℤ) → (Fin 3 → ℂ)) where
  carrier :=
    { c | (∀ k : Fin 3 → ℤ, dotIntC3 k (c k) = 0) ∧ c 0 = 0 }
  zero_mem' := by
    refine ⟨?_, ?_⟩
    · intro k
      show dotIntC3 k ((0 : (Fin 3 → ℤ) → (Fin 3 → ℂ)) k) = 0
      have : ((0 : (Fin 3 → ℤ) → (Fin 3 → ℂ)) k) = (0 : Fin 3 → ℂ) := rfl
      rw [this]
      exact dotIntC3_zero k
    · rfl
  add_mem' := by
    intro c d ⟨hc_df, hc_0⟩ ⟨hd_df, hd_0⟩
    refine ⟨?_, ?_⟩
    · intro k
      have h_add : ((c + d) k) = c k + d k := rfl
      rw [h_add, dotIntC3_add, hc_df k, hd_df k, add_zero]
    · show (c + d) 0 = 0
      have h_add : (c + d) 0 = c 0 + d 0 := rfl
      rw [h_add, hc_0, hd_0, add_zero]
  smul_mem' := by
    intro lam c ⟨hc_df, hc_0⟩
    refine ⟨?_, ?_⟩
    · intro k
      have h_smul : ((lam • c) k) = lam • c k := rfl
      rw [h_smul, dotIntC3_smul, hc_df k, mul_zero]
    · show (lam • c) 0 = 0
      have h_smul : (lam • c) 0 = lam • c 0 := rfl
      rw [h_smul, hc_0, smul_zero]

theorem mem_meanZeroDivFreeSubmodule_iff
    (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    c ∈ meanZeroDivFreeSubmodule
      ↔ (∀ k : Fin 3 → ℤ, dotIntC3 k (c k) = 0) ∧ c 0 = 0 :=
  Iff.rfl

theorem meanZeroDivFreeSubmodule_le_divFreeSubmodule :
    meanZeroDivFreeSubmodule ≤ divFreeSubmodule := by
  intro c hc
  exact hc.1

/-! ## §2 — Stokes operator acts trivially on the 0-mode -/

theorem stokesOp_at_zero (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    stokesOp c 0 = 0 := by
  show (kNormSqReal 0 : ℂ) • c 0 = 0
  rw [kNormSqReal_zero]
  show ((0 : ℝ) : ℂ) • c 0 = 0
  push_cast
  rw [zero_smul]

theorem stokesOp_preserves_meanZero
    (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) (_h_meanZero : c 0 = 0) :
    stokesOp c 0 = 0 :=
  stokesOp_at_zero c

/-! ## §3 — Heat semigroup preserves the 0-mode -/

theorem heatSemigroup_at_zero
    (t : ℝ) (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    heatSemigroup t c 0 = c 0 := by
  show (heatMultiplier t 0 : ℂ) • c 0 = c 0
  rw [show heatMultiplier t 0 = 1 from ?_]
  · push_cast
    rw [one_smul]
  · unfold heatMultiplier
    rw [kNormSqReal_zero]
    rw [show -(t * 0) = 0 from by ring]
    exact Real.exp_zero

theorem heatSemigroup_preserves_meanZero
    (t : ℝ) (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) (h_meanZero : c 0 = 0) :
    heatSemigroup t c 0 = 0 := by
  rw [heatSemigroup_at_zero, h_meanZero]

/-! ## §4 — Leray projector preserves the 0-mode -/

theorem lerayProject_preserves_meanZero
    (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) (h_meanZero : c 0 = 0) :
    lerayProject c 0 = 0 := by
  rw [lerayProject_zero_mode]
  exact h_meanZero

/-! ## §5 — Submodule-level closure under NS operators -/

theorem stokesOp_mem_meanZeroDivFree
    (c : (Fin 3 → ℤ) → (Fin 3 → ℂ))
    (hc : c ∈ meanZeroDivFreeSubmodule) :
    stokesOp c ∈ meanZeroDivFreeSubmodule := by
  refine ⟨?_, ?_⟩
  · exact stokesOp_preserves_divFree c hc.1
  · exact stokesOp_at_zero c

theorem heatSemigroup_mem_meanZeroDivFree
    (t : ℝ) (c : (Fin 3 → ℤ) → (Fin 3 → ℂ))
    (hc : c ∈ meanZeroDivFreeSubmodule) :
    heatSemigroup t c ∈ meanZeroDivFreeSubmodule := by
  refine ⟨?_, ?_⟩
  · exact heatSemigroup_preserves_divFree t c hc.1
  · exact heatSemigroup_preserves_meanZero t c hc.2

theorem lerayProject_mem_meanZeroDivFree
    (c : (Fin 3 → ℤ) → (Fin 3 → ℂ))
    (hc_meanZero : c 0 = 0) :
    lerayProject c ∈ meanZeroDivFreeSubmodule := by
  refine ⟨?_, ?_⟩
  · exact lerayProject_div_free c
  · exact lerayProject_preserves_meanZero c hc_meanZero

/-! ## §6 — Capstone -/

/-- **★ MEAN-ZERO DIV-FREE CAPSTONE ★** —
    `concrete_div_free_mean_zero_capstone`.

    The mean-zero divergence-free subspace
    `meanZeroDivFreeSubmodule ⊆ divFreeSubmodule ⊆ (Fin 3 → ℤ) → (Fin 3 → ℂ)`
    is a `Submodule ℂ` and is invariant under all three NS operators:
      (M1) the Leray projector (when the input has mean zero),
      (M2) the Stokes operator (unconditionally, since `‖0‖² = 0`
           sends the 0-mode to 0),
      (M3) the heat semigroup (since `heatMultiplier t 0 = 1` keeps
           the 0-mode unchanged, so 0 maps to 0).

    The mean-zero div-free subspace is the natural configuration
    space for the NS equations on `𝕋³`. Combined with the 12-advance
    Wave 51B residual closure ledger, this gives the substrate-level
    NS framework a complete operator-theoretic infrastructure on
    the physically correct subspace. -/
theorem concrete_div_free_mean_zero_capstone :
    -- (M0) characterization
    (∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      c ∈ meanZeroDivFreeSubmodule
        ↔ (∀ k : Fin 3 → ℤ, dotIntC3 k (c k) = 0) ∧ c 0 = 0) ∧
    -- (M1) Leray projector preserves mean-zero
    (∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      c 0 = 0 → lerayProject c ∈ meanZeroDivFreeSubmodule) ∧
    -- (M2) Stokes operator preserves mean-zero (and div-free of course)
    (∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      c ∈ meanZeroDivFreeSubmodule → stokesOp c ∈ meanZeroDivFreeSubmodule) ∧
    -- (M3) heat semigroup preserves mean-zero
    (∀ t : ℝ, ∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      c ∈ meanZeroDivFreeSubmodule → heatSemigroup t c ∈ meanZeroDivFreeSubmodule) ∧
    -- (M4) inclusion in div-free
    (meanZeroDivFreeSubmodule ≤ divFreeSubmodule) :=
  ⟨mem_meanZeroDivFreeSubmodule_iff,
   lerayProject_mem_meanZeroDivFree,
   stokesOp_mem_meanZeroDivFree,
   heatSemigroup_mem_meanZeroDivFree,
   meanZeroDivFreeSubmodule_le_divFreeSubmodule⟩

end PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

#print axioms
  PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField.concrete_div_free_mean_zero_capstone
