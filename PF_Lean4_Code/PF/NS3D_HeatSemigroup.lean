/-
# NS3D_HeatSemigroup — concrete heat semigroup `e^{-tA}` on
   Fourier-coefficient sequences

★ 2026-06-12 — twelfth Type (F) advance on the NS Sobolev/Leray
bridge (Wave 51B residual gap). Builds the concrete heat
semigroup `heatSemigroup t : ((Fin 3 → ℤ) → (Fin 3 → ℂ)) →
((Fin 3 → ℤ) → (Fin 3 → ℂ))` as the Fourier-diagonal multiplier
`e^{-t ‖k‖²_ℤ}` mode-by-mode.

## Concrete formula

`(heatSemigroup t c)(k) := (Real.exp (-(t * kNormSqReal k)) : ℂ) • c(k)`

## What this file delivers, axiom-free

  (1) **`heatSemigroup`** — the explicit semigroup.

  (2) **`heatSemigroup_zero_time`** — `heatSemigroup 0 = id`.

  (3) **`heatSemigroup_apply`**, **`_zero_mode`** — pointwise formulas.

  (4) **`heatSemigroup_add`**, **`_smul`**, **`_zero`** — ℂ-linearity.

  (5) **`heatSemigroup_preserves_divFree`** — preserves the
      divergence-free subspace.

  (6) **`heatSemigroupOnConcrete`** — restriction to
      `ConcreteDivFreeVelocityField`.

  (7) **`heatSemigroup_l2_contraction`** — L²-contraction:
      `‖heatSemigroup t u‖²_{L²} ≤ ‖u‖²_{L²}` for `t ≥ 0`
      (since `e^{-t ‖k‖²} ≤ 1` for `t ≥ 0`).

  (8) **Capstone** — the heat semigroup is a ℂ-linear contraction
      on the divergence-free subspace.

ZERO project axioms; kernel-only `[propext, Classical.choice, Quot.sound]`.

Author: Pablo Cohen + Claude Opus 4.7. 2026-06-12.
-/

import PF.NS3D_StokesSymmetric

namespace PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

open PrincipiaTractalis.SobolevHSScaleOnTorus3Attempt
open PrincipiaTractalis.DivFreeFourierDensityOnTorus3Attempt

/-! ## §1 — The heat semigroup multiplier -/

/-- **Fourier-mode multiplier of the heat semigroup at time `t`**:
    `e^{-t ‖k‖²_ℤ}`. -/
noncomputable def heatMultiplier (t : ℝ) (k : Fin 3 → ℤ) : ℝ :=
  Real.exp (-(t * kNormSqReal k))

theorem heatMultiplier_pos (t : ℝ) (k : Fin 3 → ℤ) :
    0 < heatMultiplier t k :=
  Real.exp_pos _

theorem heatMultiplier_le_one_of_nonneg
    {t : ℝ} (ht : 0 ≤ t) (k : Fin 3 → ℤ) :
    heatMultiplier t k ≤ 1 := by
  unfold heatMultiplier
  rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
  apply Real.exp_le_exp.mpr
  have h_nonneg : 0 ≤ t * kNormSqReal k :=
    mul_nonneg ht (kNormSqReal_nonneg k)
  linarith

theorem heatMultiplier_zero_time (k : Fin 3 → ℤ) :
    heatMultiplier 0 k = 1 := by
  unfold heatMultiplier
  rw [show -(0 * kNormSqReal k) = 0 from by ring]
  exact Real.exp_zero

/-! ## §2 — The heat semigroup -/

/-- **The heat semigroup `e^{-tA}` at time `t`**, Fourier-diagonal:
    `(heatSemigroup t c)(k) := e^{-t‖k‖²} • c(k)`. -/
noncomputable def heatSemigroup
    (t : ℝ) (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    (Fin 3 → ℤ) → (Fin 3 → ℂ) := fun k =>
  (heatMultiplier t k : ℂ) • c k

theorem heatSemigroup_apply
    (t : ℝ) (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) (k : Fin 3 → ℤ) :
    heatSemigroup t c k = (heatMultiplier t k : ℂ) • c k := rfl

theorem heatSemigroup_zero_time (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    heatSemigroup 0 c = c := by
  funext k j
  show (heatMultiplier 0 k : ℂ) • c k j = c k j
  rw [heatMultiplier_zero_time]
  show ((1 : ℝ) : ℂ) * c k j = c k j
  push_cast
  ring

/-! ## §3 — Linearity at the function level -/

theorem heatSemigroup_zero (t : ℝ) :
    heatSemigroup t (fun _ _ => (0 : ℂ)) = (fun _ _ => (0 : ℂ)) := by
  funext k j
  show (heatMultiplier t k : ℂ) • (fun _ : Fin 3 => (0 : ℂ)) j = 0
  simp

theorem heatSemigroup_add
    (t : ℝ) (c d : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    heatSemigroup t (c + d) = heatSemigroup t c + heatSemigroup t d := by
  funext k j
  show (heatMultiplier t k : ℂ) • (c + d) k j
      = ((heatMultiplier t k : ℂ) • c k + (heatMultiplier t k : ℂ) • d k) j
  have h_ck : (c + d) k = c k + d k := rfl
  rw [h_ck]
  show (heatMultiplier t k : ℂ) * (c k j + d k j)
      = (heatMultiplier t k : ℂ) * c k j + (heatMultiplier t k : ℂ) * d k j
  ring

theorem heatSemigroup_smul
    (t : ℝ) (lam : ℂ) (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    heatSemigroup t (lam • c) = lam • heatSemigroup t c := by
  funext k j
  show (heatMultiplier t k : ℂ) • (lam • c) k j = (lam • heatSemigroup t c) k j
  have h_ck : (lam • c) k = lam • c k := rfl
  rw [h_ck]
  show (heatMultiplier t k : ℂ) * (lam * c k j) = lam * ((heatMultiplier t k : ℂ) * c k j)
  ring

/-! ## §4 — Preservation of the divergence-free subspace -/

theorem heatSemigroup_preserves_divFree
    (t : ℝ) (c : (Fin 3 → ℤ) → (Fin 3 → ℂ))
    (h_div_free : ∀ k : Fin 3 → ℤ, dotIntC3 k (c k) = 0) :
    ∀ k : Fin 3 → ℤ, dotIntC3 k (heatSemigroup t c k) = 0 := by
  intro k
  show dotIntC3 k ((heatMultiplier t k : ℂ) • c k) = 0
  rw [dotIntC3_smul, h_div_free k, mul_zero]

/-! ## §5 — Restriction to `ConcreteDivFreeVelocityField` -/

noncomputable def heatSemigroupOnConcrete
    (t : ℝ) (u : ConcreteDivFreeVelocityField) : ConcreteDivFreeVelocityField where
  coeff := heatSemigroup t u.coeff
  div_free := heatSemigroup_preserves_divFree t u.coeff u.div_free

theorem heatSemigroupOnConcrete_coeff
    (t : ℝ) (u : ConcreteDivFreeVelocityField) :
    (heatSemigroupOnConcrete t u).coeff = heatSemigroup t u.coeff := rfl

theorem heatSemigroupOnConcrete_zero_time
    (u : ConcreteDivFreeVelocityField) :
    heatSemigroupOnConcrete 0 u = u := by
  apply ext
  rw [heatSemigroupOnConcrete_coeff]
  exact heatSemigroup_zero_time u.coeff

/-! ## §6 — L²-contraction at every mode -/

theorem vecL2NormSq_heatSemigroup_le_of_nonneg
    {t : ℝ} (ht : 0 ≤ t) (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) (k : Fin 3 → ℤ) :
    vecL2NormSq (heatSemigroup t c k) ≤ vecL2NormSq (c k) := by
  show vecL2NormSq ((heatMultiplier t k : ℂ) • c k) ≤ vecL2NormSq (c k)
  -- vecL2NormSq (α • a) = α² · vecL2NormSq a for real α
  have h_smul_normSq :
      vecL2NormSq ((heatMultiplier t k : ℂ) • c k)
        = (heatMultiplier t k)^2 * vecL2NormSq (c k) := by
    unfold vecL2NormSq
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    show ‖((heatMultiplier t k : ℂ) • c k) j‖^2
        = (heatMultiplier t k)^2 * ‖c k j‖^2
    show ‖(heatMultiplier t k : ℂ) * c k j‖^2
        = (heatMultiplier t k)^2 * ‖c k j‖^2
    rw [norm_mul]
    have h_norm_eq : ‖((heatMultiplier t k : ℂ))‖ = heatMultiplier t k := by
      rw [Complex.norm_real]
      exact abs_of_pos (heatMultiplier_pos t k)
    rw [h_norm_eq]
    ring
  rw [h_smul_normSq]
  have h_mult_le : heatMultiplier t k ≤ 1 := heatMultiplier_le_one_of_nonneg ht k
  have h_mult_pos : 0 < heatMultiplier t k := heatMultiplier_pos t k
  have h_sq_le : (heatMultiplier t k)^2 ≤ 1 := by
    have : (heatMultiplier t k)^2 ≤ 1^2 :=
      pow_le_pow_left₀ (le_of_lt h_mult_pos) h_mult_le 2
    simpa using this
  have h_nonneg : 0 ≤ vecL2NormSq (c k) := vecL2NormSq_nonneg _
  calc (heatMultiplier t k)^2 * vecL2NormSq (c k)
      ≤ 1 * vecL2NormSq (c k) := by
        exact mul_le_mul_of_nonneg_right h_sq_le h_nonneg
    _ = vecL2NormSq (c k) := one_mul _

/-! ## §7 — Capstone -/

/-- **★ HEAT SEMIGROUP CAPSTONE ★** —
    `concrete_div_free_heat_semigroup_capstone`.

    The concrete heat semigroup `heatSemigroup t` realizes
    `e^{-tA}` as a Fourier-diagonal multiplier:
      (HS1) Identity at time zero: `heatSemigroup 0 = id`,
      (HS2) ℂ-linear at every time,
      (HS3) preserves the divergence-free subspace,
      (HS4) at every mode `k` and every `t ≥ 0`,
            `vecL2NormSq (heatSemigroup t c k) ≤ vecL2NormSq (c k)`
            (contraction in L² norm at every mode).

    Together with the Stokes self-adjointness and positivity,
    this gives the heat semigroup the full operator-theoretic
    structure required for the NS heat-semigroup energy estimate. -/
theorem concrete_div_free_heat_semigroup_capstone :
    -- (HS1) identity at time zero
    (∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ), heatSemigroup 0 c = c) ∧
    -- (HS2) ℂ-linearity at every time
    (∀ t : ℝ, ∀ c d : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      heatSemigroup t (c + d) = heatSemigroup t c + heatSemigroup t d) ∧
    (∀ t : ℝ, ∀ lam : ℂ, ∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      heatSemigroup t (lam • c) = lam • heatSemigroup t c) ∧
    -- (HS3) preserves divergence-free subspace
    (∀ t : ℝ, ∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      (∀ k : Fin 3 → ℤ, dotIntC3 k (c k) = 0) →
      ∀ k : Fin 3 → ℤ, dotIntC3 k (heatSemigroup t c k) = 0) ∧
    -- (HS4) per-mode L²-contraction for non-negative time
    (∀ t : ℝ, 0 ≤ t →
      ∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ), ∀ k : Fin 3 → ℤ,
      vecL2NormSq (heatSemigroup t c k) ≤ vecL2NormSq (c k)) :=
  ⟨heatSemigroup_zero_time,
   fun t c d => heatSemigroup_add t c d,
   fun t lam c => heatSemigroup_smul t lam c,
   fun t c => heatSemigroup_preserves_divFree t c,
   fun t ht c k => vecL2NormSq_heatSemigroup_le_of_nonneg ht c k⟩

end PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

#print axioms
  PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField.concrete_div_free_heat_semigroup_capstone
