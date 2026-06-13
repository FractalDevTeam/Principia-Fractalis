/-
# NS3D_HeatSemigroupHsContraction — H^s-norm contraction
   of the heat semigroup

★ 2026-06-12 — fourteenth Type (F) advance on the NS Sobolev/Leray
bridge (Wave 51B residual gap). Lifts the per-mode L²-contraction
of the heat semigroup to a global H^s-norm contraction:

  `t ≥ 0  ⇒  hsNormSqVecOnL2 (heatSemigroup t c) s S
              ≤ hsNormSqVecOnL2 c s S`

This is the central a priori estimate for the linear heat equation
on the 3-torus.

## What this file delivers, axiom-free

  (1) **`hsNormSqVecOnL2_heatSemigroup_le_of_nonneg`** — global
      H^s contraction of the heat semigroup.

  (2) **`hsNormSqOnConcreteL2_heatSemigroup_le_of_nonneg`** — the
      same at the concrete type level.

  (3) **Capstone** — the heat semigroup is a contraction in the
      L²-style H^s norm at every `s ∈ ℝ` and every finite mode
      set `S`, for non-negative time.

ZERO project axioms; kernel-only `[propext, Classical.choice, Quot.sound]`.

Author: Pablo Cohen + Claude Opus 4.7. 2026-06-12.
-/

import PF.NS3D_MeanZeroDivFree

namespace PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

open PrincipiaTractalis.SobolevHSScaleOnTorus3Attempt
open PrincipiaTractalis.DivFreeFourierDensityOnTorus3Attempt

/-! ## §1 — H^s contraction at the function level -/

/-- **H^s contraction of the heat semigroup**:
    for `t ≥ 0`, the L²-style H^s norm-squared is monotone-non-increasing
    under the heat semigroup. -/
theorem hsNormSqVecOnL2_heatSemigroup_le_of_nonneg
    {t : ℝ} (ht : 0 ≤ t) (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) (s : ℝ)
    (S : Finset (Fin 3 → ℤ)) :
    hsNormSqVecOnL2 (heatSemigroup t c) s S ≤ hsNormSqVecOnL2 c s S := by
  unfold hsNormSqVecOnL2
  apply Finset.sum_le_sum
  intro k _
  -- per-mode: hsWeight k s * vecL2NormSq (heatSemigroup t c k)
  --         ≤ hsWeight k s * vecL2NormSq (c k)
  have h_mode :
      vecL2NormSq (heatSemigroup t c k) ≤ vecL2NormSq (c k) :=
    vecL2NormSq_heatSemigroup_le_of_nonneg ht c k
  exact mul_le_mul_of_nonneg_left h_mode (hsWeight_nonneg k s)

/-! ## §2 — H^s contraction at the concrete type level -/

theorem hsNormSqOnConcreteL2_heatSemigroup_le_of_nonneg
    {t : ℝ} (ht : 0 ≤ t) (u : ConcreteDivFreeVelocityField) (s : ℝ)
    (S : Finset (Fin 3 → ℤ)) :
    hsNormSqOnConcreteL2 (heatSemigroupOnConcrete t u) s S
      ≤ hsNormSqOnConcreteL2 u s S := by
  show hsNormSqVecOnL2 (heatSemigroupOnConcrete t u).coeff s S
      ≤ hsNormSqVecOnL2 u.coeff s S
  rw [heatSemigroupOnConcrete_coeff]
  exact hsNormSqVecOnL2_heatSemigroup_le_of_nonneg ht u.coeff s S

/-! ## §3 — Capstone -/

/-- **★ HEAT SEMIGROUP H^s CONTRACTION CAPSTONE ★** —
    `concrete_div_free_heat_semigroup_hs_contraction_capstone`.

    The heat semigroup is a contraction in the L²-style H^s norm
    at every `s ∈ ℝ` and every finite mode set `S`, for `t ≥ 0`:
      (HC1) at the function level on the ambient Fourier-coefficient
            space,
      (HC2) at the concrete `ConcreteDivFreeVelocityField` level.

    This is the central a priori estimate for the linear heat
    equation on `𝕋³`. It says that the heat semigroup smooths
    initial data: not only is the L² norm non-increasing, but
    every H^s norm is non-increasing.

    Combined with the H^s-norm structure and the heat semigroup
    semigroup property, this gives the substrate-level NS
    framework the standard linear-NS a priori bound. -/
theorem concrete_div_free_heat_semigroup_hs_contraction_capstone :
    -- (HC1) ambient H^s contraction
    (∀ t : ℝ, 0 ≤ t →
      ∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ), ∀ s : ℝ, ∀ S : Finset (Fin 3 → ℤ),
        hsNormSqVecOnL2 (heatSemigroup t c) s S ≤ hsNormSqVecOnL2 c s S) ∧
    -- (HC2) concrete H^s contraction
    (∀ t : ℝ, 0 ≤ t →
      ∀ u : ConcreteDivFreeVelocityField, ∀ s : ℝ, ∀ S : Finset (Fin 3 → ℤ),
        hsNormSqOnConcreteL2 (heatSemigroupOnConcrete t u) s S
          ≤ hsNormSqOnConcreteL2 u s S) :=
  ⟨fun t ht c s S => hsNormSqVecOnL2_heatSemigroup_le_of_nonneg ht c s S,
   fun t ht u s S => hsNormSqOnConcreteL2_heatSemigroup_le_of_nonneg ht u s S⟩

end PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

#print axioms
  PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField.concrete_div_free_heat_semigroup_hs_contraction_capstone
