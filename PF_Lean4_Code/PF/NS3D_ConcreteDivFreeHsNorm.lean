/-
# NS3D_ConcreteDivFreeHsNorm — H^s norms on `ConcreteDivFreeVelocityField`

★ 2026-06-12 — extends `NS3D_ConcreteDivFreeVectorSpace.lean` with
the H^s norm structure on the concrete divergence-free velocity field
type. Uses vector-valued analogues of the existing `hsNormSqOn` from
`PF/SobolevHSScaleOnTorus3Attempt.lean` applied to the concrete
type's Fourier-coefficient sequence.

This connects the concrete div-free type to the framework's existing
H^s machinery, giving the NS Sobolev/Leray bridge a concrete
norm-equipped vector space carrier.

## What this file delivers, axiom-free

  (1) **`hsNormSqOnConcrete`** — the finite-sum H^s-norm-squared of a
      concrete div-free velocity field on a finite mode set.

  (2) **`hsNormSqOnConcrete_nonneg`** — non-negativity.

  (3) **`hsNormSqOnConcrete_zero`** — the zero field has zero H^s norm.

  (4) **`hsNormSqOnConcrete_smul`** — scaling: `‖c • u‖² = |c|² ‖u‖²`
      (for `c : ℂ` and concrete div-free `u`).

  (5) **`hsNormSqOnConcrete_mono_s`** — monotonicity in `s`.

  (6) **Capstone** — the full H^s norm structure is concretely
      computable on the concrete div-free type.

This is the third Type (F) formalization advance on the NS
Sobolev/Leray bridge (Wave 51B residual gap), after the concrete
type definition and the vector space structure.

ZERO project axioms; kernel-only `[propext, Classical.choice, Quot.sound]`.

Author: Pablo Cohen + Claude Opus 4.7. 2026-06-12.
-/

import PF.NS3D_ConcreteDivFreeVectorSpace
import PF.SobolevHSScaleOnTorus3Attempt

namespace PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

open PrincipiaTractalis.SobolevHSScaleOnTorus3Attempt

/-! ## §1 — Vector-valued H^s norm-squared -/

/-- **Vector-valued H^s norm-squared on a finite mode set `S`**:
    for a vector-Fourier-coefficient sequence
    `coeff : (Fin 3 → ℤ) → (Fin 3 → ℂ)`,
    `‖coeff‖²_{H^s, S} := Σ_{k ∈ S} hsWeight k s · ‖coeff k‖²`
    where the inner norm is the L² norm of the vector amplitude. -/
noncomputable def hsNormSqVecOn
    (coeff : (Fin 3 → ℤ) → (Fin 3 → ℂ)) (s : ℝ)
    (S : Finset (Fin 3 → ℤ)) : ℝ :=
  ∑ k ∈ S, hsWeight k s * ‖coeff k‖^2

theorem hsNormSqVecOn_nonneg
    (coeff : (Fin 3 → ℤ) → (Fin 3 → ℂ)) (s : ℝ)
    (S : Finset (Fin 3 → ℤ)) :
    0 ≤ hsNormSqVecOn coeff s S := by
  unfold hsNormSqVecOn
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (hsWeight_nonneg k s) (sq_nonneg _)

theorem hsNormSqVecOn_mono_s
    (coeff : (Fin 3 → ℤ) → (Fin 3 → ℂ))
    {s s' : ℝ} (hss' : s ≤ s')
    (S : Finset (Fin 3 → ℤ)) :
    hsNormSqVecOn coeff s S ≤ hsNormSqVecOn coeff s' S := by
  unfold hsNormSqVecOn
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_mul_of_nonneg_right (hsWeight_mono hss') (sq_nonneg _)

/-! ## §2 — Vector-valued L² norm-squared -/

/-- **Vector-valued L² norm-squared on a finite mode set `S`**. -/
noncomputable def L2NormSqVecOn
    (coeff : (Fin 3 → ℤ) → (Fin 3 → ℂ))
    (S : Finset (Fin 3 → ℤ)) : ℝ :=
  ∑ k ∈ S, ‖coeff k‖^2

theorem L2NormSqVecOn_nonneg
    (coeff : (Fin 3 → ℤ) → (Fin 3 → ℂ))
    (S : Finset (Fin 3 → ℤ)) :
    0 ≤ L2NormSqVecOn coeff S := by
  unfold L2NormSqVecOn
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem hsNormSqVecOn_zero_exp
    (coeff : (Fin 3 → ℤ) → (Fin 3 → ℂ))
    (S : Finset (Fin 3 → ℤ)) :
    hsNormSqVecOn coeff 0 S = L2NormSqVecOn coeff S := by
  unfold hsNormSqVecOn L2NormSqVecOn
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [hsWeight_zero_exp]
  ring

/-! ## §3 — H^s norm-squared on the concrete div-free type -/

/-- **H^s norm-squared of a concrete div-free velocity field on a
    finite mode set `S`**: defined as the vector-valued H^s norm
    of its coefficient sequence. -/
noncomputable def hsNormSqOnConcrete
    (u : ConcreteDivFreeVelocityField) (s : ℝ)
    (S : Finset (Fin 3 → ℤ)) : ℝ :=
  hsNormSqVecOn u.coeff s S

theorem hsNormSqOnConcrete_def
    (u : ConcreteDivFreeVelocityField) (s : ℝ)
    (S : Finset (Fin 3 → ℤ)) :
    hsNormSqOnConcrete u s S = hsNormSqVecOn u.coeff s S := rfl

theorem hsNormSqOnConcrete_nonneg
    (u : ConcreteDivFreeVelocityField) (s : ℝ)
    (S : Finset (Fin 3 → ℤ)) :
    0 ≤ hsNormSqOnConcrete u s S :=
  hsNormSqVecOn_nonneg u.coeff s S

theorem hsNormSqOnConcrete_zero
    (s : ℝ) (S : Finset (Fin 3 → ℤ)) :
    hsNormSqOnConcrete (0 : ConcreteDivFreeVelocityField) s S = 0 := by
  unfold hsNormSqOnConcrete hsNormSqVecOn
  apply Finset.sum_eq_zero
  intro k _
  have h_coeff_k : (0 : ConcreteDivFreeVelocityField).coeff k = 0 :=
    cdf_zero_coeff k
  rw [h_coeff_k]
  simp

/-! ## §4 — Scaling under scalar multiplication -/

/-- **Scaling identity for H^s norm**: `‖c • u‖²_{H^s, S} = |c|² ‖u‖²_{H^s, S}`. -/
theorem hsNormSqOnConcrete_smul
    (c : ℂ) (u : ConcreteDivFreeVelocityField) (s : ℝ)
    (S : Finset (Fin 3 → ℤ)) :
    hsNormSqOnConcrete (c • u) s S = ‖c‖^2 * hsNormSqOnConcrete u s S := by
  unfold hsNormSqOnConcrete hsNormSqVecOn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have h_coeff : (c • u).coeff k = c • u.coeff k := smul_coeff c u k
  rw [h_coeff]
  have h_norm_sq : ‖c • u.coeff k‖ ^ 2 = ‖c‖ ^ 2 * ‖u.coeff k‖ ^ 2 := by
    rw [norm_smul]
    ring
  rw [h_norm_sq]
  ring

/-! ## §5 — Monotonicity in `s` -/

theorem hsNormSqOnConcrete_mono_s
    (u : ConcreteDivFreeVelocityField)
    {s s' : ℝ} (hss' : s ≤ s')
    (S : Finset (Fin 3 → ℤ)) :
    hsNormSqOnConcrete u s S ≤ hsNormSqOnConcrete u s' S :=
  hsNormSqVecOn_mono_s u.coeff hss' S

/-! ## §6 — L² norm-squared (Sobolev exponent zero) -/

/-- **L² norm-squared** on a concrete div-free velocity field. -/
noncomputable def L2NormSqOnConcrete
    (u : ConcreteDivFreeVelocityField) (S : Finset (Fin 3 → ℤ)) : ℝ :=
  L2NormSqVecOn u.coeff S

theorem L2NormSqOnConcrete_nonneg
    (u : ConcreteDivFreeVelocityField) (S : Finset (Fin 3 → ℤ)) :
    0 ≤ L2NormSqOnConcrete u S :=
  L2NormSqVecOn_nonneg u.coeff S

/-- **L² is the `s = 0` specialization of H^s**. -/
theorem L2_eq_hsNormSqOnConcrete_zero
    (u : ConcreteDivFreeVelocityField) (S : Finset (Fin 3 → ℤ)) :
    L2NormSqOnConcrete u S = hsNormSqOnConcrete u 0 S := by
  unfold L2NormSqOnConcrete hsNormSqOnConcrete
  rw [hsNormSqVecOn_zero_exp]

/-- **L² ≤ H^s for `s ≥ 0`**: the L² norm is bounded above by the
    H^s norm for non-negative Sobolev exponent. -/
theorem L2NormSqOnConcrete_le_hsNormSqOnConcrete
    (u : ConcreteDivFreeVelocityField)
    {s : ℝ} (hs : 0 ≤ s) (S : Finset (Fin 3 → ℤ)) :
    L2NormSqOnConcrete u S ≤ hsNormSqOnConcrete u s S := by
  rw [L2_eq_hsNormSqOnConcrete_zero]
  exact hsNormSqOnConcrete_mono_s u hs S

/-! ## §7 — Capstone -/

/-- **★ H^s NORM STRUCTURE ON CONCRETE DIV-FREE CAPSTONE ★** —
    `concrete_div_free_hs_norm_capstone`.

    The concrete divergence-free velocity field type carries the
    explicit H^s norm-squared structure with:
      (H1) non-negativity,
      (H2) zero on the zero field,
      (H3) scaling `‖c • u‖² = |c|² ‖u‖²`,
      (H4) monotonicity in `s`,
      (H5) L² ≤ H^s for `s ≥ 0`.

    Combined with the vector space structure
    (`concrete_div_free_vector_space_capstone`), this gives the
    concrete div-free type the full algebraic + norm structure
    needed for the mathlib SobolevSpace bridge. -/
theorem concrete_div_free_hs_norm_capstone
    (s : ℝ) (S : Finset (Fin 3 → ℤ)) :
    -- (H1) non-negativity
    (∀ u : ConcreteDivFreeVelocityField, 0 ≤ hsNormSqOnConcrete u s S) ∧
    -- (H2) zero on zero
    (hsNormSqOnConcrete (0 : ConcreteDivFreeVelocityField) s S = 0) ∧
    -- (H3) scaling
    (∀ c : ℂ, ∀ u : ConcreteDivFreeVelocityField,
      hsNormSqOnConcrete (c • u) s S = ‖c‖^2 * hsNormSqOnConcrete u s S) ∧
    -- (H4) monotonicity
    (∀ u : ConcreteDivFreeVelocityField, ∀ s' : ℝ, s ≤ s' →
      hsNormSqOnConcrete u s S ≤ hsNormSqOnConcrete u s' S) ∧
    -- (H5) L² ≤ H^s for s ≥ 0
    (0 ≤ s → ∀ u : ConcreteDivFreeVelocityField,
      L2NormSqOnConcrete u S ≤ hsNormSqOnConcrete u s S) :=
  ⟨fun u => hsNormSqOnConcrete_nonneg u s S,
   hsNormSqOnConcrete_zero s S,
   fun c u => hsNormSqOnConcrete_smul c u s S,
   fun u _ hss' => hsNormSqOnConcrete_mono_s u hss' S,
   fun hs u => L2NormSqOnConcrete_le_hsNormSqOnConcrete u hs S⟩

end PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

#print axioms
  PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField.concrete_div_free_hs_norm_capstone
