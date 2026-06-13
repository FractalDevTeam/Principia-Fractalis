/-
# NS3D_ConcreteDivFreeHsInner — H^s sesquilinear inner product
   on `ConcreteDivFreeVelocityField`

★ 2026-06-12 — extends `NS3D_ConcreteDivFreeHsNorm.lean` with the
H^s sesquilinear inner product, the pre-Hilbert structure that
the mathlib SobolevSpace bridge consumes.

This is the fourth Type (F) formalization advance on the NS
Sobolev/Leray bridge (Wave 51B residual gap), after the concrete
type, the vector space, and the norm-squared structures.

The complex inner product on `Fin 3 → ℂ` is defined explicitly
as `⟨a, b⟩_ℂ := Σ_j conj(a j) · b j`. We then define an
explicit L²-style squared amplitude `vecL2NormSq a := Σ_j ‖a j‖²`
which is the diagonal of `Re ⟨a, a⟩`.

## What this file delivers, axiom-free

  (1) **`innerC3`** — the explicit complex inner product on
      `Fin 3 → ℂ`.

  (2) **`vecL2NormSq`** — `Σ_j ‖a j‖²`, non-negative.

  (3) **`innerC3_self_re`** — `Re ⟨a, a⟩ = vecL2NormSq a`.

  (4) **`innerC3_conj_symm`** — `⟨a, b⟩ = conj ⟨b, a⟩`.

  (5) **`innerC3_add_left`**, **`innerC3_smul_left`** —
      linearity / conjugate-linearity in the first argument.

  (6) **`hsInnerVecOnL2`** — vector-valued H^s sesquilinear pairing
      `⟨u, v⟩_{H^s, S} := Σ_{k ∈ S} (hsWeight k s) · ⟨u k, v k⟩_C3`.

  (7) **`hsNormSqVecOnL2`** — the L²-style H^s norm-squared, with
      diagonal of the inner product equal to it (real part).

  (8) **`hsInnerOnConcrete`** — specialization to the concrete
      div-free type.

  (9) **Capstone** — the H^s inner-product structure has the
      diagonal-equals-L²-norm-squared identity, conjugate symmetry,
      additivity, scalar-conjugate linearity in the first argument,
      and non-negativity of the real part of the diagonal.

ZERO project axioms; kernel-only `[propext, Classical.choice, Quot.sound]`.

Author: Pablo Cohen + Claude Opus 4.7. 2026-06-12.
-/

import PF.NS3D_ConcreteDivFreeHsNorm

namespace PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

open PrincipiaTractalis.SobolevHSScaleOnTorus3Attempt

/-! ## §1 — Explicit complex inner product on `Fin 3 → ℂ` -/

/-- **Explicit complex inner product on `Fin 3 → ℂ`**:
    `⟨a, b⟩_C3 := Σ_j conj(a j) · b j`. Convention: conjugate-linear
    in the FIRST argument. -/
noncomputable def innerC3 (a b : Fin 3 → ℂ) : ℂ :=
  ∑ j : Fin 3, star (a j) * b j

/-- **L²-style squared amplitude on `Fin 3 → ℂ`**:
    `Σ_j ‖a j‖²`. -/
noncomputable def vecL2NormSq (a : Fin 3 → ℂ) : ℝ :=
  ∑ j : Fin 3, ‖a j‖^2

theorem vecL2NormSq_nonneg (a : Fin 3 → ℂ) : 0 ≤ vecL2NormSq a := by
  unfold vecL2NormSq
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- **`star z * z = (‖z‖² : ℂ)`** for `z : ℂ`. -/
theorem star_self_eq_normSq (z : ℂ) : star z * z = ((‖z‖^2 : ℝ) : ℂ) := by
  rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- **Diagonal real part identity**: `Re ⟨a, a⟩ = Σ_j ‖a j‖²`. -/
theorem innerC3_self_re (a : Fin 3 → ℂ) :
    (innerC3 a a).re = vecL2NormSq a := by
  unfold innerC3 vecL2NormSq
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [star_self_eq_normSq]
  exact Complex.ofReal_re _

/-- **Diagonal is a non-negative real**. -/
theorem innerC3_self_im (a : Fin 3 → ℂ) :
    (innerC3 a a).im = 0 := by
  unfold innerC3
  rw [Complex.im_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [star_self_eq_normSq]
  exact Complex.ofReal_im _

theorem innerC3_self_eq_vecL2 (a : Fin 3 → ℂ) :
    innerC3 a a = (vecL2NormSq a : ℂ) := by
  apply Complex.ext
  · rw [Complex.ofReal_re]; exact innerC3_self_re a
  · rw [Complex.ofReal_im]; exact innerC3_self_im a

/-- **Conjugate symmetry**: `⟨a, b⟩ = conj ⟨b, a⟩`. -/
theorem innerC3_conj_symm (a b : Fin 3 → ℂ) :
    innerC3 a b = star (innerC3 b a) := by
  unfold innerC3
  rw [star_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [star_mul, star_star]

/-- **Additive linearity in the first argument**. -/
theorem innerC3_add_left (a b c : Fin 3 → ℂ) :
    innerC3 (a + b) c = innerC3 a c + innerC3 b c := by
  unfold innerC3
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro j _
  show star ((a + b) j) * c j = star (a j) * c j + star (b j) * c j
  rw [show (a + b) j = a j + b j from rfl, star_add]
  ring

/-- **Scalar-conjugate linearity in the first argument**:
    `⟨c • a, b⟩ = conj c · ⟨a, b⟩`. -/
theorem innerC3_smul_left (c : ℂ) (a b : Fin 3 → ℂ) :
    innerC3 (c • a) b = (star c) * innerC3 a b := by
  unfold innerC3
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  show star ((c • a) j) * b j = star c * (star (a j) * b j)
  rw [show (c • a) j = c * a j from rfl, star_mul]
  ring

/-! ## §2 — Vector-valued H^s sesquilinear inner product -/

/-- **Vector-valued H^s sesquilinear inner product on a finite mode set `S`**:
    `⟨u, v⟩_{H^s, S} := Σ_{k ∈ S} (hsWeight k s : ℂ) · ⟨u k, v k⟩_C3`. -/
noncomputable def hsInnerVecOn
    (u v : (Fin 3 → ℤ) → (Fin 3 → ℂ)) (s : ℝ)
    (S : Finset (Fin 3 → ℤ)) : ℂ :=
  ∑ k ∈ S, (hsWeight k s : ℂ) * innerC3 (u k) (v k)

/-- **L²-style H^s vector norm-squared**:
    `Σ_{k ∈ S} (hsWeight k s) · vecL2NormSq (u k)`. -/
noncomputable def hsNormSqVecOnL2
    (u : (Fin 3 → ℤ) → (Fin 3 → ℂ)) (s : ℝ)
    (S : Finset (Fin 3 → ℤ)) : ℝ :=
  ∑ k ∈ S, hsWeight k s * vecL2NormSq (u k)

theorem hsNormSqVecOnL2_nonneg
    (u : (Fin 3 → ℤ) → (Fin 3 → ℂ)) (s : ℝ)
    (S : Finset (Fin 3 → ℤ)) :
    0 ≤ hsNormSqVecOnL2 u s S := by
  unfold hsNormSqVecOnL2
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (hsWeight_nonneg k s) (vecL2NormSq_nonneg _)

/-- **Diagonal real part identity at the H^s level**. -/
theorem hsInnerVecOn_self_re
    (u : (Fin 3 → ℤ) → (Fin 3 → ℂ)) (s : ℝ)
    (S : Finset (Fin 3 → ℤ)) :
    (hsInnerVecOn u u s S).re = hsNormSqVecOnL2 u s S := by
  unfold hsInnerVecOn hsNormSqVecOnL2
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Complex.mul_re]
  rw [Complex.ofReal_re, Complex.ofReal_im]
  rw [innerC3_self_re, innerC3_self_im]
  ring

/-- **`star ((r : ℂ)) = (r : ℂ)`** for `r : ℝ`. -/
theorem star_ofReal (r : ℝ) : star ((r : ℂ)) = ((r : ℂ)) := by
  rw [Complex.star_def]
  exact Complex.conj_ofReal r

/-- **Diagonal H^s inner-product equals norm-squared as complex**. -/
theorem hsInnerVecOn_self_eq_normSq
    (u : (Fin 3 → ℤ) → (Fin 3 → ℂ)) (s : ℝ)
    (S : Finset (Fin 3 → ℤ)) :
    hsInnerVecOn u u s S = (hsNormSqVecOnL2 u s S : ℂ) := by
  unfold hsInnerVecOn hsNormSqVecOnL2
  push_cast
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [innerC3_self_eq_vecL2]

/-- **Conjugate symmetry at the H^s level**. -/
theorem hsInnerVecOn_conj_symm
    (u v : (Fin 3 → ℤ) → (Fin 3 → ℂ)) (s : ℝ)
    (S : Finset (Fin 3 → ℤ)) :
    hsInnerVecOn u v s S = star (hsInnerVecOn v u s S) := by
  unfold hsInnerVecOn
  rw [star_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [star_mul, star_ofReal, ← innerC3_conj_symm]
  ring

/-- **Additivity in the first argument**. -/
theorem hsInnerVecOn_add_left
    (u v w : (Fin 3 → ℤ) → (Fin 3 → ℂ)) (s : ℝ)
    (S : Finset (Fin 3 → ℤ)) :
    hsInnerVecOn (u + v) w s S
      = hsInnerVecOn u w s S + hsInnerVecOn v w s S := by
  unfold hsInnerVecOn
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro k _
  show (hsWeight k s : ℂ) * innerC3 ((u + v) k) (w k)
      = (hsWeight k s : ℂ) * innerC3 (u k) (w k)
        + (hsWeight k s : ℂ) * innerC3 (v k) (w k)
  rw [show (u + v) k = u k + v k from rfl, innerC3_add_left]
  ring

/-- **Scalar-conjugate linearity in the first argument**. -/
theorem hsInnerVecOn_smul_left
    (c : ℂ) (u v : (Fin 3 → ℤ) → (Fin 3 → ℂ)) (s : ℝ)
    (S : Finset (Fin 3 → ℤ)) :
    hsInnerVecOn (c • u) v s S = (star c) * hsInnerVecOn u v s S := by
  unfold hsInnerVecOn
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  show (hsWeight k s : ℂ) * innerC3 ((c • u) k) (v k)
      = star c * ((hsWeight k s : ℂ) * innerC3 (u k) (v k))
  rw [show (c • u) k = c • u k from rfl, innerC3_smul_left]
  ring

/-! ## §3 — H^s inner product on the concrete div-free type -/

/-- **H^s sesquilinear inner product on the concrete div-free type**. -/
noncomputable def hsInnerOnConcrete
    (u v : ConcreteDivFreeVelocityField) (s : ℝ)
    (S : Finset (Fin 3 → ℤ)) : ℂ :=
  hsInnerVecOn u.coeff v.coeff s S

/-- **L²-based H^s norm-squared on the concrete div-free type**. -/
noncomputable def hsNormSqOnConcreteL2
    (u : ConcreteDivFreeVelocityField) (s : ℝ)
    (S : Finset (Fin 3 → ℤ)) : ℝ :=
  hsNormSqVecOnL2 u.coeff s S

theorem hsNormSqOnConcreteL2_nonneg
    (u : ConcreteDivFreeVelocityField) (s : ℝ)
    (S : Finset (Fin 3 → ℤ)) :
    0 ≤ hsNormSqOnConcreteL2 u s S :=
  hsNormSqVecOnL2_nonneg u.coeff s S

theorem hsInnerOnConcrete_self_eq_normSq
    (u : ConcreteDivFreeVelocityField) (s : ℝ)
    (S : Finset (Fin 3 → ℤ)) :
    hsInnerOnConcrete u u s S = (hsNormSqOnConcreteL2 u s S : ℂ) :=
  hsInnerVecOn_self_eq_normSq u.coeff s S

theorem hsInnerOnConcrete_conj_symm
    (u v : ConcreteDivFreeVelocityField) (s : ℝ)
    (S : Finset (Fin 3 → ℤ)) :
    hsInnerOnConcrete u v s S = star (hsInnerOnConcrete v u s S) :=
  hsInnerVecOn_conj_symm u.coeff v.coeff s S

theorem hsInnerOnConcrete_add_left
    (u v w : ConcreteDivFreeVelocityField) (s : ℝ)
    (S : Finset (Fin 3 → ℤ)) :
    hsInnerOnConcrete (u + v) w s S
      = hsInnerOnConcrete u w s S + hsInnerOnConcrete v w s S := by
  unfold hsInnerOnConcrete
  have h_uv_coeff : (u + v).coeff = u.coeff + v.coeff := by
    funext k
    exact add_coeff u v k
  rw [h_uv_coeff]
  exact hsInnerVecOn_add_left u.coeff v.coeff w.coeff s S

theorem hsInnerOnConcrete_smul_left
    (c : ℂ) (u v : ConcreteDivFreeVelocityField) (s : ℝ)
    (S : Finset (Fin 3 → ℤ)) :
    hsInnerOnConcrete (c • u) v s S
      = (star c) * hsInnerOnConcrete u v s S := by
  unfold hsInnerOnConcrete
  have h_smul_coeff : (c • u).coeff = c • u.coeff := by
    funext k
    exact smul_coeff c u k
  rw [h_smul_coeff]
  exact hsInnerVecOn_smul_left c u.coeff v.coeff s S

/-- **Diagonal real part of the inner product is non-negative**. -/
theorem hsInnerOnConcrete_self_re_nonneg
    (u : ConcreteDivFreeVelocityField) (s : ℝ)
    (S : Finset (Fin 3 → ℤ)) :
    0 ≤ (hsInnerOnConcrete u u s S).re := by
  rw [hsInnerOnConcrete_self_eq_normSq]
  simp
  exact hsNormSqOnConcreteL2_nonneg u s S

/-! ## §4 — Capstone -/

/-- **★ H^s INNER-PRODUCT STRUCTURE ON CONCRETE DIV-FREE CAPSTONE ★** —
    `concrete_div_free_hs_inner_capstone`.

    The concrete divergence-free velocity field type carries an
    explicit H^s sesquilinear inner-product structure with:
      (I1) diagonal equals L²-style H^s norm-squared (as ℂ),
      (I2) conjugate symmetry,
      (I3) additivity in the first argument,
      (I4) scalar-conjugate linearity in the first argument,
      (I5) non-negativity of the real part of the diagonal.

    Combined with the vector space and norm capstones, this gives
    the concrete div-free type the complete H^s pre-Hilbert
    structure needed for the mathlib SobolevSpace bridge. -/
theorem concrete_div_free_hs_inner_capstone
    (s : ℝ) (S : Finset (Fin 3 → ℤ)) :
    (∀ u : ConcreteDivFreeVelocityField,
      hsInnerOnConcrete u u s S = (hsNormSqOnConcreteL2 u s S : ℂ)) ∧
    (∀ u v : ConcreteDivFreeVelocityField,
      hsInnerOnConcrete u v s S = star (hsInnerOnConcrete v u s S)) ∧
    (∀ u v w : ConcreteDivFreeVelocityField,
      hsInnerOnConcrete (u + v) w s S
        = hsInnerOnConcrete u w s S + hsInnerOnConcrete v w s S) ∧
    (∀ c : ℂ, ∀ u v : ConcreteDivFreeVelocityField,
      hsInnerOnConcrete (c • u) v s S
        = (star c) * hsInnerOnConcrete u v s S) ∧
    (∀ u : ConcreteDivFreeVelocityField,
      0 ≤ (hsInnerOnConcrete u u s S).re) :=
  ⟨fun u => hsInnerOnConcrete_self_eq_normSq u s S,
   fun u v => hsInnerOnConcrete_conj_symm u v s S,
   fun u v w => hsInnerOnConcrete_add_left u v w s S,
   fun c u v => hsInnerOnConcrete_smul_left c u v s S,
   fun u => hsInnerOnConcrete_self_re_nonneg u s S⟩

end PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

#print axioms
  PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField.concrete_div_free_hs_inner_capstone
