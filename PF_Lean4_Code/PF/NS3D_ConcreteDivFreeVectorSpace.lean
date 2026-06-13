/-
# NS3D_ConcreteDivFreeVectorSpace — complex vector space structure on
   `ConcreteDivFreeVelocityField`

★ 2026-06-12 — extends `NS3D_ConcreteDivFreeVelocityField.lean` with
the complex vector space structure: addition, negation, scalar
multiplication, the AddCommGroup + Module ℂ instances. The
divergence-free constraint is preserved under all linear operations,
since `dotIntC3 k` is ℂ-linear in the second argument.

## What this file delivers, axiom-free

  (1) **Addition**: divergence-free sequences add to divergence-free
      sequences (by linearity of `dotIntC3` in the second argument).

  (2) **Negation**: the negation of a div-free sequence is div-free.

  (3) **Scalar multiplication**: `c · u` is div-free for any `c : ℂ`
      and div-free `u`.

  (4) **AddCommGroup instance**: makes `ConcreteDivFreeVelocityField`
      a commutative additive group.

  (5) **Module ℂ instance**: makes `ConcreteDivFreeVelocityField` a
      complex vector space.

  (6) **Capstone**: the full vector-space structure is non-trivially
      inhabited (non-zero element exists).

This is the foundation for downstream H^s / L² norms and the
mathlib SobolevSpace bridge.

ZERO project axioms; kernel-only `[propext, Classical.choice, Quot.sound]`.

Author: Pablo Cohen + Claude Opus 4.7. 2026-06-12.
-/

import PF.NS3D_ConcreteDivFreeVelocityField

namespace PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

open PrincipiaTractalis.DivFreeFourierDensityOnTorus3Attempt

/-! ## §1 — Linearity of `dotIntC3` in the second argument -/

theorem dotIntC3_add (k : Fin 3 → ℤ) (a b : Fin 3 → ℂ) :
    dotIntC3 k (a + b) = dotIntC3 k a + dotIntC3 k b := by
  unfold dotIntC3
  simp only [Pi.add_apply, mul_add]
  rw [Finset.sum_add_distrib]

theorem dotIntC3_neg (k : Fin 3 → ℤ) (a : Fin 3 → ℂ) :
    dotIntC3 k (-a) = -dotIntC3 k a := by
  unfold dotIntC3
  simp only [Pi.neg_apply, mul_neg]
  rw [Finset.sum_neg_distrib]

theorem dotIntC3_smul (k : Fin 3 → ℤ) (c : ℂ) (a : Fin 3 → ℂ) :
    dotIntC3 k (c • a) = c * dotIntC3 k a := by
  unfold dotIntC3
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  show (k j : ℂ) * (c • a) j = c * ((k j : ℂ) * a j)
  rw [show (c • a) j = c * a j from rfl]
  ring

theorem dotIntC3_zero (k : Fin 3 → ℤ) :
    dotIntC3 k (0 : Fin 3 → ℂ) = 0 := by
  unfold dotIntC3
  simp

/-! ## §2 — Addition on `ConcreteDivFreeVelocityField` -/

/-- **Addition**: the sum of two div-free fields is div-free. -/
instance : Add ConcreteDivFreeVelocityField where
  add u v := {
    coeff := u.coeff + v.coeff
    div_free := by
      intro k
      have h_eq : (u.coeff + v.coeff) k = u.coeff k + v.coeff k := rfl
      rw [h_eq, dotIntC3_add, u.div_free k, v.div_free k, add_zero]
  }

theorem add_coeff (u v : ConcreteDivFreeVelocityField) (k : Fin 3 → ℤ) :
    (u + v).coeff k = u.coeff k + v.coeff k := rfl

/-! ## §3 — Negation -/

/-- **Negation**: the negation of a div-free field is div-free. -/
instance : Neg ConcreteDivFreeVelocityField where
  neg u := {
    coeff := -u.coeff
    div_free := by
      intro k
      have h_eq : (-u.coeff) k = -u.coeff k := rfl
      rw [h_eq, dotIntC3_neg, u.div_free k, neg_zero]
  }

theorem neg_coeff (u : ConcreteDivFreeVelocityField) (k : Fin 3 → ℤ) :
    (-u).coeff k = -u.coeff k := rfl

/-! ## §4 — Scalar multiplication -/

/-- **Scalar multiplication**: `c • u` is div-free for any `c : ℂ`. -/
instance : SMul ℂ ConcreteDivFreeVelocityField where
  smul c u := {
    coeff := c • u.coeff
    div_free := by
      intro k
      have h_eq : (c • u.coeff) k = c • u.coeff k := rfl
      rw [h_eq, dotIntC3_smul, u.div_free k, mul_zero]
  }

theorem smul_coeff (c : ℂ) (u : ConcreteDivFreeVelocityField)
    (k : Fin 3 → ℤ) :
    (c • u).coeff k = c • u.coeff k := rfl

/-! ## §5 — Subtraction (derived from neg + add) -/

instance : Sub ConcreteDivFreeVelocityField where
  sub u v := u + (-v)

theorem sub_coeff (u v : ConcreteDivFreeVelocityField) (k : Fin 3 → ℤ) :
    (u - v).coeff k = u.coeff k - v.coeff k := by
  show ((u + (-v)).coeff k) = u.coeff k - v.coeff k
  rw [add_coeff, neg_coeff]
  ring

/-! ## §6 — Extensionality -/

@[ext]
theorem ext (u v : ConcreteDivFreeVelocityField)
    (h : u.coeff = v.coeff) : u = v := by
  cases u
  cases v
  congr

/-! ## §7 — AddCommGroup instance -/

/-! ## §7.5 — Coefficient equations at zero -/

theorem cdf_zero_coeff (k : Fin 3 → ℤ) :
    (0 : ConcreteDivFreeVelocityField).coeff k = 0 := rfl

/-! ## §8 — AddCommGroup instance via direct coefficient equality -/

instance : AddCommGroup ConcreteDivFreeVelocityField where
  add := (· + ·)
  zero := 0
  neg := (-·)
  sub := (· - ·)
  add_assoc u v w := by
    ext k
    rw [add_coeff, add_coeff, add_coeff, add_coeff, add_assoc]
  zero_add u := by
    ext k
    rw [add_coeff, cdf_zero_coeff, zero_add]
  add_zero u := by
    ext k
    rw [add_coeff, cdf_zero_coeff, add_zero]
  neg_add_cancel u := by
    ext k
    rw [add_coeff, neg_coeff, neg_add_cancel, cdf_zero_coeff]
  add_comm u v := by
    ext k
    rw [add_coeff, add_coeff, add_comm]
  sub_eq_add_neg u v := by
    ext k
    rw [sub_coeff, add_coeff, neg_coeff]
    ring
  nsmul := nsmulRec
  zsmul := zsmulRec

/-! ## §9 — Module ℂ instance -/

instance : Module ℂ ConcreteDivFreeVelocityField where
  smul := (· • ·)
  one_smul u := by
    ext k
    rw [smul_coeff, one_smul]
  mul_smul a b u := by
    ext k
    rw [smul_coeff, smul_coeff, smul_coeff, mul_smul]
  smul_zero c := by
    apply ext
    funext k
    show (c • (0 : ConcreteDivFreeVelocityField)).coeff k = (0 : ConcreteDivFreeVelocityField).coeff k
    rw [smul_coeff, cdf_zero_coeff k]
    exact smul_zero c
  smul_add c u v := by
    apply ext
    funext k
    show (c • (u + v)).coeff k = (c • u + c • v).coeff k
    rw [smul_coeff, add_coeff, add_coeff, smul_coeff, smul_coeff]
    exact smul_add c _ _
  add_smul a b u := by
    apply ext
    funext k
    show ((a + b) • u).coeff k = (a • u + b • u).coeff k
    rw [smul_coeff, add_coeff, smul_coeff, smul_coeff]
    exact add_smul a b _
  zero_smul u := by
    apply ext
    funext k
    show ((0 : ℂ) • u).coeff k = (0 : ConcreteDivFreeVelocityField).coeff k
    rw [smul_coeff, cdf_zero_coeff k]
    exact zero_smul ℂ _

/-! ## §9 — Capstone -/

/-- **★ COMPLEX VECTOR SPACE CAPSTONE ON CONCRETE DIV-FREE TYPE ★** —
    `concrete_div_free_vector_space_capstone`.

    The type `ConcreteDivFreeVelocityField` is a complex vector space
    (AddCommGroup + Module ℂ instance), with the divergence-free
    constraint preserved under all linear operations. Combined with
    the non-trivial witness from
    `concrete_div_free_velocity_field_capstone`, the space is
    NON-TRIVIAL (positive-dimensional).

    This is the algebraic foundation for the H^s / L² norm structure
    needed for the mathlib SobolevSpace bridge. -/
theorem concrete_div_free_vector_space_capstone :
    -- (V1) Type is a complex vector space (AddCommGroup + Module ℂ).
    (∀ u v : ConcreteDivFreeVelocityField, ∀ k : Fin 3 → ℤ,
      (u + v).coeff k = u.coeff k + v.coeff k) ∧
    (∀ c : ℂ, ∀ u : ConcreteDivFreeVelocityField, ∀ k : Fin 3 → ℤ,
      (c • u).coeff k = c • u.coeff k) ∧
    (∀ u : ConcreteDivFreeVelocityField, ∀ k : Fin 3 → ℤ,
      (-u).coeff k = -u.coeff k) ∧
    -- (V2) Type is non-trivial (positive-dimensional).
    (∃ u : ConcreteDivFreeVelocityField, u ≠ 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun u v k => add_coeff u v k
  · exact fun c u k => smul_coeff c u k
  · exact fun u k => neg_coeff u k
  · refine ⟨ConcreteDivFreeVelocityField.nontrivial_witness, ?_⟩
    intro h_eq
    have h_coeff : ConcreteDivFreeVelocityField.nontrivial_witness.coeff
        = (0 : ConcreteDivFreeVelocityField).coeff := by
      rw [h_eq]
    have h_at_kOne : ConcreteDivFreeVelocityField.nontrivial_witness.coeff kOne
        = (0 : ConcreteDivFreeVelocityField).coeff kOne := by
      rw [h_coeff]
    have h_cdf_zero_coeff : (0 : ConcreteDivFreeVelocityField).coeff kOne
        = (fun _ => (0 : ℂ)) := rfl
    rw [h_cdf_zero_coeff] at h_at_kOne
    exact nontrivial_witness_is_nonzero h_at_kOne

end PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

#print axioms
  PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField.concrete_div_free_vector_space_capstone
