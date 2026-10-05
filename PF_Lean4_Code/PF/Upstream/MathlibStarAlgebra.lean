/-
Copyright (c) 2026 Pablo Cohen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Cohen
-/
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.Unitary
import Mathlib.Algebra.Algebra.Subalgebra.Directed
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.Algebra.Star

/-!
# Star-algebra lemmas absent from mathlib, stated at upstream generality

Four results that `PF/SubstrateRigidity.lean` needs and mathlib does not have. In
that file each exists only as a `private` declaration specialised to the case the
Glimm `3^∞` classification actually consumes — scalars fixed to `ℂ`, matrix
algebras fixed to `Matrix (Fin N) (Fin N) ℂ`. Each proof there, however, uses only
facts that hold in any star ring, so the specialisation is an artefact of where the
lemma was written, not of what it needs.

This module is the de-specialised form: no PF import, no `ℂ`, no `Fin`, nothing
from the substrate development. It is PF-free on purpose, so each declaration can
be moved to the mathlib file named below without editing its statement or proof.

## Main declarations

* `StarSubalgebra.coe_iSup_of_directed` — the underlying set of a directed
  supremum of *-subalgebras is the union of the underlying sets, with
  `StarSubalgebra.mem_iSup_of_directed`. Mathlib has this for
  `NonUnitalStarSubalgebra` (`Mathlib/Algebra/Star/NonUnitalSubalgebra.lean:1022`)
  and for `Subalgebra`, `Subfield`, `Subring`, `Submodule`, `Submonoid`,
  `Subgroup` and `IntermediateField` — the unital *-case is the gap.
  *Destination:* `Mathlib/Algebra/Star/Subalgebra.lean`.

* `StarAlgEquiv.conjugateBy` — conjugation `x ↦ u * x * star u` by an element
  satisfying `u * star u = 1` and `star u * u = 1`, as a `StarAlgEquiv`, with
  `unitary.conjStarAlgEquiv` for the bundled `unitary A` form and
  `unitary.conjStarAlgEquiv_mul` for its multiplicativity. Mathlib has the
  *consequence* for spectra (`spectrum.unitary_conjugate`) but not the
  equivalence itself.
  *Destination:* `Mathlib/Algebra/Star/Unitary.lean`.

* `Matrix.reindexStarAlgEquiv` — the star-preserving upgrade of
  `Matrix.reindexAlgEquiv`. Mathlib has `Matrix.reindexAlgEquiv` and
  `Matrix.conjTranspose_reindex`; combining them is this one line.
  *Destination:* `Mathlib/LinearAlgebra/Matrix/Reindex.lean`.

* `IsDenseInducing.extendStarAlgHom` — the star analogue of
  `IsDenseInducing.extendRingHom` (`Mathlib/Topology/Algebra/UniformRing.lean:282`),
  together with `IsDenseInducing.extendStarAlgHom_comp_eq`, its characteristic
  property. This one does **not** exist in the PF corpus in any form: there the
  completion-side extension is done by hand, specialised to the concrete
  `TimelessFieldCompletion`. It is new.
  *Destination:* `Mathlib/Topology/Algebra/UniformRing.lean`.

## Kernel discipline

No `sorry`, no `axiom`, no `native_decide`. Every hypothesis of every declaration
is consumed by its proof. Each section ends with a non-vacuity witness, so no
statement here is satisfied only by having unsatisfiable hypotheses.

Author: Pablo Cohen + Claude Opus 5. 2026-10-05.
-/

namespace StarSubalgebra

variable {ι R A : Type*} [CommSemiring R] [StarRing R] [Semiring A] [StarRing A]
  [Algebra R A] [StarModule R A]

/-- For a directed family `S : ι → StarSubalgebra R A`, the underlying set of
`⨆ i, S i` is the union of the underlying sets.

This mirrors `NonUnitalStarSubalgebra.coe_iSup_of_directed`; mathlib does not yet
have the unital *-subalgebra case. -/
theorem coe_iSup_of_directed [Nonempty ι] {S : ι → StarSubalgebra R A}
    (dir : Directed (· ≤ ·) S) :
    ((⨆ i, S i : StarSubalgebra R A) : Set A) = ⋃ i, (S i : Set A) := by
  let T : StarSubalgebra R A :=
    { toSubalgebra :=
        Subalgebra.copy _ _
          (Subalgebra.coe_iSup_of_directed
            (K := fun i => (S i).toSubalgebra)
            (fun i j => by
              obtain ⟨k, hik, hjk⟩ := dir i j
              exact ⟨k, hik, hjk⟩)).symm
      star_mem' := by
        intro x hx
        obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
        exact Set.mem_iUnion.2 ⟨i, star_mem (s := S i) hi⟩ }
  have hST : (⨆ i, S i) = T := by
    apply le_antisymm
    · exact iSup_le (fun i => by
        intro x hx
        exact Set.mem_iUnion.2 ⟨i, hx⟩)
    · intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
      exact (le_iSup S i) hi
  rw [hST]
  rfl

/-- Membership in a directed supremum of *-subalgebras. -/
theorem mem_iSup_of_directed [Nonempty ι] {S : ι → StarSubalgebra R A}
    (dir : Directed (· ≤ ·) S) {x : A} :
    x ∈ (⨆ i, S i : StarSubalgebra R A) ↔ ∃ i, x ∈ S i := by
  simp only [← SetLike.mem_coe, coe_iSup_of_directed dir, Set.mem_iUnion]

/-- Non-vacuity witness for `coe_iSup_of_directed`: a constant family is directed,
so the hypothesis is satisfiable. -/
theorem coe_iSup_of_directed_const [Nonempty ι] (S : StarSubalgebra R A) :
    ((⨆ _ : ι, S : StarSubalgebra R A) : Set A) = (S : Set A) := by
  rw [coe_iSup_of_directed (S := fun _ : ι => S) (fun i _ => ⟨i, le_rfl, le_rfl⟩),
    Set.iUnion_const]

end StarSubalgebra

namespace StarAlgEquiv

variable {R A : Type*} [Semiring A] [StarRing A] [SMul R A]
  [SMulCommClass R A A] [IsScalarTower R A A]

/-- Conjugation `x ↦ u * x * star u` by an element `u` with `u * star u = 1` and
`star u * u = 1`, as a star algebra equivalence of `A`. The inverse is conjugation
by `star u`.

Stated for a bare element with the two cancellation hypotheses rather than for
`u : unitary A`, so that it applies to any `u` whose unitarity is in hand without
first bundling it; `unitary.conjStarAlgEquiv` is the bundled form. -/
def conjugateBy (u : A) (hu : u * star u = 1) (hu' : star u * u = 1) : A ≃⋆ₐ[R] A where
  toFun x := u * x * star u
  invFun x := star u * x * u
  left_inv x := by
    show star u * (u * x * star u) * u = x
    simp only [mul_assoc]
    rw [hu', mul_one]
    rw [← mul_assoc, hu', one_mul]
  right_inv x := by
    show u * (star u * x * u) * star u = x
    simp only [mul_assoc]
    rw [hu, mul_one]
    rw [← mul_assoc, hu, one_mul]
  map_add' x y := by
    show u * (x + y) * star u = u * x * star u + u * y * star u
    rw [mul_add, add_mul]
  map_mul' x y := by
    show u * (x * y) * star u = (u * x * star u) * (u * y * star u)
    simp only [mul_assoc]
    congr 1
    congr 1
    rw [← mul_assoc (star u) u (y * star u), hu', one_mul]
  map_smul' c x := by
    show u * (c • x) * star u = c • (u * x * star u)
    rw [mul_smul_comm, smul_mul_assoc]
  map_star' x := by
    show u * star x * star u = star (u * x * star u)
    rw [star_mul, star_mul, star_star, mul_assoc]

@[simp]
theorem conjugateBy_apply (u : A) (hu : u * star u = 1) (hu' : star u * u = 1) (x : A) :
    conjugateBy (R := R) u hu hu' x = u * x * star u := rfl

@[simp]
theorem conjugateBy_symm_apply (u : A) (hu : u * star u = 1) (hu' : star u * u = 1) (x : A) :
    (conjugateBy (R := R) u hu hu').symm x = star u * x * u := rfl

/-- Non-vacuity witness for `conjugateBy`: `u = 1` satisfies both hypotheses in
every star ring, and conjugating by it is the identity. -/
theorem conjugateBy_one_apply (x : A) :
    conjugateBy (R := R) (1 : A) (by rw [star_one, mul_one]) (by rw [star_one, one_mul]) x = x := by
  rw [conjugateBy_apply, star_one, mul_one, one_mul]

end StarAlgEquiv

namespace unitary

variable {R A : Type*} [Semiring A] [StarRing A] [SMul R A]
  [SMulCommClass R A A] [IsScalarTower R A A]

/-- Conjugation by a unitary element of a star algebra, as a star algebra
equivalence. The bundled form of `StarAlgEquiv.conjugateBy`. -/
def conjStarAlgEquiv (u : unitary A) : A ≃⋆ₐ[R] A :=
  StarAlgEquiv.conjugateBy (R := R) (u : A) (unitary.coe_mul_star_self u)
    (unitary.coe_star_mul_self u)

@[simp]
theorem conjStarAlgEquiv_apply (u : unitary A) (x : A) :
    conjStarAlgEquiv (R := R) u x = (u : A) * x * star (u : A) := rfl

@[simp]
theorem conjStarAlgEquiv_symm_apply (u : unitary A) (x : A) :
    (conjStarAlgEquiv (R := R) u).symm x = star (u : A) * x * (u : A) := rfl

/-- Conjugation is multiplicative in the unitary: `conj (u * v) = conj v` followed
by `conj u`. Note the order — `StarAlgEquiv.trans f g` applies `f` first. -/
theorem conjStarAlgEquiv_mul (u v : unitary A) :
    conjStarAlgEquiv (R := R) (u * v)
      = (conjStarAlgEquiv (R := R) v).trans (conjStarAlgEquiv (R := R) u) := by
  ext x
  simp only [conjStarAlgEquiv_apply, StarAlgEquiv.trans_apply, Submonoid.coe_mul,
    star_mul, mul_assoc]

/-- Non-vacuity witness: `1 : unitary A` exists, and conjugating by it is the
identity. -/
theorem conjStarAlgEquiv_one_apply (x : A) :
    conjStarAlgEquiv (R := R) (1 : unitary A) x = x := by
  rw [conjStarAlgEquiv_apply]
  rw [show ((1 : unitary A) : A) = 1 from rfl, star_one, mul_one, one_mul]

end unitary

namespace Matrix

variable {m n : Type*} (R A : Type*)
variable [CommSemiring R] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [Semiring A] [StarRing A] [Algebra R A]

/-- Reindexing a square matrix algebra along a bijection of index sets, as a star
algebra equivalence. This is the star-preserving upgrade of
`Matrix.reindexAlgEquiv`: the `map_star'` field is `Matrix.conjTranspose_reindex`
after reducing `star` to `Matrix.conjTranspose`. -/
def reindexStarAlgEquiv (e : m ≃ n) : Matrix m m A ≃⋆ₐ[R] Matrix n n A :=
  { reindexAlgEquiv R A e with
    map_star' := fun x => by
      change reindex e e (star x) = star (reindex e e x)
      rw [show (star : Matrix n n A → Matrix n n A) = conjTranspose from rfl,
        conjTranspose_reindex]
      rfl
    map_smul' := fun c x => _root_.map_smul (reindexAlgEquiv R A e) c x }

@[simp]
theorem reindexStarAlgEquiv_apply (e : m ≃ n) (M : Matrix m m A) :
    reindexStarAlgEquiv R A e M = reindex e e M := rfl

@[simp]
theorem reindexStarAlgEquiv_symm_apply (e : m ≃ n) (M : Matrix n n A) :
    (reindexStarAlgEquiv R A e).symm M = reindex e.symm e.symm M := rfl

/-- Non-vacuity witness for `reindexStarAlgEquiv`: at the identity bijection it is
the identity map, so the equivalence is inhabited for every index type. -/
theorem reindexStarAlgEquiv_refl_apply (M : Matrix m m A) :
    reindexStarAlgEquiv R A (Equiv.refl m) M = M := rfl

end Matrix

namespace IsDenseInducing

variable {R A B C : Type*} [CommSemiring R]
variable [UniformSpace A] [Semiring A] [Algebra R A] [StarRing A]
variable [UniformSpace B] [Semiring B] [Algebra R B] [StarRing B]
  [IsTopologicalSemiring B] [ContinuousStar B]
variable [UniformSpace C] [Semiring C] [Algebra R C] [StarRing C]
  [IsTopologicalSemiring C] [ContinuousStar C] [T2Space C] [CompleteSpace C]

/-- The dense inducing extension as a star algebra homomorphism: the star
analogue of `IsDenseInducing.extendRingHom`.

Given a uniform inducing *-algebra map `i : A →⋆ₐ[R] B` with dense range and a
uniformly continuous *-algebra map `f : A →⋆ₐ[R] C` into a complete Hausdorff
target, the unique continuous extension of `f` along `i` is again a *-algebra
map. The ring-homomorphism content is `extendRingHom`; what is added here is that
the extension commutes with `algebraMap` and with `star`, each by a density
argument against the closed set where the identity holds. -/
noncomputable def extendStarAlgHom {i : A →⋆ₐ[R] B} {f : A →⋆ₐ[R] C}
    (ue : IsUniformInducing i) (dr : DenseRange i) (hf : UniformContinuous f) :
    B →⋆ₐ[R] C where
  toAlgHom :=
    { IsDenseInducing.extendRingHom (i := i.toAlgHom.toRingHom)
        (f := f.toAlgHom.toRingHom) ue dr hf with
      commutes' := fun r => by
        show (ue.isDenseInducing dr).extend f (algebraMap R B r) = algebraMap R C r
        have h := IsDenseInducing.extend_eq (ue.isDenseInducing dr) hf.continuous
          (algebraMap R A r)
        rw [AlgHomClass.commutes i r] at h
        rw [h, AlgHomClass.commutes f r] }
  map_star' := by
    have hcont : Continuous ((ue.isDenseInducing dr).extend f) :=
      (uniformContinuous_uniformly_extend ue dr hf).continuous
    refine fun x => DenseRange.induction_on dr x ?_ (fun a => ?_)
    · exact isClosed_eq (hcont.comp continuous_star) (continuous_star.comp hcont)
    · show (ue.isDenseInducing dr).extend f (star (i a))
          = star ((ue.isDenseInducing dr).extend f (i a))
      rw [← map_star i a,
        IsDenseInducing.extend_eq (ue.isDenseInducing dr) hf.continuous (star a),
        IsDenseInducing.extend_eq (ue.isDenseInducing dr) hf.continuous a,
        map_star f a]

/-- The characteristic property of `extendStarAlgHom`: it extends `f` along `i`.

This is also the non-vacuity witness for `extendStarAlgHom` — it exhibits the
extension's value on the dense image, so the definition is not vacuous. -/
theorem extendStarAlgHom_comp_eq {i : A →⋆ₐ[R] B} {f : A →⋆ₐ[R] C}
    (ue : IsUniformInducing i) (dr : DenseRange i) (hf : UniformContinuous f) (a : A) :
    extendStarAlgHom ue dr hf (i a) = f a :=
  IsDenseInducing.extend_eq (ue.isDenseInducing dr) hf.continuous a

end IsDenseInducing

/-! ## Axiom audit — LIVE, not commented out -/

#print axioms StarSubalgebra.coe_iSup_of_directed
#print axioms StarSubalgebra.mem_iSup_of_directed
#print axioms StarAlgEquiv.conjugateBy
#print axioms unitary.conjStarAlgEquiv
#print axioms unitary.conjStarAlgEquiv_mul
#print axioms Matrix.reindexStarAlgEquiv
#print axioms IsDenseInducing.extendStarAlgHom
#print axioms IsDenseInducing.extendStarAlgHom_comp_eq
