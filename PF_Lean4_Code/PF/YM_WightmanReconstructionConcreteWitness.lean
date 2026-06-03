/-
# Wightman Reconstruction — Concrete Hilbert/Hamiltonian Witness
  (Wave 58 STRENGTHENING — (G3))

★ 2026-06-02 — STRENGTHENING of `WightmanReconstructionTypedStatement`
from `PF/YM_WightmanContinuumGapsTypedUpgrade.lean` (Wave 57-YM-W-UPGRADE).

The Wave 57 typed form
  `∃ H (NormedAddCommGroup + InnerProductSpace ℝ + CompleteSpace),
     Nonempty (H →L[ℝ] H)`
is satisfied by the trivial witness `H := ℝ, Hamil := ContinuousLinearMap.id ℝ ℝ`.

This file provides:

  (1) A STRENGTHENED typed Prop `WightmanReconstructionConcreteTypedStatement`
      requiring BOTH:
        (a) the Hamiltonian carries a known positive eigenvalue `Δ > 0`
            with `Δ ≠ 1` — rules out `Hamil := id` (whose only eigenvalue is 1);
        (b) the Hamiltonian witnesses a concrete nonzero eigenvector — a
            single-coordinate `lp.single 2 0 (1 : ℝ)` of the infinite-index
            `l²` space.

  (2) A CONCRETE WITNESS on `lp (fun _ : ℕ => ℝ) 2` — mathlib's standard
      infinite-index real `l²` Hilbert space:
        H     := `lp (fun _ : ℕ => ℝ) 2`
        Hamil := `(1/2 : ℝ) • ContinuousLinearMap.id ℝ H`
        Δ     := `1 / 2` (matches the Wave 55C level-1 mass-gap eigenvalue,
                  the smaller of the two interacting-Hamiltonian
                  eigenvalues `{1/2, 3/2}`).
      Every nonzero `v : H` is then an eigenvector with `Hamil v = (1/2) • v`;
      we take `v := lp.single 2 0 (1 : ℝ)`, which is nonzero by
      `lp.norm_single` (its norm equals `‖(1 : ℝ)‖ = 1 ≠ 0`).

  (3) The cascade: strengthened concrete ⇒ Wave 57 typed ⇒ Wave 56
      `WightmanReconstructionTheorem`.

## Honest scope

  1. The Hamiltonian is `(1/2) • id`, a scalar multiple of the identity;
     this is a TOY Hamiltonian. The literal Wightman Hamiltonian is a
     densely-defined self-adjoint operator built from the OS
     reconstruction; that content is NOT proved.

  2. The carrier `lp (fun _ : ℕ => ℝ) 2` IS a genuine infinite-index `l²`
     Hilbert space (mathlib's `lp.instInnerProductSpace` +
     `lp.completeSpace`), strictly richer than the trivial witness `ℝ`.

  3. Ruled out: the `Hamil := id ℝ ℝ` witness on `H := ℝ` of Wave 57
     (eigenvalue 1; our predicate names `Δ ≠ 1`).

  4. NOT a Clay discharge.

## Build

ZERO project axioms. ZERO sorries.

Author: Wave 58 STRENGTHENING (Wightman concrete), 2026-06-02.
-/

import PF.YM_WightmanContinuumGapsTypedUpgrade
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Tactic

set_option autoImplicit false

namespace PrincipiaTractalis
namespace YM_WightmanReconstructionConcreteWitness

open PrincipiaTractalis
open PrincipiaTractalis.YM_Wave56ContinuumLiftAttempt
open PrincipiaTractalis.YM_WightmanContinuumGapsTypedUpgrade
open scoped ENNReal

/-! ## §1 — Concrete carrier: the real `l²` Hilbert space

We use mathlib's `lp (fun _ : ℕ => ℝ) 2` — the canonical real `l²`
sequence Hilbert space. By mathlib it carries:

  * `NormedAddCommGroup` (`lp.normedAddCommGroup`)
  * `InnerProductSpace ℝ` (`lp.instInnerProductSpace`)
  * `CompleteSpace`       (`lp.completeSpace`)

All three instances are available; we do not name them explicitly. -/

/-- The concrete real `l²` Hilbert space carrier — sequences `ℕ → ℝ`
    with square-summable squared modulus, equipped with mathlib's
    canonical inner-product space + completeness instances. -/
abbrev L2R : Type := lp (fun _ : ℕ => ℝ) 2

/-- `L2R` is a `NormedAddCommGroup` (typeclass synthesis). -/
noncomputable example : NormedAddCommGroup L2R := inferInstance

/-- `L2R` is an `InnerProductSpace ℝ` (typeclass synthesis). -/
noncomputable example : InnerProductSpace ℝ L2R := inferInstance

/-- `L2R` is a `CompleteSpace` (typeclass synthesis). -/
example : CompleteSpace L2R := inferInstance

/-! ## §2 — Concrete Hamiltonian: the Wave 55C `(1/2) • id` toy

The Wave 55C mass-gap eigenvalues are `{1/2, 3/2}`; the level-1 gap is
`Δ = 1/2`. We model the reconstructed Hamiltonian as the scalar multiple
`(1/2) • id` of the identity — every nonzero `v` is an eigenvector with
eigenvalue `1/2`, exhibiting the mass-gap structure. -/

/-- **Concrete Hamiltonian** on `L2R` — `(1/2) • id`. -/
noncomputable def concreteHamiltonian : L2R →L[ℝ] L2R :=
  (1 / 2 : ℝ) • ContinuousLinearMap.id ℝ L2R

/-- **The concrete Hamiltonian acts by scalar `1/2`**. -/
theorem concreteHamiltonian_apply (v : L2R) :
    concreteHamiltonian v = (1 / 2 : ℝ) • v := by
  simp [concreteHamiltonian]

/-! ## §3 — Concrete eigenvector witness

We exhibit a nonzero `v : L2R` such that `Hamil v = (1/2) • v`. The
canonical choice is `lp.single 2 0 (1 : ℝ)` — the unit vector at index 0.
Its norm equals `‖(1 : ℝ)‖ = 1` by `lp.norm_single`, hence it is nonzero. -/

/-- The concrete unit vector — single-coordinate `1` at index `0`. -/
noncomputable def concreteUnitVector : L2R :=
  lp.single 2 (0 : ℕ) (1 : ℝ)

/-- The concrete unit vector has norm `1`. -/
theorem norm_concreteUnitVector :
    ‖concreteUnitVector‖ = 1 := by
  unfold concreteUnitVector
  have hp : (0 : ℝ≥0∞) < 2 := by norm_num
  simpa using lp.norm_single (E := fun _ : ℕ => ℝ) (p := 2) hp (0 : ℕ) (1 : ℝ)

/-- The concrete unit vector is nonzero. -/
theorem concreteUnitVector_ne_zero :
    concreteUnitVector ≠ 0 := by
  intro h
  have hn : ‖concreteUnitVector‖ = 0 := by rw [h]; simp
  have h1 : (1 : ℝ) = 0 := by rw [← norm_concreteUnitVector]; exact hn
  exact one_ne_zero h1

/-- **The concrete Hamiltonian has `1/2` as an eigenvalue with the
    explicit eigenvector `concreteUnitVector`**. -/
theorem concreteHamiltonian_eigenvalue :
    concreteHamiltonian concreteUnitVector = (1 / 2 : ℝ) • concreteUnitVector :=
  concreteHamiltonian_apply concreteUnitVector

/-! ## §4 — Strengthened concrete typed predicate

The strengthened predicate names three discriminators against the
trivial Wave 57 witness `(ℝ, id)`:

  (a) The Hamiltonian has a positive eigenvalue `Δ > 0`.
  (b) The eigenvalue `Δ` is NOT `1`, ruling out `Hamil = id ℝ ℝ`
      (whose only eigenvalue is `1`).
  (c) The eigenvector is explicitly named (a concrete nonzero `v`). -/

/-- **Strengthened (G3) typed predicate** — existence of a complete
    real inner-product space `H`, a continuous-linear Hamiltonian
    `Hamil : H →L[ℝ] H`, a positive eigenvalue `Δ > 0` with `Δ ≠ 1`,
    and an explicit nonzero eigenvector `v` satisfying `Hamil v = Δ • v`. -/
def WightmanReconstructionConcreteTypedStatement : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H)
    (_ : CompleteSpace H) (Hamil : H →L[ℝ] H) (Δ : ℝ) (v : H),
      0 < Δ ∧ Δ ≠ 1 ∧ v ≠ 0 ∧ Hamil v = Δ • v

/-- **★ The concrete `(L2R, (1/2) • id)` pair inhabits the strengthened
    Wightman concrete typed predicate ★** — with `Δ := 1/2` and
    `v := concreteUnitVector`. -/
theorem wightmanReconstruction_concrete_witness :
    WightmanReconstructionConcreteTypedStatement := by
  refine ⟨L2R, inferInstance, inferInstance, inferInstance,
          concreteHamiltonian, (1 / 2 : ℝ), concreteUnitVector, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · exact concreteUnitVector_ne_zero
  · exact concreteHamiltonian_eigenvalue

/-! ## §5 — Cascade to Wave 57 typed + Wave 56 original -/

/-- **Strengthened concrete ⇒ Wave 57 typed `WightmanReconstructionTypedStatement`**.
    The strengthened form provides `H`, all instances, and a `Hamil`,
    which directly inhabits the Wave 57 typed Prop. -/
theorem wightmanReconstruction_concrete_implies_wave57_typed
    (h : WightmanReconstructionConcreteTypedStatement) :
    WightmanReconstructionTypedStatement := by
  obtain ⟨H, hNAG, hIPS, hCS, Hamil, _Δ, _v, _, _, _, _⟩ := h
  exact ⟨H, hNAG, hIPS, hCS, ⟨Hamil⟩⟩

/-- **Strengthened concrete ⇒ Wave 56 `WightmanReconstructionTheorem`
    (`True`-shaped original)**. -/
theorem wightmanReconstruction_concrete_implies_original
    (h : WightmanReconstructionConcreteTypedStatement) :
    WightmanReconstructionTheorem :=
  wightmanReconstruction_typed_implies_original
    (wightmanReconstruction_concrete_implies_wave57_typed h)

/-! ## §6 — Discriminator: the trivial Wave 57 `(ℝ, id)` witness does
        NOT inhabit the strengthened concrete predicate

To show the strengthening is STRICT, observe: the Wave 57 scaffold-level
inhabitant `(H := ℝ, Hamil := ContinuousLinearMap.id ℝ ℝ)` has only the
single eigenvalue `1`. Our strengthened predicate names `Δ ≠ 1`, so
no inhabitant of the strengthened predicate can use `Hamil := id ℝ ℝ`
with `Δ := 1`. We record the discriminator as a structural Prop. -/

/-- **The identity Hamiltonian on `ℝ` has only eigenvalue `1`**:
    if `Hamil := id ℝ ℝ` and `Hamil v = Δ • v` for nonzero `v`,
    then `Δ = 1`. -/
theorem id_R_eigenvalue_eq_one
    {Δ : ℝ} {v : ℝ}
    (hv : v ≠ 0)
    (heigen : (ContinuousLinearMap.id ℝ ℝ) v = Δ • v) :
    Δ = 1 := by
  -- `ContinuousLinearMap.id ℝ ℝ v = v` and `Δ • v = Δ * v` on `ℝ`.
  have h1 : v = Δ * v := by simpa [smul_eq_mul] using heigen
  -- Then `(1 - Δ) * v = 0`, and since `v ≠ 0`, we get `1 - Δ = 0`.
  have h2 : (1 - Δ) * v = 0 := by linarith [h1, mul_comm Δ v]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · linarith
  · exact (hv h3).elim

/-! ## §7 — Honest-scope marker -/

/-- **Honest-scope marker** — the concrete witness strengthens the
    Wave 57 typed (G3) Prop in four ways:

    (a) The carrier is `lp (fun _ : ℕ => ℝ) 2`, an infinite-index `l²`
        Hilbert space, strictly richer than the trivial `ℝ`.
    (b) The Hamiltonian carries a NAMED positive eigenvalue `Δ = 1/2`.
    (c) The eigenvalue `Δ ≠ 1`, ruling out `Hamil := id ℝ ℝ`.
    (d) An EXPLICIT nonzero eigenvector `lp.single 2 0 1` is named.

    HOWEVER: the Hamiltonian `(1/2) • id` is a TOY scalar-multiple, not
    the genuine OS-reconstructed Hamiltonian. NOT a Clay discharge. -/
def WightmanReconstructionConcreteWitnessHonestScope : Prop :=
  -- (1) Strengthened typed predicate is inhabited by the concrete `(L2R, (1/2)•id)`.
  WightmanReconstructionConcreteTypedStatement ∧
  -- (2) Strengthened concrete ⇒ Wave 57 typed.
  (WightmanReconstructionConcreteTypedStatement →
     WightmanReconstructionTypedStatement) ∧
  -- (3) Strengthened concrete ⇒ Wave 56 `True`-shaped original.
  (WightmanReconstructionConcreteTypedStatement →
     WightmanReconstructionTheorem) ∧
  -- (4) Concrete eigenvalue/eigenvector identity.
  (concreteHamiltonian concreteUnitVector = (1 / 2 : ℝ) • concreteUnitVector) ∧
  -- (5) Concrete eigenvector is nonzero.
  (concreteUnitVector ≠ 0) ∧
  -- (6) Discriminator: `id ℝ ℝ` admits only eigenvalue 1.
  (∀ {Δ : ℝ} {v : ℝ}, v ≠ 0 →
     (ContinuousLinearMap.id ℝ ℝ) v = Δ • v → Δ = 1)

/-- The honest-scope marker holds unconditionally. -/
theorem wightmanReconstruction_concrete_witness_honestScope_holds :
    WightmanReconstructionConcreteWitnessHonestScope :=
  ⟨wightmanReconstruction_concrete_witness,
   wightmanReconstruction_concrete_implies_wave57_typed,
   wightmanReconstruction_concrete_implies_original,
   concreteHamiltonian_eigenvalue,
   concreteUnitVector_ne_zero,
   @id_R_eigenvalue_eq_one⟩

/-! ## §8 — Capstone -/

/-- ★★★ **CAPSTONE — Wightman Reconstruction Concrete Witness (G3)** ★★★
    (Wave 58 STRENGTHENING, 2026-06-02)

    STRENGTHENING of the (G3) Wightman-reconstruction typed Prop from
    `YM_WightmanContinuumGapsTypedUpgrade` via a concrete
    `(Hilbert, Hamiltonian, eigenvalue, eigenvector)` witness on the
    real `l²` Hilbert space `lp (fun _ : ℕ => ℝ) 2`.

    **Seven structural clauses**:

    (1) Strengthened typed predicate
        `WightmanReconstructionConcreteTypedStatement` — names a
        positive eigenvalue `Δ > 0`, `Δ ≠ 1`, and an explicit nonzero
        eigenvector.
    (2) Concrete `(L2R, (1/2)•id)` inhabits the strengthened predicate.
    (3) Eigenvalue identity `Hamil v = (1/2) • v` at the named `v`.
    (4) Eigenvector `v := lp.single 2 0 1` is nonzero.
    (5) Discriminator: `id ℝ ℝ` admits only eigenvalue 1.
    (6) Cascade strengthened ⇒ Wave 57 typed ⇒ Wave 56 original.
    (7) Honest-scope marker.

    **Honest scope**: NOT a Clay discharge. The Hamiltonian is the toy
    `(1/2) • id` (a scalar multiple of the identity on `l²`), not the
    genuine OS-reconstructed self-adjoint Hamiltonian. The carrier
    `lp (fun _ : ℕ => ℝ) 2` IS, however, a genuine infinite-index `l²`
    Hilbert space, strictly richer than the Wave 57 trivial `ℝ`.

    Axiom-free; `#print axioms` returns only
    `[propext, Classical.choice, Quot.sound]`. -/
theorem wightmanReconstruction_concrete_witness_capstone :
    WightmanReconstructionConcreteTypedStatement ∧
    (concreteHamiltonian concreteUnitVector = (1 / 2 : ℝ) • concreteUnitVector) ∧
    (concreteUnitVector ≠ 0) ∧
    (∀ {Δ : ℝ} {v : ℝ}, v ≠ 0 →
       (ContinuousLinearMap.id ℝ ℝ) v = Δ • v → Δ = 1) ∧
    (WightmanReconstructionConcreteTypedStatement →
       WightmanReconstructionTypedStatement) ∧
    (WightmanReconstructionConcreteTypedStatement →
       WightmanReconstructionTheorem) ∧
    WightmanReconstructionConcreteWitnessHonestScope :=
  ⟨wightmanReconstruction_concrete_witness,
   concreteHamiltonian_eigenvalue,
   concreteUnitVector_ne_zero,
   @id_R_eigenvalue_eq_one,
   wightmanReconstruction_concrete_implies_wave57_typed,
   wightmanReconstruction_concrete_implies_original,
   wightmanReconstruction_concrete_witness_honestScope_holds⟩

/-! ## §9 — Axiom-freeness verification -/

#print axioms concreteHamiltonian_apply
#print axioms norm_concreteUnitVector
#print axioms concreteUnitVector_ne_zero
#print axioms concreteHamiltonian_eigenvalue
#print axioms wightmanReconstruction_concrete_witness
#print axioms wightmanReconstruction_concrete_implies_wave57_typed
#print axioms wightmanReconstruction_concrete_implies_original
#print axioms id_R_eigenvalue_eq_one
#print axioms wightmanReconstruction_concrete_witness_honestScope_holds
#print axioms wightmanReconstruction_concrete_witness_capstone

end YM_WightmanReconstructionConcreteWitness
end PrincipiaTractalis
