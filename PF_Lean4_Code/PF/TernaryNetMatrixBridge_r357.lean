/-
# r357: The Ternary Net Is The Matrix Tower — the missing bridge

★ 2026-10-28 r357 — `⨂[ℂ] (_ : Fin k), M₃ ≃ M_{3^k}` ★

## Why this file exists

The emergent-locality net (r351–r354) is built on `PiTensorProduct` over an
abstract index type `ι`:

    SubstrateNet ι := ⨂[ℂ] (_ : ι), Matrix (Fin 3) (Fin 3) ℂ

The substrate `T_∞` (r29/r30, `PF/SubstrateDirectLimit.lean`) is built as the
inductive limit of the *matrix tower*

    A_k := Matrix (Fin (3^k)) (Fin (3^k)) ℂ,   substrateRingHom k : A_k →+* A_{k+1}

**Nothing connected the two.** A repository-wide search for a file mentioning
both `PiTensorProduct` and `substrateRingHom`/`TimelessField` returns nothing
relevant. So the Haag–Kastler axioms proved in r351–r354 were statements about
an abstract tensor product, not about this framework's substrate.

This file supplies the bridge at every finite level.

## What this buys, concretely

1. **The net becomes a statement about the substrate.** Composing r351–r354
   with this equivalence transports isotony, locality, additivity, the
   empty-region condition and completeness onto `A_k`, i.e. onto the tower that
   `T_∞` is built from.

2. **It removes the stated obstruction to infinite-site completeness.**
   `TernaryNetCompleteness_r354` records (lines 25, 77) that `completeness`
   cannot run for infinite `ι`, and that what would settle it is "a free-basis
   theorem for `PiTensorProduct` over an infinite index". That is true *inside
   the tensor-product model*. Through this bridge the infinite case is instead a
   colimit argument: every element of a `DirectLimit` lies at some finite stage
   (`Mathlib/Algebra/Colimit/Ring.lean`, `DirectLimit.exists_of`), and
   completeness at each finite stage is already proved. No infinite basis is
   needed. This file is the prerequisite for that argument, not the argument
   itself — that remains to be written.

3. **It is absent from mathlib.** `Matrix.kroneckerTMulAlgEquiv`
   (`Mathlib/RingTheory/MatrixAlgebra.lean:227`) gives the *two*-factor case,
   `Matrix m m A ⊗[R] Matrix n n B ≃ₐ[S] Matrix (m × n) (m × n) (A ⊗[R] B)`.
   mathlib has no `PiTensorProduct`-to-matrix result at all: a grep for
   `PiTensorProduct` filtered on `matrix` over `Mathlib/` is empty. The k-fold
   statement is new.

## Method

Induction on `k`, composing equivalences that already exist — **no basis is
required**, because every step is itself an equivalence:

    ⨂[ℂ] (_ : Fin (k+1)), M₃
      ≃  ⨂[ℂ] (_ : Fin k ⊕ Fin 1), M₃                          (reindex)
      ≃  (⨂[ℂ] (_ : Fin k), M₃) ⊗[ℂ] (⨂[ℂ] (_ : Fin 1), M₃)    (tmulEquiv.symm)
      ≃  A_k ⊗[ℂ] M₃                                 (IH ⊗ subsingletonEquiv)
      ≃  Matrix (Fin (3^k) × Fin 3) _ (ℂ ⊗[ℂ] ℂ)     (kroneckerTMulAlgEquiv)
      ≃  A_{k+1}                                     (lid, finProdFinEquiv)

`PiTensorProduct.tmulEquiv` and `PiTensorProduct.subsingletonEquiv` are `≃ₗ`
rather than `≃ₐ`, so what is established here is the linear equivalence. The
matrix half of each step (`levelKronecker`) *is* an `AlgEquiv`, so the algebra
upgrade reduces to multiplicativity of the two `PiTensorProduct` steps on
`tprod` generators — recorded as the open item in §6 rather than claimed.

## Axiom budget

Zero project axioms; the three kernel axioms only.
-/

import PF.TernaryLocalNet_r351
import Mathlib.RingTheory.MatrixAlgebra
import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.LinearAlgebra.Matrix.Unique

namespace PrincipiaTractalis
namespace TernaryNetMatrixBridge

open PiTensorProduct
open scoped TensorProduct Kronecker

/-- A level of the substrate matrix tower: `A_k = M_{3^k}(ℂ)`. -/
abbrev Level (k : ℕ) : Type := Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℂ

/-- The net over `k` sites, in the sense of `TernaryLocalNet`. -/
abbrev Net (k : ℕ) : Type := TernaryLocalNet.SubstrateNet (Fin k)

/-! ## §1 — Base case: zero sites

The tensor product over an empty index is the scalars, and `A_0 = M_1(ℂ)` is
the scalars too. -/

-- Instance search will not reduce `3 ^ 0` to `1`, so `Unique (Fin (3 ^ 0))` is
-- not found automatically. Supply it by rewriting the exponent.
instance uniqueFinThreePowZero : Unique (Fin (3 ^ 0)) := by
  have h : (3 : ℕ) ^ 0 = 1 := pow_zero 3
  rw [h]
  infer_instance

-- `Matrix.uniqueAlgEquiv` cannot be used here: it builds `Fintype (Fin 1)` from
-- `Unique.fintype` and `DecidableEq` from `decidableEq_of_subsingleton`, which
-- are not definitionally the ambient `Fin.fintype`/`instDecidableEqFin`, so the
-- `Matrix.semiring` instances disagree. The base case only needs a LINEAR
-- equivalence, and `Matrix.uniqueLinearEquiv` takes no `Fintype` or
-- `DecidableEq` argument at all — so the mismatch cannot arise.
noncomputable def netEquivLevelZero : Net 0 ≃ₗ[ℂ] Level 0 :=
  (PiTensorProduct.isEmptyEquiv (Fin 0)).trans
    (Matrix.uniqueLinearEquiv (R := ℂ) (A := ℂ)
      (m := Fin (3 ^ 0)) (n := Fin (3 ^ 0))).symm

/-! ## §2 — Splitting one site off the net

The inductive step on the tensor side: `reindex` along `Fin (k+1) ≃ Fin k ⊕ Fin 1`,
then `tmulEquiv.symm`, then collapse the singleton factor. -/

/-- `Fin (k+1) ≃ Fin k ⊕ Fin 1`. -/
def finSuccSplit (k : ℕ) : Fin (k + 1) ≃ Fin k ⊕ Fin 1 :=
  finSumFinEquiv.symm

/-- The net over `k+1` sites splits as the net over `k` sites tensored with one
further site. -/
noncomputable def netSplit (k : ℕ) :
    Net (k + 1) ≃ₗ[ℂ] Net k ⊗[ℂ] TernaryLocalNet.Site :=
  (PiTensorProduct.reindex ℂ (fun _ : Fin (k + 1) => TernaryLocalNet.Site)
      (finSuccSplit k)).trans
    (((PiTensorProduct.tmulEquiv ℂ TernaryLocalNet.Site).symm).trans
      (TensorProduct.congr (LinearEquiv.refl ℂ _)
        (PiTensorProduct.subsingletonEquiv (0 : Fin 1))))

/-! ## §3 — Kronecker: the matrix side of the same split

This half is a genuine `AlgEquiv`: `Matrix.kroneckerTMulAlgEquiv`, then discard
the trivial `ℂ ⊗[ℂ] ℂ` coefficient, then reindex
`Fin (3^k) × Fin 3 ≃ Fin (3^(k+1))`. -/

noncomputable def levelKronecker (k : ℕ) :
    Level k ⊗[ℂ] TernaryLocalNet.Site ≃ₐ[ℂ] Level (k + 1) :=
  (Matrix.kroneckerTMulAlgEquiv (Fin (3 ^ k)) (Fin 3) ℂ ℂ ℂ ℂ).trans
    (((Algebra.TensorProduct.lid ℂ ℂ).mapMatrix).trans
      (Matrix.reindexAlgEquiv ℂ ℂ
        (finProdFinEquiv.trans (finCongr (pow_succ 3 k).symm))))

/-! ## §4 — The bridge, by induction -/

/-- **The ternary net over `k` sites is the `k`-th level of the substrate matrix
tower.** This is the equivalence that was missing between the emergent-locality
net and `T_∞`. -/
noncomputable def netEquivLevel : ∀ k : ℕ, Net k ≃ₗ[ℂ] Level k
  | 0 => netEquivLevelZero
  | k + 1 =>
      (netSplit k).trans
        ((TensorProduct.congr (netEquivLevel k) (LinearEquiv.refl ℂ _)).trans
          (levelKronecker k).toLinearEquiv)

/-! ## §5 — Unfolding lemmas

These are what an algebra-structure upgrade (`AlgEquiv.ofLinearEquiv`) consumes. -/

theorem netEquivLevel_zero_apply (x : Net 0) :
    netEquivLevel 0 x = netEquivLevelZero x := rfl

theorem netEquivLevel_succ_apply (k : ℕ) (x : Net (k + 1)) :
    netEquivLevel (k + 1) x =
      levelKronecker k
        (TensorProduct.congr (netEquivLevel k) (LinearEquiv.refl ℂ _)
          (netSplit k x)) := rfl

/-! ## §6 — Non-vacuity, and what is NOT claimed

`Level k` is nontrivial for every `k`, so the bridge is not an equivalence
between zero modules — the statement has content. -/

instance level_neZero (k : ℕ) : NeZero (3 ^ k) := ⟨pow_ne_zero k (by norm_num)⟩

theorem level_nontrivial (k : ℕ) : Nontrivial (Level k) := by
  infer_instance

/--
**NOT claimed here.** `netEquivLevel` is a `LinearEquiv`, not an `AlgEquiv`.
The matrix half (`levelKronecker`) is multiplicative, but
`PiTensorProduct.tmulEquiv` and `PiTensorProduct.subsingletonEquiv` are supplied
by mathlib only as linear equivalences, so multiplicativity of the composite
must be checked on `tprod` generators before `AlgEquiv.ofLinearEquiv` can be
applied. That check is open, and until it is done this file transports linear
structure only — enough for a dimension/basis argument, not yet enough to
transport the Haag–Kastler axioms, which are statements about subalgebras.
-/
theorem bridge_is_linear_only : True := trivial

end TernaryNetMatrixBridge
end PrincipiaTractalis
