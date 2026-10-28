/-
# r358: The bridge is an ALGEBRA isomorphism

★ 2026-10-28 r358 — upgrades r357 from `≃ₗ[ℂ]` to `≃ₐ[ℂ]` ★

## What r357 left open, and why it mattered

r357 built `netEquivLevel k : (⨂[ℂ] (_ : Fin k), M₃) ≃ₗ[ℂ] M_{3^k}(ℂ)` and said
explicitly that it was a **linear** equivalence only: `PiTensorProduct.tmulEquiv`
and `PiTensorProduct.subsingletonEquiv` are supplied by mathlib as `≃ₗ`, so
multiplicativity of the composite was unproved.

That mattered because isotony, locality, additivity and completeness (r352–r354)
are statements about **subalgebras** of the net. A linear equivalence cannot
transport them. This file closes that gap.

## The method, and why it avoids a spanning argument

`PiTensorProduct.liftAlgHom` (`Mathlib/RingTheory/PiTensorProduct.lean:204`)
takes a `MultilinearMap`, a proof it sends `1` to `1`, and a proof it is
multiplicative **on `Π i, A i`** — the pointwise product of site-families, not
on the tensor product — and returns an `AlgHom` out of the tensor product.
Feeding it `netEquivLevel k ∘ tprod` reduces the whole upgrade to
multiplicativity on `tprod` generators: an induction on `k` whose step is
"Kronecker of products = product of Kroneckers". No basis, no spanning argument,
no `induction_on` over arbitrary elements.

Bijectivity is then free: `AlgEquiv.ofBijective` consumes the `AlgHom` together
with the bijectivity r357 already established.

## One ordering trap, recorded because it is easy to walk into

In the successor step the rewrites must push `TensorProduct.congr` through the
pure tensor **before** splitting the product with `tmul_mul_tmul`. Done the
other way round, `congr` is left facing a product and cannot distribute over it
— `congr` is linear, which is precisely the property under proof. The order
below is: `congr_tmul` first, then split.

## Axiom budget

Zero project axioms; the three kernel axioms only.
-/

import PF.TernaryNetMatrixBridge_r357

namespace PrincipiaTractalis
namespace TernaryNetMatrixAlgBridge

open PiTensorProduct TernaryNetMatrixBridge
open scoped TensorProduct Kronecker

/-! ## §1 — `netSplit` on a generator

Everything downstream rests on this computation. The index bookkeeping is the
only subtle part: `finSuccSplit k = finSumFinEquiv.symm`, so `reindex`
reintroduces `finSumFinEquiv`, and `finSumFinEquiv (.inl i) = Fin.castAdd 1 i`
and `finSumFinEquiv (.inr 0) = Fin.last k` both hold by `rfl`. -/

theorem netSplit_tprod (k : ℕ) (f : Fin (k + 1) → TernaryLocalNet.Site) :
    netSplit k (tprod ℂ f) =
      (tprod ℂ fun i : Fin k => f (Fin.castAdd 1 i)) ⊗ₜ[ℂ] f (Fin.last k) := by
  simp only [netSplit, LinearEquiv.trans_apply, finSuccSplit,
    PiTensorProduct.reindex_tprod, Equiv.symm_symm,
    PiTensorProduct.tmulEquiv_symm_apply, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, PiTensorProduct.subsingletonEquiv_apply_tprod]
  rfl

/-! ## §2 — The unit -/

theorem netEquivLevel_one : ∀ k : ℕ, netEquivLevel k 1 = 1
  | 0 => by
      rw [show (1 : Net 0) = tprod ℂ (1 : Fin 0 → TernaryLocalNet.Site) from
        PiTensorProduct.one_def]
      simp only [netEquivLevel, netEquivLevelZero, LinearEquiv.trans_apply,
        PiTensorProduct.isEmptyEquiv_apply_tprod]
      ext i j
      have hij : i = j := Subsingleton.elim i j
      subst hij
      -- `uniqueLinearEquiv.symm` is `fun a => of fun _ _ => a`, reached through
      -- `uniqueAddEquiv` and `uniqueEquiv`; all three must be unfolded, after
      -- which the goal is `of (fun _ _ => 1) i i = 1`, which is definitional.
      simp only [Matrix.uniqueLinearEquiv, Matrix.uniqueAddEquiv, Matrix.uniqueEquiv,
        Matrix.one_apply_eq]
      rfl
  | k + 1 => by
      have h := netEquivLevel_one k
      rw [show (1 : Net (k + 1)) = tprod ℂ (1 : Fin (k + 1) → TernaryLocalNet.Site) from
        PiTensorProduct.one_def]
      rw [netEquivLevel_succ_apply, netSplit_tprod, TensorProduct.congr_tmul,
        LinearEquiv.refl_apply]
      simp only [Pi.one_apply]
      rw [show (tprod ℂ fun _ : Fin k => (1 : TernaryLocalNet.Site)) = 1 from
        (PiTensorProduct.one_def).symm, h]
      exact map_one _

/-! ## §3 — Multiplicativity on generators, by induction on the number of sites

The inductive hypothesis arrives in exactly the shape the successor step needs:
after `netSplit_tprod` and `congr_tmul` the left tensor slot is
`netEquivLevel k` applied to a `tprod`, so the IH applies verbatim. -/

theorem netEquivLevel_tprod_mul :
    ∀ (k : ℕ) (x y : Fin k → TernaryLocalNet.Site),
      netEquivLevel k (tprod ℂ x * tprod ℂ y) =
        netEquivLevel k (tprod ℂ x) * netEquivLevel k (tprod ℂ y)
  | 0, x, y => by
      have hx : x = 1 := Subsingleton.elim _ _
      have hy : y = 1 := Subsingleton.elim _ _
      subst hx; subst hy
      rw [show (tprod ℂ (1 : Fin 0 → TernaryLocalNet.Site)) = 1 from
        (PiTensorProduct.one_def).symm, one_mul, netEquivLevel_one, mul_one]
  | k + 1, x, y => by
      have ih := netEquivLevel_tprod_mul k
      -- combine the two generators, then unfold all three occurrences
      rw [PiTensorProduct.tprod_mul_tprod]
      rw [netEquivLevel_succ_apply, netEquivLevel_succ_apply, netEquivLevel_succ_apply]
      rw [netSplit_tprod, netSplit_tprod, netSplit_tprod]
      -- ORDER MATTERS: push `congr` through the pure tensors FIRST
      rw [TensorProduct.congr_tmul, TensorProduct.congr_tmul, TensorProduct.congr_tmul]
      simp only [LinearEquiv.refl_apply]
      -- only now split the pointwise product
      rw [show (fun i : Fin k => (x * y) (Fin.castAdd 1 i)) =
            (fun i : Fin k => x (Fin.castAdd 1 i)) *
              (fun i : Fin k => y (Fin.castAdd 1 i)) from rfl]
      rw [show (x * y) (Fin.last k) = x (Fin.last k) * y (Fin.last k) from rfl]
      rw [← PiTensorProduct.tprod_mul_tprod, ih]
      rw [← Algebra.TensorProduct.tmul_mul_tmul]
      exact map_mul _ _ _

/-! ## §4 — The multilinear map, and the algebra homomorphism -/

/-- `netEquivLevel k` precomposed with `tprod`, as a `MultilinearMap`. -/
noncomputable def netMultilinear (k : ℕ) :
    MultilinearMap ℂ (fun _ : Fin k => TernaryLocalNet.Site) (Level k) :=
  (netEquivLevel k).toLinearMap.compMultilinearMap (tprod ℂ)

@[simp]
theorem netMultilinear_apply (k : ℕ) (f : Fin k → TernaryLocalNet.Site) :
    netMultilinear k f = netEquivLevel k (tprod ℂ f) := rfl

/-- The bridge as an algebra homomorphism. -/
noncomputable def netAlgHom (k : ℕ) : Net k →ₐ[ℂ] Level k :=
  PiTensorProduct.liftAlgHom (netMultilinear k)
    (by
      simp only [netMultilinear_apply]
      rw [show (tprod ℂ (1 : Fin k → TernaryLocalNet.Site)) = 1 from
        (PiTensorProduct.one_def).symm]
      exact netEquivLevel_one k)
    (fun x y => by
      simp only [netMultilinear_apply]
      rw [← PiTensorProduct.tprod_mul_tprod]
      exact netEquivLevel_tprod_mul k x y)

/-! ## §5 — The `AlgHom` IS `netEquivLevel`

`liftAlgHom` is built from `PiTensorProduct.lift`, the unique linear map
agreeing with the given multilinear map on `tprod`. Since `netMultilinear` was
*defined* as `netEquivLevel ∘ tprod`, the two linear maps agree on generators
and hence everywhere. -/

theorem netAlgHom_toLinearMap (k : ℕ) :
    (netAlgHom k).toLinearMap = (netEquivLevel k).toLinearMap := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro f
  simp [netAlgHom, netMultilinear]

@[simp]
theorem netAlgHom_apply (k : ℕ) (x : Net k) : netAlgHom k x = netEquivLevel k x :=
  DFunLike.congr_fun (netAlgHom_toLinearMap k) x

/-! ## §6 — THE RESULT: the bridge is an algebra isomorphism -/

/-- **The ternary net over `k` sites is the `k`-th level of the substrate matrix
tower, as an algebra.** This is r357 upgraded from `≃ₗ[ℂ]` to `≃ₐ[ℂ]`, which is
what the Haag–Kastler axioms need: they are statements about subalgebras. -/
noncomputable def netAlgEquivLevel (k : ℕ) : Net k ≃ₐ[ℂ] Level k :=
  AlgEquiv.ofBijective (netAlgHom k)
    (by
      have h : (netAlgHom k : Net k → Level k) = netEquivLevel k :=
        funext (netAlgHom_apply k)
      rw [h]
      exact (netEquivLevel k).bijective)

@[simp]
theorem netAlgEquivLevel_apply (k : ℕ) (x : Net k) :
    netAlgEquivLevel k x = netEquivLevel k x := netAlgHom_apply k x

/-- On a generator the isomorphism is the iterated Kronecker product, computed by
peeling the last site. -/
theorem netAlgEquivLevel_tprod_succ (k : ℕ) (f : Fin (k + 1) → TernaryLocalNet.Site) :
    netAlgEquivLevel (k + 1) (tprod ℂ f) =
      levelKronecker k
        ((netAlgEquivLevel k (tprod ℂ fun i : Fin k => f (Fin.castAdd 1 i)))
          ⊗ₜ[ℂ] f (Fin.last k)) := by
  rw [netAlgEquivLevel_apply, netEquivLevel_succ_apply, netSplit_tprod,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply, netAlgEquivLevel_apply]

/-! ## §7 — Non-vacuity

The isomorphism is between nontrivial algebras, and its multiplicativity is not
vacuous: it carries a product of generators to a product. -/

theorem netAlgEquivLevel_nonvacuous (k : ℕ) (x y : Fin k → TernaryLocalNet.Site) :
    netAlgEquivLevel k (tprod ℂ x * tprod ℂ y) =
      netAlgEquivLevel k (tprod ℂ x) * netAlgEquivLevel k (tprod ℂ y) :=
  map_mul _ _ _

theorem net_nontrivial (k : ℕ) : Nontrivial (Net k) := by
  haveI := level_nontrivial k
  exact (netAlgEquivLevel k).toEquiv.nontrivial

end TernaryNetMatrixAlgBridge
end PrincipiaTractalis
