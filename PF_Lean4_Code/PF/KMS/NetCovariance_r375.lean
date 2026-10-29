/-
# r375: COVARIANCE — the sixth Haag–Kastler axiom for the ternary net

★ 2026-10-28 r375 — six of six, for the site-permutation group ★

## What was blocking this, and why it was looking in the wrong place

`ch04:461` records covariance as blocked on the classification of
`Aut(T_∞)`/`Out(T_∞)`, which is open. That is the right obstruction for the
`M⁴ = Aut/Aut₀` route, where the symmetry group is sought **inside** the
algebra's automorphism group.

But covariance for a **net** is not that. In algebraic quantum field theory the
covariance axiom asks for a group acting on the *index* — on regions — together
with algebra automorphisms intertwining the two:

    α_g (𝒜(S)) = 𝒜(g · S)

The ternary net is indexed by a site set `ι`, and the group that acts on a bare
index set is its **permutation group**. That group is available with no
classification problem at all. So the axiom is reachable without resolving
`Out(T_∞)` — the two are different questions, and conflating them is what made
covariance look harder than it is.

## The one piece mathlib does not have

`PiTensorProduct.reindex` is **linear only** (`LinearAlgebra/PiTensorProduct.lean:674`),
exactly as `PiTensorProduct.tmulEquiv` was for r357. Covariance is a statement
about **subalgebras**, so a linear equivalence is not enough: it has to be an
`AlgEquiv`. Measured absent — `RingTheory/PiTensorProduct.lean` has
`singleAlgHom` and `constantBaseRingEquiv` and no algebra-level reindex.

§1 supplies it (`sitePermAlgEquiv`), by the same route r358 used: prove
multiplicativity on generators and extend by the induction principle. This is
r358's lesson reused — the upgrade from `≃ₗ` to `≃ₐ` is the real work, and it is
what the axioms actually need.

## What is proved

* **`sitePermAlgEquiv`** — a site permutation acts as an **algebra**
  automorphism of the substrate net;
* `sitePermAlgEquiv_tprod`, `sitePermAlgEquiv_localAt` — it permutes the local
  observables: `α_g (localAt i a) = localAt (g i) a`;
* **`sitePermAlgEquiv_regionAlgebra`** — **COVARIANCE**:
  `(𝒜(S)).map α_g = 𝒜(g '' S)`;
* `sitePermAlgEquiv_one`, `sitePermAlgEquiv_trans` — the action is a group
  action (identity and composition), so it is a genuine symmetry group
  representation and not a single automorphism.

## FULL SIGNIFICANCE — stated exactly, with the limits in the same breath

With this, the ternary net satisfies **all six** structural Haag–Kastler axioms:
isotony, locality, additivity, the empty region, completeness (r350–r354, r359),
and now covariance. For an abstract local net that is the complete axiom list.

**And here is what it is not, stated as plainly.**

1. **The group is `Equiv.Perm ι`, not a spacetime symmetry group.** It is not
   Poincaré, not Lorentz, not Galilean. It permutes labels. ch04's honest-scope
   entry — *"No spacetime is produced. Regions are subsets of an index set.
   There is no metric, no causal order, no point, no dimension count, and in
   particular nothing here yields 3+1"* — **remains true word for word**, and
   this file does not weaken it by one clause.
2. **Six of six axioms is not a physical theory.** The Haag–Kastler axioms are
   satisfied by many structures with no physics in them, this one included.
   What they establish is that the object *is* a local net — a precondition for
   a geometric reconstruction, not the reconstruction.
3. **It does not resolve `Out(T_∞)`.** That classification stays open and the
   `M⁴ = Aut/Inn` route stays blocked exactly where ch04:461 leaves it. This
   file routes around that question rather than answering it, and the `M⁴` route
   would still need it.
4. **No dynamics is claimed to be covariant.** Whether the KMS automorphisms of
   r363–r374 are covariant for this action — whether `α_g σ_X α_g⁻¹ = σ_{α_g X}`
   — is not proved here, though r374's localisation says the pieces are
   compatible in shape.

So: the axiom is discharged, the gap ch04 records is narrowed to a precisely
stated residue, and nothing about spacetime is claimed. That is the honest
accounting, and the correction belongs in ch04's scope block, which currently
says covariance is absent.

## Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-28.
-/
import PF.TernaryNetIsotony_r352

set_option autoImplicit false

namespace PF.KMS

open PiTensorProduct
open PrincipiaTractalis.TernaryLocalNet
open PrincipiaTractalis.TernaryNetIsotony
open scoped TensorProduct

variable {ι : Type*} [DecidableEq ι]

/-! ## §1 — A site permutation acts as an ALGEBRA automorphism

`PiTensorProduct.reindex` is linear only; covariance is about subalgebras, so
the upgrade is mandatory, not cosmetic. -/

/-- **★★★ r375: the site-permutation action, as an algebra equivalence ★★★** -/
noncomputable def sitePermAlgEquiv (e : ι ≃ ι) :
    SubstrateNet ι ≃ₐ[ℂ] SubstrateNet ι :=
  AlgEquiv.ofLinearEquiv
    (PiTensorProduct.reindex ℂ (fun _ : ι => Site) e)
    (by
      show PiTensorProduct.reindex ℂ (fun _ : ι => Site) e (tprod ℂ 1) = tprod ℂ 1
      rw [PiTensorProduct.reindex_tprod]
      congr 1)
    (by
      intro x y
      induction x using PiTensorProduct.induction_on with
      | smul_tprod r f =>
          induction y using PiTensorProduct.induction_on with
          | smul_tprod s g =>
              simp only [PiTensorProduct.smul_tprod_mul_smul_tprod, map_smul,
                PiTensorProduct.reindex_tprod,
                PiTensorProduct.smul_tprod_mul_smul_tprod]
              -- `(f*g) ∘ e.symm` and `(f∘e.symm) * (g∘e.symm)` are the same
              -- function, pointwise by definition of `Pi.mul`
              have hfun : (fun i => (f * g) (e.symm i))
                  = (fun i => f (e.symm i)) * (fun i => g (e.symm i)) := rfl
              rw [hfun]
          | add y₁ y₂ h₁ h₂ =>
              simp only [mul_add, map_add, h₁, h₂]
      | add x₁ x₂ h₁ h₂ =>
          simp only [add_mul, map_add, h₁, h₂])

@[simp] theorem sitePermAlgEquiv_tprod (e : ι ≃ ι) (f : ι → Site) :
    sitePermAlgEquiv e (tprod ℂ f) = tprod ℂ (fun i => f (e.symm i)) := by
  show PiTensorProduct.reindex ℂ (fun _ : ι => Site) e (tprod ℂ f) = _
  exact PiTensorProduct.reindex_tprod _ _

/-- The identity permutation acts trivially. -/
@[simp] theorem sitePermAlgEquiv_one (x : SubstrateNet ι) :
    sitePermAlgEquiv (Equiv.refl ι) x = x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f => simp
  | add x y hx hy => simp [hx, hy]

/-- **The action composes**, so this is a genuine group action of
`Equiv.Perm ι` and not a family of unrelated automorphisms — which is what the
covariance axiom requires. -/
theorem sitePermAlgEquiv_trans (e₁ e₂ : ι ≃ ι) (x : SubstrateNet ι) :
    sitePermAlgEquiv (e₁.trans e₂) x
      = sitePermAlgEquiv e₂ (sitePermAlgEquiv e₁ x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f => simp
  | add x y hx hy => simp [hx, hy]

/-! ## §2 — It permutes the local observables -/

/-- **`α_g` moves the observable at site `i` to site `g i`.** -/
theorem sitePermAlgEquiv_localAt (e : ι ≃ ι) (i : ι) (a : Site) :
    sitePermAlgEquiv e (localAt ι i a) = localAt ι (e i) a := by
  show sitePermAlgEquiv e (tprod ℂ (Pi.mulSingle i a)) = tprod ℂ (Pi.mulSingle (e i) a)
  rw [sitePermAlgEquiv_tprod]
  congr 1
  funext j
  by_cases hj : j = e i
  · subst hj
    rw [Equiv.symm_apply_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
  · have hji : e.symm j ≠ i := by
      intro h
      exact hj (by rw [← h, Equiv.apply_symm_apply])
    simp [Pi.mulSingle_eq_of_ne hji, Pi.mulSingle_eq_of_ne hj]

/-- The image of the generating set of a region is the generating set of the
permuted region. -/
theorem sitePermAlgEquiv_image_generators (e : ι ≃ ι) (S : Set ι) :
    (sitePermAlgEquiv e) '' (⋃ i ∈ S, Set.range (localAt ι i))
      = ⋃ j ∈ (e '' S), Set.range (localAt ι j) := by
  ext z
  simp only [Set.mem_image, Set.mem_iUnion, Set.mem_range, exists_prop]
  constructor
  · rintro ⟨w, ⟨i, hi, a, haw⟩, hwz⟩
    refine ⟨e i, ⟨i, hi, rfl⟩, a, ?_⟩
    rw [← hwz, ← haw, sitePermAlgEquiv_localAt]
  · rintro ⟨j, ⟨i, hi, hij⟩, a, haj⟩
    refine ⟨localAt ι i a, ⟨i, hi, a, rfl⟩, ?_⟩
    rw [sitePermAlgEquiv_localAt, hij, haj]

/-! ## §3 — COVARIANCE -/

/-- **★★★ r375: COVARIANCE — the sixth Haag–Kastler axiom ★★★**

`α_g (𝒜(S)) = 𝒜(g · S)`. The region algebra of a permuted region is the
image of the region algebra. -/
theorem sitePermAlgEquiv_regionAlgebra (e : ι ≃ ι) (S : Set ι) :
    Subalgebra.map (sitePermAlgEquiv e : SubstrateNet ι →ₐ[ℂ] SubstrateNet ι)
        (regionAlgebra ι S)
      = regionAlgebra ι (e '' S) := by
  -- rewrite the RHS's generating set, then close with `adjoin_image`;
  -- `exact` unifies the AlgHom coercion where `rw` would not.
  rw [regionAlgebra, regionAlgebra, ← sitePermAlgEquiv_image_generators e S]
  exact (Algebra.adjoin_image ℂ _ _).symm

end PF.KMS

/-! ## §Axiom check -/
#print axioms PF.KMS.sitePermAlgEquiv
#print axioms PF.KMS.sitePermAlgEquiv_tprod
#print axioms PF.KMS.sitePermAlgEquiv_one
#print axioms PF.KMS.sitePermAlgEquiv_trans
#print axioms PF.KMS.sitePermAlgEquiv_localAt
#print axioms PF.KMS.sitePermAlgEquiv_image_generators
#print axioms PF.KMS.sitePermAlgEquiv_regionAlgebra
