/-
# r345 — `d₁Free` and the kernel: the descent to `d₁`, up to the quotient lift

★ 2026-10-24 — step 2 of the Grothendieck route, the mathematical content ★

## What this file does

`r344` proved the three well-definedness conditions for `d₁` in the
`S`-multiplied form that `KaehlerDifferential.kerTotal` requires. This file
uses them: it builds the candidate map on the free module and proves it kills
the whole relation submodule.

    d1Free : (S →₀ S) →+ Form R S 2 ,        d1Free (single y a) = d₀a ∧ d₀y
    d1Free_kills_kerTotal : z ∈ kerTotal R S → d1Free z = 0

Since `Ω¹ ≅ (S →₀ S) ⧸ kerTotal R S` (`quotKerTotalEquiv`), the second theorem
is exactly the well-definedness of `d₁` on `Ω¹`. What remains after this file
is the quotient lift itself.

## The two things that make this non-trivial

**1. The induction has to be strengthened.** `kerTotal` is the `S`-SPAN of the
three relation families, and `d1Free` is only ADDITIVE — `d₀` is not
`S`-linear. So `Submodule.span_induction` on the predicate `d1Free z = 0`
fails at its `smul` case: additivity gives nothing about `d1Free (s • z)` from
`d1Free z = 0`. The predicate is therefore strengthened to

    ∀ s : S, d1Free (s • z) = 0

which closes: `smul` becomes `smul_smul` plus the hypothesis at `s * a`, `add`
becomes `smul_add` plus additivity, and `mem` becomes exactly the three lemmas
`r344` proved. Recovering the original statement is `one_smul`.

**2. The three generator cases are precisely r344's three lemmas.** That is not
a coincidence — it is why those lemmas were stated in the `S`-multiplied form
rather than the bare one. Under `single y a ↦ d₀a ∧ d₀y`:

    s • (1·dx + 1·dy − 1·d(x+y))   ↦  descent_additive_relation
    s • (x·dy + y·dx − 1·d(xy))    ↦  descent_leibniz_relation
    s • (1·d(algebraMap r))        ↦  descent_algebraMap_relation

The Leibniz case is the one with content: its cross terms cancel pairwise and
the surviving `s •` factor multiplies the degree-1 antisymmetry obstruction.

## What is and is not claimed

**Claimed.** `d1Free` exists as an additive map on the free module, computes as
`d₀a ∧ d₀y` on generators, and annihilates `KaehlerDifferential.kerTotal R S`.
Equivalently: the candidate `d₁` is well defined on `Ω¹`.

**Not claimed.**

1. `d₁ : Ω¹ → Ω²` ITSELF. The quotient lift is not performed here. Lifting an
   additive (not `S`-linear) map through a `Submodule` quotient does not go via
   `Submodule.liftQ`; it needs `Quotient.liftOn'` against
   `Submodule.quotientRel`, whose relation is `x - y ∈ p`. That is Lean
   bureaucracy rather than mathematics, and it is left to the next step rather
   than half-done here.
2. `d ∘ d = 0` in any degree above the degree-1 shadow in `r344`, and no
   `d_n` for `n ≥ 2`.
3. No complex, no cohomology, nothing global — quasi-coherent sheaves, sheaf
   cohomology, hypercohomology and spectral sequences all count ZERO files in
   mathlib at this pin — and nothing about the Hodge conjecture, whose content
   needs Chow groups and the cycle class map, both absent.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-24.
-/

import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Tactic
import PF.AlgebraicDeRhamWedge_r344

namespace PrincipiaTractalis
namespace AlgebraicDeRhamAffine

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

/-! ## §1 — `d₀` of zero -/

/-- `d₀ 0 = 0`. Needed so the coefficient map below is an `AddMonoidHom`. -/
theorem d0_zero : d0 R S 0 = 0 := by
  unfold d0
  rw [map_zero, map_zero]

/-! ## §2 — The candidate `d₁` on the free module -/

/-- For a fixed differentiated variable `y`, the coefficient map
`a ↦ d₀a ∧ d₀y`, as an additive homomorphism.

It is additive because `d₀` is (`d0_add`) and `wedge` is additive in its left
argument (`wedge_add_left`). It is NOT `S`-linear, which is the whole
difficulty of the descent. -/
noncomputable def d1Coeff (y : S) : S →+ Form R S 2 where
  toFun a := wedge R S (d0 R S a) (d0 R S y)
  map_zero' := by rw [d0_zero, wedge_zero_left]
  map_add' a b := by rw [d0_add, wedge_add_left]

/-- **The candidate `d₁`, on the free module `S →₀ S`.**

`Finsupp.liftAddHom` assembles the per-variable coefficient maps into a single
additive map. On a generator `a · dy` it is `d₀a ∧ d₀y`, which is the classical
formula `d(a dy) = da ∧ dy`. -/
noncomputable def d1Free : (S →₀ S) →+ Form R S 2 :=
  Finsupp.liftAddHom (d1Coeff R S)

@[simp]
theorem d1Free_single (y a : S) :
    d1Free R S (Finsupp.single y a) = wedge R S (d0 R S a) (d0 R S y) :=
  Finsupp.liftAddHom_apply_single (d1Coeff R S) y a

/-! ## §3 — `d1Free` annihilates the relation submodule -/

/-- **★★★ The descent is well defined.**

`d1Free` kills `KaehlerDifferential.kerTotal R S`, the submodule of relations
presenting `Ω¹`. Since `Ω¹ ≅ (S →₀ S) ⧸ kerTotal R S`, this IS the
well-definedness of `d₁`.

The induction is run on the strengthened predicate `∀ s, d1Free (s • z) = 0`,
because `kerTotal` is an `S`-span while `d1Free` is only additive; the plain
predicate's `smul` case is not provable. See this file's header. -/
theorem d1Free_kills_kerTotal {z : S →₀ S}
    (hz : z ∈ KaehlerDifferential.kerTotal R S) :
    d1Free R S z = 0 := by
  have key : ∀ s : S, d1Free R S (s • z) = 0 := by
    induction hz using Submodule.span_induction with
    | mem w hw =>
        intro s
        rcases hw with (⟨⟨u, v⟩, rfl⟩ | ⟨⟨u, v⟩, rfl⟩) | ⟨r, rfl⟩
        · -- additive relation: 1·du + 1·dv − 1·d(u+v)
          simp only [smul_add, smul_sub, Finsupp.smul_single, map_add, map_sub,
            d1Free_single, mul_one, smul_eq_mul]
          rw [sub_eq_zero]
          exact descent_additive_relation R S s u v
        · -- Leibniz relation: u·dv + v·du − 1·d(uv)
          simp only [smul_add, smul_sub, Finsupp.smul_single, map_add, map_sub,
            d1Free_single, mul_one, smul_eq_mul]
          rw [sub_eq_zero]
          exact descent_leibniz_relation R S s u v
        · -- algebraMap relation: 1·d(algebraMap r)
          simp only [Finsupp.smul_single, map_add, d1Free_single, mul_one, smul_eq_mul]
          exact descent_algebraMap_relation R S s r
    | zero => intro s; rw [smul_zero, map_zero]
    | add x y _ _ ihx ihy =>
        intro s; rw [smul_add, map_add, ihx s, ihy s, add_zero]
    | smul a x _ ih =>
        intro s; rw [smul_smul]; exact ih (s * a)
  simpa using key 1

/-! ## §4 — Capstone -/

/-- **Step 2's mathematical content, as one statement.**

The candidate `d₁` exists on the free module, computes as `d₀a ∧ d₀y` on
generators, and is well defined modulo the relations. The quotient lift is the
remaining step; see this file's "Not claimed". -/
theorem d1_descent_well_defined :
    (∀ y a : S, d1Free R S (Finsupp.single y a)
        = wedge R S (d0 R S a) (d0 R S y)) ∧
    (∀ z : S →₀ S, z ∈ KaehlerDifferential.kerTotal R S → d1Free R S z = 0) :=
  ⟨d1Free_single R S, fun _ hz => d1Free_kills_kerTotal R S hz⟩

end AlgebraicDeRhamAffine
end PrincipiaTractalis

/-! ## §Axiom check -/

#print axioms PrincipiaTractalis.AlgebraicDeRhamAffine.d0_zero
#print axioms PrincipiaTractalis.AlgebraicDeRhamAffine.d1Free_single
#print axioms PrincipiaTractalis.AlgebraicDeRhamAffine.d1Free_kills_kerTotal
#print axioms PrincipiaTractalis.AlgebraicDeRhamAffine.d1_descent_well_defined
