/-
# r354 — The completeness axiom: proved for finite site sets, open for infinite

★ 2026-10-25 — emergent locality, fifth brick ★

## What this adds

`r353` closed with the fifth Haag–Kastler axiom named as missing: a net should
*exhaust* the substrate, `𝒜(ι) = ⊤`. This file settles it — and the answer is
not uniform in `ι`, so it is not stated as though it were.

    tprod_restrictPi_mem   every finitely-supported pure tensor is local   (any ι)
    net_eq_iSup_finite     𝒜(ι) = ⨆ S : Finset ι, 𝒜(S)                     (any ι)
    completeness           𝒜(ι) = ⊤                                        (Fintype ι)

### Why the split is real and not a convenience

`PiTensorProduct.span_tprod_eq_top` carries **no** finiteness hypothesis: pure
tensors span the substrate always. Finiteness enters one step later, in writing
a pure tensor as a *product of one-site operators*. That product has one factor
per site, so for infinite `ι` there is no such product to form.

Concretely `Finset.univ_prod_mulSingle` — the identity
`∏ i, Pi.mulSingle i (f i) = f` that would do it in one line — carries
`[Fintype I]`. The proof of `completeness` cannot be run for infinite `ι`; it
is not that a shortcut is missing.

### A measured obstruction worth recording

mathlib *does* have `PiTensorProduct.tprod_prod`, exactly the lemma
`tprod (∏ k ∈ s, x k) = ∏ k ∈ s, tprod (x k)` one would reach for. It sits in
the `CommSemiring` section, because `Finset.prod` needs a commutative target.
Our site algebra is `M₃(ℂ)`, which is **not** commutative — the substrate is a
noncommutative ring and `Finset.prod` is not available in it at all. The lemma
is present and does not apply to us.

The route that does work is `Finset` induction through `tprod_mul_tprod`, which
lives in the `NonAssocSemiring` section and needs no commutativity. The
induction peels off one site at a time and uses `r352`'s isotony to re-seat the
inductive hypothesis in the larger region. So noncommutativity — the thing that
makes the net physically nontrivial — is also what forces the proof to be an
induction over sites rather than a rewrite.

## The infinite case is OPEN, not refuted

For infinite `ι` this file proves `𝒜(ι) = ⨆ S : Finset ι, 𝒜(S)`: the net is the
directed union of its finite-region algebras. That is the inductive-limit form
of the axiom, and it is the correct statement of completeness for an infinite
system.

Whether that supremum is all of `⊤` is **neither proved nor refuted here.**

* What would settle it: a free-basis theorem for `PiTensorProduct` over an
  infinite index set. There is **no such theorem anywhere in mathlib at this
  pin** — measured, not assumed.
* My expectation is that `𝒜(ι) = ⊤` is **false** for infinite `ι`, because the
  algebraic `⨂` contains pure tensors differing from `1` at infinitely many
  sites and no finite product of one-site operators reaches them. **That
  expectation is not a theorem and nothing below depends on it.** It is
  recorded as a conjecture so a later file can discharge or kill it.
* If it is false, the fix is not a cleverer proof but a different object: the
  C*-inductive limit of the finite-region algebras (a UHF algebra), where
  completeness holds by construction. `UHF` is 0 files at this pin, so that
  object is not expressible here.

So: four axioms unconditional, the fifth proved for finite site sets and given
its inductive-limit form in general. Five of five for `ι = Fin k` — the tower
level `M_{3^k}` — and four and a half for the full substrate.

## What is and is not claimed

**Claimed.** The three theorems above and the two capstones.

**Not claimed.**

1. `𝒜(ι) = ⊤` for infinite `ι`. Open, as above.
2. **Still no spacetime.** Regions are subsets of an index set. No metric, no
   causal order, no point. Unchanged from r350–r353.
3. **Covariance** remains absent and blocked on `Aut(T_∞)` (ch04:461), not
   expressible at this pin.

## Process note

Every lemma below was measured at this pin before a line was written, including
how each is *proved* and not only what it states. Two of those measurements
changed the code:

* `PiTensorProduct.one_def` is `rfl`, so `tprod ℂ 1 = 1` is definitional.
* `Subalgebra.mem_toSubmodule` is `Iff.rfl` and `coe_toSubmodule` is `rfl`.
  An `Iff.rfl` lemma has no syntactic pattern, so `rw` **fails** on it — this
  is the precise defect that cost `r352` three builds. The final step of
  `completeness` therefore closes by `exact`, on definitional equality.

One name was still wrong on the first build, and the failure was reading rather
than measuring: `toSubmodule_eq_top` sits inside `namespace Algebra` in
`Subalgebra/Lattice.lean`, so it is `Algebra.toSubmodule_eq_top`, not
`Subalgebra.toSubmodule_eq_top`. The correct spelling was already present in
the measurement output that preceded the file — two mathlib call sites use it —
and was not read. Measuring is necessary and not sufficient; the output has to
be read. Cost: one 5-second build.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-25.
-/

import Mathlib.RingTheory.PiTensorProduct
import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import PF.TernaryNetAdditivity_r353

namespace PrincipiaTractalis
namespace TernaryNetCompleteness

open PiTensorProduct TernaryLocalNet TernaryNetIsotony TernaryNetAdditivity
open scoped TensorProduct

variable (ι : Type*) [DecidableEq ι]

/-! ## §1 — One-site operators as pure tensors -/

/-- `localAt i a` is the pure tensor with `a` in slot `i` and `1` elsewhere.

`singleAlgHom` is defined via `MonoidHom.mulSingle`; this restates it with
`Pi.mulSingle`, which is the form the `Finset` induction below produces.
`MonoidHom.mulSingle_apply` is stated unapplied, so it rewrites underneath
`tprod` without a `funext`. -/
theorem localAt_eq_tprod_mulSingle (i : ι) (a : Site) :
    localAt ι i a = tprod ℂ (Pi.mulSingle i a) := by
  simp only [localAt, singleAlgHom_apply, MonoidHom.mulSingle_apply]

/-- A one-site operator lies in the algebra of any region containing its site. -/
theorem localAt_mem_regionAlgebra {S : Set ι} {i : ι} (hi : i ∈ S) (a : Site) :
    localAt ι i a ∈ regionAlgebra ι S :=
  Algebra.subset_adjoin (Set.mem_biUnion hi ⟨a, rfl⟩)

/-- A region's algebra is below `B` as soon as every one-site generator is. -/
theorem regionAlgebra_le {S : Set ι} {B : Subalgebra ℂ (SubstrateNet ι)}
    (h : ∀ i ∈ S, ∀ a : Site, localAt ι i a ∈ B) : regionAlgebra ι S ≤ B := by
  unfold regionAlgebra
  apply Algebra.adjoin_le
  intro z hz
  simp only [Set.mem_iUnion, Set.mem_range] at hz
  obtain ⟨i, hi, a, rfl⟩ := hz
  exact h i hi a

/-! ## §2 — Restricting a configuration to a finite region -/

/-- `restrictPi f S` agrees with `f` on `S` and is `1` off `S`. Its pure tensor
is the natural candidate element of `𝒜(S)`. -/
def restrictPi (f : ι → Site) (S : Finset ι) : ι → Site :=
  fun i => if i ∈ S then f i else 1

@[simp] theorem restrictPi_empty (f : ι → Site) : restrictPi ι f ∅ = 1 := by
  funext i
  simp [restrictPi]

/-- Peeling one site off the region factors off one one-site operator.

This is the entire content of the induction, and it is an identity in
`Π i, Site` — no tensor product and no commutativity anywhere in it. -/
theorem restrictPi_insert (f : ι → Site) {a : ι} {T : Finset ι} (ha : a ∉ T) :
    restrictPi ι f (insert a T) = Pi.mulSingle a (f a) * restrictPi ι f T := by
  funext i
  by_cases hi : i = a
  · subst hi
    simp [restrictPi, ha]
  · simp [restrictPi, Pi.mul_apply, Finset.mem_insert, hi]

/-! ## §3 — Every finitely-supported pure tensor is local (any `ι`) -/

/-- **★★★ The net generates every finitely-supported pure tensor.**

No finiteness on `ι`. Induction on the region: the empty region contributes
`1` (and `tprod ℂ 1 = 1` definitionally, by `PiTensorProduct.one_def`), while
inserting a site `a` factors off `localAt a (f a)` and `r352`'s isotony re-seats
the inductive hypothesis in the larger region.

This is the general content of completeness and the strongest form available
without `Fintype ι`. -/
theorem tprod_restrictPi_mem (f : ι → Site) (S : Finset ι) :
    tprod ℂ (restrictPi ι f S) ∈ regionAlgebra ι (↑S : Set ι) := by
  induction S using Finset.induction_on with
  | empty =>
      rw [restrictPi_empty, ← PiTensorProduct.one_def]
      exact one_mem _
  | insert a T ha ih =>
      rw [restrictPi_insert ι f ha, ← tprod_mul_tprod]
      have hsub : (↑T : Set ι) ⊆ (↑(insert a T) : Set ι) :=
        Finset.coe_subset.mpr (Finset.subset_insert a T)
      have h₂ : tprod ℂ (restrictPi ι f T) ∈ regionAlgebra ι (↑(insert a T) : Set ι) :=
        isotony ι hsub ih
      have h₁ : tprod ℂ (Pi.mulSingle a (f a)) ∈ regionAlgebra ι (↑(insert a T) : Set ι) := by
        rw [← localAt_eq_tprod_mulSingle]
        exact localAt_mem_regionAlgebra ι (by simp) (f a)
      exact mul_mem h₁ h₂

/-! ## §4 — The inductive-limit form of completeness (any `ι`) -/

/-- **★★★ The net is the directed union of its finite-region algebras.**

`𝒜(ι) = ⨆ S : Finset ι, 𝒜(S)`, with no finiteness on `ι`.

This is the inductive-limit form of the completeness axiom and the correct
statement of it for an infinite site set. Both inclusions are one line: `≥` is
`r352`'s isotony applied to `↑S ⊆ univ`, and `≤` holds because each one-site
generator already lies in the algebra of its singleton region. -/
theorem net_eq_iSup_finite :
    regionAlgebra ι (Set.univ : Set ι)
      = ⨆ S : Finset ι, regionAlgebra ι (↑S : Set ι) := by
  refine le_antisymm (regionAlgebra_le ι fun i _ a => ?_)
    (iSup_le fun S => isotony ι (Set.subset_univ _))
  exact le_iSup (fun S : Finset ι => regionAlgebra ι (↑S : Set ι)) ({i} : Finset ι)
    (localAt_mem_regionAlgebra ι (by simp) a)

/-! ## §5 — Completeness itself, for a finite site set -/

/-- **★★★ Completeness.** For a finite site set the local algebras generate the
whole substrate: `𝒜(ι) = ⊤`.

Two measured ingredients: pure tensors span (`span_tprod_eq_top`, which needs
no finiteness), and when `ι` is finite every pure tensor is finitely supported,
so `tprod_restrictPi_mem` places all of them in `𝒜(ι)`.

The last step closes by `exact` rather than `rw`: `Subalgebra.mem_toSubmodule`
is `Iff.rfl` and `coe_toSubmodule` is `rfl`, so the membership is definitional
and there is no pattern for `rw` to match.

At `ι = Fin k` this says the tower level `M_{3^k} ≅ ⨂_{i<k} M₃` is generated by
its `k` single-site subalgebras — the net exhausts the substrate exactly. -/
theorem completeness [Fintype ι] : regionAlgebra ι (Set.univ : Set ι) = ⊤ := by
  refine Algebra.toSubmodule_eq_top.mp (le_antisymm le_top ?_)
  rw [← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro x ⟨f, rfl⟩
  have h := tprod_restrictPi_mem ι f (Finset.univ : Finset ι)
  have hf : restrictPi ι f (Finset.univ : Finset ι) = f := by
    funext i
    simp [restrictPi]
  rw [hf, Finset.coe_univ] at h
  exact h

/-! ## §6 — Capstones -/

/-- **The ternary net over a finite site set satisfies all five structural
Haag–Kastler axioms.**

(1) isotony — `r352`
(2) locality — `r352`
(3) additivity — `r353`
(4) the empty region — `r353`
(5) **completeness** — here

Covariance is the sixth axiom and is absent: it needs a group acting on sites,
which for the full substrate is the `Aut(T_∞)` problem (ch04:461), not
expressible at this mathlib pin. -/
theorem ternary_net_five_axioms [Fintype ι] :
    (∀ S T : Set ι, S ⊆ T → regionAlgebra ι S ≤ regionAlgebra ι T) ∧
    (∀ S T : Set ι, (∀ i ∈ S, ∀ j ∈ T, i ≠ j) →
      ∀ x y : SubstrateNet ι,
        x ∈ regionAlgebra ι S → y ∈ regionAlgebra ι T → Commute x y) ∧
    (∀ S T : Set ι,
      regionAlgebra ι (S ∪ T) = regionAlgebra ι S ⊔ regionAlgebra ι T) ∧
    (regionAlgebra ι (∅ : Set ι) = ⊥) ∧
    (regionAlgebra ι (Set.univ : Set ι) = ⊤) :=
  ⟨fun _ _ h => isotony ι h,
   fun _ _ hST _ _ hx hy => region_locality ι hST hx hy,
   additivity ι,
   regionAlgebra_empty ι,
   completeness ι⟩

/-- **For an arbitrary site set: the same four axioms, plus the inductive-limit
form of completeness.**

The fifth clause is `𝒜(ι) = ⨆ S : Finset ι, 𝒜(S)` rather than `𝒜(ι) = ⊤`.
Whether that supremum is `⊤` for infinite `ι` is open — see the header. -/
theorem ternary_net_axioms_inductive_limit :
    (∀ S T : Set ι, S ⊆ T → regionAlgebra ι S ≤ regionAlgebra ι T) ∧
    (∀ S T : Set ι, (∀ i ∈ S, ∀ j ∈ T, i ≠ j) →
      ∀ x y : SubstrateNet ι,
        x ∈ regionAlgebra ι S → y ∈ regionAlgebra ι T → Commute x y) ∧
    (∀ S T : Set ι,
      regionAlgebra ι (S ∪ T) = regionAlgebra ι S ⊔ regionAlgebra ι T) ∧
    (regionAlgebra ι (∅ : Set ι) = ⊥) ∧
    (regionAlgebra ι (Set.univ : Set ι)
      = ⨆ S : Finset ι, regionAlgebra ι (↑S : Set ι)) :=
  ⟨fun _ _ h => isotony ι h,
   fun _ _ hST _ _ hx hy => region_locality ι hST hx hy,
   additivity ι,
   regionAlgebra_empty ι,
   net_eq_iSup_finite ι⟩

end TernaryNetCompleteness
end PrincipiaTractalis

/-! ## §Axiom check -/

#print axioms PrincipiaTractalis.TernaryNetCompleteness.tprod_restrictPi_mem
#print axioms PrincipiaTractalis.TernaryNetCompleteness.net_eq_iSup_finite
#print axioms PrincipiaTractalis.TernaryNetCompleteness.completeness
#print axioms PrincipiaTractalis.TernaryNetCompleteness.ternary_net_five_axioms
#print axioms PrincipiaTractalis.TernaryNetCompleteness.ternary_net_axioms_inductive_limit
