/-
# `localAt` is injective, and the region separation loses a hypothesis

**Date**: 2026-11-25 (Legion).

## What this is

`PF/KMS/ModularFlowSeparatesRegions_2026_11_24.lean` proved that the modular
flow separates a region from every region disjoint from it, but took a
non-commuting pair inside `𝒜(S)` as a hypothesis, and named the obstruction to
discharging it:

> **Removal condition.** [...] a non-commuting pair inside `𝒜(S)` at `Net k`.
> `within_region_not_commutative` (r350) gives one at the single ternary
> **site** (`M_3`), not at `Net k`, and lifting it needs **injectivity of
> `localAt`**, which the corpus does not currently have.

This file supplies that injectivity and discharges the hypothesis.

## The proof is simplicity, not slot extraction

The obvious route — build a left inverse extracting tensor slot `i` — needs an
infinite product of functionals when `ι` is infinite, and does not work. The
right route is one line of ring theory:

**`M_3(ℂ)` is a simple ring**, so a *unital* algebra homomorphism out of it has
kernel `⊥`. mathlib supplies both halves at this pin:
`IsSimpleRing.matrix` (the matrix ring over a simple ring is simple) together
with `DivisionRing.isSimpleRing` for `ℂ`, and
`IsSimpleRing.one_mem_of_ne_zero_mem` for the kernel argument. Nothing about
the tensor product is used, so the result holds for an arbitrary index set.

## What is proved

1. `localAt_injective` — `localAt ι i` is injective for any index set `ι`,
   given that the net is nontrivial. That hypothesis is genuinely needed: it is
   what rules out the degenerate target in which `1 = 0`.
2. `localAt_injective_fin` — the same at `ι = Fin k`, **unconditionally**,
   discharging the nontriviality from r358's `net_nontrivial`.
3. `localAt_reflects_not_commute` — an injective algebra map reflects
   non-commutation, so r350's site-level witness lifts to the net.
4. `site_region_has_noncommuting_pair` — **unconditional**: the algebra of a
   one-site region contains a non-commuting pair, and the first element of the
   pair is r370's `witnessWeight`, which is invertible.
5. `modular_flow_separates_regions_at_site` — the separation with the
   non-commuting-pair hypothesis **removed**.

## Why `witnessWeight` and not `E01`

r350's witness pair is `E₀₁, E₁₁`, which is the natural choice for
non-commutativity but useless here: `E₀₁` is nilpotent, so it cannot be the
*weight* of a modular automorphism, which requires an invertible determinant.
r370's `witnessWeight = diag(1,2,1)` has `det = 2` and is already proved not to
commute with `witnessElem`, so it serves as both.

## Scope — what is NOT claimed

* **No `M⁴`, no spacetime, no metric, no dimension.** As in the file this
  extends: "region" is a subset of the site index set and "disjoint" means
  disjoint index sets. Sites are not spacetime points.
* **Invertibility is still a hypothesis.** The separation now needs only
  `IsUnit (netAlgEquivLevel k w).det`, taken at matrix level exactly as r374
  takes it. That is the one hypothesis left, down from two.
* **No overlapping-region claim.** The flow separates `S` from regions
  *disjoint* from `S`; nothing here separates overlapping regions.
* `localAt` injectivity says nothing about the *image* being a proper
  subalgebra, nor about `regionAlgebra` for `|S| > 1`.

SPDX-License-Identifier: Apache-2.0
Author: Pablo Cohen.  2026-11-25.
-/

import PF.KMS.ModularFlowSeparatesRegions_2026_11_24
import Mathlib.RingTheory.SimpleRing.Matrix

set_option autoImplicit false

namespace PF.KMS

open Matrix
open PrincipiaTractalis.TernaryLocalNet
open PrincipiaTractalis.TernaryNetIsotony
open PrincipiaTractalis.TernaryNetCompleteness
open PrincipiaTractalis.TernaryNetMatrixBridge
open PrincipiaTractalis.TernaryNetMatrixAlgBridge

/-! ## §1 — `localAt` is injective

The content is that `M_3(ℂ)` is simple. Nothing here is about tensor products,
so `ι` is arbitrary. -/

/-- **★★★ `localAt ι i` is injective.**

`Site = M_3(ℂ)` is a simple ring, so the kernel of the unital algebra map
`localAt ι i` is a two-sided ideal that cannot contain `1`; simplicity then
forces it to be `⊥`.

The nontriviality hypothesis is doing real work: without it the target could be
the zero ring, where every map is non-injective and `1 = 0`. -/
theorem localAt_injective {ι : Type*} [DecidableEq ι]
    [Nontrivial (SubstrateNet ι)] (i : ι) :
    Function.Injective (localAt ι i) :=
  (localAt ι i : Site →ₐ[ℂ] SubstrateNet ι).toRingHom.injective

/-- The same at a finite site set, **unconditionally** — the nontriviality is
    discharged from r358's `net_nontrivial`. -/
theorem localAt_injective_fin (k : ℕ) (i : Fin k) :
    Function.Injective (localAt (Fin k) i) := by
  haveI := net_nontrivial k
  exact localAt_injective i

/-! ## §2 — Injectivity reflects non-commutation -/

/-- An injective algebra map reflects non-commutation: if the images commute,
    so do the sources. This is what lifts r350's site-level witness. -/
theorem localAt_reflects_not_commute {ι : Type*} [DecidableEq ι]
    [Nontrivial (SubstrateNet ι)]
    (i : ι) {a b : Site} (h : ¬ Commute a b) :
    ¬ Commute (localAt ι i a) (localAt ι i b) := by
  intro hc
  refine h ?_
  have := hc.eq
  rw [← map_mul, ← map_mul] at this
  exact (localAt_injective i) this

/-! ## §3 — A one-site region contains a non-commuting pair, with an
invertible first element

`witnessWeight = diag(1,2,1)` rather than `E₀₁`: the modular automorphism needs
an invertible weight, and `E₀₁` is nilpotent. -/

/-- **★★ Unconditional: the algebra of the one-site region `{i}` contains a
    non-commuting pair whose first element is `witnessWeight`.**

This is the hypothesis `modular_flow_separates_regions` had to assume. -/
theorem site_region_has_noncommuting_pair (k : ℕ) (i : Fin k) :
    localAt (Fin k) i witnessWeight ∈ regionAlgebra (Fin k) ({i} : Set (Fin k)) ∧
    localAt (Fin k) i witnessElem ∈ regionAlgebra (Fin k) ({i} : Set (Fin k)) ∧
    ¬ Commute (localAt (Fin k) i witnessWeight) (localAt (Fin k) i witnessElem) := by
  haveI := net_nontrivial k
  refine ⟨localAt_mem_regionAlgebra (Fin k) (Set.mem_singleton i) _,
          localAt_mem_regionAlgebra (Fin k) (Set.mem_singleton i) _, ?_⟩
  exact localAt_reflects_not_commute i (fun hc => witnessWeight_not_commute hc.eq)

/-! ## §4 — The separation, with the pair hypothesis removed -/

/-- **★★★ The modular flow separates a one-site region from every region
    disjoint from it — no non-commuting-pair hypothesis.**

Given only that the weight's matrix image has invertible determinant, the flow
of `witnessWeight` localised at site `i`:

* **moves** an observable of `𝒜({i})`, namely `witnessElem` at the same site;
* **fixes every** observable of **every** region disjoint from `{i}`.

The pair hypothesis of `modular_flow_separates_regions` is discharged by
`site_region_has_noncommuting_pair`, which rests on `localAt` injectivity,
which rests on `M_3(ℂ)` being simple. Invertibility is the one hypothesis
left.

**This is not a map to a spacetime point.** See the header's scope. -/
theorem modular_flow_separates_regions_at_site (k : ℕ) (i : Fin k)
    (hX : IsUnit (netAlgEquivLevel k (localAt (Fin k) i witnessWeight)).det) :
    (localAt (Fin k) i witnessElem ∈ regionAlgebra (Fin k) ({i} : Set (Fin k)) ∧
       netModularAut k (netAlgEquivLevel k (localAt (Fin k) i witnessWeight))
         (localAt (Fin k) i witnessElem) ≠ localAt (Fin k) i witnessElem) ∧
    ∀ T : Set (Fin k), (∀ p ∈ ({i} : Set (Fin k)), ∀ q ∈ T, p ≠ q) →
      ∀ v : Net k, v ∈ regionAlgebra (Fin k) T →
        netModularAut k (netAlgEquivLevel k (localAt (Fin k) i witnessWeight)) v = v := by
  obtain ⟨hw, hu, hnc⟩ := site_region_has_noncommuting_pair k i
  exact modular_flow_separates_regions k hw hu hX hnc

/-! ## §5 — One citable bundle -/

/-- **`localAt_injectivity_bundle`** — the three facts together.

(1) `localAt` is injective at every finite level, unconditionally.
(2) It therefore reflects non-commutation.
(3) So a one-site region's algebra contains a non-commuting pair with an
    invertible first element, and the region separation needs no such
    hypothesis.

Composed from `IsSimpleRing.matrix` + `DivisionRing.isSimpleRing` (mathlib),
r358's `net_nontrivial`, r354's `localAt_mem_regionAlgebra`, and r370's
`witnessWeight_not_commute`. No new mathematics beyond the simplicity
argument, and no spacetime claim — see the header. -/
theorem localAt_injectivity_bundle (k : ℕ) (i : Fin k) :
    Function.Injective (localAt (Fin k) i) ∧
    (∀ a b : Site, ¬ Commute a b →
       ¬ Commute (localAt (Fin k) i a) (localAt (Fin k) i b)) ∧
    ¬ Commute (localAt (Fin k) i witnessWeight) (localAt (Fin k) i witnessElem) := by
  haveI := net_nontrivial k
  exact ⟨localAt_injective_fin k i,
         fun _ _ h => localAt_reflects_not_commute i h,
         (site_region_has_noncommuting_pair k i).2.2⟩

end PF.KMS

/-! ## §Axiom audit -/
#print axioms PF.KMS.localAt_injective
#print axioms PF.KMS.localAt_injective_fin
#print axioms PF.KMS.localAt_reflects_not_commute
#print axioms PF.KMS.site_region_has_noncommuting_pair
#print axioms PF.KMS.modular_flow_separates_regions_at_site
#print axioms PF.KMS.localAt_injectivity_bundle
