/-
# r351 — The ternary local net over an arbitrary site set

★ 2026-10-25 — emergent locality, second brick: from two factors to an indexed
family of ternary sites ★

## What this adds to r350

`r350` proved the commutation axiom for the two-factor case
(`A ⊗ B`, left observables commute with right ones) and showed it is
non-vacuous (within one ternary site, observables need not commute). That is
the right first object but it is not yet a *net*: a net assigns an algebra to
each region of an index set.

This file does the indexed version. The substrate over a site set `ι` is

    𝒜(ι) = ⨂[ℂ] (_ : ι), M₃(ℂ)

one ternary tensor factor per site, and the local algebra at site `i` is the
image of `PiTensorProduct.singleAlgHom i`, i.e. `a ↦ 1 ⊗ ⋯ ⊗ a ⊗ ⋯ ⊗ 1` with
`a` in slot `i`. The locality axiom then reads: **observables at distinct sites
commute**, for any `i ≠ j` in any index set.

The index set is arbitrary — `Fin k`, `ℕ`, or anything else — so this covers
the whole substrate tower `M_{3^k} ≅ ⊗_{i<k} M₃` uniformly rather than one
level at a time.

## Why the proof is short, and what carries the content

`singleAlgHom i a = tprod (Pi.mulSingle i a)`, so two local observables are
`tprod` of two functions that are `1` away from a single slot. mathlib's
`Commute.tprod` lifts a pointwise commutation in `Π i, A i` to the tensor
product, and for `i ≠ j` the pointwise check is trivial: at `i` it is
`a · 1 = 1 · a`, at `j` it is `1 · b = b · 1`, elsewhere `1 · 1`. So the
mathematical content is exactly "disjoint supports commute", and the tensor
product does the rest.

That is the point worth keeping: locality here is **not** an axiom imposed on
the substrate. It is a consequence of the substrate being a tensor product over
sites, and the proof is short precisely because the structure already contains
it.

## What is and is not claimed

**Claimed.** For any index set `ι` with decidable equality and any `i ≠ j`,
observables localised at sites `i` and `j` in the ternary substrate commute;
equivalently, the local subalgebras at distinct sites commute elementwise. The
local algebras are genuine subalgebras, being ranges of algebra homomorphisms.

**Not claimed.**

1. **No spacetime.** "Site" is an index, not a point of a manifold; "distinct"
   is inequality of indices, not spacelike separation. No metric, no causal
   order, no dimension, nothing that produces a point. Unchanged from r350.
2. **Not the full Haag–Kastler net.** Isotony for *regions* (`S ⊆ T ⇒
   𝒜(S) ⊆ 𝒜(T)` for subsets `S, T ⊆ ι`) needs the region-indexed algebra
   `𝒜(S) = ⨂_{i∈S} M₃` and the inclusion maps between them; that is a further
   construction and is not here. Covariance needs a group acting on sites —
   which for the full substrate runs into the `Aut(T_∞)` problem recorded at
   ch04:461 and is not expressible at this pin (mathlib: UHF = 0 files).
   Additivity is likewise absent.
3. **Non-vacuity is at the site level, not lifted into the net.** `r350`'s
   `within_region_not_commutative` shows `M₃(ℂ)` itself is non-commutative, so
   the locality statement has content. Transporting that *into* the net — i.e.
   showing `singleAlgHom i E₀₁` and `singleAlgHom i E₁₁` fail to commute in
   `𝒜(ι)` — would need injectivity of `singleAlgHom`, which is not available
   here and is not assumed.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-25.
-/

import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace TernaryLocalNet

open PiTensorProduct
open scoped TensorProduct

/-! ## §1 — The substrate over a site set -/

/-- **One ternary site**: the algebra `M₃(ℂ)`. -/
abbrev Site : Type := Matrix (Fin 3) (Fin 3) ℂ

variable (ι : Type*) [DecidableEq ι]

/-- **The substrate algebra over the site set `ι`**: one ternary factor per
site. At `ι = Fin k` this is the tower level `M_{3^k} ≅ ⊗_{i<k} M₃`. -/
abbrev SubstrateNet : Type _ := ⨂[ℂ] (_ : ι), Site

/-- **The local algebra at site `i`**, as an algebra homomorphism into the
substrate: `a ↦ 1 ⊗ ⋯ ⊗ a ⊗ ⋯ ⊗ 1` with `a` in slot `i`. -/
noncomputable abbrev localAt (i : ι) : Site →ₐ[ℂ] SubstrateNet ι :=
  singleAlgHom (R := ℂ) (A := fun _ : ι => Site) i

/-! ## §2 — Locality: distinct sites commute -/

/-- **★★★ Locality for the ternary net.**

Observables localised at distinct sites commute.

The proof is three lines of content. `singleAlgHom i a = tprod (mulSingle i a)`
(`singleAlgHom` is `@[simps]`), so two local observables are `tprod` of
functions that are `1` away from a single slot. `Commute.tprod` reduces the
goal to a pointwise commutation in `Π i, Site`, and for `i ≠ j` the three cases
are `a · 1 = 1 · a` at `i`, `1 · b = b · 1` at `j`, and `1 · 1` elsewhere.

So locality is a consequence of the substrate being a tensor product over
sites, not an axiom imposed on it — the proof is short precisely because the
structure already contains it. -/
theorem local_commute {i j : ι} (hij : i ≠ j) (a b : Site) :
    Commute (localAt ι i a) (localAt ι j b) := by
  simp only [localAt, singleAlgHom_apply]
  apply Commute.tprod
  funext k
  simp only [Pi.mul_apply, MonoidHom.mulSingle_apply]
  by_cases hki : k = i
  · subst hki
    rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij]
    simp
  · by_cases hkj : k = j
    · subst hkj
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hki]
      simp
    · -- Both factors are `1` at this `k`, so `rw` closes the goal by `rfl`
      -- and no `simp` is needed (one here reports "no goals").
      rw [Pi.mulSingle_eq_of_ne hki, Pi.mulSingle_eq_of_ne hkj]

/-- **The local subalgebras at distinct sites commute elementwise.**

The same statement at the level of subalgebras: the ranges of `localAt i` and
`localAt j` consist of mutually commuting observables. -/
theorem localAt_range_commute {i j : ι} (hij : i ≠ j)
    {x y : SubstrateNet ι}
    (hx : x ∈ (localAt ι i).range) (hy : y ∈ (localAt ι j).range) :
    Commute x y := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact local_commute ι hij a b

/-! ## §3 — Capstone -/

/-- **The ternary local net satisfies the locality (Einstein causality)
axiom**, over an arbitrary site set.

Clause 1: observables at distinct sites commute.
Clause 2: the same elementwise between the local subalgebras.

Isotony over regions, covariance and additivity are not here; see the header's
"Not claimed". -/
theorem ternary_net_locality :
    (∀ (i j : ι), i ≠ j → ∀ a b : Site,
      Commute (localAt ι i a) (localAt ι j b)) ∧
    (∀ (i j : ι), i ≠ j → ∀ x y : SubstrateNet ι,
      x ∈ (localAt ι i).range → y ∈ (localAt ι j).range → Commute x y) :=
  ⟨fun _ _ hij _ _ => local_commute ι hij _ _,
   fun _ _ hij _ _ hx hy => localAt_range_commute ι hij hx hy⟩

end TernaryLocalNet
end PrincipiaTractalis

/-! ## §Axiom check -/

#print axioms PrincipiaTractalis.TernaryLocalNet.local_commute
#print axioms PrincipiaTractalis.TernaryLocalNet.localAt_range_commute
#print axioms PrincipiaTractalis.TernaryLocalNet.ternary_net_locality
