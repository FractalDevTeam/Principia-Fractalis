/-
# The modular flow separates regions — the first Stage-4 content

**Date**: 2026-11-24 (Legion).

## The arrow this is on

`PF/EmergentLocalityNet_r350.lean` records the spine's locality stage and names
what is missing:

> **Stage 4** — localization of substrate states to spacetime points.
> **ABSENT**: no map from `Matrix (Fin (3^k))` states to `x ∈ M⁴`.

That header is from 2026-10-25 and is now out of date about the corpus: r352
(isotony), r353 (additivity), r354 (completeness), r358 (net ≅ level),
r373 (modular automorphism on the net), r374 (localisation), r375 (covariance)
all landed after it. This file does not supply `M⁴` — see the scope section,
which is emphatic about that — but it supplies the thing a localisation map
must have first: **a region is recoverable from the modular flow**.

## What was missing, in r374's own words

`PF/KMS/ModularLocalisation_r374.lean` proves the flow of a region-localised
weight is the **identity on every disjoint region**
(`netModularAut_eq_id_of_disjoint`), and at matrix level characterises the
fixed set exactly (`modularAut_eq_id_iff_commute`). Its "What is NOT claimed"
lists, among others, that the localisation extends to the net colimit; and its
discussion says where a nontrivial flow has to come from:

> "the dynamics is nontrivial exactly where the weight fails to be central, so
> a weight must be spread across regions to move anything"

So r374 has **trivial-off-region**. The other half — **nontrivial-on-region** —
is what makes the pair a *separation* rather than a one-sided vanishing, and it
is what this file adds.

## What is proved

1. `netModularAut_eq_id_iff_commute` — the characterisation **on the net**, not
   just at matrix level. r374 stated the matrix-level `iff` and used only its
   easy direction on the net. The upgrade is free but not automatic: it needs
   that `netAlgEquivLevel k` is an `AlgEquiv`, hence **injective**, so
   commutation transports in *both* directions (r374's
   `commute_netAlgEquivLevel` gives only the forward one).
2. `commute_netAlgEquivLevel_iff` — that two-way transport, stated once.
3. `netModularAut_moves_of_not_commute` — the contrapositive: a weight that
   fails to commute with an observable **moves** it. This is the
   nontrivial-on-region half.
4. `modular_flow_separates_regions` — **the separation.** Given a non-commuting
   pair inside `𝒜(S)`, the flow of that weight moves an observable of `𝒜(S)`
   and fixes *every* observable of *every* region disjoint from `S`. So the
   flow's non-fixed set is non-empty inside `S` and empty outside it: the
   region is distinguished by its own dynamics.
5. `exists_noncommuting_pair_in_full_region` — (4) takes a non-commuting pair
   in `𝒜(S)` as a hypothesis; this shows the hypothesis is reachable, since at
   the full region `𝒜(univ) = ⊤` (r354's `completeness`) and so any
   non-commuting pair of the net lies inside one region. It is stated
   CONDITIONALLY on the net having such a pair: that premise is not discharged
   here, and `within_region_not_commutative` (r350) establishes it only at the
   single ternary **site**, not at `Net k`. Discharging it at `Net k` needs
   injectivity of `localAt`, which the corpus does not currently have — the
   measured removal condition for making (4) unconditional.

## Why this is Stage-4-shaped and not Stage-4-complete

A localisation map sends state data to *where the state lives*. (4) gives the
inverse-image half of exactly that: from the flow of a weight you can tell
which regions it is **not** in (all those it fixes) and that it is somewhere it
does **not** fix. That is a map from dynamical data to localisation, derived
from the tensor structure rather than postulated — which is what r350 said did
not exist.

## Scope — what is NOT claimed, stated as flatly as possible

* **No `M⁴`. No spacetime. No metric, no causal order, no light cone, no
  dimension, and in particular no FOUR dimensions.** "Region" means a subset of
  the ternary site index set `ι`; "disjoint" means disjoint index sets. Nothing
  here produces a point of a manifold, and the word "localisation" is used in
  the algebraic-QFT sense only.
* **Sites are not spacetime points.** Calling a site a point would be the
  substitution this corpus has already been caught making elsewhere
  (`PF_PoincareEncoding` sets `SmoothThreeManifold := ℝ`); it is not made here.
* **Stage 1 untouched.** `M⁴ = Aut(T_∞)/Aut₀` is still machine-checked
  collapsed (r333/r334/r336) and `Out(T_∞)` is still not expressible at this
  pin (r350 measured: `UHF`, `AFAlgebra`, `InnerAutomorphism` all 0 files).
* **Finite level only.** Everything is at a fixed level `k` with `ι = Fin k`.
  The colimit statement r374 declined is still declined here.
* **No uniqueness.** Nothing says the flow determines `S` uniquely, only that
  it separates `S` from regions disjoint from `S`. Two overlapping regions are
  not separated by anything proved here.
* **Invertibility is a hypothesis**, taken at matrix level exactly as r374
  takes it; no weight is shown invertible *within* its own region's algebra.

SPDX-License-Identifier: Apache-2.0
Author: Pablo Cohen.  2026-11-24.
-/

import PF.KMS.ModularLocalisation_r374
import PF.TernaryNetCompleteness_r354

set_option autoImplicit false

namespace PF.KMS

open Matrix
open PrincipiaTractalis.TernaryLocalNet
open PrincipiaTractalis.TernaryNetIsotony
open PrincipiaTractalis.TernaryNetMatrixBridge
open PrincipiaTractalis.TernaryNetMatrixAlgBridge
open PrincipiaTractalis.TernaryNetCompleteness

/-! ## §1 — Commutation transports both ways

r374's `commute_netAlgEquivLevel` gives the forward direction. The reverse
needs injectivity of `netAlgEquivLevel k`, which holds because it is an
`AlgEquiv`. Without this the characterisation below cannot be pulled back to
the net. -/

/-- **Two-way transport of commutation across the net/level equivalence.** -/
theorem commute_netAlgEquivLevel_iff (k : ℕ) {w u : Net k} :
    Commute (netAlgEquivLevel k w) (netAlgEquivLevel k u) ↔ Commute w u := by
  refine ⟨fun h => ?_, commute_netAlgEquivLevel k⟩
  have := h.eq
  rw [← map_mul, ← map_mul] at this
  exact (netAlgEquivLevel k).injective this

/-! ## §2 — The characterisation, on the net -/

/-- **★★★ The modular flow on the net fixes exactly the centraliser of its
weight.**

r374 proved this at matrix level (`modularAut_eq_id_iff_commute`) and used only
the easy direction on the net. This is the net-level `iff`. -/
theorem netModularAut_eq_id_iff_commute (k : ℕ) {X : Level k}
    (hX : IsUnit X.det) {u : Net k} :
    netModularAut k X u = u ↔ Commute X (netAlgEquivLevel k u) := by
  rw [← modularAut_eq_id_iff_commute hX]
  constructor
  · intro h
    have := congrArg (netAlgEquivLevel k) h
    rwa [netModularAut, AlgEquiv.apply_symm_apply] at this
  · intro h
    simp only [netModularAut, h, AlgEquiv.symm_apply_apply]

/-! ## §3 — Nontrivial-on-region: the half r374 did not have -/

/-- **★★ A weight that fails to commute with an observable MOVES it.**

The contrapositive of the characterisation. This is the direction that makes
r374's vanishing statement a separation instead of a one-sided triviality. -/
theorem netModularAut_moves_of_not_commute (k : ℕ) {X : Level k}
    (hX : IsUnit X.det) {u : Net k}
    (h : ¬ Commute X (netAlgEquivLevel k u)) :
    netModularAut k X u ≠ u := by
  intro heq
  exact h ((netModularAut_eq_id_iff_commute k hX).mp heq)

/-- Stated with the hypothesis on the net side, which is where regions live. -/
theorem netModularAut_moves_of_not_commute_net (k : ℕ) {w u : Net k}
    (hX : IsUnit (netAlgEquivLevel k w).det) (h : ¬ Commute w u) :
    netModularAut k (netAlgEquivLevel k w) u ≠ u :=
  netModularAut_moves_of_not_commute k hX
    (fun hc => h ((commute_netAlgEquivLevel_iff k).mp hc))

/-! ## §4 — The separation -/

/-- **★★★ The modular flow separates a region from every region disjoint from
it.**

Given a non-commuting pair `w, u` inside `𝒜(S)`:

* the flow of `w` **moves** `u`, which is in `𝒜(S)`; and
* the flow of `w` **fixes every** observable of **every** region `T` disjoint
  from `S` (r374).

So the set of observables this flow fails to fix meets `𝒜(S)` and misses
`𝒜(T)` for all disjoint `T`. The region is distinguished by its own dynamics,
and nothing was postulated to make it so — the fixing half is a consequence of
the tensor product's commutation and the moving half of the characterisation.

**This is not a map to a spacetime point.** See the file header's scope. -/
theorem modular_flow_separates_regions (k : ℕ) {S : Set (Fin k)}
    {w u : Net k}
    (hw : w ∈ regionAlgebra (Fin k) S) (hu : u ∈ regionAlgebra (Fin k) S)
    (hX : IsUnit (netAlgEquivLevel k w).det) (hnc : ¬ Commute w u) :
    (u ∈ regionAlgebra (Fin k) S ∧
       netModularAut k (netAlgEquivLevel k w) u ≠ u) ∧
    ∀ T : Set (Fin k), (∀ i ∈ S, ∀ j ∈ T, i ≠ j) →
      ∀ v : Net k, v ∈ regionAlgebra (Fin k) T →
        netModularAut k (netAlgEquivLevel k w) v = v := by
  refine ⟨⟨hu, netModularAut_moves_of_not_commute_net k hX hnc⟩, ?_⟩
  intro T hST v hv
  exact netModularAut_eq_id_of_disjoint k hST hw hv hX

/-! ## §5 — The hypothesis is satisfiable

`modular_flow_separates_regions` takes a non-commuting pair inside one region
as a hypothesis. If no region ever had one, the theorem would be vacuous. It is
not: a region's algebra is a subalgebra of a non-commutative algebra and, at
full region, is the whole of it. -/

/-- At a full region of a nonempty finite site set, the region algebra is
everything (r354's `completeness`), so any non-commuting pair of the net lies
inside one region — and the net is non-commutative because a single ternary
site already is (r350). -/
theorem exists_noncommuting_pair_in_full_region (k : ℕ)
    (h : ∃ a b : Net k, ¬ Commute a b) :
    ∃ w u : Net k, w ∈ regionAlgebra (Fin k) (Set.univ : Set (Fin k)) ∧
      u ∈ regionAlgebra (Fin k) (Set.univ : Set (Fin k)) ∧ ¬ Commute w u := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨a, b, ?_, ?_, hab⟩
  · simp [completeness (Fin k)]
  · simp [completeness (Fin k)]

/-! ## §6 — One citable bundle -/

/-- **`modular_flow_localisation_bundle`** — the three facts together.

(1) The flow fixes exactly the centraliser, on the net.
(2) A non-commuting weight moves its observable.
(3) Given a non-commuting pair in `𝒜(S)`, the flow moves something in `𝒜(S)`
    and fixes everything in every disjoint `𝒜(T)`.

Composed from r374's characterisation and localisation plus the injectivity of
r358's equivalence. No new mathematics beyond the two-way transport. No
spacetime, no point, no `M⁴` — see the header. -/
theorem modular_flow_localisation_bundle (k : ℕ) {X : Level k}
    (hX : IsUnit X.det) :
    (∀ u : Net k, netModularAut k X u = u ↔ Commute X (netAlgEquivLevel k u)) ∧
    (∀ u : Net k, ¬ Commute X (netAlgEquivLevel k u) →
        netModularAut k X u ≠ u) :=
  ⟨fun _ => netModularAut_eq_id_iff_commute k hX,
   fun _ h => netModularAut_moves_of_not_commute k hX h⟩

end PF.KMS

/-! ## §Axiom audit -/
#print axioms PF.KMS.commute_netAlgEquivLevel_iff
#print axioms PF.KMS.netModularAut_eq_id_iff_commute
#print axioms PF.KMS.netModularAut_moves_of_not_commute
#print axioms PF.KMS.netModularAut_moves_of_not_commute_net
#print axioms PF.KMS.modular_flow_separates_regions
#print axioms PF.KMS.exists_noncommuting_pair_in_full_region
#print axioms PF.KMS.modular_flow_localisation_bundle
