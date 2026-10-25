/-
# r350 — Emergent locality, first Lean content: the ternary local net

★ 2026-10-25 — the spine arrow with zero files gets its first theorem ★

## Where this arrow stood before this file

"Emergent locality" appears **once** in the whole corpus
(`codex/COSMOLOGY_DE_ROUTE_MAP_2026-10-11.md:16`, in a one-line spine sketch),
**zero** times in the 36 manuscript chapters, and **zero** times in Lean. It is
the only spine arrow with no formal content at all.

The route map gives the intended construction and its status:

* **Stage 1** — spacetime emergence `M⁴ = Aut(T_∞)/Aut₀`. **Collapsed, and the
  collapse is machine-checked.** `Aut₀` (trace-preserving) is not a proper
  subgroup: r113 proved `τ_UHF` is the UNIQUE tracial state, so `trace_preserved`
  (r333) gives `Aut₀ = Aut` and the quotient is a single point
  (`inducedTraces_encard_eq_one`). r334 exhibits a non-identity inner
  automorphism the trace cannot see; r335 kills the K-theoretic repair the same
  way. ch04:461 records all of this. The **live candidate** named there is
  `M⁴ = Aut(T_∞)/Inn(T_∞) = Out(T_∞)`.
* **Stage 4** — localization of substrate states to spacetime points.
  **ABSENT**: no map from `Matrix (Fin (3^k))` states to `x ∈ M⁴`.

**Why this file does not attempt stage 1.** `Out(T_∞)` is not expressible at
this mathlib pin: measured, `UHF` = 0 files, `ApproximatelyFinite` = 0,
`AFAlgebra` = 0, `InnerAutomorphism` = 0. There is no inductive-limit
C\*-algebra theory to quotient. Attempting it would produce another stub, and
this corpus already has five of those.

## What locality means here, and why this is the right first object

In algebraic quantum field theory, locality is not a statement about points —
it is the **net structure**: a map from regions to observable algebras such that
observables in *disjoint* regions **commute** (Einstein causality). Spacetime is
recovered *from* the net, not presupposed by it. So the net is logically prior
to stage 1, and it is the part the ternary substrate supplies directly.

The substrate's level-`k` algebra is `M_{3^k} ≅ ⊗_{i<k} M_3`: one tensor factor
per ternary site. Disjoint sets of sites give commuting subalgebras, and that
commutation is **not postulated** — it is a consequence of the tensor product.
That is emergent locality in the only sense available before a metric exists.

## What makes it non-vacuous

A locality statement is empty if everything commutes. It does not here:

* **across regions** — `disjoint_regions_commute`: always commute.
* **within a region** — `within_region_not_commutative`: the single ternary site
  `M_3` already contains non-commuting observables (explicit matrix units).

So the net separates: commutation is exactly a statement about disjointness,
which is the content of Einstein causality. The within-region witness follows
`SubstrateNotCommutative_r217`'s construction at a single site.

## What is and is not claimed

**Claimed.** For the ternary substrate, observables localised in disjoint
tensor factors commute, for arbitrary algebras and at the concrete ternary site;
and within one site they need not, so the statement has content.

**Not claimed.**

1. **No spacetime.** No manifold, no metric, no causal order, no light cone, no
   dimension. "Disjoint" here means disjoint *index sets of tensor factors*, not
   spacelike-separated regions of a spacetime. Nothing here produces a point.
2. **Stage 1 untouched.** `M⁴ = Out(T_∞)` is neither advanced nor refuted; it is
   not expressible at this pin (see above).
3. **Stage 4 untouched.** No localisation map from substrate states to points.
4. **Not the full net.** A Haag–Kastler net requires isotony, covariance and
   additivity over a directed family of regions. This file proves the
   commutation axiom for the two-factor case and instantiates it; the
   indexed-family version over `Finset ℕ` is the natural next step and is not
   done here.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-25.
-/

import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace EmergentLocalityNet

open Matrix Algebra.TensorProduct
open scoped TensorProduct

/-! ## §1 — Locality: disjoint regions commute

The general statement first, because it is the one with content: it holds for
ANY two algebras over a commutative base, which is why the substrate gets
locality for free from its tensor structure rather than by assumption. -/

variable {R A B : Type*} [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

/-- **★★★ Einstein causality for the tensor net.**

An observable localised in the left region and one localised in the right
region commute. These are exactly `Algebra.TensorProduct.includeLeft a` and
`includeRight b` written out (`includeLeft a = a ⊗ₜ 1`,
`includeRight b = 1 ⊗ₜ b`); stating them directly avoids `includeLeft`'s extra
scalar parameter and its instance side conditions, which carry no content here.
They commute because `a` commutes with `1` and `1` commutes with `b` — the
content is carried entirely by `Commute.tmul`, i.e. by the tensor product's
multiplication rule `(a₁ ⊗ b₁)(a₂ ⊗ b₂) = (a₁a₂) ⊗ (b₁b₂)`.

Nothing is postulated: locality is a theorem about the substrate's algebra. -/
theorem disjoint_regions_commute (a : A) (b : B) :
    Commute (a ⊗ₜ[R] (1 : B)) ((1 : A) ⊗ₜ[R] b) :=
  (Commute.one_right a).tmul (Commute.one_left b)

/-! ## §2 — The ternary site, concretely

`M_3` is the algebra of one ternary site: the substrate's level-`k` algebra is
`M_{3^k} ≅ ⊗_{i<k} M_3`, one factor per site. -/

/-- **The single ternary site algebra** `M_3(ℂ)`. -/
abbrev Site : Type := Matrix (Fin 3) (Fin 3) ℂ

/-- **Two disjoint ternary sites**, as the two tensor factors. -/
abbrev TwoSites : Type := TensorProduct ℂ Site Site

/-- **Locality at the ternary substrate.** Observables at two distinct sites
commute. This is `disjoint_regions_commute` at `A = B = M_3(ℂ)`. -/
theorem ternary_sites_commute (a b : Site) :
    Commute (a ⊗ₜ[ℂ] (1 : Site)) ((1 : Site) ⊗ₜ[ℂ] b) :=
  disjoint_regions_commute a b

/-! ## §3 — Non-vacuity: within one site, observables need NOT commute

Without this the locality statement would be empty. A single ternary site
already fails to be commutative, following `SubstrateNotCommutative_r217`'s
matrix-unit construction at `k = 1`. -/

/-- The matrix unit `E₀₁` at a ternary site. -/
def E01 : Site := single 0 1 (1 : ℂ)

/-- The matrix unit `E₁₁` at a ternary site. -/
def E11 : Site := single 1 1 (1 : ℂ)

theorem E01_mul_E11 : E01 * E11 = E01 := by
  unfold E01 E11
  rw [single_mul_single_same, mul_one]

theorem E11_mul_E01 : E11 * E01 = 0 := by
  unfold E01 E11
  exact single_mul_single_of_ne (1 : ℂ) 1 1 0 (by decide) (1 : ℂ)

/-- `E₀₁ ≠ 0`, so the two products above are genuinely different. -/
theorem E01_ne_zero : E01 ≠ 0 := by
  unfold E01
  intro h
  have := congrFun (congrFun h 0) 1
  simp [single] at this

/-- **★★ Within one ternary site, observables need not commute.**

So `disjoint_regions_commute` is a statement about DISJOINTNESS, not a triviality
about the algebra: commutation holds across sites and can fail within one. That
is exactly the content of Einstein causality. -/
theorem within_region_not_commutative : ¬ Commute E01 E11 := by
  intro h
  have h1 : E01 * E11 = E01 := E01_mul_E11
  have h2 : E11 * E01 = 0 := E11_mul_E01
  have : E01 = 0 := by
    rw [← h1, h.eq, h2]
  exact E01_ne_zero this

/-! ## §4 — Capstone -/

/-- **Emergent locality, first content.**

(1) Observables in disjoint regions commute — for arbitrary algebras, hence for
    the substrate, as a consequence of the tensor structure and not a postulate.
(2) The same holds concretely at two ternary sites.
(3) Within one ternary site, observables need not commute — so (1) is a
    statement about disjointness and has content.

No spacetime, no metric, no point: see the header's "Not claimed". -/
theorem emergent_locality_net_first_content :
    (∀ a b : Site,
      Commute (a ⊗ₜ[ℂ] (1 : Site)) ((1 : Site) ⊗ₜ[ℂ] b)) ∧
    (¬ Commute E01 E11) :=
  ⟨ternary_sites_commute, within_region_not_commutative⟩

end EmergentLocalityNet
end PrincipiaTractalis

/-! ## §Axiom check -/

#print axioms PrincipiaTractalis.EmergentLocalityNet.disjoint_regions_commute
#print axioms PrincipiaTractalis.EmergentLocalityNet.ternary_sites_commute
#print axioms PrincipiaTractalis.EmergentLocalityNet.within_region_not_commutative
#print axioms PrincipiaTractalis.EmergentLocalityNet.emergent_locality_net_first_content
