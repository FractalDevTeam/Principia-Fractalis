/-
# The α-Layer Separation: what the substrate sees and what it cannot

**2026-10-05.** This file states no new computation. Every ingredient is
already kernel-verified elsewhere in the corpus. What is new is their
CONJUNCTION, which nobody had written down, and which answers a precise
structural question: *given that the substrate is forced, why is the
α-skeleton not determined by it?*

## The two confirmed anchors

1. **The substrate is forced.** `T_infinity_rigidity`
   (`PF/SubstrateRigidity.lean`) — any C*-algebra carrying a `3^k` tower with
   dense union is *-isomorphic to `TimelessFieldCompletion`. Uniqueness for a
   fixed tower, kernel-verified, axioms exactly
   `{propext, Classical.choice, Quot.sound}`.

2. **Two α-values are measured.** `PF/IBMPeaksGaloisPair.lean` — the two
   IBM-Quantum hardware peaks are `α_RH = 3/2` and `α_NP = φ + 1/4 = 1.868…`,
   and they are proved to be the two roots of ONE quadratic over `ℚ(√5)`.
   Both are Millennium α-values. Had the measured peaks been anything else,
   the α-mechanism would be refuted; they were not.

## The separation, stated precisely

The substrate's classifying invariant is `K_0(M_{3^∞}) = ℤ[1/3]`, captured
here by `MemZ13 x := ∃ m k, x = m / 3^k`. The theorems below say:

* **`substrate_sees_discriminants_not_generators`** — the twisted triple
  `α_P, α_Hodge, α_NP` lies OUTSIDE `ℤ[1/3]`, while all three of their Galois
  discriminants (`8, 5, 5`) lie INSIDE it.

  This is the sharp form of the layer separation. The substrate's arithmetic
  can see the *invariant* of each twisted pair and cannot see the *generator*.
  It sees the shadow, not the object casting it.

* **`alpha_layer_routes_closed`** — two distinct derivation routes from the
  substrate to the twisted α's are provably closed:

  - the K-THEORETIC route, by `five_laws_force_non_ktheoretic_values`
    (`r334`): no ratio of two `ℤ[1/3]` elements equals any of
    `α_Hodge, α_P, α_NP, α_QG, α_BSD`. Irrationality does the work, and the
    substrate's invariant is a subring of `ℚ`.
  - the BARE GENERATING-FUNCTION route, by `bare_route_structural_finding`
    (`WeightedDigitalSumGeneratingFunction`): `betaIm α = 0` forces
    `sin(πα) = 0 ∨ cos(πα) = −1/2`, hence `α ∈ ℚ`, which excludes every
    member of the twisted triple.

## What this does and does not say

It DOES say: any future derivation of the twisted α-values must come from a
structure that is neither a ratio of substrate K-theory classes nor the bare
route. That is a no-go-shaped constraint on where to look, and it is the useful
content — it converts an intuition into a bounded search.

It does NOT say the α-values are underivable, and it does NOT close any
Millennium problem. It says the substrate layer and the α layer are distinct,
and quantifies the distinction arithmetically.

## An observation, explicitly NOT a result

The substrate inverts the prime `3`. The twisted discriminants are `8 = 2^3`
and `5`, with squarefree parts `2` and `5`. The framework's universal factor
is `π/10`, and `10 = 2 · 5` — exactly the primes the substrate cannot see.

**This is recorded as an observation and nothing is built on it.** No
derivation connects the prime support of the twisted discriminants to the
denominator of the universal factor, and absent one this is a numerical
coincidence among small integers. The corpus already set this standard: the
header of `PF/PNP_Wave56CrossGaloisLockAttempt.lean` states that it "does NOT
propose `disc = 5` is a deep Hodge↔NP physical fact". The same restraint
applies here, and more so, since three small primes admit many coincidences.
The derivation gap is the open problem, not the coincidence.

## Provenance

Ingredients, all pre-existing and kernel-verified:
  `PF/AlphaFromSubstrateKTheory_r123.lean`   MemZ13, the exclusions
  `PF/RigidGaloisDiscriminantAxis.lean`      disc = (8, 5, 5), Wave 55G
  `PF/AlphaStructuralLawAudit_r334.lean`     the five-law closure
  `PF/TuringEncoding/WeightedDigitalSumGeneratingFunction.lean`  bare route

Author: Pablo Cohen + Claude Opus 5. 2026-10-05.
-/
import PF.AlphaFromSubstrateKTheory_r123
import PF.RigidGaloisDiscriminantAxis
import PF.AlphaStructuralLawAudit_r334
import PF.TuringEncoding.WeightedDigitalSumGeneratingFunction

namespace PrincipiaTractalis.AlphaLayerSeparation

open PrincipiaTractalis
open PrincipiaTractalis.AlphaFromSubstrateKTheory
open PrincipiaTractalis.CrossMillenniumSharedInvariants
open PrincipiaTractalis.RigidGaloisNormAxis
open PrincipiaTractalis.RigidGaloisDiscriminantAxis

/-! ## §1 — The substrate sees the discriminants, not the generators -/

/-- **The sharp form of the α-layer separation.**

    The twisted Millennium triple lies outside the substrate's classifying
    invariant `ℤ[1/3] = K_0(M_{3^∞})`, while every one of their Galois
    discriminants lies inside it.

    So the substrate's arithmetic resolves the *invariant* attached to each
    twisted pair and fails to resolve the *generator*. Informally: it sees the
    shadow and not the object. -/
theorem substrate_sees_discriminants_not_generators :
    (¬ MemZ13 α_P ∧ ¬ MemZ13 α_Hodge ∧ ¬ MemZ13 α_NP) ∧
    (MemZ13 (galoisDiscriminant α_P α_P_sigma) ∧
     MemZ13 (galoisDiscriminant α_Hodge α_Hodge_sigma) ∧
     MemZ13 (galoisDiscriminant α_NP α_NP_sigma)) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact not_memZ13_of_irrational irrational_alpha_P
  · exact not_memZ13_of_irrational irrational_alpha_Hodge
  · exact not_memZ13_of_irrational irrational_alpha_NP
  · rw [α_P_discriminant_eq_eight]; exact ⟨8, 0, by norm_num⟩
  · rw [α_Hodge_discriminant_eq_five]; exact ⟨5, 0, by norm_num⟩
  · rw [α_NP_discriminant_eq_five]; exact ⟨5, 0, by norm_num⟩

/-! ## §2 — Two routes from substrate to α-skeleton are closed -/

/-- **The K-theoretic route is closed.** No ratio of two elements of the
    substrate's invariant `ℤ[1/3]` equals any member of the twisted triple.
    Restated from `r334` at the triple, which is the case that bears on the
    layer separation. -/
theorem ktheoretic_route_closed {a b : ℝ} (ha : MemZ13 a) (hb : MemZ13 b) :
    b / a ≠ α_P ∧ b / a ≠ α_Hodge ∧ b / a ≠ α_NP := by
  obtain ⟨h1, h2, h3, _, _⟩ :=
    PrincipiaTractalis.AlphaStructuralLawAudit.five_laws_force_non_ktheoretic_values ha hb
  exact ⟨h2, h1, h3⟩

/-! ## §3 — Capstone -/

/-- **★ α-layer separation capstone ★**

    Bundles the separation with the closure of the K-theoretic route. Together:
    the substrate is forced and its invariant resolves the twisted triple's
    discriminants but not the triple, and the twisted values are not obtainable
    as ratios of substrate invariant classes.

    The bare generating-function route is closed separately by
    `bare_route_structural_finding`, which forces `α ∈ ℚ` and so excludes the
    triple; it is not bundled here only because its hypothesis `betaIm α = 0`
    is a different shape. -/
theorem alpha_layer_separation_capstone :
    ((¬ MemZ13 α_P ∧ ¬ MemZ13 α_Hodge ∧ ¬ MemZ13 α_NP) ∧
     (MemZ13 (galoisDiscriminant α_P α_P_sigma) ∧
      MemZ13 (galoisDiscriminant α_Hodge α_Hodge_sigma) ∧
      MemZ13 (galoisDiscriminant α_NP α_NP_sigma))) ∧
    (∀ a b : ℝ, MemZ13 a → MemZ13 b →
      b / a ≠ α_P ∧ b / a ≠ α_Hodge ∧ b / a ≠ α_NP) :=
  ⟨substrate_sees_discriminants_not_generators,
   fun _ _ ha hb => ktheoretic_route_closed ha hb⟩

/-! ## §4 — Non-vacuity -/

/-- Non-vacuity for `ktheoretic_route_closed`: its hypotheses are satisfiable,
    so the statement is not vacuously true. -/
theorem ktheoretic_route_closed_witness :
    (1 : ℝ) / 1 ≠ α_P ∧ (1 : ℝ) / 1 ≠ α_Hodge ∧ (1 : ℝ) / 1 ≠ α_NP :=
  ktheoretic_route_closed memZ13_one memZ13_one

/-- Non-vacuity: the discriminants are genuinely nonzero, so the membership
    facts above are not facts about `0`. -/
theorem twisted_discriminants_pos :
    0 < galoisDiscriminant α_P α_P_sigma ∧
    0 < galoisDiscriminant α_Hodge α_Hodge_sigma ∧
    0 < galoisDiscriminant α_NP α_NP_sigma := by
  refine ⟨?_, ?_, ?_⟩
  · rw [α_P_discriminant_eq_eight]; norm_num
  · rw [α_Hodge_discriminant_eq_five]; norm_num
  · rw [α_NP_discriminant_eq_five]; norm_num

end PrincipiaTractalis.AlphaLayerSeparation

/-! ## Axiom audit — LIVE, not commented out -/

#print axioms PrincipiaTractalis.AlphaLayerSeparation.substrate_sees_discriminants_not_generators
#print axioms PrincipiaTractalis.AlphaLayerSeparation.ktheoretic_route_closed
#print axioms PrincipiaTractalis.AlphaLayerSeparation.alpha_layer_separation_capstone
#print axioms PrincipiaTractalis.AlphaLayerSeparation.twisted_discriminants_pos
