# feat(Analysis/CStarAlgebra): unitary classification of unital `*`-homs `Mₙ(ℂ) → M_{kn}(ℂ)`

**STATUS: DRAFT — NOT SUBMITTED. Awaiting author decision + multi-model vetting, and a rebuild against mathlib master.**

## What this adds

Any two unital `*`-homomorphisms `φ, ψ : Mₙ(ℂ) → M_{kn}(ℂ)` are conjugate by a
unitary:

```
theorem unital_star_hom_inner_unique
    (φ ψ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] Matrix (Fin (k*n)) (Fin (k*n)) ℂ) :
    ∃ U, U * star U = 1 ∧ star U * U = 1 ∧ ∀ x, φ x = U * ψ x * star U
```

and every such `*`-hom is unitarily equivalent to the standard `k`-fold
block-diagonal amplification `blockDiagonalStarAlgHom` — so `Mₙ(ℂ)` has exactly
one unital `*`-representation of each multiplicity `k` up to unitary equivalence,
with the amplification a complete set of representatives.

## Why it is not already in mathlib (delta vs master, checked 2026-10-09)

Master has Noether–Skolem for the **automorphism** case only:
- `StarAlgEquiv.eq_linearIsometryEquivConjStarAlgEquiv` (PR #33017) —
  `(V →L[𝕜] V) ≃⋆ₐ[𝕜] (W →L[𝕜] W)` continuous `⇒ f = U.conjStarAlgEquiv`.
- `AlgEquiv.eq_linearEquivConjAlgEquiv` (PR #28100) — non-star version.

Both require `f` **bijective** (an equivalence). The present result concerns
unital `*`-**homs** that are injective but not surjective (`k > 1`), i.e. the
amplification/embedding case those theorems do not reach. The `k = 1`
specialisation recovers the automorphism statement; the content is general `k`.
This is the rigidity the UHF/Glimm direct-limit construction consumes, and
mathlib currently has no `IsInner` predicate and no amplification classification.

## Proof outline (classical)

matrix-unit calculus (`E_of_*`) → projection-trace count fixing the multiplicity
→ orthonormal basis built from the `*`-hom image (`phiONB`) → change-of-basis
unitary (`unitaryOfONBpair`) → conjugation identity → capstone.

## Provenance

Extracted PF-free from a research development (the Glimm `3^∞` UHF classification),
where it is the inductive embedding step. The proofs import only mathlib and are
axiom-clean (`[propext, Classical.choice, Quot.sound]`) against pinned mathlib
`eed770a4`. Apache-2.0, author Pablo Cohen.

## Remaining before this is PR-ready (NOT done in this draft)

1. Rebuild and re-verify against mathlib **master** (checked on the pin only).
2. mathlib conventions: drop the `PrincipiaTractalis.SubstrateRigidity` namespace;
   rename to `Matrix.*`; relocate the generic matrix-unit lemmas to their proper
   file; bundle the conclusion via `unitary (M_{kn}(ℂ))` / `conjStarAlgEquiv` to
   match #33017's shape rather than a raw `U` with two cancellation sides.
3. Confirm master has no rectangular/amplification form anywhere (not just in the
   one file inspected).
4. CLA, fork, branch — the external submission, author-gated.

Candidate source staged at `mathlib_candidates/NoetherSkolemAmplification.lean`
(proof region byte-identical to the verified `PF/Upstream/NoetherSkolemC2.lean`).
