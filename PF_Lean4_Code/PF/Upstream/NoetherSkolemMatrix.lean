/-
Copyright (c) 2026 Pablo Cohen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Cohen
-/
import PF.Upstream.NoetherSkolemC2
import PF.Upstream.MathlibStarAlgebra

/-!
# Noether–Skolem for matrix *-algebras, in bundled form

The C2 arc of `PF/SubstrateRigidity.lean` proves Noether–Skolem for the
embeddings the Glimm `3^∞` classification needs, as
`unital_star_hom_inner_unique` (`:1412`): any two unital *-homs
`M_n(ℂ) →⋆ₐ[ℂ] M_{kn}(ℂ)` are conjugate by a unitary. Its conclusion is stated
as a raw conjunction — a matrix `U`, two cancellation identities, and a
pointwise equation.

**CORRECTED 2026-10-05 — MATHLIB HAS THIS, AND HAS SINCE DECEMBER 2025.**
The claim below was verified against the pinned revision `eed770a` and is false
of master. Verified against mathlib master (HEAD `9194f400a4`):

* `AlgEquiv.eq_linearEquivConjAlgEquiv` in
  `Mathlib/LinearAlgebra/GeneralLinearGroup/AlgEquiv.lean` — every algebra
  automorphism of an endomorphism algebra over a field is inner. PR #28100,
  merged 2025-12-08.
* `StarAlgEquiv.eq_linearIsometryEquivConjStarAlgEquiv` in
  `Mathlib/Analysis/Normed/Operator/ContinuousAlgEquiv.lean` — for
  finite-dimensional `V`, where continuity is automatic, this IS "every
  *-automorphism of `M_n(ℂ)` is inner via a unitary". PR #33017, merged
  2025-12-27.

Both by Monica Omar, the same author as `UnitaryStarAlgAut` — which is exactly
the risk that was flagged when this re-check was commissioned.

So `starAlgEquiv_eq_conj` below **duplicates mathlib** and must not be offered
upstream. The statements here remain correct Lean and the proofs are untouched;
what was false was the novelty claim around them. The lesson is the same one
this corpus has now learned three times in one day: **a pinned revision is
evidence about the pin, not about the library.**

What genuinely survives in this line, by exhaustive non-truncated search of
master: `IsDenseInducing.extendStarAlgHom` (absent); UHF / Glimm / supernatural
number content (absent from the entire 9366-file tree, with no
direct-limit-of-matrix-algebras construction anywhere under
`Analysis/CStarAlgebra`); no `IsInner` predicate; and no *general*
central-simple-algebra Skolem–Noether in mathlib, although the third-party
TauCeti project already has that. The project's real contribution is the UHF
substrate work, not this bundling.

Superseded claim, retained for provenance:

> "Mathlib has no Noether–Skolem theorem in any form. The only `Skolem` in
> the library is the unrelated model-theoretic Skolemisation in the `choose`
> tactic. There is no `IsInner`, no inner-automorphism machinery for algebras,
> and no statement that automorphisms of a matrix algebra are conjugations."

Of that paragraph, only two parts remain true: there is no `IsInner`
predicate, and the only `Skolem` *path* in the library is
`Mathlib/ModelTheory/Skolem.lean`. The rest is superseded.

This module restates the C2 result in the form the theorem is actually quoted
in, and draws the consequences the raw form leaves implicit:

## Main results

* `exists_unitary_conj` — the rectangular case, bundled: the witness is an
  element of `unitary (M_{kn}(ℂ))` and the conclusion is an application of
  `unitary.conjStarAlgEquiv`, so unitarity travels with the witness instead of
  being carried as two side conditions.

* `exists_unitary_conj_square` — the square case `M_n(ℂ) → M_n(ℓ)`, obtained
  from the rectangular case at `k = 1` through `exists_unitary_conj_of_dim`.

* `starAlgEquiv_eq_conj` — **the classical Noether–Skolem statement for
  `M_n(ℂ)`: every *-automorphism is inner.** An equation between
  star-algebra equivalences, not a pointwise identity: `f = conjStarAlgEquiv u`.
  This is the form the theorem is cited in, and it is not derivable from
  `unital_star_hom_inner_unique` without the `conjStarAlgEquiv` of
  `PF/Upstream/MathlibStarAlgebra.lean`, because there was previously no term
  on the right-hand side to equate `f` to.

* `exists_unitary_conj_blockDiagonal` — every unital *-hom
  `M_n(ℂ) → M_{kn}(ℂ)` is unitarily equivalent to the standard `k`-fold
  block-diagonal amplification. This pins down *all* such homs up to unitary
  equivalence, by combining C2 with the C1 arc's `blockDiagonalStarAlgHom`.

## Upstream status

**This module and its entire proof chain are now PF-free.** It imports
`PF.Upstream.NoetherSkolemC2` (the C1 and C2 arcs, extracted verbatim from
`SubstrateRigidity.lean` and depending only on mathlib) and
`PF.Upstream.MathlibStarAlgebra` (four star-algebra lemmas mathlib lacks, also
mathlib-only). There is no longer any path from these statements to the
substrate development.

Earlier on 2026-10-05 this section said the opposite -- that the proofs rested
on roughly 700 lines inside `SubstrateRigidity.lean` and that extracting them
was "a larger job ... not attempted here." That was true when written and is
false now. A dependency map of `SubstrateRigidity.lean` showed the two matrix
arcs borrow **nothing** from the rest of that file -- not one name -- so they
were never entangled with the substrate, merely co-located with it. The
extraction was a slice, not a rewrite, and the proof text is byte-identical.

**What still stands between this and a mathlib PR** is naming, not dependency:
the declarations sit in the PF-local namespace
`PrincipiaTractalis.SubstrateRigidity` and carry PF-local names. Upstreaming
needs mathlib naming and placement -- `Matrix.*`, with the matrix-unit calculus
C2.1–C2.5 going to the file where those lemmas belong. That is mechanical. The
part that actually blocked it is done.

Author: Pablo Cohen + Claude Opus 5. 2026-10-05.
-/

namespace PrincipiaTractalis.Upstream.NoetherSkolem

open PrincipiaTractalis.SubstrateRigidity

/-- **Noether–Skolem, rectangular bundled form.** Any two unital *-homs
`M_n(ℂ) →⋆ₐ[ℂ] M_{kn}(ℂ)` differ by conjugation by a unitary.

Same mathematical content as `unital_star_hom_inner_unique`, with the witness
bundled as an element of `unitary` and the conclusion expressed through
`unitary.conjStarAlgEquiv`, so that it composes. -/
theorem exists_unitary_conj (n k : ℕ) [NeZero k]
    (φ ψ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ]
           Matrix (Fin (k * n)) (Fin (k * n)) ℂ) :
    ∃ u : unitary (Matrix (Fin (k * n)) (Fin (k * n)) ℂ),
      ∀ x, φ x = _root_.unitary.conjStarAlgEquiv (R := ℂ) u (ψ x) := by
  obtain ⟨U, hU1, hU2, hconj⟩ := unital_star_hom_inner_unique n k φ ψ
  refine ⟨⟨U, hU2, hU1⟩, fun x => ?_⟩
  rw [_root_.unitary.conjStarAlgEquiv_apply]
  exact hconj x

/-- Dimension transport for `exists_unitary_conj`: the codomain size need only
be *equal* to `k * n`, not syntactically `k * n`. Proved by substituting the
dimension equation, which is cleaner than reindexing along `finCongr`. -/
theorem exists_unitary_conj_of_dim {n m k : ℕ} [NeZero k] (hm : m = k * n)
    (φ ψ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] Matrix (Fin m) (Fin m) ℂ) :
    ∃ u : unitary (Matrix (Fin m) (Fin m) ℂ),
      ∀ x, φ x = _root_.unitary.conjStarAlgEquiv (R := ℂ) u (ψ x) := by
  subst hm
  exact exists_unitary_conj n k φ ψ

/-- **Noether–Skolem, square case.** Any two unital *-endomorphisms of
`M_n(ℂ)` differ by conjugation by a unitary. The `k = 1` instance. -/
theorem exists_unitary_conj_square (n : ℕ)
    (φ ψ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ) :
    ∃ u : unitary (Matrix (Fin n) (Fin n) ℂ),
      ∀ x, φ x = _root_.unitary.conjStarAlgEquiv (R := ℂ) u (ψ x) :=
  exists_unitary_conj_of_dim (k := 1) (one_mul n).symm φ ψ

/-- **Every *-automorphism of `M_n(ℂ)` is inner**, pointwise form. -/
theorem starAlgEquiv_conj_apply (n : ℕ)
    (f : Matrix (Fin n) (Fin n) ℂ ≃⋆ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ) :
    ∃ u : unitary (Matrix (Fin n) (Fin n) ℂ),
      ∀ x, f x = _root_.unitary.conjStarAlgEquiv (R := ℂ) u x := by
  obtain ⟨u, hu⟩ :=
    exists_unitary_conj_square n
      (StarAlgHomClass.toStarAlgHom f)
      (StarAlgHom.id ℂ (Matrix (Fin n) (Fin n) ℂ))
  refine ⟨u, fun x => ?_⟩
  have h := hu x
  simpa using h

/-- **Noether–Skolem for `M_n(ℂ)`, the classical statement.** Every
star-algebra automorphism of `M_n(ℂ)` *is* conjugation by a unitary — an
equation between star-algebra equivalences.

This is the form in which the theorem is normally quoted. It cannot be stated
from `unital_star_hom_inner_unique` alone: that lemma's conclusion is a
pointwise equation about a bare matrix, and there was no bundled conjugation
equivalence in the corpus to equate `f` to until
`unitary.conjStarAlgEquiv`. -/
theorem starAlgEquiv_eq_conj (n : ℕ)
    (f : Matrix (Fin n) (Fin n) ℂ ≃⋆ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ) :
    ∃ u : unitary (Matrix (Fin n) (Fin n) ℂ),
      f = _root_.unitary.conjStarAlgEquiv (R := ℂ) u := by
  obtain ⟨u, hu⟩ := starAlgEquiv_conj_apply n f
  exact ⟨u, StarAlgEquiv.ext hu⟩

/-- **Classification of unital *-homs `M_n(ℂ) → M_{kn}(ℂ)` up to unitary
equivalence.** Every such hom is unitarily equivalent to the standard `k`-fold
block-diagonal amplification `blockDiagonalStarAlgHom`.

Combines the C2 arc (any two are conjugate) with the C1 arc (the amplification
is one of them), so the amplification is a complete set of representatives:
there is exactly one unitary equivalence class. -/
theorem exists_unitary_conj_blockDiagonal (n k : ℕ) [NeZero k]
    (φ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ]
         Matrix (Fin (k * n)) (Fin (k * n)) ℂ) :
    ∃ u : unitary (Matrix (Fin (k * n)) (Fin (k * n)) ℂ),
      ∀ x, φ x
        = _root_.unitary.conjStarAlgEquiv (R := ℂ) u
            (blockDiagonalStarAlgHom n k x) :=
  exists_unitary_conj n k φ (blockDiagonalStarAlgHom n k)

/-! ## Non-vacuity witnesses

Each statement above is an existential over unital *-homs. If no such hom
existed the statements would be vacuous, so exhibit them. -/

/-- Non-vacuity: `blockDiagonalStarAlgHom` is a unital *-hom
`M_n(ℂ) → M_{kn}(ℂ)`, so the hypothesis class of `exists_unitary_conj` is
inhabited and the theorem is not vacuous. -/
theorem blockDiagonal_is_witness (n k : ℕ) [NeZero k] :
    blockDiagonalStarAlgHom n k 1 = 1 :=
  blockDiagonalStarAlgHom_unital n k

/-- Non-vacuity for the automorphism statement: the identity automorphism
exists, and `starAlgEquiv_eq_conj` applied to it returns a unitary
implementing it. -/
theorem refl_is_inner (n : ℕ) :
    ∃ u : unitary (Matrix (Fin n) (Fin n) ℂ),
      (StarAlgEquiv.refl : Matrix (Fin n) (Fin n) ℂ ≃⋆ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ)
        = _root_.unitary.conjStarAlgEquiv (R := ℂ) u :=
  starAlgEquiv_eq_conj n StarAlgEquiv.refl

end PrincipiaTractalis.Upstream.NoetherSkolem

/-! ## Axiom audit — LIVE, not commented out -/

#print axioms PrincipiaTractalis.Upstream.NoetherSkolem.exists_unitary_conj
#print axioms PrincipiaTractalis.Upstream.NoetherSkolem.exists_unitary_conj_square
#print axioms PrincipiaTractalis.Upstream.NoetherSkolem.starAlgEquiv_eq_conj
#print axioms PrincipiaTractalis.Upstream.NoetherSkolem.exists_unitary_conj_blockDiagonal
