# Mathlib upstream extraction — four star-algebra gaps, de-specialised

**Date:** 2026-10-05
**Module:** `PF_Lean4_Code/PF/Upstream/MathlibStarAlgebra.lean` (NEW)
**Wired:** `PF.lean:1360`
**Gate:** `PRISTINE  PF.Upstream.MathlibStarAlgebra` — 14/14 declarations, all five criteria
**Mathlib rev checked against:** `eed770a434957369c6262aa3fb1d6426419016d4` (Lean 4 v4.24.0-rc1)
**Predecessor:** `codex/MATHLIB_PR_42093_RESPONSE_2026-09-10.md`, which queued five candidates

## Why this is not repair work

`codex/BOOK_RIGOR_LEDGER_SPEC.md` fixes the rule that any claim whose closure
would resolve a Millennium problem is CONDITIONAL REDUCTION and never PROVEN,
because the Clay-statement-form discharge is not established. Repair work does
not move that line — it makes the book's description of the corpus true, which is
necessary but is not new mathematics.

This is new mathematics, at a scale that is honest about itself: four lemmas that
mathlib does not have, stated at the generality at which they are actually true
rather than at the generality the substrate development happened to need. It
moves nothing in the Millennium ledger and does not pretend to. It is a
contribution to the library every formalisation in this area depends on.

## What was already true before today

`PF.lean:1355`, the `PF.SubstrateRigidity` entry, already claimed the module
"fills six mathlib gaps as by-products: `conjByUnitary`, `reindexStarAlgEquiv`,
`coe_iSup_of_directed_starSubalgebra`, non-commutative C*-direct-limit apparatus,
star lift for `UniformSpace.Completion`, `IsTracialLinearFunctional` predicate."
That claim was correct. What was missing is that each of those existed only as a
`private` declaration inside a 2,513-line file, specialised to scalars `ℂ` and to
`Matrix (Fin N) (Fin N) ℂ` — the form the Glimm `3^∞` classification consumes. In
that form none of them is shippable, and in fact none of them was even
*probeable by name*: they are among the 21 private declarations the pristine gate
reports as excluded from criterion (b).

The specialisation was an artefact of where each lemma was written. Reading the
proofs establishes that each uses only facts holding in any star ring:
`mul_assoc`, `one_mul`, `star_mul`, `star_star`, `mul_add`, `add_mul`, and the
scalar-tower lemmas. Nothing in any of the four proofs needs `ℂ`, needs `Fin`,
or needs completeness of the substrate.

## The four declarations, and what generalisation each required

### 1. `StarSubalgebra.coe_iSup_of_directed`

**Corpus form:** `SubstrateRigidity.lean:1500`, `private`, `StarSubalgebra ℂ A`
with `A` the ambient `CStarAlgebra` section variable. A second variant at `:302`.

**Generalisation:** scalars `ℂ → R` for any `[CommSemiring R] [StarRing R]`, and
`A` from `CStarAlgebra` to `[Semiring A] [StarRing A] [Algebra R A]
[StarModule R A]` — i.e. exactly the typeclasses `StarSubalgebra R A` requires
and nothing more. No C*-structure, no norm, no completeness. Proof ported
unchanged.

**Verified gap:** mathlib ships `coe_iSup_of_directed` for `Submonoid`,
`Subsemigroup`, `Subgroup`, `Submodule`, `Subsemiring`, `Subring`,
`NonUnitalSubsemiring`, `NonUnitalSubring`, `Subalgebra`,
`NonUnitalSubalgebra`, `Subfield`, `IntermediateField`, and
`NonUnitalStarSubalgebra` (`Mathlib/Algebra/Star/NonUnitalSubalgebra.lean:1022`).
The unital *-subalgebra case is the single omission in that list.

**Added beyond the corpus:** `mem_iSup_of_directed`, the membership form mathlib
pairs with every one of the above.

**Destination:** `Mathlib/Algebra/Star/Subalgebra.lean`.

### 2. `StarAlgEquiv.conjugateBy`

**Corpus form:** `SubstrateRigidity.lean:1936`, `private noncomputable def
conjByUnitary`, fixed to `Matrix (Fin N) (Fin N) ℂ`.

**Generalisation:** any `[Semiring A] [StarRing A] [SMul R A]
[SMulCommClass R A A] [IsScalarTower R A A]`. The two matrix-specific rewrites
`Matrix.mul_smul` / `Matrix.smul_mul` become the general `mul_smul_comm` /
`smul_mul_assoc`; everything else ports verbatim. It need not be `noncomputable`.

**Verified gap:** mathlib has the *consequence* for spectra —
`spectrum.unitary_conjugate` (`Mathlib/Algebra/Star/Unitary.lean:409`) — but not
the equivalence. There is no `innerAut` for star algebras.

**Added beyond the corpus:** `unitary.conjStarAlgEquiv`, the bundled form taking
`u : unitary A` so the two cancellation hypotheses come from `u.prop` rather than
being carried by hand; and `unitary.conjStarAlgEquiv_mul`, multiplicativity in
the unitary, which the corpus never states. Note the order:
`conj (u * v) = (conj v).trans (conj u)`, since `trans` applies its first
argument first.

**Of note:** `StarAlgEquiv.conjugateBy` **depends on no axioms at all** — not
even `propext`. It is a construction, not a classical theorem.

**Destination:** `Mathlib/Algebra/Star/Unitary.lean`.

### 3. `Matrix.reindexStarAlgEquiv`

**Corpus form:** `SubstrateRigidity.lean:1986`, `private noncomputable def`,
fixed to `Fin m ≃ Fin n` and `ℂ`.

**Generalisation:** arbitrary index types `m ≃ n` with
`[Fintype] [DecidableEq]`, arbitrary coefficients `[Semiring A] [StarRing A]
[Algebra R A]` over `[CommSemiring R]` — matching `Matrix.reindexAlgEquiv`'s own
generality exactly, which is the right target for a star upgrade of it. `R` and
`A` made explicit, as `reindexAlgEquiv` has them.

**Verified gap:** mathlib has `Matrix.reindexAlgEquiv`
(`Mathlib/LinearAlgebra/Matrix/Reindex.lean:111`) and
`Matrix.conjTranspose_reindex`
(`Mathlib/LinearAlgebra/Matrix/ConjTranspose.lean:428`). Combining them is one
line, and nobody has.

**Destination:** `Mathlib/LinearAlgebra/Matrix/Reindex.lean`.

### 4. `IsDenseInducing.extendStarAlgHom` — NEW

This is the one that exists in **no form anywhere in the corpus**. The grep
across `PF/` for `extendStarAlgHom` returns nothing; the completion-side star
lift is done by hand in the W-arc, specialised to the concrete
`TimelessFieldCompletion`.

**Statement:** given a uniform-inducing `i : A →⋆ₐ[R] B` with dense range and a
uniformly continuous `f : A →⋆ₐ[R] C` into a complete Hausdorff `C`, the unique
continuous extension of `f` along `i` is again a *-algebra homomorphism.

**Construction:** the ring-homomorphism content is delegated to mathlib's
`IsDenseInducing.extendRingHom` (`Mathlib/Topology/Algebra/UniformRing.lean:282`)
rather than reproved. What is added is the two fields that map has no reason to
carry:

- `commutes'` — the extension respects `algebraMap`, because
  `i (algebraMap R A r) = algebraMap R B r` puts the point inside the dense image,
  where `IsDenseInducing.extend_eq` applies directly. No density argument needed.
- `map_star'` — a genuine density argument: `{x | extend f (star x) = star (extend f x)}`
  is closed (`isClosed_eq`, using continuity of the extension from
  `uniformContinuous_uniformly_extend`, composed with `ContinuousStar` on both
  sides) and contains the image of `i`, hence is everything by
  `DenseRange.induction_on`.

**Also provided:** `extendStarAlgHom_comp_eq`, the characteristic property
`extendStarAlgHom ue dr hf (i a) = f a`. Any user needs it, and it doubles as the
non-vacuity witness.

**Verified gap:** mathlib has `extendRingHom` and nothing star-flavoured near it.

**Destination:** `Mathlib/Topology/Algebra/UniformRing.lean`.

## The fifth candidate is deliberately NOT included

`IsTracialLinearFunctional` (`SubstrateRigidity.lean:123`, and the one of the five
that is *not* private) is held back, and this is a scope judgement, not an
oversight.

Its own docstring records the reason: the predicate **omits positivity**
(`∀ x, 0 ≤ (φ (star x * x)).re`) **and star-hermitianness**
(`∀ x, φ (star x) = star (φ x)`). That is sufficient for the Elliott
specialisation to `3^∞`, which is why it was written that way and why r337 could
strengthen `T_infinity_rigidity` by deleting the unique-trace hypothesis and
recovering it as `Substrate3Inf.trace_unique`. But a predicate missing positivity
cannot defensibly take the upstream name "tracial state", and mathlib has no
named `TracialState` class to align with. Offering it under that name would be
the naming equivalent of a downgrade: it would look like the standard notion and
not be it.

This is the honest position: three generalised, one new, one withheld pending a
design that earns the name. Four of five shipped is the result; five of five
would have required pretending.

## Verification record

```
$ taskset -c 0,1 lake build PF.Upstream.MathlibStarAlgebra
Built PF.Upstream.MathlibStarAlgebra (2.1s)
'StarSubalgebra.coe_iSup_of_directed'           [propext, Classical.choice, Quot.sound]
'StarSubalgebra.mem_iSup_of_directed'           [propext, Classical.choice, Quot.sound]
'StarAlgEquiv.conjugateBy'                      does not depend on any axioms
'unitary.conjStarAlgEquiv'                      [propext, Quot.sound]
'unitary.conjStarAlgEquiv_mul'                  [propext, Quot.sound]
'Matrix.reindexStarAlgEquiv'                    [propext, Classical.choice, Quot.sound]
'IsDenseInducing.extendStarAlgHom'              [propext, Classical.choice, Quot.sound]
'IsDenseInducing.extendStarAlgHom_comp_eq'      [propext, Classical.choice, Quot.sound]
Build completed successfully (1546 jobs).

$ PF_TREE=.../PF_Lean4_Code bash scripts/pristine_gate.sh PF.Upstream.MathlibStarAlgebra
  PASS  (c) no sorry / native_decide / axiom in code
  PASS  (a) UP-TO-DATE per lake content hash
  PASS  (d) no unused binders in this module
  PASS  (d2) PremiseAudit: no dead / contained / vacuous premises over 14 decls
  PASS  (b) axioms ⊆ {propext, Classical.choice, Quot.sound} over 14 inspected
            axiom records (14 probeable declarations)
  PASS  (e) no Prop-valued definitions introduced — no vacuity obligation
PRISTINE  PF.Upstream.MathlibStarAlgebra
```

Criterion (d2) is the load-bearing one for a module of this kind: it certifies
that **every hypothesis of every declaration is consumed by its proof**. A
generalisation that carried a typeclass it did not need, or a lemma that took a
hypothesis the proof ignored, would fail here. The first draft of
`PF/Collapse/RateModulation.lean` failed exactly this check with 8 dead premises
and had to be unbundled; this module passed on the first attempt.

Non-vacuity is additionally witnessed inside the module itself, per declaration,
rather than being argued in prose:

- `StarSubalgebra.coe_iSup_of_directed_const` — a constant family is directed, so
  the `Directed` hypothesis is satisfiable.
- `StarAlgEquiv.conjugateBy_one_apply` — `u = 1` satisfies both cancellation
  hypotheses in every star ring, and conjugation by it is the identity.
- `unitary.conjStarAlgEquiv_one_apply` — `1 : unitary A` exists.
- `Matrix.reindexStarAlgEquiv_refl_apply` — at the identity bijection the
  equivalence is the identity map.
- `IsDenseInducing.extendStarAlgHom_comp_eq` — exhibits the extension's value on
  the dense image.

## PF-free by construction

The module imports only mathlib:

```
Mathlib.Algebra.Star.Subalgebra
Mathlib.Algebra.Star.Unitary
Mathlib.Algebra.Algebra.Subalgebra.Directed
Mathlib.LinearAlgebra.Matrix.Reindex
Mathlib.LinearAlgebra.Matrix.ConjTranspose
Mathlib.Topology.Algebra.UniformRing
Mathlib.Topology.Algebra.Star
```

No `PF.` import, no `ℂ`, no `Fin`, no `CStarAlgebra`, nothing from the substrate
development. Each declaration can be moved to the mathlib file named above
without editing its statement or its proof. That property is the deliverable, not
a convenience.

## What is NOT claimed

- Not claimed: that any of this is submitted to mathlib. Opening a PR is an
  outward-facing action and is Pablo's decision, not mine. Nothing has been
  pushed anywhere; `master` remains unpushed.
- Not claimed: that these lemmas are deep. They are not. Three are
  generalisations whose proofs ported with one substitution each, and the fourth
  is a density argument of the standard shape. Their value is that the library
  lacks them and every formalisation in this area re-derives them privately —
  which is precisely what this corpus did for a year.
- Not claimed: any movement in the rigor ledger. No CONDITIONAL REDUCTION became
  PROVEN today.

## Next, if this line is continued

1. The `private` declarations in `SubstrateRigidity.lean` can now be *replaced*
   by applications of the general forms, which would shrink that file and remove
   seven of the 21 declarations the gate cannot probe by name (the three
   candidates account for seven private declarations there: `coe_iSup...` at
   `:1500` plus its W4 variant at `:302`; `conjByUnitary` at `:1936` plus its
   `_apply` simp lemma; `reindexStarAlgEquiv` at `:1986` plus its `_apply` and
   `_symm_apply`). That is a
   refactor of a 2,513-line file holding the corpus's strongest result, so it
   wants its own gate run against `T_infinity_rigidity` specifically, not a
   drive-by edit.
2. `IsTracialLinearFunctional` needs the positivity and star-hermitianness
   design decision before it can carry an upstream name.
3. The remaining two items in the `PF.lean:1355` list of six —
   "non-commutative C*-direct-limit apparatus" and "star lift for
   `UniformSpace.Completion`" — have not been assessed for generality. The second
   is now partly subsumed by `extendStarAlgHom`; the first is a larger body of
   work and may not be upstreamable in its current shape.

Author: Pablo Cohen + Claude Opus 5. 2026-10-05.


---

# Addendum, same day: Noether--Skolem in bundled form

**Module:** `PF_Lean4_Code/PF/Upstream/NoetherSkolemMatrix.lean` (NEW)
**Wired:** `PF.lean`, immediately after `PF.Upstream.MathlibStarAlgebra`
**Gate:** `PRISTINE  PF.Upstream.NoetherSkolemMatrix` -- 8/8 declarations

This is the first thing the four extracted lemmas were good for, and it arrived
the same day, which is the point of extracting them.

## The gap

**Mathlib has no Noether--Skolem theorem in any form.** Verified: the only
`Skolem` in the library is the unrelated model-theoretic Skolemisation in the
`choose` tactic. There is no `IsInner`, no inner-automorphism machinery for
algebras, and no statement anywhere that automorphisms of a matrix algebra are
conjugations.

The corpus already had the content. `SubstrateRigidity.lean:1412`,
`unital_star_hom_inner_unique`, proves that any two unital *-homs
`M_n(C) -> M_{kn}(C)` are unitarily conjugate, off the C2 arc's roughly 700
lines of matrix-unit calculus, projection-trace counting, orthonormal-basis
construction and change-of-basis unitary. What it did not have was the
*statement*: its conclusion is a raw conjunction of a bare matrix `U`, two
cancellation identities, and a pointwise equation.

## What the bundling buys, concretely

`starAlgEquiv_eq_conj` -- *every *-automorphism of `M_n(C)` is inner* -- is the
form in which Noether--Skolem is cited. It is an **equation between
star-algebra equivalences**, `f = conjStarAlgEquiv u`.

That equation was **not statable in this corpus yesterday.** Not hard to prove;
not statable. `unital_star_hom_inner_unique` gives a pointwise identity about a
bare matrix, and there was no bundled conjugation equivalence anywhere in the
corpus to put on the right-hand side of the equals sign. The private
`conjByUnitary` inside `SubstrateRigidity.lean` was exactly such a term, but
being `private` it could not appear in any other module's statement -- which is
the sharpest illustration of why those four lemmas were worth de-privatising
and generalising. Making a definition public changed what theorems can be
*written*, not merely what proofs are convenient.

## The results

- `exists_unitary_conj` -- rectangular case, witness bundled as an element of
  `unitary (M_{kn}(C))`, conclusion an application of
  `unitary.conjStarAlgEquiv`. Unitarity now travels with the witness instead of
  being carried alongside it as two side conditions that every caller must
  thread.
- `exists_unitary_conj_of_dim`, `exists_unitary_conj_square` -- the square case.
  Obtained by `subst` on a dimension equation `m = k * n`, which turned out
  cleaner than the route through `Matrix.reindexStarAlgEquiv` and `finCongr`
  that this module was originally going to take: `1 * n` is not definitionally
  `n`, but substituting the equation sidesteps the cast entirely rather than
  transporting across it.
- `starAlgEquiv_eq_conj` -- the classical statement, as above.
- `exists_unitary_conj_blockDiagonal` -- **classification up to unitary
  equivalence.** Combining C2 (any two such homs are conjugate) with C1 (the
  amplification is one of them) gives: every unital *-hom `M_n(C) -> M_{kn}(C)`
  is unitarily equivalent to the standard `k`-fold block-diagonal amplification.
  So there is exactly **one** unitary equivalence class, and
  `blockDiagonalStarAlgHom` is a complete set of representatives. The two arcs
  were each proved to serve the Elliott back-and-forth; stated together they
  are a classification theorem, and nothing in the corpus said so.

## Upstream status -- stated honestly

The statements are upstreamable and the library wants them. **The proofs are
not yet.** They rest on the C2 arc inside `SubstrateRigidity.lean`, and shipping
Noether--Skolem to mathlib means extracting that arc too -- a substantially
larger job than the four lemmas, and not attempted. This module therefore
imports `PF.SubstrateRigidity`, is **not** PF-free, and its header says so
rather than implying otherwise by sitting in the same directory as a module that
is.

## Lints observed in passing, not fixed

The gate charged none of these to this module; recorded so they are not lost.

- `PF/SubstrateRigidity.lean:1223:19` -- unused simp argument.
- `PF/SubstrateBase3Norm.lean:102:6` -- unused variable `k`.
- `PF/TuringEncoding/WeightedDigitalSumGeneratingFunction.lean:151:52` --
  unused variable `α`.

Also noted while reading, and **not** acted on: the docstring of
`Substrate3Inf.connect_iso` (`SubstrateRigidity.lean`, ~`:163`) says the lemma
is "Deferred as a leaf" and describes an intended future proof, while the body
immediately below it is the complete proof `fun _ _ => rfl` -- correct, because
a `StarSubalgebra` carries the subspace metric from the ambient algebra, so an
inclusion is isometric by definition. Same defect class as the file header
repaired on 2026-10-02: a declaration's self-description outliving the facts.
A docstring, not a proof, so it changes no result -- but it is exactly the kind
of thing a referee reads and believes.


---

# CORRECTION 2026-10-05 (same day): two of the four are not gaps

Dispatched external review refuted two of this document's central claims, and
the refutation holds. Verified by fetching mathlib master directly rather than
by argument.

| declaration | claimed | actual, at mathlib master |
|---|---|---|
| `StarSubalgebra.coe_iSup_of_directed` | "the unital *-case is the single omission" | **EXISTS** in `Mathlib/Algebra/Star/Subalgebra.lean`, with the same statement, variable names included |
| unitary conjugation as `StarAlgEquiv` | "mathlib has only the spectral consequence" | **EXISTS** as `Unitary.conjStarAlgAut : unitary R →* (R ≃⋆ₐ[S] R)` in `Mathlib/Algebra/Star/UnitaryStarAlgAut.lean` (Monica Omar, 2025), with `_apply`, `_symm_apply`, `_trans_`, `_mul_apply` — covering the multiplicativity lemma too, and bundling the monoid-hom structure more neatly than the pair here |
| `Matrix.reindexStarAlgEquiv` | absent | **absent** — survives |
| `IsDenseInducing.extendStarAlgHom` | absent | **absent** — survives |

## The methodological error, stated plainly

Every absence claim in this document was checked against the pinned revision
`eed770a434957369c6262aa3fb1d6426419016d4`. That check was performed correctly
and the results were true of that revision. The error was treating it as
evidence about mathlib. **A pinned revision is evidence about the pin.** The
pin is roughly seven months old, and `UnitaryStarAlgAut.lean` is dated 2025,
so the declaration may well have existed upstream before this corpus wrote its
private version — which means the original specialisation was arguably
redundant from the start.

The general rule this earns: **a novelty claim about a fast-moving library can
only be made against that library's current state, and a local checkout is
never that.** This is the same failure shape as the stale self-description
class catalogued elsewhere in this corpus — a measurement that was true when
taken, retained past its validity, and then relied on.

## What is unaffected

- Both declarations remain **correct**, remain PRISTINE, and remain used by
  `PF/Upstream/NoetherSkolemMatrix.lean`. Nothing is withdrawn mathematically
  and no proof changes.
- `Matrix.reindexStarAlgEquiv` and `IsDenseInducing.extendStarAlgHom` survive
  as genuine upstream candidates.
- The C1+C2 extraction, the de-duplication, and the Noether–Skolem bundling
  are untouched by this: none of them rested on the novelty claim.
- Mathlib still appears to carry **no Noether–Skolem theorem**, which remains
  the most valuable thing in this line. Caveat recorded: third-party Lean 4
  formalisations of Skolem–Noether exist outside mathlib (e.g. `TNLean`), so
  the defensible claim is "mathlib lacks it", not "nobody has formalised it".

## Consequence for the PR plan

Two candidates, not five. `IsTracialLinearFunctional` stays withheld for the
reason already given. Before offering either survivor, re-check it against
master on the day of submission — not against the pin.
