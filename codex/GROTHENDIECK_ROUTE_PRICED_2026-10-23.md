# The Grothendieck route, PRICED — and it is not a multi-year project

**Legion, 2026-10-23.** Closes the one `OPEN` item left by
`codex/HODGE_SCOPING_BLOCKED_2026-10-17.md` §6.

## What was open, and why it was the item that mattered

That note named the Hodge blocker and recommended leaving the axis alone. Its
own §6 `OPEN` left exactly one direction unexamined:

> "whether `AlgebraicGeometry.Scheme` plus `RingTheory/Kaehler` could support
> *algebraic* de Rham cohomology for smooth affine schemes (the Grothendieck
> route) — **that is the one direction I have not priced**, and it would be a
> multi-year mathlib project rather than a PF build"

Two claims in one sentence: *not priced*, and *multi-year*. The second does not
follow from the first, and this note measures it.

**Why this route and not another.** The program's spine terminates in
**Grothendieck gluing** — global coherence recovered from local data, no central
driver. Algebraic de Rham cohomology is that proposition as a theorem:
Grothendieck (1966) showed that for a smooth variety over `ℂ` the *analytic* de
Rham cohomology is computed by the *algebraic* de Rham complex. Transcendental
data, recovered from algebraic data, by gluing. The Hodge conjecture is the
place where the corresponding recovery is still conjectural. So this is not an
arbitrary pick off a blocked axis — it is the axis's only measured route toward
stating Hodge theory algebraically rather than transcendentally.

## The measurement

Counts over `.lake/packages/mathlib/Mathlib`, with the sanity check the blocking
note itself prescribed after a broken-grep incident (`LinearMap` = 1031, so the
pattern works):

| layer | concept | files | verdict |
|---|---|---|---|
| **below the gap** | `KaehlerDifferential` | 17 | present |
| | `Derivation` | 31 | present |
| | `exteriorPower` | 4 | present, thin |
| **THE GAP** | `deRham` / `DeRham` | **0** | **absent** |
| | `exteriorDerivative` | **0** | **absent** |
| | `differentialForms` | **0** | **absent** |
| **above the gap** | `HomologicalComplex` | 111 | present, rich |
| | `CochainComplex` | 50 | present |
| | `homology` | 108 | present |
| | `QuasiIso` | 26 | present |
| Grothendieck side | `Scheme` | 83 | present |
| | `FormallySmooth` | 10 | present |
| | `Algebra.Smooth` | 5 | present |

**The missing piece is one construction, between two developed layers.**

## The price, stated as work

1. `Ω^n_{S/R} := exteriorPower n (Ω[S/R])` — **assembly from present pieces.**
   Kähler differentials and exterior powers both exist; this is a definition.
2. **The exterior derivative `d_n : Ω^n → Ω^{n+1}` with `d ∘ d = 0`.** This is
   the genuinely new work: the universal derivation gives `d_0`, and the general
   case needs the standard formula plus well-definedness on the exterior power.
   Nontrivial, standard, and **finite**.
3. Package as a `CochainComplex` — **existing API**, 50 files of it.
4. `H^n_dR(S/R)` as the cohomology of that complex — **existing API**, 108
   files of homology machinery.

Three of the four steps are assembly. **One construction is the whole price.**

## What it buys, and what it does NOT

**Buys:** an algebraic substitute for the analytic de Rham machinery mathlib
lacks entirely; the ability to *state* Grothendieck's comparison theorem; and
the foundation on which a Hodge filtration could be defined algebraically rather
than through harmonic theory, which is the absence that blocked everything else.

**Does not buy — and this is the part that must not be lost:** Chow groups, the
cycle class map, intersection theory. All still absent. **The Hodge
conjecture's content is the inclusion into the image of the cycle class map,
and this route does not touch it.** Nor does it give the Hodge decomposition,
which needs the degeneration of the Hodge–de Rham spectral sequence.

So: this route makes Hodge *theory* expressible algebraically. It does not make
the Hodge *conjecture* provable, or even stateable. Anyone citing this note as
progress on the conjecture would be misreading it, and the note says so here so
that cannot happen quietly.

## Recommendation

**The axis should not have been closed, and this is why.** The blocking note's
verdict was sound for every route it priced; the one route it did not price is
the cheapest of them, and it was dismissed on an estimate rather than a
measurement. That is worth saying plainly because the same note's discipline —
measure, do not assume — is what produced the correction.

**The work is mathlib-shaped, not PF-shaped.** An algebraic de Rham complex over
Kähler differentials is a contribution mathlib wants independently of this
program, which means it can be landed in the open, reviewed by people who do
this for a living, and cited afterwards rather than asserted. That is the same
route the four existing PRs took, and it is the strongest available form of
evidence: a result that strangers maintain.

**Order of operations, if this is taken up:** price step 2 against a specific
smooth affine case before building the general construction — the same
falsify-first discipline the march's fold work used, where a probe that matched
the real emitted structure settled in minutes what two estimates had argued
about for hours.

## Companion result, same pass

`PF/AlgebraicGeometry/ComplexTorusHodgeLattice_2026_10_23.lean` takes the other
opening the blocking note left: its structural claim "YM had a lattice, Hodge
has no surrogate" is true for general smooth projective varieties and **false
for complex tori**, where `H^k(A,ℚ) = ⋀^k Hom(Λ,ℚ)` holds exactly and the
fibrewise linear algebra IS the global cohomology. That file gives the repo its
first Hodge-type-`(1,1)` predicate that can fail — with an explicit class on the
split `E × E` model that does fail — replacing an archive definition that was
`True` and entailed `False`. Left-hand side, degree 2, cited comparison; no part
of the conjecture.
