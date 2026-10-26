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


---

## Step 2, PRICED — the easy route is refuted, the viable route is named

**Legion, 2026-10-24.** This closes the "Order of operations" item above, which
said to price step 2 before building anything general. Measured against mathlib
at the pin, not estimated.

### The obvious route does not work

To define `d_n : Ω^n → Ω^{n+1}` one needs a map out of an exterior power, and
mathlib has the canonical tool for exactly that —
`ExteriorPower.alternatingMapLinearEquiv`:

    (M [⋀^Fin n]→ₗ[R] N) ≃ₗ[R] (⋀[R]^n M →ₗ[R] N)

i.e. to give a linear map out of `⋀^n M` it suffices to give an alternating
map. That is precisely the well-definedness machinery the earlier pricing
called "the genuinely new work", and finding it looked like the price had
collapsed.

**It does not apply.** That equivalence produces an `R`-LINEAR map, and the
exterior derivative is **not** `S`-linear: `d(aω) = da ∧ ω + a·dω`, so `d` is
only `R`-linear over the base and satisfies Leibniz over `S`. Since `Ω^n` is
the exterior power over `S`, the equivalence that would discharge
well-definedness is the one whose hypothesis `d` fails.

Confirmed by a second measurement: **no `Derivation` into an exterior power
exists anywhere in `Mathlib/LinearAlgebra/ExteriorPower/`** (zero files). There
is no prepared route for a non-linear-but-Leibniz map out of `⋀^n`.

This is worth stating plainly because the opposite conclusion was one grep away
from being reported as "step 2 is also assembly".

### The viable route, with its mathlib lemma

`Mathlib/RingTheory/Kaehler/Basic.lean` carries a `Presentation` section
(lines 479–599) and, at lines 628 and 654, the statement that matters:

> "The kernel of the presentation `⊕ₓ B dx ↠ Ω_{B/R}` is spanned by the image
> of the [relations]"

So the construction is: define `d` on the FREE module `⊕ₓ B dx`, where it is
unproblematic; prove it annihilates the spanning set of the kernel; descend.
A kernel **spanned** by an explicit family is the good case — well-definedness
reduces to a check on generators rather than on arbitrary elements.

### Revised price

| step | verdict |
|---|---|
| 1. `Ω^n := exteriorPower n (Ω[S⁄R])` | assembly, unchanged |
| 2. `d_n` with `d∘d = 0` | **the whole price, and harder than the equiv suggested** — must go through the Kaehler presentation and its spanned kernel, not through `alternatingMapLinearEquiv` |
| 3. package as `CochainComplex` | assembly, unchanged |
| 4. `H^n_dR` as its cohomology | assembly, unchanged |

The four-step shape and the "one construction is the whole price" verdict both
survive. What changed is the route through step 2, and the change is from a
false cheap route to a real one.

### What this does NOT change

Everything the earlier note refused to claim, it still refuses. Chow groups,
the cycle class map and intersection theory remain absent, so the Hodge
conjecture is still not stateable, and this route does not touch its content.
Nothing here is progress on the conjecture.


---

## SCOPE CORRECTION — this note prices the AFFINE case only

**Legion, 2026-10-24,** prompted by Pablo asking whether sheaves are important
to this route. They are, and this note had understated it.

### What the earlier sections got wrong

The four-step price above lists steps 3 (package as a `CochainComplex`) and 4
(`H^n_dR` as its cohomology) as "existing API", citing `HomologicalComplex`
(111 files) and `homology` (108 files). **That is correct for a complex of
MODULES over a ring — i.e. for a smooth AFFINE scheme — and it does not carry
over to a variety.**

For a general smooth variety the de Rham complex is a complex of **sheaves**,
and its cohomology is the **hypercohomology** of that complex, computed from an
affine cover. The assembly steps then need a layer this note never measured.

### The sheaf layer, measured

Same method and the same sanity check as the table above (`LinearMap` = 1031,
so the pattern works):

| layer | concept | files | verdict |
|---|---|---|---|
| **present** | `Sheaf` | 167 | rich |
| | `presheaf` | 168 | rich |
| | `Cech` | 17 | present |
| | `AffineOpen` | 24 | present |
| | `Scheme.Opens` | 16 | present |
| | `SheafOfModules` | 13 | present, thin |
| **THE GAP** | `QuasicoherentSheaf` | **0** | **absent** |
| | `CoherentSheaf` | **0** | **absent** |
| | `sheafCohomology` | **0** | **absent** |
| | `Hypercohomology` | **0** | **absent** |
| | `SpectralSequence` | **0** | **absent** |

General sheaf theory is well developed, and Cech machinery and affine covers
exist. What is absent is the whole coherent-sheaf-cohomology layer: no
quasi-coherent sheaves, no sheaf cohomology, no hypercohomology, no spectral
sequences.

### Consequence for the price

The route splits in two, and only the first half was priced:

1. **Affine algebraic de Rham** — priced above, and the price stands: one
   construction (`d_n` through the Kaehler presentation's spanned kernel),
   three assembly steps. This is the LOCAL BUILDING BLOCK.
2. **Gluing it to a variety** — **NOT priced, and four pillars are at zero.**
   Needs quasi-coherent sheaves, sheaf cohomology, hypercohomology of a complex
   of sheaves, and — for the Hodge filtration — spectral sequences.

This matters more than a bookkeeping correction, because **gluing is not an
incidental step in this program**: the spine terminates in Grothendieck
gluing — global coherence recovered from local data with no central driver —
and that is exactly step 2. Pricing step 1 and calling the route priced
understated the one step the program actually cares about.

`SpectralSequence = 0` also independently confirms what the earlier section
already refused to claim: the Hodge–de Rham degeneration is not merely unproved
here, it is not currently expressible.

### What stands, and what is withdrawn

**Stands.** The affine construction is cheap, mathlib-shaped, wanted
independently, and the step-2 route through the Kaehler presentation is real.
The original note's central correction — that the blocking note dismissed this
direction on an estimate rather than a measurement — also stands.

**Withdrawn.** Any reading of this note as pricing a route to Hodge *theory* on
varieties. It prices the affine piece. The honest headline is: the local block
is cheap and buildable now; the gluing that the spine actually names is
unpriced and sits behind four absent layers.

As before: Chow groups, the cycle class map and intersection theory remain
absent, so no part of the Hodge conjecture is touched by any of this.

---

## STEP 2c PRICED — and the "viable route" does NOT extend past `d₁`

**Legion, 2026-10-25,** after landing r355 (`d₁` + `d∘d = 0`) and r356 (`d₁` is
`R`-linear and `S`-Leibniz). This section corrects this note's own step-2
prescription, measured at the pin with the sanity check passing
(`LinearMap` = 1031 files).

### What this note prescribed, and where it holds

The "viable route" above says:

> "define `d` on the FREE module `⊕ₓ B dx`, where it is unproblematic; prove it
> annihilates the spanning set of the kernel; descend. A kernel **spanned** by
> an explicit family is the good case."

**That was correct, and it worked — for `d₁` only.** r345 defined `d` on
`S →₀ S`, proved it annihilates `KaehlerDifferential.kerTotal`, and r355
descended it and read off `d ∘ d = 0`. The route did exactly what this note
said it would.

### Why it does not extend to `d_n`, `n ≥ 2`

The prescription is about the **Kähler** presentation, whose relations are
additive, Leibniz and `algebraMap` — and `d` kills all three (that is r345).
For `n ≥ 2` the object is `Ωⁿ = ⋀[S]ⁿ Ω¹`, and its presentation is a
*different* one whose relations `d` does **not** kill:

    inductive exteriorPower.Rels
      | add  (m : ι → M) (i : ι) (x y : M)
      | smul (m : ι → M) (i : ι) (r : R) (x : M)     ← this one
      | alt  (m : ι → M) (i j : ι) (hm : m i = m j) (hij : i ≠ j)

The `.smul` relation is
`single (update m i (r • x)) 1 - r • single (update m i x) 1`. The candidate
differential `d(m₀ ∧ ⋯ ∧ m_{n-1}) = Σᵢ (-1)ⁱ m₀ ∧ ⋯ ∧ d₁(mᵢ) ∧ ⋯ ∧ m_{n-1}`
fails it: scaling slot `k` by `c` gives, via r356's Leibniz,

    c • d(m₀ ∧ ⋯ ∧ m_k ∧ ⋯) + (-1)^k m₀ ∧ ⋯ ∧ (d₀c ∧ m_k) ∧ ⋯

and the second term does not vanish. So `d` is not `S`-multilinear in the
slots, and the spanned kernel is not annihilated.

**And the two routes are the same object.** `exteriorPower.alternatingMapLinearEquiv`
is constructed from `exteriorPower.presentation` via `isPresentationCore`
(`ExteriorPower/Basic.lean`, `presentation` then `alternatingMapLinearEquiv`
immediately after). So this note's "viable route" and the route it refutes are
the **same universal property** when applied to `⋀ⁿ`. The distinction that made
the route viable was never presentation-vs-equivalence; it was *which module*
is being presented. Kähler presentation: `d` kills the relations. Exterior-power
presentation: `d` does not.

This note should not be read as offering a general route to `d_n`. It offers a
route to `d₁`, which has been taken.

### What `d_n` would actually cost, measured

| ingredient | files at pin | verdict |
|---|---|---|
| `GradedDerivation` | **0** | absent |
| `SuperDerivation` | **0** | absent |
| `AntiDerivation` / `antiderivation` | **0** | absent |
| `IsAntiderivation` | **0** | absent |
| `Derivation` in `ExteriorPower/` or `ExteriorAlgebra/` | **0** | absent |
| `ExteriorPower/` total | 2 | thin |
| `ExteriorAlgebra/` total | 3 | thin |
| `deRham` / `DeRham` | **0** | absent |

The concept `d` *is* — a graded (odd) anti-derivation of degree `+1` — does not
exist in mathlib at this pin, under any of six spellings. `ExteriorAlgebra.lift`
does not substitute: it requires `f m * f m = 0` and produces an **algebra
homomorphism**, and `d` is not one.

So `d_n` requires building the anti-derivation concept and its well-definedness
machinery from nothing, because the one prepared tool for mapping out of `⋀ⁿ`
is precisely the tool whose hypothesis `d` fails. That is mathlib-infrastructure
work, not PF assembly. **Weeks, not days** — and unlike the earlier "multi-year"
claim, that estimate now rests on a specific named absence rather than on
unfamiliarity.

### Even the TRUNCATED complex is blocked, for a separate reason

`S → Ω¹ → Ω²` with `d ∘ d = 0` is already in hand, so packaging a three-term
cochain complex looks free. It is not. `d₁` is **not** `S`-linear (r356), so the
complex is not a complex of `S`-modules; it is a complex of `R`-modules. But
r343 recorded that mathlib **does not propagate an `R`-module structure onto the
exterior power at this pin** — which is why `d₀` was not packaged as
`Derivation R S (Form R S 1)` in the first place. So the category the truncated
complex lives in is not available either.

Two independent blockers, then, and neither is about effort:

1. `d_n` for `n ≥ 2` — no anti-derivation concept, and the only universal
   property for `⋀ⁿ` rejects non-`S`-linear maps.
2. packaging anything as a complex — no `R`-module structure on `Form`.

### Revised price table

| step | verdict |
|---|---|
| 1. `Ωⁿ`, `d₀`, wedge | **DONE** — r343, r344 |
| 2a. `d₁`, `d ∘ d = 0` | **DONE** — r345, r355 |
| 2b. `d₁` is `R`-linear, `S`-Leibniz | **DONE** — r356 |
| 2c. `d_n`, `n ≥ 2` | **BLOCKED** — anti-derivation concept is 0 files; `⋀ⁿ`'s universal property rejects `d` |
| 3. `CochainComplex` | **BLOCKED** — no `R`-module structure on `Form` |
| 4. `Hⁿ_dR` | blocked behind 3 |
| gluing to a variety | unpriced, five pillars at 0 files |

### What this does NOT change

Everything this note refused to claim, it still refuses. Chow groups, the cycle
class map and intersection theory remain absent, the Hodge conjecture is still
not stateable, and none of r343–r356 touches its content. The affine local
block is real and is now four-sevenths built; the rest is named, not estimated.
