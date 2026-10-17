# Hodge scoping: BLOCKER NAMED, and harder than Yang-Mills — there is no lattice here. The archive "COMPLETE" files are not empty, they are INCONSISTENT (demonstrated).

**Date:** 2026-10-17 (Legion, audit on Acer). Scoping. No Lean landed (one probe,
run and removed). Labels FACT / MEASURED / JUDGEMENT / OPEN.

**VERDICT: BLOCKER NAMED.** Stronger than the Yang-Mills blocker, for a
structural reason: **YM had a lattice, Hodge has no surrogate.** Gauge theory
has a genuine finite regularisation that preserves the question's shape; the
Hodge conjecture is intrinsically about transcendental cohomology of smooth
projective varieties over `ℂ`, and no finite model's solution would say
anything about it.

**Three findings, in order of consequence:**

1. **The archive `Hodge_Conjecture_COMPLETE.lean` files are INCONSISTENT, not
   merely vacuous.** A single axiom entails `False`. **Machine-demonstrated**
   this session, `EXIT=0`.
2. **mathlib has nothing**: no Kähler manifolds, Hodge decomposition, harmonic
   forms, Hodge star, de Rham, Dolbeault, complex manifolds, algebraic cycles,
   Chow groups, or cycle class map. (The 5 "Kähler" hits are Kähler
   *differentials* — commutative algebra.)
3. **The one piece of real Hodge content in the repo is the audit layer**, and
   it is correct: `Ch20Ch25NumericObstructions.lean` refutes the book's own
   worked examples from genuine Hodge numbers. **That is the model for what is
   worth doing here — and it is already done.**

---

## 1. The ARCHIVE "COMPLETE" orphans — worse than empty. MEASURED

Two copies, `ARCHIVE/2026-06-08-cleanup/PF_Lean4_Code_orphans/` (238 lines) and
`ARCHIVE/2026-06-16-orphans/` (616 lines), different md5s. **Each carries 5
`axiom` declarations.** The 616-line copy's objects:

```lean
def SingularCohomology (X) (k) : Type := ℚ          -- cohomology IS ℚ
noncomputable def betti_number (X) (k) : ℕ := 0     -- "Placeholder"
def HodgeComponent (X) (p q) : Type := ℂ            -- just ℂ
noncomputable def cycle_class_map X p Z := 0        -- "Placeholder", constant 0
noncomputable def spectral_concentration ξ : ℝ := 0.95   -- "Placeholder", constant
def IsHodgeClass X p ξ : Prop := ∃ (c : HodgeComponent X p p), True
```

Rio predicted "a COMPLETE file with no Hodge object is empty". **It is worse.**
Unfold the definitions:

* `IsHodgeClass X p ξ = ∃ (c : ℂ), True` = **`True`**, so
  `HodgeClasses X p = Set.univ`;
* `cycle_class_map` is constantly `0`, so
  `AlgebraicClasses X p = {0}`;
* `spectral_concentration ξ = 0.95`, so the hypothesis
  `spectral_concentration ξ ≥ 0.95` is the **tautology** `0.95 ≥ 0.95`.

Hence the axiom (archive lines 339-343)

```lean
axiom concentration_implies_algebraic :
  ∀ X p ξ, spectral_concentration ξ ≥ 0.95 → ξ ∈ AlgebraicClasses X p
```

asserts, with an always-true hypothesis, that **every element of `ℚ` equals
`0`**.

**Demonstrated, not asserted.** I replicated the definitions verbatim and the
axiom, and derived `False`:

```
'HodgeArchiveProbe.archive_axiom_is_inconsistent' depends on axioms:
  [propext, Classical.choice,
   HodgeArchiveProbe.concentration_implies_algebraic, Quot.sound]
EXIT=0
```

`theorem hodge_conjecture` (archive line 354) is then proved in two steps from
this axiom and its sibling — a derivation from an inconsistent premise.

**Consequences, stated precisely:**

* **No live soundness risk.** Both files are ARCHIVE orphans, outside
  `PF_Lean4_Code`, not imported by `PF.lean`. Nothing in the build depends on
  them. **FACT.**
* **They must never be revived or cited.** From an inconsistent axiom set every
  statement is derivable, so the file's `theorem hodge_conjecture` has no
  content whatever — it is not a weak result, it is no result.
* **JUDGEMENT:** the defect class to watch is *placeholder definitions plus
  axioms carrying the real content*. The placeholders make the axioms'
  hypotheses tautologous and their conclusions absurd; neither half looks wrong
  in isolation. This is a sharper failure mode than the P/NP and YM patterns,
  where the content was true-but-irrelevant rather than contradictory.

## 2. Book ch25 vs what the files prove — FACT

ch25 has **7 `theorem` environments** and, like ch23, **3
`\manuscriptcorrection{}` ledger notes**. The reconciliation is exact and
unflattering in one specific way:

| # | ch25 label | line | what the Lean actually has |
|---|---|---|---|
| 1 | `thm:lefschetz` [Lefschetz (1924)] | 186 | **correct citation** of the (1,1)-theorem |
| 2 | `thm:known-cases` [Kodaira, Spencer] | 192 | **correct citation/survey** |
| 3 | `thm:critical-threshold` | 351 | the `0.95` numerology; **ledger-corrected** (`ε_quantum`) |
| 4 | **`thm:hodge-concentration`** | 375 | ⇒ archive **`axiom hodge_class_high_concentration`** |
| 5 | **`thm:low-rank`** | 422 | ⇒ archive **`axiom concentration_implies_algebraic`** — *the inconsistent one* |
| 6 | `thm:algorithm-correctness` | 486 | cycle extraction w.p. `≥ 1−δ`, `δ = 10⁻⁸` — no Lean |
| 7 | `thm:complexity-hodge` | 490 | `O(N³ + rN² log N)` — no Lean |

> **The two statements the book labels `theorem` (4 and 5) are exactly the two
> the formalisation had to introduce as `axiom`s — and the second is
> inconsistent with that formalisation's own definitions.** That is the line-by-line
> answer: where the book says "proved", the Lean says "assumed", and the
> assumption is contradictory.

### The ledger already refuted the worked examples, correctly. FACT

ch25's results table is corrected in place (flagged 2026-10-05, **formalized** at
`PF/Ch20Ch25NumericObstructions.lean`):

* **"K3 surface — 22 divisors"** is impossible. A complex K3 has `b₂ = 22` with
  `(h^{2,0}, h^{1,1}, h^{0,2}) = (1, 20, 1)`; Hodge classes must be rational
  *and* of pure type `(p,p)`, so the 2-dimensional `H^{2,0} ⊕ H^{0,2}` summand
  contains none; divisor classes lie in `H^{1,1} ∩ H²(X,ℚ)`, so
  `ρ ≤ h^{1,1} = 20`. Since `22 > 20` the entry is impossible, and **the excess
  is exactly the two dimensions unavailable to Hodge classes**. The note also
  records that the chapter **contradicts itself ten lines below** ("K3 surface
  with ρ=20").
* **"Abelian 4-fold — 240 cycles"** is impossible. `h^{p,q} = C(4,p)C(4,q)`, so
  Hodge classes occupy `h^{p,p} = C(4,p)²` of dimensions `1, 16, 36, 16, 1` —
  **70 across every codimension**. `240 > 70`.

**JUDGEMENT: this is genuinely good work and should be said so.** The argument
is correct, it uses real Hodge numbers, it localises the discrepancy to exactly
the non-`(p,p)` part, and it is formalised. It is the only mathematically honest
Hodge content in the repo.

**But it is not Hodge theory.** The file is ℕ-arithmetic over Hodge numbers
entered as literals — `k3_betti_decomposition : 1 + 20 + 1 = 22 := by decide`,
`k3_twentytwo_exceeds_picard_bound : 20 < 22 ∧ ∀ ρ ≤ 20, ρ ≠ 22`,
`abelian_fourfold_total_hodge_dimension : [1,16,36,16,1].sum = 70 ∧ 70 < 240`.
There is no variety and no cohomology; the Hodge numbers are cited classical
facts. **That is the right design for an obstruction** — refuting a claim needs
only the published numbers plus arithmetic — but it is a consistency checker,
not a stepping stone.

### The Hodge→P/NP bridge: it stays found. FACT

`GRAND_PROBLEM_DEPENDENCY_GRAPH_2026-08-23.md:116,126` records
`PvsNP_via_Hodge_disc5_Bridge_Open : Prop := ∃ f : Set Language → ℝ,
f ClassP = √2 ∧ f ClassNP = φ + 1/4`, **NAMED OPEN**, with
`open_bridge_iff_P_neq_NP : … ↔ ClassP ≠ ClassNP`.

**That is the same α-realisation `iff` the P/NP audit found**
(`alpha_realization_canonical_pair_iff_classes_distinct`,
`PNP_SPECTRAL_GAP_PARKED_2026-10-16.md` §2). So the "Hodge→P/NP bridge" is the
circularity already adjudicated, under a different name — and `α_Hodge := φ`
means Hodge's entire role in the α-web is "the golden ratio". The ~20
`AlphaHodge*` files are φ-identities (Fibonacci recursions, golden identities,
hyperbolic ladders): number theory about φ, not Hodge theory. **Confirmed; it
stays found; no further work owed.**

Also on record: `GRAND_PROBLEM_DEPENDENCY_GRAPH:296` — *"The substrate-level
statement `HodgeConjecture` on `HodgeAmbient` is discharged for dim=1 only, and
its bridge to actual varieties is not made."*

## 3. mathlib at the pin — the real API, not the hoped-for API. MEASURED

Searched `.lake/packages/mathlib/Mathlib` (6860 `.lean` files):

| concept | files |
|---|---|
| Kähler **manifolds** | **0** |
| Hodge decomposition | **0** |
| Hodge structure | **0** |
| harmonic forms | **0** |
| Hodge star | **0** |
| de Rham cohomology | **0** |
| Dolbeault | **0** |
| complex manifolds | **0** |
| algebraic cycles | **0** |
| Chow groups | **0** |
| cycle class map | **0** |
| differential forms (named API) | **0** |

**Present and relevant:** `AlgebraicGeometry.Scheme` (30), `ExteriorAlgebra`
(7), `ExteriorPower` (3), `IsHermitian` (8), `EllipticCurve` (18), and
`RingTheory/Kaehler/*` — **Kähler differentials** `Ω[S/R]`, which is
commutative algebra, not Kähler geometry.

**Method note, and it cost me a wrong intermediate answer.** My first pass used
`grep -E "a\|b"`, where `\|` is a *literal pipe* in ERE, not alternation — so
every multi-alternative count came back `0`, including `EllipticCurve: 0`, which
is plainly false. Caught by a sanity check (`EllipticCurve` is 18 files), redone
with correct syntax, and the redo surfaced the 5 Kähler files the broken pattern
had hidden. **Fourth harness-lies instance this week; the fix is the same one —
sanity-check a pattern against a case you know the answer to before trusting a
zero.**

## 4. The Clay statement, in formalizable terms

**Hodge conjecture.** Let `X` be a smooth projective variety over `ℂ` of
dimension `n`. For each `p`, the rational cohomology `H^{2p}(X, ℚ)` sits inside
`H^{2p}(X, ℂ) = ⊕_{r+s=2p} H^{r,s}(X)`. Define

  `Hdg^p(X) := H^{2p}(X, ℚ) ∩ H^{p,p}(X)`  — the **Hodge classes**,

and let `Alg^p(X) ⊆ H^{2p}(X, ℚ)` be the `ℚ`-span of the images of the **cycle
class map** `cl : CH^p(X) → H^{2p}(X, ℚ)` on algebraic cycles of codimension
`p`. The conjecture asserts

> **`Hdg^p(X) = Alg^p(X)` for every `p` and every smooth projective `X/ℂ`.**

(`⊇` is classical; the content is `⊆`.)

**What a faithful formalisation needs, and the status of each piece:**

| ingredient | status at pin |
|---|---|
| smooth projective variety over `ℂ` | partial (`Scheme`; no smoothness+projectivity package aimed this way) |
| `H^k(X, ℚ)` singular/sheaf cohomology | **absent** |
| the `(p,q)` decomposition of `H^k(X,ℂ)` | **absent** (needs harmonic theory or Dolbeault) |
| `CH^p(X)`, rational equivalence | **absent** |
| the cycle class map `cl` | **absent** |

**So the Clay statement is not writable, and not nearly writable.** Unlike
Navier–Stokes (where every Fefferman operator existed and only a `divergence`
helper was missing) and unlike Yang-Mills (where the lattice form is writable
today), **four of the five ingredients are wholly absent**, and the missing
pieces are not helpers — they are the subject.

## 5. Nearest formalizable stepping stone — and it is one rung, not a ladder

The only genuinely reachable piece is the **fibrewise linear-algebra core**: for
a finite-dimensional real vector space `V` with a complex structure and a
Hermitian form,

  `⋀ᵏ(V ⊗ ℂ) = ⊕_{p+q=k} ⋀^{p,q}`,  and the predicate *"ξ is of type `(p,p)`"*.

Machinery present: `ExteriorAlgebra`, `ExteriorPower`, `IsHermitian`,
`Complex.I`. This is the pointwise statement that globalises — via harmonic
theory, which is absent — to the Hodge decomposition.

**What it buys.** A *real* definition of "class of type `(p,p)`", replacing the
archive's `∃ c : ℂ, True`. That would let the repo state the Hodge **condition**
faithfully for the first time, and it would retire the inconsistent definition
permanently.

**What it does not buy — and this is the honest part.** Nothing about varieties,
cycles, or algebraicity. The conjecture's content is the `⊆` inclusion into the
image of the cycle class map, and that needs Chow groups, which need
intersection theory, none of which exists. **A faithful `(p,p)` predicate gets
you a statement of half the conjecture's left-hand side. There is no route from
there to the conjecture at this pin.**

**Rejected alternatives, for the record:**

* *Lefschetz (1,1) for a concrete surface* — needs `H²`, `Pic`, and the
  comparison between them. All absent.
* *A single (p,p)-class verification on a specific variety* — needs that
  variety's cohomology as a computed object. Absent.
* *A lattice/finite surrogate, as for YM* — **does not exist.** This is the
  structural difference: lattice gauge theory converges to the continuum theory
  and the gap question survives the regularisation; the Hodge conjecture has no
  discretisation whose resolution bears on it.

## 6. Verdict and recommendation

**BLOCKER NAMED.** No entry point to the conjecture exists at this pin, and
none is one or two files away.

**Recommendation — leave this axis alone, and do three cheap things:**

1. **Do not revive the archive files, and record why.** They are inconsistent,
   demonstrated. Their `theorem hodge_conjecture` is not a weak result, it is no
   result. **Candidate: delete them or add an inline `INCONSISTENT — DO NOT
   IMPORT` header. Pablo-gated (archive deletion is destructive).**
2. **Fix the two `theorem` labels** `thm:hodge-concentration` and
   `thm:low-rank`, which the Lean concedes as axioms — the same remedy ch23's
   2026-10-05 note prescribes for its own labels. **Pablo-gated (public text).**
   Note the ledger corrected ch25's *examples* but not these *labels* — the same
   guard-scope gap found on the YM axis.
3. **Keep `Ch20Ch25NumericObstructions.lean` and extend it if anything.** It is
   the one correct, honest Hodge artefact: published Hodge numbers plus
   arithmetic, refuting specific false claims. That is a real contribution at
   this pin, and it is the *only* shape of Hodge work that is.

**JUDGEMENT on the queue.** Of the axes scoped so far, this is the first with
**no** reachable first theorem. Yang-Mills got one (reflection positivity of the
Wilson measure, one missing instance away). Hodge gets none, because mathlib
lacks the subject rather than a lemma. **If the Millennium axes are being worked
in order of reachability, Hodge is last, and saying so now is the deliverable.**

**OPEN / not done:** whether `AlgebraicGeometry.Scheme` plus `RingTheory/Kaehler`
could support *algebraic* de Rham cohomology for smooth affine schemes (the
Grothendieck route) — that is the one direction I have not priced, and it would
be a multi-year mathlib project rather than a PF build; and whether the 238-line
archive copy differs from the 616-line one in any way that matters (different
md5s, same 5 axioms, I read the larger).

---

## Label summary

* **FACT (quoted/read from source):** both archive copies' 5 axioms and the six
  placeholder definitions verbatim; `theorem hodge_conjecture`'s two-step proof;
  ch25's 7 theorem labels and 3 `manuscriptcorrection` notes including the K3
  and abelian-4-fold refutations with their Hodge numbers; the
  `Ch20Ch25NumericObstructions.lean` theorem statements; the
  `PvsNP_via_Hodge_disc5_Bridge_Open ↔ ClassP ≠ ClassNP` record and the dim=1-only
  discharge.
* **MEASURED (this session):** `archive_axiom_is_inconsistent : False` compiles,
  `EXIT=0`, depending on exactly the replicated axiom; the twelve mathlib
  zero-counts; the present-machinery counts; `EllipticCurve = 18` as the sanity
  check that exposed the broken grep.
* **JUDGEMENT (mine):** that inconsistency is a distinct and sharper defect class
  than the P/NP and YM vacuity patterns; that the obstruction file is good work
  and the right shape; that there is no Hodge surrogate for the lattice; that the
  `(p,p)` predicate is one rung and not a ladder; that this axis should be last.
* **NOT established:** that no route exists in principle — only that none exists
  at this pin, and that the algebraic de Rham direction is unpriced (§6 OPEN).
