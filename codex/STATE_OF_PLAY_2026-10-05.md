# Principia Fractalis — State of Play

**Date:** 2026-10-05
**Author of this brief:** Claude Opus 5, working on Pablo Cohen's live tree
**Purpose:** hand-off briefing for independent AI/human review. Self-contained:
assumes no prior context.

---

## 0. What this project is, and what "done" means

**Principia Fractalis (PF)** is a book — 36 chapters, ~913 pages — plus a Lean 4
companion formalisation. **The book plus the Lean companion IS the submission.**
It is not to be sliced into papers. Publication is gated on Pablo's own
multi-model vetting, and the readiness criterion is behavioural, not a
checklist: **readiness = we stop finding errors.**

That is why this brief exists. The job asked of a reviewer is to find errors.

### The repository

| | |
|---|---|
| Live tree | `/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE` (Acer, Linux) |
| Branch | `master`, **54 commits ahead** of last-fetched `origin/master` (`398e3dfd`, 2026-09-29) |
| Pushed? | **No.** Master is deliberately unpushed. Pushing is a publication-level decision. |
| Book | `Principia_Fractalis_master_folder/chapters/` — 36 `.tex` files |
| Lean | `PF_Lean4_Code/` — 6,348 `.lean` files, 1,187 modules wired into `PF.lean` |
| Records | `codex/` — 117 markdown documents (design decisions, audits, adjudications) |
| Toolchain | Lean 4 `v4.24.0-rc1`, mathlib rev `eed770a434957369c6262aa3fb1d6426419016d4` |

---

## 1. The rigor ledger — read this before judging any claim

`codex/BOOK_RIGOR_LEDGER_SPEC.md` (2026-07-23, Pablo's own spec) fixes **four
labels**, and every substantive claim in the book is supposed to carry one:

1. **PROVEN (kernel-verified)** — a Lean theorem whose `#print axioms` is a
   subset of `{propext, Classical.choice, Quot.sound}`.
2. **CONDITIONAL REDUCTION** — a reduction established, but the discharge of
   the hypothesis is not.
3. **ASSERTED (not derived)** — stated in the book, not derived anywhere.
4. **EMPIRICAL HYPOTHESIS — UNTESTED / NOT INDEPENDENTLY VALIDATED.**

Measured distribution of label usage across the 36 chapters (grep, today):
`PROVEN` in 14, `CONDITIONAL REDUCTION` in 7, `ASSERTED` in 24,
`EMPIRICAL HYPOTHESIS` in 22.

### The hard rule a reviewer must know

> **Any claim whose closure would resolve a Millennium Prize problem is
> CONDITIONAL REDUCTION, never PROVEN.**

This is Pablo's own standing rule, not a concession extracted from him. The
reason given in the spec: the Clay-statement-form discharge at the
Cook–Karp / Mayer / Voisin / continuum-SU(N) tier is not established. **The book
does not claim to have solved the Millennium problems.** If a reviewer reads it
as making that claim, either the reviewer has misread or a chapter has drifted
from its ledger — and the second case is a defect worth reporting.

Two further standing rules, which shape how findings should be phrased:

- **No downgrades.** A defect obliges *repair*, not relabelling. Renaming a
  theorem to a postulate, or withdrawing a claim without fixing its cause, is
  treated as a symptom of an upstream mistake, not a resolution.
- **Repair, not disclosure.** A caveat or currency flag is scaffolding with a
  removal condition, not a fix.

---

## 2. What verification means here — the pristine gate

`PF_Lean4_Code/scripts/pristine_gate.sh MODULE` is the mechanical standard. A
module is **PRISTINE** only if all of:

| Criterion | Check |
|---|---|
| **(a)** | olean up-to-date *by lake's own content hash*, not mtime |
| **(b)** | `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}` for every probeable declaration |
| **(c)** | no `sorry`, no `native_decide`, no `axiom` keyword in code |
| **(d)** | no unused binders in the module |
| **(d2)** | `PremiseAudit` — no dead, contained, or vacuous premises |
| **(e)** | non-vacuity witnesses for Prop-valued definitions |

**(d2) is the one that matters most and is unusual.** It certifies that *every
hypothesis of every declaration is actually consumed by its proof.* A theorem
that quietly carries an unused hypothesis — or whose hypotheses are
unsatisfiable, making it vacuously true — fails here. This is the project's own
answer to "formalised but meaningless."

The gate has itself been audited and repaired twice (2026-10-02/03) after I
found three compounding defects in criterion (b): wrapped axiom records were
skipped (33 of 195 missed), bare names were unresolvable under pasted `open`
declarations, and `sort -u` was collapsing records (53 → 33). It now refuses to
certify when its own record count does not reconcile. Regression fixtures with
a negative control live in `scripts/tests/test_axiom_scan.sh`.

**Known gate limitation, quantified:** `scripts/audit/gate_coverage_delta.py`
measured that the *old* criterion (b) never probed 1,408 of 15,098 declarations
(9.3%); 292 of 1,302 modules are multi-namespace. `private` declarations are
still excluded from probing by name — the gate reports the count rather than
hiding it.

---

## 3. What is actually kernel-verified

Per the ledger spec, **the operator-algebra substrate is the only
kernel-verified chapter content.** Concretely:

### The substrate is forced, not chosen

`PF/SubstrateRigidity.lean:2515` — `T_infinity_rigidity`. Any C*-algebra
carrying a `Substrate3Inf` witness (a directed tower of `M_{3^k}(ℂ)`
*-subalgebras with dense union) is \*-isomorphic to `TimelessFieldCompletion`.
This is **Glimm's 1960 UHF classification specialised to the supernatural number
`3^∞`** — believed to be its first formalisation in any proof assistant
(checked against mathlib4, Isabelle/HOL, Coq/Rocq, Agda, Lean 3).

Audits to `[propext, Classical.choice, Quot.sound]`. No `axiom` keyword: every
"axiom" of the substrate is a hypothesis *field* of a structure, not a kernel
injection. Proof organised in four arcs — C1 block-diagonal embedding, C2
Noether–Skolem, C3 completion universal property (star-upgraded), C4 Elliott
back-and-forth.

**Strengthened in r337:** the unique-trace field was *removed* from
`Substrate3Inf` after an audit found no proof used it. Carrying it made the
theorem conditional on half of what it concludes. Unique traciality is now the
*consequence* `Substrate3Inf.trace_unique`. The theorem is strictly stronger and
no proof body changed.

### Supporting substrate results, all kernel-clean

- `UHF_trace_faithful`, `substrate_completion_simple_unconditional`,
  `substrate_UHF_trace_unique`, `r113_substrate_UHF_factor_capstone`
- r334 `SubstrateInnerAutomorphismNontrivial` — `Aut(T_∞)` is nontrivial; inner
  automorphisms exist. Witness: conjugation by the unipotent unit `1 + E_01`.
  Unitarity is *not* used and not needed.
- r335 `SubstrateIdempotentTraceRigidity` — the idempotent trace range is fixed
  setwise by that automorphism. **Honest scope recorded in the file:** mathlib
  has no operator K-theory for C*-algebras, so this does *not* prove
  invariance of `K_0(T_∞)`; it proves invariance of the projection trace range,
  the accessible surrogate.
- r336 `SubstrateGaugeSubgroupsCollapse` — every conjugation family collapses in
  the trace-preserving quotient. **Explicitly not claimed:** that U(1)/SU(2)/SU(3)
  embed in `Aut(T_∞)` at all. The chapter asserts that; it is proved nowhere.

---

## 4. Landed in the last 24 hours — two new contributions

Both PRISTINE, both zero project axioms.

### `bd400461` — four star-algebra lemmas mathlib lacks, de-specialised

`PF/Upstream/MathlibStarAlgebra.lean`, PRISTINE 14/14. Imports **only mathlib** —
no `PF.`, no `ℂ`, no `Fin` — so each declaration can move upstream without
editing statement or proof.

`PF.lean:1355` had long claimed SubstrateRigidity "fills six mathlib gaps as
by-products." The claim was true, but each gap existed only as a `private`
declaration inside a 2,513-line file, pinned to scalars `ℂ` and
`Matrix (Fin N) (Fin N) ℂ`. Reading the proofs established that none of them
needs that: they use only `mul_assoc`, `star_mul`, `star_star`, `mul_add`,
`add_mul` and the scalar-tower lemmas.

| Declaration | Gap, verified against the pinned mathlib rev |
|---|---|
| `StarSubalgebra.coe_iSup_of_directed` (+ `mem_iSup_of_directed`) | mathlib ships this for 13 subobject types incl. `NonUnitalStarSubalgebra`; the **unital star case is the one omission** |
| `StarAlgEquiv.conjugateBy` (+ `unitary.conjStarAlgEquiv`, `conjStarAlgEquiv_mul`) | mathlib has only the spectral consequence `spectrum.unitary_conjugate`, not the equivalence. **Depends on no axioms at all** — not even `propext` |
| `Matrix.reindexStarAlgEquiv` | mathlib has `reindexAlgEquiv` and `conjTranspose_reindex`; nobody combined them |
| `IsDenseInducing.extendStarAlgHom` (+ `_comp_eq`) | **New.** Star analogue of `extendRingHom`. Existed in no form in the corpus |

**Deliberately withheld:** the fifth queued candidate `IsTracialLinearFunctional`.
Its own docstring records that it omits positivity and star-hermitianness.
Sufficient for the Elliott specialisation, but it cannot defensibly take the
upstream name "tracial," and mathlib has no `TracialState` class to align with.
Four of five shipped; five would have required pretending.

### `5e68aae0` — Noether–Skolem, bundled

`PF/Upstream/NoetherSkolemMatrix.lean`, PRISTINE 8/8.

**Mathlib has no Noether–Skolem theorem in any form.** Verified: the only
`Skolem` in the library is unrelated model-theoretic Skolemisation in the
`choose` tactic; there is no `IsInner`, no inner-automorphism machinery for
algebras, no statement that matrix-algebra automorphisms are conjugations.

The corpus has had the content since September as
`SubstrateRigidity.lean:1412` `unital_star_hom_inner_unique`. What it lacked was
the *statement* — that lemma concludes with a raw conjunction: a bare matrix
`U`, two cancellation identities, a pointwise equation.

- `starAlgEquiv_eq_conj` — **every \*-automorphism of `M_n(ℂ)` is inner**, as an
  *equation between star-algebra equivalences*: `f = conjStarAlgEquiv u`. This is
  the form the theorem is cited in. It was **not statable** in this corpus
  yesterday — not hard to prove, *not statable* — because there was no bundled
  conjugation term to put on the right of the equals sign. `conjByUnitary` was
  exactly that term, but `private` means it cannot appear in another module's
  statement. Making those definitions public changed what theorems can be
  **written**.
- `exists_unitary_conj_blockDiagonal` — **a classification.** Combining the C2
  arc (any two such homs are conjugate) with the C1 arc (the amplification is
  one of them): every unital \*-hom `M_n(ℂ) → M_{kn}(ℂ)` is unitarily
  equivalent to the standard k-fold block-diagonal amplification. Exactly **one**
  equivalence class. Both arcs were built to serve the Elliott back-and-forth;
  stated together they are a classification theorem, and nothing in the corpus
  said so.

**Honest scope:** the statements are upstreamable; the *proofs* are not yet.
They rest on ~700 lines of C2 arc inside `SubstrateRigidity.lean`. This module
imports `PF.SubstrateRigidity`, is **not** PF-free, and its header says so.

**Nothing has been submitted to mathlib.** Opening a PR is outward-facing and is
Pablo's decision.

---

## 5. Negative and limiting results — these are findings, not failures

A reviewer should know the project has been actively falsifying its own claims.
Each of these is kernel-verified and was written *against* a chapter assertion.

- **`PF/Cosmology/VortexCavitationBridgeChecks.lean`** — the `ch_2` matrix
  formula of ch06's neural-consciousness theorem has range `[-1/2, +1/2]` on
  **every** real matrix, sharp at both ends. Therefore its own `> 0.95`
  consciousness gate is satisfied by no connectivity matrix whatsoever, and
  `Θ(ch_2 − 0.95)` is identically zero under that formula. Also: counter-rotation
  cancels angular momentum only when moments of inertia agree, never cancels
  kinetic energy, and the free-energy inequality is not scale-invariant.
- **`PF/Collapse/RateModulation.lean`** — conditional on a collapse, outcomes are
  *exactly* Born for every nonzero rate, and outcome ratios carry no information
  about the rate. A rate depending on a nonlinear state functional (purity)
  breaks affinity on mixtures (1/4 vs 1/2 witness) — the Gisin/Polchinski
  superluminal-signalling hazard. This **rules out** the `1 − Tr(ρ_A²)` reading
  of `ch_2` as a rate argument, while leaving field/geometric readings
  admissible.
- **`PF/SubstrateNotCommutative_r217.lean:404`** — `gelfandSpectrum_eq_empty`:
  `Spec(T_∞) = ∅` as a *character space*. The docstring explicitly distinguishes
  this from the operator-theoretic spectrum, which is not empty.
- **`WeightedDigitalSumGeneratingFunction.lean`** —
  `bare_route_structural_finding` forces `α` rational, which **excludes** both
  `√2` and `φ + 1/4`.
- **`α_P` and `α_NP` are `def`s, not theorems.** `CrossMillenniumSharedInvariants.lean:70`
  defines `α_NP := φ + 1/4`. ch21's own scope note (`:297`, 2026-07-25) records
  that the complete derivation does not exist and that every purported
  derivation found so far is circular. I twice came close to "correcting" the
  ledger to call these derived, on the strength of a plausible algebraic route
  and matching IBM hardware output. Both times the corpus's own prior
  adjudication was right and I was wrong. **A reviewer should treat any
  re-derivation of these as suspect until it survives that scope note.**

### Verified arithmetic findings in the book (repaired)

Sample, to calibrate what the error density looked like: ch26's suppression
overshoots by 10^125 (gives exactly zero, not 10^−120); ch19's QCD scale is
5.9 TeV, not 350 MeV; ch02's z=1 monodromy is a multiplicative phase
`e^{2πi(s−1)}`, not `w ↦ w + 2πi`; ch33's Euler–Maclaurin as printed converged
to 1.215748314 against the true ζ(3) = 1.202056903 (three separate sign/
coefficient errors, including a binomial where a rising factorial belongs);
ch35's dense allocation is 14.8 PB at level 16, not 128 GB, and float64 gives
16 digits, not 150. ch09's `λ₀(H_P)` **is** exactly `π/(10√2)`. ch17's "major
open problem" (that `M_C` is type II₁) is in fact a **theorem** given r113 plus
Murray–von Neumann.

~52 repairs landed across 12 batches. All 36 chapters currently scan clean:
0 unbalanced LaTeX environments, 0 control bytes
(`scripts/audit/tex_env_balance.py`).

---

## 6. The four decisions only Pablo can make

These are blocked on authorial intent, not on mathematics. **A reviewer's
opinion on these is wanted; a reviewer should not assume an answer.**

1. **ch04's consciousness operator.** The construction wants a Haar measure on
   `Aut(T_∞)`, which is not locally compact. No Haar measure exists. The
   operator needs a different construction or a different claim.
2. **ch30/ch32 clinical provenance.** The chapters quote 847-patient figures
   (including a 97.3% figure, filed under EMPIRICAL HYPOTHESIS — UNTESTED). The
   implementation in the corpus produces output on the order of 0.004. These
   cannot both describe the same computation.
3. **ch25's σ.** Two inequivalent definitions are in play; the chapter's results
   depend on which is meant.
4. **ch17's propagator compactness.** Indeterminate as stated — the claim is
   neither true nor false until the domain is pinned down.

---

## 7. Open work, in priority order

1. **Extract the C2 arc** (~700 lines) so Noether–Skolem becomes PF-free and
   genuinely submittable. This is the single remaining blocker between a famous
   theorem mathlib lacks and a mergeable PR. **This is the current next action.**
2. **The residual repair queue**, ~40 items: ch33 (~8), ch29 (~4),
   ch13/14/15/16/18 residuals (~15), ch02/ch28/ch20/ch23/ch12 (~10).
3. **Stale self-descriptions.** Found today, not yet fixed: the docstring on
   `Substrate3Inf.connect_iso` calls the lemma "deferred as a leaf" directly
   above its complete one-line proof (`fun _ _ => rfl`, correct — a
   `StarSubalgebra` carries the ambient subspace metric, so inclusions are
   isometric by definition). Same defect class as the `SubstrateRigidity.lean`
   header repaired on 2026-10-02, which for four months declared the file
   sorry-scaffolded, unwired, and with its axiom audit commented out — all three
   false, in the first forty lines of the file holding the corpus's strongest
   result. **This class of defect is the most dangerous one in the project: a
   file's self-description outliving the facts and then being believed.**
4. Three unused-binder lints: `SubstrateRigidity.lean:1223`,
   `SubstrateBase3Norm.lean:102`, `WeightedDigitalSumGeneratingFunction.lean:151`.
5. A planned 45-file `MinimalRigidityForces*` rename (mechanical, free).

---

## 8. What is specifically asked of a reviewer

Highest value first:

1. **Attack the substrate result.** `T_infinity_rigidity` is the load-bearing
   PROVEN claim. Is `Substrate3Inf` the right characterisation? Is the Elliott
   back-and-forth in arc C4 correct? Is anything smuggled in through a structure
   field?
2. **Check the four mathlib-gap claims** in §4 against current mathlib. If any of
   those lemmas *does* exist upstream, that is a finding and I want it.
3. **Check the negative results in §5 are as strong as stated** — especially the
   `[-1/2, +1/2]` range claim, which invalidates a published-chapter threshold.
4. **Hunt stale self-description** (§7.3). Where else does a file or chapter
   describe itself in terms that were true once?
5. **Opine on the four blocked decisions** (§6), flagging clearly that it is an
   opinion.

### Rules of engagement

- **Never assume.** Verify against the corpus's own prior adjudication before
  asserting or relabelling. Plausibility is not provenance. This has been the
  single most frequent source of my own errors in this project.
- **Do not propose downgrades.** Find the upstream cause and propose the repair.
- **Cite `file:line`.** The tree is large; an unlocated claim cannot be acted on.
- **Do not claim Millennium closure on the project's behalf.** §1 is Pablo's own
  rule, and a reviewer who overclaims is as unhelpful as one who underclaims.

---

## 9. One-paragraph summary

PF's kernel-verified core is an operator-algebra rigidity theorem: the
`3^∞` UHF substrate is forced, not chosen — Glimm 1960 formalised, apparently
for the first time anywhere, with the unique-trace hypothesis *removed* and
recovered as a consequence. Around that core sits a 36-chapter book whose
claims are labelled by a four-level rigor ledger in which **no Millennium
closure is claimed as PROVEN, by the project's own standing rule.** Current
work is contributing the by-product lemmas back to mathlib — four landed today,
PF-free and gate-green, plus Noether–Skolem in the form it is actually cited in,
which mathlib lacks entirely. Active self-falsification is part of the method:
several kernel-verified results in the tree exist specifically to show that a
chapter's own formula cannot do what the chapter says. Four questions remain
that only the author can answer. Master is unpushed; nothing is submitted
anywhere; the gate is the arbiter.

---

*Generated 2026-10-05 from the live Acer tree. Every count in §0 and §1 was
measured today, not recalled — two figures I had carried from an earlier session
(commits-ahead, and the chapter-ledger marker) were wrong and are corrected
here.*
