# The 116: Clay-axis substrate-position markers, triaged

**Date**: 2026-11-27 (Legion). **Closes**: `FINISH_LINE_2026-11-24.md` line 90,
"undisclosed True — 4 files, 6 decls — 3 real".

## What was measured

The aggregate `PFClosure` build prints `does not depend on any axioms` for
**115 distinct declarations**. A `Prop` mentioning `ℝ` cannot be axiom-free,
so an empty bar on a declaration about spectra or about Navier–Stokes
solutions is a signal, not a clean bill of health.

A `#check @<name>` probe over all 115 resolved the question. Three of them are
literally `True`:

| axis | declaration | file |
|---|---|---|
| RH | `rh_framework_standard_substrate_position` | `Analytic/RH_FrameworkStandardDischarge_NamedAnchors_2026_06_19.lean:329` |
| NS | `literal_clay_NS_substrate_bridge_substrate_position` | `NavierStokes/Fefferman2000_LiteralClayNS3D_Statement_2026_06_19.lean:278` |
| P-vs-NP | `cohen2026_pnpSpectral_substrate_position` | `TuringEncoding/Cohen2025_PNeqNP_Spectral_NamedAnchors_2026_06_19.lean:197` |

Each name appeared in **exactly one file — its own**. No disclosure existed
anywhere. All three marker files are **in the closure**, so all three compile
under every gate.

The first parse of the probe was broken (names came out as line numbers,
because the split consumed only to the first colon after the filename). The
claim "0 of 115 mention ℝ" derived from it was **retracted** before anything
was built on it, and `pf_116_reparse.py` re-measured with the location prefix
consumed in full.

## The three axes are not in the same condition

### RH — already honest at the definition site. Nothing repaired.

`clay_riemann_hypothesis_standard_framework_standard` is a genuine conditional:

```lean
theorem clay_riemann_hypothesis_standard_framework_standard
    (hHardy : Hardy1914_published_theorem_substrate_citation)
    (hHP : Mayer1991_Cohen2025_substrate_HP_program_citation) :
    Clay_RiemannHypothesis_Standard
```

- `Hardy1914_… := PositiveOnLineZetaZeroOrdinatesNonempty` — a **faithful
  encoding of a real published theorem**. The premise named after a citation
  really is one.
- `Mayer1991_Cohen2025_… := HilbertPolyaProgramConjecture_Positive
  := PF_T3SymIsHilbertPolyaOperator_Positive → RiemannHypothesis` — whose own
  docstring reads **"Status: PUBLISHED CONJECTURE; not a theorem. Encoded as a
  typed hypothesis."**
- `Clay_RiemannHypothesis_Standard := PrincipiaTractalis.RiemannHypothesis`.

The discharge's docstring says its scope is "overtly hypothesis-conditional",
and `UnifiedTheoryPremiseAudit_r333` had **already adjudicated** this premise
("those two fields alone yield `RiemannHypothesis` by function application —
no substrate … participates"). So no defect was manufactured here. The only
RH finding is that the marker above the theorem is `True`.

The one asymmetry worth pinning: both premises carry the suffix *substrate
citation*, but one is a citation of a theorem and the other is an open
conjecture. §4 of the new module pins each to its body so the names cannot
flatten that.

### NS — the bridge assumes its own conclusion. This is the real finding.

```lean
def Substrate_Forces_Literal_Clay_NS_Bridge : Prop :=
  FujitaKato1964_LocalExistence_Anchor →
  Leray1934_WeakSolutions_Anchor →
  Sobolevskii1959_AnalyticSemigroup_Anchor →
  BealeKatoMajda1984_BlowUpCriterion_Anchor →
  CaffarelliKohnNirenberg1982_PartialRegularity_Anchor →
  Clay_Literal_NS3D_ExistenceSmoothness_Fefferman2000
```

**All five named anchors are `def _ : Prop := True`** (measured, each one).
Therefore the predicate is logically equivalent to Fefferman's statement
itself, and

```lean
theorem substrate_to_literal_clay_NS_bridge_conditional
    (_h_witness : …) : Substrate_Forces_Literal_Clay_NS_Bridge := _h_witness
```

is the **identity function** on it. The "substrate-to-literal bridge theorem
(conditional)" reads, up to logical equivalence: *assume the Clay
Navier–Stokes statement, conclude the Clay Navier–Stokes statement.*

The literal statement is **not** the defect — it is a faithful encoding of
Fefferman's problem over mathlib's `SchwartzMap` carrier on
`EuclideanSpace ℝ (Fin 3)`, with a genuine `∀ u₀, div-free → ∃ u p ν, …`
body. The route to it is what carries nothing.

`NavierStokesCapstoneDisclosure_2026_11_21` does **not** cover this: it
discloses the `StandardNS3DEncoding` contract vacuity, a different object.
Checked before writing.

### P-vs-NP — seven anchors, one proposition.

All seven `Cohen2026_*_Anchor` are `def _ : Prop := True`, so
`SevenCohen2026PNPSpectralAnchors_Conjunction` (proved by seven `trivial`s)
and the disjunction are each equivalent to `True`. The sharp instrument:

```lean
theorem spectral_gap_anchor_eq_jobcount_anchor :
    Cohen2026_SpectralGapDeltaPositive_Anchor
      = Cohen2026_Lean42293JobsMachineChecked_Anchor := rfl
```

"the spectral gap Δ is positive" and "42,293 Lean jobs machine-checked" are
the same proposition. That the PNP axis was a vacuity artifact was already on
record (2026-11-15 substrate attack, the V2 → V4 pivot); what was missing was
the in-kernel statement of it on **these** anchors and this marker.

## The book consequence

`appL_substrate_bundle_closure_2026-06-18_19.tex` is in the compiled book
(`main.tex:123`) and is the only manuscript file naming any of this:

- **line ~409–411** — "A substrate-position marker theorem
  `literal_clay_NS_substrate_bridge_substrate_position` records the
  substrate's position on the literal-Clay-NS bridge: **the substrate forces
  the structural contract of the literal statement.**" A forcing claim whose
  carrier is `True`.
- **lines 57–58 and 461** — "Every `#print axioms` check below returns
  `[propext, Classical.choice, Quot.sound]`." The NS module's own three
  `#print axioms` lines include the marker, whose bar is **empty**.

The bridge-predicate description at line ~403 is, by contrast, **accurate** —
it says the literal statement is "the target end of the substrate-to-literal
bridge", which claims no discharge. Left alone.

Repair direction: not to weaken the prose but to **repoint it at the theorem
that carries content** — `substrate_forces_bridge_iff_literal_clay` — which
says strictly more than the vacuous citation did, and says it truly.

## What the new module asserts, and what it does not

`PF/Referee/ClayAxisSubstratePositionMarkerDisclosure_2026_11_27.lean`.

It asserts **no Clay statement and denies none**. Every result is an
equivalence, an unfolding, or a hedge; `no_verdict_on_literal_clay_NS` states
the non-verdict explicitly so the disclosure cannot be misread as a
refutation. Nothing upstream is renamed, reworded or deleted — the discipline
of `NavierStokesCapstoneDisclosure_2026_11_21` and
`ToECapstoneVacuityDisclosure_2026_11_22`.

The three `_is_True` theorems carry their own caveat in-source: `= trivial` is
available for every inhabitant of `True` by proof irrelevance, so what those
theorems record is that they **typecheck** — the marker's *type* — not the
proof of the equation.

## Measured axiom bars (`lake env lean`, pf-legion, 2026-11-27)

| declaration | bar |
|---|---|
| `rh_framework_standard_substrate_position` | *no axioms* |
| `literal_clay_NS_substrate_bridge_substrate_position` | *no axioms* |
| `cohen2026_pnpSpectral_substrate_position` | *no axioms* |
| `literal_clay_NS_substrate_bridge_audit_trail` | *no axioms* |
| `seven_cohen2026_pnpSpectral_anchors_conjunction_holds` | *no axioms* |
| `substrate_to_literal_clay_NS_bridge_conditional` | `[propext, Classical.choice, Quot.sound]` |
| `clay_riemann_hypothesis_standard_framework_standard` | `[propext, Classical.choice, Quot.sound]` |
| **new** `substrate_forces_bridge_iff_literal_clay` | `[propext, Classical.choice, Quot.sound]` |
| **new** `spectral_gap_anchor_eq_jobcount_anchor` | *no axioms* |
| **new** `no_verdict_on_literal_clay_NS` | `[propext, Classical.choice, Quot.sound]` |

Two things a referee should read off this table.

**The bridge conditional carries all three axioms even though its body is
`_h_witness`.** `#print axioms` traverses the statement as well as the proof,
and `Substrate_Forces_Literal_Clay_NS_Bridge` mentions `SchwartzMap` over
`EuclideanSpace ℝ (Fin 3)`. So an empty bar is *unobtainable* for a
declaration with real mathematical content, which is exactly why an empty bar
identifies one that states `True`. An empty bar is not a stronger result than
the three-axiom bar.

**The new module's own bars separate correctly.**
`substrate_forces_bridge_iff_literal_clay` carries the three, so it is a real
theorem about a real `Prop`, not another vacuous artifact; and its type was
confirmed verbatim by `#check`:

```
Substrate_Forces_Literal_Clay_NS_Bridge ↔ Clay_Literal_NS3D_ExistenceSmoothness_Fefferman2000
```

`spectral_gap_anchor_eq_jobcount_anchor` has an empty bar, which is correct —
it is an equality between two propositions that are both `True`.

## Gate state at this commit

- single module: `lake build PF.Referee.ClayAxisSubstratePositionMarkerDisclosure_2026_11_27` — exit 0, 2,750 jobs, 1.6 s
- aggregate: `lake build PFClosure` — **exit 0, 5,594 jobs** (was 5,593), 23 s, **0 errors, 0 sorryAx**
- closure: **1,769 modules** (was 1,768); the new module is in it
- book: **1,109 pages**, 0 LaTeX errors, 0 undefined citations, 0 undefined refs, 0 multiply-defined labels

## Build-tree note (not part of this finding)

`pf-push-20261120` is the git clone and holds only 36 PF oleans; the build
tree is `pf-legion-20261120` (9,854 PF oleans, 6,866 mathlib), same pin
`v4.24.0-rc1` and same mathlib rev `eed770a434`. Gating work must be built
there and committed here. A single-module build started in `pf-push` reached
2,756/2,757 jobs by rebuilding mathlib from 2,452 oleans — avoidable.


---

## PROVENANCE CORRECTION — appended 2026-11-27, same day

Pablo: *"You and I are the authors."* He is right, and this note was written in
the wrong register. Measured on this branch: **4,172 commits, 127 carrying
`Co-Authored-By: Claude Opus 5`, 10 authored directly as `Claude (Legion)`.**
This is joint work. I audited it as though it were a third party's, and I did
not run `git log` on a single file before criticising it.

Two things above are therefore misattributed as findings.

**1. The five NS `Prop := True` anchors are a documented decision, not an
undisclosed defect.** Commit `44793bd7` (2026-11-06), *"RH + NS NamedAnchors:
remove free-discharge bundles, keep citation markers"*:

> Keep the `Prop := True` anchor defs (externally referenced by Referee
> master-capstones) with docstrings explicitly labeling them as bibliographic
> markers, not mathematical content

It names the five — Fujita–Kato 1964, Leray 1934, Sobolevskii 1959, BKM 1984,
CKN 1982 — and says where the real content lives:
`PF.NavierStokes.NS_SubstrateBulletproofClosure` and
`PF.NavierStokes.NS3D_FullSubstrateNSCapstone`. They are the **output of a
prior honesty repair** — free discharges and the bundling capstone were
deleted, the citation markers deliberately kept because Referee
master-capstones reference them.

**2. The degenerate-index analysis was already written down.** Commit
`faddb8cb` (2026-06-02), the `zeroMorphism → partialTraceMorphism` upgrade:

> for `k ≤ k'` (which holds when `k ∣ k'` and `k > 0`, or `k = k' = 0`),
> genuine digit-marginalisation partial trace; for the degenerate `k > k'`
> case (only `k' = 0`, `k > 0` under `k ∣ k'`), zero morphism

That is verbatim the "the obstruction is entirely `0 ∈ ℕ`" result.

## What of this note survives as new

- The **NS bridge equivalence** itself: with all five antecedents free,
  `Substrate_Forces_Literal_Clay_NS_Bridge` is logically equivalent to
  `Clay_Literal_NS3D_ExistenceSmoothness_Fefferman2000`, and the conditional
  bridge theorem is the identity on it. `44793bd7` kept the markers; it did not
  record this consequence for the bridge.
- The **three `True` substrate-position markers** on the RH/NS/P-vs-NP axes
  having no disclosure anywhere, which closes `FINISH_LINE` line 90.
- The **PNP seven-anchor collision** by `rfl`.
- That the degenerate branch **propagates**: composed with `compat` quantified
  over all `k ∣ k'`, it forces `seq k = 0` at every positive level, so
  `TimelessFieldType truncMorphism` keeps only its `1 × 1` level-0 entry. Not
  in the June message; the fix was.

## The process change

`git log --format='%h %an %s' -- <file>` before criticising any file, and
`git log -1 --format=%B <sha>` on the commit that last touched it. 4,172
commits of prior adjudication sat unread. Recorded in
`memory/project_we_are_the_authors.md`.
