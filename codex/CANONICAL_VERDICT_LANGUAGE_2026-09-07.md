# CANONICAL VERDICT LANGUAGE — α-CONSTANTS

**Issued by Pablo Cohen, 2026-09-07, following the completed eight-law rigidity
audit (r332, r334, r335). This is the project's voice.**

This file is the **single source** for how the α-constant result is stated. The
completion-theorem draft, the label-retirement patch list, the rigidity audit
report, the countermodel ledger, the book, the papers and the Lean docstrings all
draw their wording from here. If wording drifts, this file is correct and the
copy is wrong.

---

## 1. THE VERDICT — canonical wording

> The substrate does not derive the α-constants; L5 is impossible through its
> formalized substrate-ratio channel; the other seven laws are independent of the
> formalized substrate assumptions; together the laws form a triangular,
> noncircular constraint system; therefore the constants are explicit postulates
> — not hidden consequences, but not an inconsistent patchwork.

### 1a. The count, corrected and closed

The wording above originally read *"the other six"*. It was issued against the
r334 report, when seven of the eight laws had been audited; **r335 audited I7
afterwards**.

Pablo approved the correction to **seven** on 2026-09-07, conditional on I7's
kernel verdict being landed and independent. **The condition is met:**

| | |
|---|---|
| theorem | `PrincipiaTractalis.AlphaStructuralLawAuditI7.I7_necessary` |
| file | `PF/AlphaStructuralLawAuditI7_r335.lean` |
| commit | `9a68ad01` |
| axioms | `[propext, Classical.choice, Quot.sound]` — exactly the mathlib three |
| `sorryAx` / `ofReduceBool` | none |
| verdict | **independent** |

The other seven are **L1, L2, L3, L4, I6, I9 and I7**. L5 is the one closed
outright, through its formalized substrate-ratio channel (r332).

**This item is closed.** No further confirmation pending.

---

## 2. THE PER-LAW FACTS BEHIND THE VERDICT

| law | forces | status against the formalized substrate | verdict |
|---|---|---|---|
| **L5** `α_NS = α_RH·π` | 3π/2 | **impossible** through the formalized substrate-ratio channel — π is not a ratio of `ℤ[1/3]` elements (r332) | independent |
| **L1** `α_Hodge² = α_Po·α_Hodge + α_Po` | φ | irrational; not ratio-reachable (r334) | independent |
| **L2** `α_P² = α_YM` | √2 | irrational; not ratio-reachable (r334) | independent |
| **L3** `α_Po + 2(α_NP − α_Hodge) = α_RH` | φ + ¼ | irrational; not ratio-reachable (r334) | independent |
| **L4** `α_QG² = α_YM·π` | √(2π) | irrational; not ratio-reachable (r334) | independent |
| **I6** `α_NS = α_YM·α_BSD` | 3π/4 | irrational; not ratio-reachable (r334) | independent |
| **I9** `α_RH·α_YM = 3` | 3/2 | **compatible** — a ratio of `ℤ[1/3]` elements. No linking theorem exists (r334, r335) | independent |
| **I7** `α_YM = α_Po + 1` | 2 | **compatible** — lies in `ℤ[1/3]`. No linking theorem exists (r335) | independent |

Structure: with the anchor, nine unknowns and nine constraints, **one constraint
per value, nowhere over-determined** — triangular. Noncircular: no law's
statement mentions the value it forces.

---

## 3. THE MANDATORY CAVEAT

**This sentence appears in every publication that states the verdict. It is not
optional and is not to be paraphrased away:**

> "Independent" means independent **relative to the formalized base theory and
> the exact constructions tested** — it does not establish independence from
> every future extension of Principia Fractalis.

Where the shorter form is needed inline: *"independent relative to the formalized
base theory and the constructions tested."* The full sentence must appear at
least once per document.

---

## 4. THE FIVE STRATA

Every statement of the result — the completion theorem, the papers, the book —
**visibly separates these five**. They are not to be merged, reordered into a
single narrative, or presented as one deduction.

| # | stratum | contents | status |
|---|---|---|---|
| **I** | **Substrate-derived structure** | What the Ocean / Timeless Field actually yields: `T_∞` as a pre-C\*-algebra, its completion, the UHF tower, the unique trace with range `ℤ[1/3]` | genuinely derived |
| **II** | **Independent selection laws** | The eight α-laws. Postulates that select a branch. Independent per §1, with the §3 caveat | postulated |
| **III** | **Constants determined after accepting those laws** | The nine α-values, unique given stratum II plus positivity plus the Perelman anchor | consequences **of II**, not of I |
| **IV** | **Unformalized physical motivation for each law** | The Galois/minimal-polynomial readings of L1, L2, L4; the "gauge duality" gloss on I6; the π-scaling narrative on L5; the H₃ Coxeter lead for φ and the ¼ | **marked as such, always** — motivation, not derivation |
| **V** | **Empirical consequences that could test the selected branch** | Predictions that distinguish this branch from others, with observable maps, stated prospectively | separate claim ladder (directive §6) |

**Stratum IV is the one that has caused the trouble.** The Galois language reads
as derivation and is not; the H₃ lead is real mathematics with no proved link to
the substrate — `H3CoxeterOrigin.lean` says so itself. Motivation must be labelled
motivation everywhere it appears.

**Stratum III must never be attributed to stratum I.** The constants follow from
the laws, and the laws are postulates. That is the whole content of the verdict.

---

## 5. NARRATIVE FRAMING — for docs, book and papers

> The Ocean / Timeless Field supply the generative arena and structural
> possibilities; the α-laws select the realized physical branch; mathematics
> constrains the branch coherently but does not currently select its constants
> without postulates.

This is the sanctioned narrative. It is accurate to all five strata: the arena is
stratum I, the selection is stratum II, the coherence is the triangular
noncircular structure, and "without postulates" is the verdict.

**It is also the honest reading of what the framework achieved** — a coherent
constrained branch — rather than a retreat from a failed derivation. The
mathematics does real work; it constrains. It does not, today, select.

---

## 6. SANCTIONED REPLACEMENT PHRASE (retired-label patching)

Where "derived", "forced" or "no free parameters" described the α-constants:

> independently postulated laws forming a triangular (minimal,
> non-over-determined) system that uniquely pins the values

Longer form for headline sites:

> The nine α-values are uniquely pinned by eight independently postulated
> structural laws together with positivity and the external Perelman anchor.
> Those laws form a triangular, non-over-determined system: one constraint per
> value. They are postulates of the framework, not consequences of its
> substrate. ("Independent" here means independent relative to the formalized
> base theory and the exact constructions tested; it does not establish
> independence from every future extension of Principia Fractalis.)

---

## 7. WHAT MAY STILL BE SAID

| claim | permitted? |
|---|---|
| "unique **given** the eight laws, positivity and the anchor" | **yes** — r128, correct and kernel-green |
| "triangular, noncircular constraint system" | **yes** — r334, r335 |
| "explicit postulates, not hidden consequences" | **yes** — this is the verdict |
| "not an inconsistent patchwork" | **yes** — the system is coherent; that is a real property |
| "derived" / "forced by the substrate" / "no free parameters" | **no** — retired |
| "independent" **without** the §3 caveat | **no** |
| stratum IV motivation presented as stratum I derivation | **no** |

---

*Canonical as of 2026-09-07. Count corrected six → seven and closed (§1a).
Public HEAD `96c71da7`. NO PUSH.*
