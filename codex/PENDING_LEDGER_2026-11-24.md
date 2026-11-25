# PENDING LEDGER — 2026-11-24 EOD

Written because the pending set is now larger than one context buffer can be
trusted to hold. Every number here was measured today, not recalled. Items are
ordered by what is at risk, not by effort.

---

## 0. AT RISK — uncommitted, exists in exactly one place

| item | where | size | status |
|---|---|---|---|
| **ch07 fine-structure RETRACTION** | Acer working tree only | +95 lines | **NOT on Legion, NOT on origin** |
| ch09_spectral_unity correction | Acer working tree only | 2 lines | not on origin |
| `/--` → `/-!` orphan-docstring fix (2 Lean files) | Acer working tree | 2 lines | already matches Legion; safe |
| 1 unpushed commit | Acer `lean/acer-runner-switch-2026-11-20` | verify.yml runner | branch already merged to master |

ch07 withdraws `α_EM = R_f(1,2)·π/10` with: *"rests on a value of R_f(1,2)
that the series does not take."* The book therefore **currently asserts a claim
its author has already determined is false**, and the fix is uncommitted.
Preserved three ways at `D:\CLAUDE-i9\_tmp\acer_preserve_2026-11-24`
(patch + full file copies + status). **Landing it is a claim withdrawal =
Pablo-only.**

## 1. PUBLIC REPO IS 4 DAYS AND 67 COMMITS STALE

`FractalDevTeam/Principia-Fractalis` is **PUBLIC**, default branch `master`,
tip `1048f733` (2026-11-20). All 67 commits of 2026-11-20→24 corrections sit on
`lean/ns-faithful-and-vacuity-retirements-2026-11-20` (`d9a9f331`), which is
**67 ahead / 0 behind** — a clean fast-forward, no conflicts.

Live on the public master right now, all already fixed on the branch:
"Poincaré Clay-standard reproduces Perelman 2026"; Stage 1 labelled "Open
content"; 16 drifted `chNN:LLL` citations; appL's "109 anchors each axiom-free";
appH's unresolved ch₂ band contradiction.

Also: `main` is **4,048 commits behind master** (22 ahead) — dead branch, not
the default, harmless but confusing. 76 heads on origin; 6 already merged into
master and deletable.

**Merging master is Pablo-only.**

## 2. LEAN — leaf panels (compute, not proof)

| | |
|---|---|
| panel sources (`PF/Analytic/`) | 8,717 |
| panel oleans built | 7,361 |
| **remaining** | **1,356** |
| est. single-core wall time | ~35 h (1,085 Fourier ≈ 9 h @ ~29 s; 220 Box900 ≈ 25 h @ ~415 s) |

180 of 200 sampled have **no importer** — they gate nothing, they are additive
certificates. `LEAN_NUM_THREADS=1` is the OOM control, not `taskset`.

## 3. LEAN — the real remaining defect surface

* **3 files** with a comment-stripped `Prop := True` and no disclosure anywhere:
  `Empirical/ProblemClassTriClass_2026_06_22`,
  `NumberTheory/AndrewsCurtisFrameworkAttack`, `Referee/FrontierLedger`.
  (`Analytic/Hardy1914_..._Anchor` is disclosed in a companion file — not a
  defect.)
* `Prop := True` total: **272** comment-stripped (337 raw; 65 was comment
  inflation). 232 are full `def … : Prop := True`.
* **0 sorry, 0 native_decide, 0 project axioms** — the two `axiom ` greps are
  false positives (prose in a string; an error message in `PremiseAudit.lean`).
* **`localAt` injectivity** — the measured removal condition that would make
  `modular_flow_separates_regions` (landed today, `d9a9f331`) unconditional.

## 4. BOOK — unswept, 3,503 lines of 37,046 (9.5%)

43 of 52 `.tex` files carry a self-grading ledger. Remaining, by risk:

| file | lines | why it matters |
|---|---|---|
| **ch23_yang_mills** | 784 | a Clay chapter with **no ledger at all** |
| **appC_clinical** | 462 | no ledger, AND its 0.50–0.74 "vegetative" band straddles its own ROC bins (0.50–0.69 at 8%, 0.70–0.89 at 42%) — the other half of the appH contradiction |
| appK | 1,007 | **swept today, zero defects found**; needs its ledger written |
| appB_brst | 348 | unswept |
| ch20 rev2 inserts | 238 | unswept |
| appD / appG / appF / appE | 664 | reference material, low claim density |

Expect **~10 more defects** at the measured session rate of 2.8 per 1,000 lines,
concentrated in ch23 and appC.

## 5. OWED CORRECTIONS (identified, not yet made)

* **NS (C) qualifier** — the α-web cites the Córdoba/Buckmaster/OpenAI chain
  without the qualifier that it settles Fefferman **(C)**, not (A)/(B).
* **ch25 abelian 4-fold** label + codimension — figure withdrawn, not replaced.
  **Pablo's call.**
* **appH / appC band reconciliation** — closes when either the normal-waking
  figure is re-measured with an interval (any value ≥ 0.6099 as-printed clears
  the band) or appC's cut-points are re-derived from its own outcome table.

## 6. THE α-SKELETON, MEASURED TODAY — read this before quoting "coincidences"

29 identities, verified to hold at the stated values (all residuals 0).
Solution variety: **one point, 0 free parameters** — the 29 do uniquely
determine all nine α's.

**But the Gröbner basis of all 29 has exactly 9 generators, and they are the
nine definitions:**

```
a_Poincare − 1   a_P² − 2    a_RH − 3/2   a_YM − 2    a_NS − 3π/2
a_BSD − 3π/4     a_QG² − 2π  a_Hodge² − a_Hodge − 1   a_NP − a_Hodge − 1/4
```

**All 29 identities are implied by the other 28** (ideal membership via Gröbner
reduction). Negative control passed: three false identities correctly read
INDEPENDENT, two true consequences correctly read REDUNDANT — the test
discriminates.

So: 9 constraints, 9 unknowns, exactly determined, **zero slack**. Confirms
`ADVERSARIAL_ALPHA_2026-10-02` ("exactly determined with zero redundancy") and
`ALPHA_SUPPLIED_VS_DERIVED_2026-10-01` ("those were written down by reading the
literals they are then used to re-derive"). The 29-locus file's own header
already calls the surplus "AMPLE algebraic content", not independent evidence.

Only two generators carry structure rather than stipulation:
`a_Hodge² − a_Hodge − 1` (φ's defining equation) and the two square roots.

## 7. CORPUS DEPTH, honestly separated

| | files | lines | theorem/lemma |
|---|---|---|---|
| **hand-written** | 2,149 | 503,477 | **20,723** |
| generated panels | 8,717 | 7,699,388 | 303,071 |
| mathlib at this pin | 6,860 | 1,857,771 | 157,603 |

**The honest number is 20,723 theorems across 2,149 hand-written files = 13.1%
of mathlib's theorem count.** Quoting the 323,794 total would be a 94%-panel
artifact. Largest single build closure observed in a log: 10,103 jobs.

## 8. SPINE BALANCE — not equal, and the first arrow is a naming artifact

| arrow | non-panel files |
|---|---|
| Ocean of timelessness | **not separately named** — `Ocean` appears in 1 file, as a citation to the prior book *The Ocean of Timeless Existence*; the arrow is realised as the `Timeless*` family |
| T_∞ / Timeless substrate | 108 |
| Consciousness | 185 |
| Grothendieck gluing | 34 |
| Emergent locality (net/KMS) | 27 |
| Distinguishability | 12 |
| Modified relativity | 5 |
| Churn | 4 |

Effort is **~46:1** between the heaviest and lightest arrow. Equalising it is a
real programme, not a sweep.

## 9. STALE HEADERS — the recurring defect class, three instances today

A file's own header is **not** a map of the corpus. Confirmed three times:

* `EmergentLocalityNet_r350` (2026-10-25) says Stage 4 ABSENT and locality has
  zero Lean files — 27 files landed after it.
* `TimelessField.lean:157` called Stage 1 "Open content" — machine-checked
  collapsed since 2026-09-17 (r333/r334/r336). Fixed `a0a85c8b`.
* r336/r217's `chNN:LLL` citations drifted up to +250 lines. Fixed `a0a85c8b`.

Instrument: `codex/check_book_citation_drift.sh`. Companion:
`codex/check_clause_counts.py` (depth-aware; a naive `grep -c '∧'` miscounts
bracket bundles).

---

**Count of my own flags raised and retracted on measurement today: 14.** Every
one would have become a false correction to the manuscript. The retraction rate
is the gate working, not waste — but it is also why no number in this ledger
should be quoted without its measurement.
