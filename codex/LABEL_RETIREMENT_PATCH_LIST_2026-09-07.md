# LABEL RETIREMENT — PATCH LIST (NOT APPLIED)

**Dispatched:** 2026-09-07, following the completed eight-law rigidity audit
(r332, r334, r335) and `codex/ALPHA_RIGIDITY_AUDIT_REPORT_2026-09-07.md`.

**Nothing in this list has been applied.** Per the standing corrections-review
rule, the book is not mass-edited without Pablo seeing the list first. This
document *is* the list.

---

## THE RULE

Retire **"derived"**, **"forced"**, and **"no free parameters"** wherever they
describe the α-constants.

**Canonical source:** `codex/CANONICAL_VERDICT_LANGUAGE_2026-09-07.md`. That file
is Pablo's wording and is authoritative; this list draws from it. If the two
differ, the canonical file is right.

**The verdict, canonical wording:**

> The substrate does not derive the α-constants; L5 is impossible through its
> formalized substrate-ratio channel; the other six laws are independent of the
> formalized substrate assumptions; together the laws form a triangular,
> noncircular constraint system; therefore the constants are explicit postulates
> — not hidden consequences, but not an inconsistent patchwork.

*(r335 audited I7 after that wording was issued, so "the other six" is now the
other seven. Substance unchanged; pending Pablo's confirmation of the count.)*

**MANDATORY in every patched document — not optional, not to be paraphrased:**

> "Independent" means independent **relative to the formalized base theory and
> the exact constructions tested** — it does not establish independence from
> every future extension of Principia Fractalis.

**Narrative framing, for prose sites:**

> The Ocean / Timeless Field supply the generative arena and structural
> possibilities; the α-laws select the realized physical branch; mathematics
> constrains the branch coherently but does not currently select its constants
> without postulates.

**Sanctioned replacement (Pablo, 2026-09-07), to be used verbatim or adapted
minimally:**

> independently postulated laws forming a triangular (minimal,
> non-over-determined) system that uniquely pins the values

**What still holds, and may still be said:** *unique*, qualified — "unique given
the eight structural laws, positivity, and the external Perelman anchor."
`AlphaSkeletonUniqueness_r128` is correct, non-circular and kernel-green. The
audit changes the **label**, not the theorem.

**Why:** all eight laws are `independent` — none redundant (remove-and-survey
witnesses, r334/r335), none derivable from the substrate (six closed by the
trace-range obstruction; the two survivors, I7 and I9, have no linking theorem),
none circular. The system is triangular: nine unknowns, nine constraints, one per
value, nowhere over-determined. Nine numerals in, nine values out.

---

## TIER 1 — HIGHEST PRIORITY (the claim is made as a headline)

| # | file:line | current | issue |
|---|---|---|---|
| **T1.1** | `Principia_Fractalis_master_folder/chapters/ch34A_substrate_theorem.tex:132` | "These values are *not* free parameters: they are forced" | both retired terms, stated as fact |
| **T1.2** | `ch34A:1010` | "the framework's nine α-values are not free parameters but…" | headline restatement |
| **T1.3** | `ch34A:1146` | "nine α-values are forced by cross-Millennium algebraic…" | "forced" |
| **T1.4** | `ch34A:438` | "deductive: the α-skeleton is forced by the invariant…" | claims *deductive*; the audit says postulated |
| **T1.5** | `ch34A:1318` | "machine-check that fourteen non-Clay α-values are forced" | "forced"; also a count to re-verify |
| **T1.6** | `ch34A:1424` | "the framework's substrate forces:" | **"substrate forces" is the exact claim r332/r334/r335 refute** |
| **T1.7** | `README.md:220` | "The nine α-values, uniquely forced (in the substrate framework) by twelve simultaneous…" | front-door claim; also "twelve" vs the audited eight |
| **T1.8** | `docs/REFEREE_QUICKSTART.md:320` | "The framework's 9-value α-skeleton is uniquely forced by the…" | referee-facing |

**T1.6 and T1.7 are the two to fix first.** "Substrate forces" is precisely the
proposition closed negatively, and the README is the first thing a reader sees.

## TIER 2 — PAPERS

| # | file:line | current | note |
|---|---|---|---|
| **T2.1** | `Papers/principia_fractalis_alpha_skeleton_2026-07-13.tex:461` | "α_Poincaré = 1 downstream-forced by (I3)+(I11)+(I7)" | the skeleton paper's own claim |
| **T2.2** | `Papers/principia_fractalis_millennium_problems_2026-07-13.tex` | 23 candidate sites | latest of the series |
| **T2.3** | `Papers/principia_fractalis_millennium_problems_2026-07-{01,05,06,07,08,09}.tex` | 23–29 sites each | **superseded dated copies — decision needed:** patch, or leave as frozen history? Recommend leaving, and patching only the latest |
| **T2.4** | `Papers/principia_fractalis_clean_2026-06-29.tex` | 5 sites | |

**Already honest — do NOT patch:**
`principia_fractalis_millennium_problems_2026-07-13.tex:160` carries an explicit
2026-07-25 honest-scope note stating the α_NP "forcing" is *circular* and "should
not be read as a derivation", and that `framework_alpha_NP_matches_IBM_empirical_peak`
is `:= rfl` between two definitions with "no measurement enters it". That
paragraph already says what this audit says. It is a model for the replacement
language elsewhere.

## TIER 3 — LEAN DOCSTRINGS

Docstrings are load-bearing: they are what a referee reads next to the theorem.

| # | file:line | current |
|---|---|---|
| **T3.1** | `PF/CrossMillenniumSharedInvariants.lean:257` | "the 9 α-values are **not free parameters**: any redefinition…" |
| **T3.2** | `PF/AlphaArchitecturalIdentities.lean:6` | "The framework's 9 α-instances are NOT independent — they are forced" |
| **T3.3** | `PF/Wave58MasterCapstone.lean:39` | "α_YM = 2, α_Poincaré = 1, α_RH = 3/2 are algebraically forced." |
| **T3.4** | `PF/Referee/MinimalSubstrateRigidityUnified.lean:19,46` | "α-skeleton is uniquely forced by:" / "those 9 numbers are forced to be" |
| **T3.5** | `PF/Analytic/RH_FrameworkStandardDischarge_NamedAnchors_2026_06_19.lean:89,212` | "α_RH = 3/2 uniquely forced by the 12 cross-Millennium algebraic…" |
| **T3.6** | `PF/CrossMillenniumReverseChains.lean:12` | "the structurally-coupled α-instances are forced to be realised at…" |
| **T3.7** | `PF/NavierStokes/NSSmoothnessProofAttemptViaAlphaRigidity.lean:23` | "`α_NS = α_YM · α_BSD` are forced by the cross-Millennium…" |
| **T3.8** | `PF/Referee/MinimalRigidityForcesPolylogResonanceAtGaloisPair.lean:19` | "α_NP = (1+√5)/2 + 1/4 are forced parametrically" |

**Do NOT patch — these already say the right thing:**

- `PF/AlphaWebDegreesOfFreedom_r124.lean:9,24,217` — r124 *quotes* the corpus's
  "not free parameters" claim in order to refute it, and its line 217 already
  distinguishes "seven of the nine are genuinely forced; α_NS and α_BSD are
  forced only…". Editing these would damage a correct negative result.
- `PF/AlphaStructuralLawAudit_r334.lean:82` — states the retirement itself.

## NOT IN SCOPE — correct uses of "free parameters" about *other* theories

Leave untouched. These are accurate and their meaning depends on the phrase:

- `ch29_observational_tests.tex:45` — ΛCDM's six free parameters
- `ch19_physical_applications.tex:110` — the Standard Model's ~19 free parameters
- `codex/R220_R222_LOG_FREQUENCY_ORIGIN_AUDIT_2026-08-24.md` — an audit *of* the
  phrase, already recommending its own corrections

## SEPARATE ISSUE, FLAGGED NOT FIXED

- `ch07_constants.tex:613` — "The universe has no free parameters—only
  mathematical necessity." This is a **cosmological** claim, not an α-skeleton
  claim, so it is outside this retirement. It is also unsupported by anything in
  the corpus. Recommend it be reviewed on its own terms.
- **Count drift.** README and several docstrings say **twelve** invariants;
  the audited system is **eight structural laws + one anchor**. r128's header
  already records that the paper's twelve are *consequences*, not inputs. Any
  patch should fix the count at the same time, or the replacement text will be
  precise about the wrong system.

---

## FIVE-STRATA RULE FOR PATCHED TEXT

Every patched passage keeps the five strata visibly separate (canonical file §4):
**I** substrate-derived structure · **II** independent selection laws ·
**III** constants determined after accepting II · **IV** unformalized physical
motivation, *marked as such* · **V** empirical consequences that could test the
branch.

Stratum III is never attributed to stratum I. Stratum IV — the Galois readings,
the "gauge duality" gloss, the π-scaling narrative, the H₃ lead — is labelled
motivation wherever it appears. That is what most of the retired language was
doing: presenting stratum IV as stratum I.

## SUGGESTED REPLACEMENT TEXT

For a headline sentence (T1.1, T1.2, T1.7, T3.1):

> The nine α-values are uniquely pinned by eight independently postulated
> structural laws together with positivity and the external Perelman anchor.
> Those laws form a triangular, non-over-determined system: one constraint per
> value. They are explicit postulates of the framework, not consequences of its
> substrate — not hidden consequences, but not an inconsistent patchwork.
> ("Independent" here means independent relative to the formalized base theory
> and the exact constructions tested; it does not establish independence from
> every future extension of Principia Fractalis.)

For a "substrate forces" site (T1.6, T3.5):

> The framework posits laws under which α_X takes this value. No derivation of
> that value from the substrate exists; the substrate's classifying invariant has
> range ℤ[1/3], and the value lies outside it (r123, r332, r334, r335).

For I7 and I9 specifically — the two laws not closed by the obstruction:

> α_YM = 2 and α_RH = 3/2 are compatible with the substrate's trace range, so a
> derivation is not excluded for these two. None currently exists.

---

## APPLICATION ORDER, IF APPROVED

1. **T1.6, T1.7** — the two live false claims (README, ch34A "substrate forces").
2. **T3.1–T3.8** — Lean docstrings; mechanical, low-risk, referee-visible.
3. **T1.1–T1.5, T1.8** — remaining book/doc headline sites.
4. **T2.1, T2.2** — current papers.
5. **T2.3** — only if Pablo wants dated copies rewritten; recommend not.

**Counts to expect:** ~8 book/doc sites, ~8 Lean docstrings, ~24 in the current
papers, ~150 across superseded dated copies if those are included.

---

*Compiled 2026-09-07. Nothing applied. Public HEAD `96c71da7`. NO PUSH.*
