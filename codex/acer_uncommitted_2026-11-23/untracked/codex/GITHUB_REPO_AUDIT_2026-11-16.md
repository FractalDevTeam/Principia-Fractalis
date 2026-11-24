# GitHub repository audit — FractalDevTeam/Principia-Fractalis

**Date:** 2026-11-16. **HEAD at audit:** `0285a6cb` on `origin/master` (divergence `0 0`).
**Scope:** the *repository as a public artifact* — metadata, licensing, CI, the GitHub
Pages site, branch/tag/release surface, tracked-content hygiene, and the public-facing
claim surface. **Not** a re-audit of the mathematics or the book prose; those have their
own campaigns (`AI_SLOP_AUDIT_*`, `LEAN_CITATION_AUDIT_*`, `FRAMEWORK_CLAIMS_GAP_INVENTORY_*`,
`HONEST_REFEREE_PROOF_ASSESSMENT_*`) and this audit does not duplicate them.

**Why this audit did not exist before:** `codex/` holds 34 audit documents, all of them
content audits. The repository itself — the thing a referee, a journalist, or a Clay
reviewer actually opens first — had never been audited. It is step 3 of the slop
remediation program ("then clean up the GitHub repository"), reached early because the
public surface now contradicts the corpus's own current position.

**Repo facts:** PUBLIC · 348,012 KB disk · 7 stars · 1 fork · issues enabled, 0 open ·
default branch `master` · 29 remote branches · 6 tags · 1 release (2025-11-22) ·
13,220 tracked files (10,768 `.lean`, 807 `.v`, 505 `.md`, 351 `.py`, 249 `.tex`, 99 `.pdf`).

---

## Severity 1 — The public referee documents assert four Clay axes "unconditional" on `True` markers

**This is the finding that matters.** `docs/REFEREE_QUICKSTART.md` — the document the
site directs a referee to read first — and `docs/CLAY_PER_AXIS_CITATION_CARDS.md` tell a
referee that four of the six Clay axes are unconditionally discharged:

- `REFEREE_QUICKSTART.md:115` — "Clay-Standards are unconditional on V4"
- `REFEREE_QUICKSTART.md:129` — `ym_unconditional_marker : True` — "YM is unconditional on V4"
- `REFEREE_QUICKSTART.md:131` — `hodge_unconditional_marker : True` — "Hodge is unconditional at V4 substrate scope"
- `REFEREE_QUICKSTART.md:128` — `ns_bootstrap : NS_LocalToGlobalBootstrap` — "**ceremonial** (proof body does not consume it; V4 NS is unconditional)"
- `REFEREE_QUICKSTART.md:79` — instructs the referee to run
  `#print axioms PF.Referee.UnifiedClayClosureLinkage.four_axes_unconditional`
- `CLAY_PER_AXIS_CITATION_CARDS.md:378` — "For four axes (NS, YM, BSD, Hodge): an **unconditional** discharge"

**Verified against the Lean tree, not inferred:**

| Public claim | Actual Lean content |
|---|---|
| `ym_unconditional_marker` | `PF/Referee/PerelmanAnchoredSimultaneousClosure.lean:194` — field of type **`True`** |
| `hodge_unconditional_marker` | same file `:202` — field of type **`True`** |
| `ns_bootstrap` "ceremonial" | a **dead hypothesis**, publicly described as such |
| `four_axes_unconditional` | exists, `PF/Referee/UnifiedClayClosureLinkage.lean:169`. Its **type** is honest — `Clay_X_Standard` applied to `PF_NS3DEncodingV2` / `PF_YMEncodingBridge5` / `PF_BSDEncodingV5` / `PF_HodgeEncoding`, i.e. **PF's own encodings**. Its **docstring** says `★★★ FOUR AXES UNCONDITIONALLY CLOSED ★★★ — NS, YM, BSD, Hodge are each AXIOM-FREE Clay-Standard discharged`. |

So a referee following the quickstart prints the axioms of a theorem whose docstring says
four Clay problems are closed, gets the clean three-axiom bar back, and is given two
`True` markers and one dead hypothesis as the evidence. **This is precisely the vacuity
pattern Acer disclosed in-kernel for P vs NP V2 on 2026-11-15** (`0285a6cb`:
`computability : True` ⇒ `class_P_typedV2 = Set.univ` ⇒ the headline composition was
vacuously true). The in-kernel disclosure landed. The public web page saying the same kind
of thing about four *other* axes did not.

It also contradicts the project's own current position on every axis it names: five open
substantive cores as of `0285a6cb`, Hodge rated **BLOCKED** and P vs NP **PARKED** in
`MILLENNIUM_STATUS_2026-11-11.md`, and the book's own ch20–ch25 preambles opening with
"The Clay statement remains open."

**Repair (not disclosure):** the upstream cause is that the June–September honest-scope
campaign had `chapters/` in scope and `docs/` outside it. The fix is to bring `docs/` under
the same pass that produced `revision2_changes.tex` — per-axis, with the structural-vs-
substantive distinction the 2026-11-15 session established, and with `True`-typed markers
named as structural tags rather than as "unconditional". No claim needs weakening that
the book has not already stated more carefully; this is a sync, not a retreat.

---

## Severity 2 — The honesty campaign's scope gap, enumerated

Same root cause as S1, remaining instances. Every file below is live on
`https://fractaldevteam.github.io/Principia-Fractalis/` and redeploys on every push
(67 successful Pages deployments).

| File | Last changed | Claim that is now wrong |
|---|---|---|
| `docs/ADVERSARIAL_REBUTTAL_2026_06_23.md:222` | 2026-09-29 | "discharged literal-mathlib-form Clay content on **5 of 6 axes**"; "**29/9 over-determination** on the algebraic spine" — the forcing test answer is NO (rank 10 in 10 unknowns), per `codex/` forcing-test adjudication |
| `docs/ADVERSARIAL_REBUTTAL_2026_06_23.md:135` | 2026-09-29 | "3 named open conjectures + **4 UNCONDITIONAL discharges**" |
| `docs/governance/FRAMEWORK_FIRST.md:48` | — | supplies an approved sentence to repeat: "substrate-linkage + **11 cross-Millennium invariants** + α-skeleton — all machine-verified, **axiom-free**". The invariant count is **15** in Lean (`CrossMillenniumSharedInvariants.lean`), **12** in `CITATION.cff`, **11** here |
| `docs/CLAY_PER_AXIS_CITATION_CARDS.md` | **2026-06-21** | five months stale; predates the P/NP vacuity findings, the YM mass-gap refutation, the Hodge block, the π/10 retraction, and the empirical scorecard |
| `docs/index.html` | 2026-07-23 | four months stale. Content is otherwise **the best artifact in the repo** — scoped to the UHF result, explicit "to the best of our knowledge… we welcome pointers to prior art" |

Note the internal inconsistency the docs already contain:
`CLAY_PER_AXIS_CITATION_CARDS.md:246` says "**Honest residual**: the unconditional V4
discharge is tautological by…" while `:378` of the same file summarises it as an
"unconditional discharge". The honest sentence is already written; it just lost to the
summary.

---

## Severity 3 — The README badge advertises a verification gate that has never passed

`README.md` line 3 is a status badge for `verify.yml`, described in the workflow header as
"Outcome (PASS / FAIL) gates the green/red badge displayed in README.md."

**All-time run history for `verify.yml` (GitHub API, full pagination): 1,223 runs —
1,216 cancelled, 6 failure, 1 in progress, 0 success.** It has never passed. Four
independent defects:

1. **Operational.** `concurrency: { group: verify-${{ github.ref }}, cancel-in-progress: true }`
   plus a build that takes ≥16 minutes, against pushes minutes apart (2026-11-16: 03:59,
   04:03, 04:12, 04:17, 04:23). Every run is cancelled by the next push. On a productive
   day the gate *cannot* complete.
2. **Logic — the gate cannot fail on axiom content.** `verify.sh:86-91` builds the
   unexpected-axiom list as
   `grep -E "depends on axioms:" | grep -vE "propext|Classical\.choice|Quot\.sound" | grep -v Hardy1914… | …`.
   Every `#print axioms` line contains `propext`, so the allowlist deletes **every**
   line — including one that also carried `sorryAx`. `UNEXPECTED_AXIOMS` is always empty,
   the `exit 0` path always taken, `exit 2` unreachable. Known since 2026-10-17
   (`infrastructure_ci_axiom_gate_vacuous`), fix proposed, never applied — Pablo's call.
3. **A failed checker still passes.** `verify.sh:78-80` runs the three `AxiomCheck_*`
   builds with `|| true`. If the checker module fails to build, the log is empty and the
   gate reports PASS. Same trap as the Legion verify tree, where a FAILED build printed a
   clean axiom bar.
4. **Stale contract.** The allowlist encodes a four-citation-axiom contract
   (`Hardy1914_published_theorem_substrate_citation`,
   `Mayer1991_Cohen2025_substrate_HP_program_citation`,
   `Mayer1991_Cohen2025_T3_sym_HP_program_citation`,
   `framework_substrate_pins_bulletproof_bundle`) that the corpus's current
   "three-axiom bar throughout" position has moved past.

The three `AxiomCheck_*` modules it builds all still exist — that part is fine.

**Repair:** drop `cancel-in-progress` (or raise the concurrency group to the workflow and
let runs queue); invert the allowlist to a positive match (`grep -oE "axioms: \[.*\]"`
then reject any token outside the permitted set, per-line, counting rejects); remove
`|| true` or test the log is non-empty before concluding; re-pin the expected axiom set to
the current contract.

---

## Severity 4 — The license the repo states is not the license it ships

| Source | States |
|---|---|
| `LICENSE` (139 lines) | "PRINCIPIA FRACTALIS NON-COMMERCIAL RESEARCH LICENSE / Copyright (c) 2025 Pablo Cohen / **All Rights Reserved**" — a bespoke licence |
| `README.md:6` | "License: **CC BY-NC 4.0**" |
| `CITATION.cff` | `license: "CC-BY-NC-4.0"` |
| GitHub | classifies the licence as **"other"** (it cannot match the bespoke text) |

CC BY-NC 4.0 and a bespoke all-rights-reserved licence are materially different grants.
Anyone reusing the work on the README's stated terms would be relying on terms the LICENSE
does not give. Pick one and make the other two match.

Second issue in the same area: **12 files under `PF_Lean4_Code/PF` carry mathlib's
`Released under Apache 2.0 license` header**, and `mathlib_candidates/` (9 files) +
`mathlib_submission/` (14) + `vendor/interval` (74) are third-party-derived. The headers
are preserved — correct — and `vendor/interval` ships its own `LICENSE` plus a
`VENDORING.md`, which is good practice. But the top-level LICENSE asserts "All Rights
Reserved" over the whole tree with no carve-out for files bearing their own terms. One
sentence in LICENSE fixes it.

---

## Severity 5 — Version identity sprawl: a citer cannot determine what they are citing

| Source | Version / title |
|---|---|
| `CITATION.cff` (what GitHub's "Cite this repository" reads) | **2.6.1**, released 2026-06-23, titled "Principia Fractalis: A Substrate-Level Theory of Everything" |
| `README.md:290` | **2.6.1** |
| Book title page | **2.7.1** / 2.7.0 |
| `main.pdf` internal title | **"Fractal Resonance Mathematics: The Definitive Textbook"** |
| Newest git tag | **v2.2.0** |
| Latest GitHub release | "Principia Fractalis Lean Skeleton V2", **2025-11-22** (a year old) |
| `ARCHIVE/README.md` | describes the live manuscript as "**Version 1.2.0**, Substrate-Level Meta-Theorem Edition" |

Seven identities. `CITATION.cff` is the one that propagates into other people's
bibliographies, and it is five months stale with an abstract that reads much harder than
the current position — see S6.

---

## Severity 6 — `CITATION.cff`'s abstract is the strongest overclaim in the repository

It is the canonical citation metadata, and it asserts, unqualified:

- "Principia Fractalis is a substrate-level **Theory of Everything**" — the project's own
  position is that it is not a ToE until the physical dictionary is derived and one number
  confirmed.
- the six Clay problems "arise as six co-implied substrate-level projections … **uniquely
  forced** by twelve cross-Millennium algebraic invariants" — the forcing test returns NO
  (rank 10 in 10 unknowns), and the invariant count is 15, not twelve.
- "the sharpened per-axis Riemann Hypothesis discharge … **closes the literal Clay-standard
  predicate** on `Complex.riemannZeta` under exactly two named substrate-tier **citation
  axioms**" — "closes the literal Clay-standard predicate" is the claim the whole book now
  declines to make, and "citation axioms" are project axioms, which contradicts the
  README's own "zero project axioms" headline three files away.
- "**four unconditional axis discharges (NS, YM, BSD, Hodge with no axiom dependency)**" —
  the S1 finding, in the citation metadata.

Also stale in the same file: the mathlib-PR situation, and the Coq characterisation (which
is, to its credit, careful: "the Coq layer is a structural-shape mirror").

---

## Severity 7 — Four top-level documents tell the public the mathlib PRs are merged

| File | Last changed | Says |
|---|---|---|
| `DO_THIS_NOW_mathlib.md:40` | 2026-08-01 | "**#42093 is already done** — grunweg added it for you. Don't touch it." |
| `SUBMIT_MATHLIB_PRS.md:90,97` | 2026-08-03 | "Build+Lint green, **MERGEABLE**"; "Build ✅ Test+lint ✅ **MERGEABLE**" |
| `HANDOFF_2026-07-28.md:75` | 2026-07-29 | "**green, mergeable**" |
| `MATHLIB_PR_ROADMAP.md` | 2026-07-23 | "file complete & kernel-verified … awaiting `gh auth` to fork/submit" |

**Live state (`gh`, 2026-11-16): 3 open (#42093, #42095, #42100), 2 closed (#42101, #46025),
0 merged.** #46025 closed 2026-11-15 06:27Z carrying `LLM-generated` and
`increases-technical-debt` labels. "mergeable" is CI language for "no merge conflict"; it
has never meant merged, and these four files are the origin of any "our work is in mathlib"
impression. They sit at the repository root, where they are among the first things a
visitor sees.

`HANDOFF_2026-07-28.md:144` is worth preserving as written: "**No Millennium Problem is
solved.** Not RH, not P vs NP, not BSD, not…". That sentence is the standard the rest of
the public surface should meet.

---

## Severity 8 — ARCHIVE: 121 tracked `.lean` files with maximal-claim names, two inconsistent, in the two subdirectories `ARCHIVE/README.md` does not mention

Tracked and public:

```
ARCHIVE/2026-06-16-orphans/Hodge_Conjecture_COMPLETE.lean          (616 lines)
ARCHIVE/2026-06-08-cleanup/.../Hodge_Conjecture_COMPLETE.lean      (238 lines)
ARCHIVE/2026-06-16-orphans/P_NP_Proof_COMPLETE.lean
ARCHIVE/2026-06-16-orphans/P_NP_COMPLETE_FINAL.lean
ARCHIVE/.../PF_AXIOM_FREE_TEST/P_NP_Complete_Proof_PROVEN.lean
ARCHIVE/2026-06-16-orphans/NavierStokes_COMPLETE.lean
ARCHIVE/2026-06-16-orphans/AXIOM_ELIMINATION_COMPLETE.lean
ARCHIVE/2026-06-08-cleanup/.../Problems143_COMPLETE.lean
ARCHIVE/2026-06-08-cleanup/.../ClinicalValidation_COMPLETE.lean
ARCHIVE/2026-06-16-orphans/PF/RH_Complete_ATTACK.lean
```

Verified directly: both `Hodge_Conjecture_COMPLETE.lean` copies declare
`axiom hodge_class_high_concentration` and `axiom concentration_implies_algebraic` and then
prove `theorem hodge_conjecture` from them. Per `HODGE_SCOPING_BLOCKED_2026-10-17.md` that
axiom pair is **inconsistent** (entails `False`), machine-demonstrated, and the same doc
correctly records "**No live soundness risk** — both files are ARCHIVE orphans, outside
`PF_Lean4_Code`, not imported by `PF.lean`." The technical risk is zero. The presentational
risk is not: the files are public, their names are the strongest possible claims, and an
inconsistent file "proves" anything a reader asks it for.

**`ARCHIVE/README.md` is good where it reaches and does not reach here.** It opens
correctly ("Status: Historical reference only. Nothing in this directory participates in
the active build…") and documents four subdirectories. The six that exist are
`2026-05-XX-historical`, `2026-06-08-cleanup`, `2026-06-16-orphans`, `2026-06-19-pre-shine`,
`2026-06-24-bait-paper-retired`, `2026-11-03-pnp-axiom-elimination-retired`. **The two
undocumented ones are exactly `2026-06-08-cleanup` and `2026-06-16-orphans`** — the two
holding all 121 `.lean` files and both inconsistent copies. This is the third instance in
this audit of a guard that was correct inside its scope while the defect sat outside it.

Two further defects in that README: it claims three paths are "tracked as orphan submodule
pointer", but the index contains **0 gitlinks** and there is **no `.gitmodules`** — the
mechanism it describes does not exist; and nothing states the inconsistency or the
never-revive rule.

**Repair:** extend `ARCHIVE/README.md` to all six subdirectories, name the two
inconsistent files explicitly with the never-revive rule and a pointer to the scoping doc,
and correct the submodule sentence. Deletion is not the repair — the git history and the
audit trail are the point of keeping them. Whether 484 MB of superseded material belongs
in the *same* public repository is a separate call that is Pablo's.

Outside ARCHIVE, **70 tracked filenames are claim-shaped**, including
`PF_Coq_Code/PF/{RH,YM,NS,BSD,Hodge,PNP}_SubstrateBulletproofClosureCoq.v`,
`Bulletproof_FrameworkClosureCoq.v`, `P_NP_Complete_ProofCoq.v`,
`PerelmanSolvedCaseCrossValidationCoq.v`, `PFCompleteFrameworkCapstoneCoq.v`,
`PF_Lean4Lean/PF_L4L/Referee/BulletproofedClosure_*`. These are live, not archived. The
`★★★` / "BULLETPROOF" docstring register is also what mathlib reviewers reacted to on
#46025.

---

## Severity 9 — Tracked third-party raw data and build junk; `.gitignore` rules that miss their own targets

| Item | Size | Note |
|---|---|---|
| `ARCHIVE/…/physionet-sleep-data/SC4001E0-PSG.edf` | **47 MB** | PhysioNet Sleep-EDF raw recording, redistributed with **no accompanying licence or attribution file** anywhere in the tree |
| `ARCHIVE/…/physionet-sleep-data/tmpe44v3pjv` | **15.9 MB** | a literal temp file, tracked |
| `hodge_conjecture_hirez.png` | 11.6 MB **× 2** | live + ARCHIVE copy = 23 MB for one image |
| `main.pdf` | 9.8 MB + 8.9 MB | live + ARCHIVE copy |
| `Papers/principia_fractalis_millennium_problems_2026-07-0{5..9}.pdf` | ~1.2–1.4 MB × 5 | consecutive daily snapshots, all tracked |
| `ARCHIVE/2026-06-16-orphans/…_814pages_SECTION_RESTORED.pdf` | 8.7 MB | superseded manuscript |
| tracked `.log` | 13 files | incl. LaTeX `texput.log`, `main.log` |
| tracked `.bak_attrib_*` / `.prefix_*` | 18 files | content duplicated from history |
| tracked `.pkl` / `.npz` | 7 / 12 | pickled analysis state |

`.gitignore` already forbids most of these — `*.log`, `*.bak`,
`*.prefix_20[0-9][0-9]-[0-9][0-9]-[0-9][0-9]`, and specifically
`FRAMEWORK_APPLICATION/Real_EEG_validation/raw_data/`. Two reasons they are here anyway:
ignore rules never apply to files already tracked, and **the EEG rule names the live path
while the 63 MB copy lives at `ARCHIVE/2026-06-08-cleanup/dirs/FRAMEWORK_APPLICATION/…`**,
outside the pattern. Fourth guard-scope instance.

Credit where due: `.gitignore` is the most self-aware file in the repository. Its own
comments record that `a1_v4.sh` was left untracked for days and then filtered out of
`git status`, "which made a 'tree clean' report false", and conclude "Anything whose
content is NOT already in git gets TRACKED, never ignored." That is the right standard; it
is simply younger than the violations.

Nothing in `.lake/` and no `.olean` is tracked — that dimension is clean.

---

## Severity 10 — Branch and release surface

- **29 remote branches. 14 are from November 2025.** Public, claim-shaped, year-old:
  `zero-sorries-complete`, `complete-100-percent-coverage`, `axiom-elimination-complete`,
  `final-zero-sorries`, `final-publication-ready`, `turing-machine-complete`,
  `coq-millennium-verification`, `millennium-bridges`.
- **`origin/main` is a trap.** Default branch is `master`, but a branch named `main` exists
  at `397ec5fe` (2025-11-28), **22 commits ahead on its own line and 3,972 behind master**.
  Any tool, script, CI, or person who assumes `main` gets a year-old tree from the
  "zero-sorries-complete" era.
- **Latest release is `Lean` / "Principia Fractalis Lean Skeleton V2", 2025-11-22** — a
  year old, while the book is at 2.7.1 and the corpus at 10,774 files. There is also a tag
  named simply `Lean`.
- Three `backup/pre-ai-strip-2026-11-07/*` tags are fine and well-named.

---

## Severity 11 — README reproducibility block is stale, and one pin is wrong

`README.md` presents a "Verified build data at HEAD `ff4c50f2` (2026-07-23)" table, updated
to 2026-08-05, and states the figures elsewhere are historical — honest, but HEAD is now
2026-11-15 and the numbers (`lake build PF` 4,471 jobs; full 8,928) no longer describe the
corpus (today's builds report 3,100–3,400 jobs).

**One factual error:** the table says "mathlib pin `eed770a4`". In
`PF_Lean4_Code/lake-manifest.json`, `eed770a4…` is the **`interval` package's** rev;
mathlib is pinned at **`c205f530…`**. The toolchain line (`leanprover/lean4:v4.24.0-rc1`)
is correct and matches `lean-toolchain`.

---

## What is clean, and should be said so

- **No secrets.** A pattern scan across all 13,220 tracked files for GitHub tokens, OpenAI
  keys, AWS keys, Google keys, Slack tokens and PEM private-key blocks returns **nothing**.
  No `.env`, no `*.pem`, no `*.key`, no `id_rsa`, no credential files tracked.
- The only emails in tracked content are Pablo's own (111 × `psolorzano@gmail.com`,
  30 × the Berklee alumni address, 22 × `pablo@xluxx.net`) — deliberate authorship
  metadata, consistent with the ORCID. Worth knowing they are harvestable from a public
  repo; not a leak.
- **Every internal link in `README.md` resolves** to a file on disk. Zero dead links.
- **`main.pdf` in the repo is the current book** — 1,044 pages, 9.8 MB, matching the
  2026-11-15 state including Appendix M.
- No build artifacts tracked (`.lake/`, `*.olean`: zero).
- `vendor/interval` is properly vendored: upstream `LICENSE` retained plus a `VENDORING.md`
  explaining provenance.
- `docs/index.html` is the strongest public artifact in the repository: it leads with the
  one unimpeachable result (UHF construction, faithful trace, simplicity), states the
  axiom bar, and closes with "to the best of our knowledge … we welcome pointers to prior
  art." It is the model the rest of `docs/` should follow.
- `ARCHIVE/README.md`'s opening status paragraph and `.gitignore`'s commentary are both
  examples of the project policing itself correctly; both simply have scope gaps rather
  than wrong content.

---

## Ordered repair list

Each item is a correction to the repository, not a new document.

1. **Re-sync `docs/` under the honest-scope pass** (S1, S2). Per-axis, using the
   structural-vs-substantive distinction from 2026-11-15; name `True`-typed markers as
   structural tags; retire "four axes unconditional" in favour of the encoding-relative
   statement the Lean types actually carry. Also amend the `four_axes_unconditional`
   docstring so the prose matches its own type.
2. **Fix `verify.yml` + `verify.sh`** (S3): queue instead of cancel; positive-match axiom
   allowlist; drop `|| true`; re-pin the expected axiom contract. Until then the badge
   should not be in the README, because it has never reflected a pass.
3. **Reconcile the licence** (S4): make `LICENSE`, `README.md`, and `CITATION.cff` state
   the same grant, and add the carve-out sentence for files bearing their own terms.
4. **Rewrite `CITATION.cff`** (S5, S6) against the current position, and settle one
   version identity across `CITATION.cff` / README / title page / tags / releases.
5. **Correct the four root-level mathlib documents** (S7) to "submitted, none merged",
   with #46025's closure and the decomposition plan.
6. **Extend `ARCHIVE/README.md`** to all six subdirectories, name the two inconsistent
   files with the never-revive rule, and fix the false submodule-pointer sentence (S8).
7. **Add PhysioNet attribution or untrack the 63 MB** (S9), and untrack `tmpe44v3pjv`.
8. **Prune or rename the year-old claim-shaped branches, and resolve `origin/main`** (S10)
   — at minimum a commit on `main` pointing at `master`, so nobody lands on 2025 content.
9. **Refresh the README build block and correct the mathlib pin** (S11).
10. **Cut a current release** so the newest public artifact is not a year-old Lean skeleton.

**One standing note for whoever executes this:** four of the eleven findings above are the
same failure — a guard that was correct inside its scope while the defect sat just outside
it (`chapters/` vs `docs/`; the EEG ignore rule vs the ARCHIVE copy; `ARCHIVE/README.md`'s
four documented subdirs vs the two that mattered; the axiom allowlist vs the lines it
deleted). When fixing any guard here, state its scope explicitly and check the complement.

---

*Audit performed from the Acer live tree at `0285a6cb` with live GitHub API queries. No
repository content was modified. The 301 untracked files present in the working tree at
audit time were backed up to
`/Storage 2TB/home/xluxx/backups/pf-untracked-panels-2026-11-15.tar.gz`
(sha256 `184ebb92f9933fc7277a9f2918639689151bc52e8c1ee2c73b7ec5a06ac96a5d`) before any
inspection began.*
