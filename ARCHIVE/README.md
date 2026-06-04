# ARCHIVE/

**Status:** Historical reference only. Nothing in this directory participates in the active build, the current manuscript, or the current axiom audit.

The contents are preserved with full git history (`git mv`) so that prior
states, audit trails, and superseded versions remain inspectable. Active
development lives at the repository root — see top-level [`README.md`](../README.md)
for the current repository map.

## What is here, and why

### Superseded manuscript and formalization snapshots

| Path | Why archived |
|---|---|
| `Principia_Fractalis_master_folder_rev2/` | Superseded by `Principia_Fractalis_master_folder/` (Version 1.2.0, Substrate-Level Meta-Theorem Edition). |
| `Principia_Fractalis_FINAL_SUBMISSION_2025-11-18/` | Pre-Version 1.0 submission bundle. Superseded by V1.2.0. (Empty in the index; tracked as orphan submodule pointer.) |
| `principia_fractalis_formalization/` | Earliest formalization scaffold. Superseded by `PF_Lean4_Code/` and `PF_Coq_Code/`. (Empty in the index; tracked as orphan submodule pointer.) |
| `PF_canonical/` | Earlier name for the canonical Lean source. Replaced by `PF_Lean4_Code/`. (Empty in the index; tracked as orphan submodule pointer.) |
| `PF_Coq/` | Superseded by `PF_Coq_Code/` (Wave 58 cross-prover layer). |

### Session-artifact audit documents

The 2026-05-25 audit cycle produced a set of standalone audit `.md` files
that have since been folded into the manuscript, `OPEN_PROBLEMS.md`,
`AXIOM_AUDIT.md`, `PROOF_PACKAGE.md`, and `CHANGELOG.md`. They are kept
here for cross-reference:

- `ANNOTATION_FRESHNESS_AUDIT_2026-05-25.md`
- `BIBLIOGRAPHY_AUDIT_2026-05-25.md`
- `CROSS_PROVER_PARITY_AUDIT_2026-05-25.md`
- `EVIDENCE_AUDIT_2026-05-25.md`
- `HODGE_MATHLIB_GAP_2026-05-25.md`
- `ORPHAN_BIB_TRIAGE_2026-05-25.md`
- `STRATEGIC_AUDIT_2026-05-25.md`
- `MANUSCRIPT_FULL_READ_2026-05-24.md`
- `MANUSCRIPT_MAP_2026-05-25.md`

### Superseded planning / synthesis documents

- `DERIVATION_ANALYSIS_alpha_NP.md` — folded into `PF_Lean4_Code/PF/CrossMillennium/AlphaValuesFirstPrinciples.lean`.
- `MATHEMATICAL_VALIDATION_REPORT.md` — folded into `PROOF_PACKAGE.md` and `AXIOM_AUDIT.md`.
- `PROOF_COMPLETENESS_AUDIT.md` — folded into `PROOF_PACKAGE.md`.
- `PROOF_ROADMAP.md` — superseded by current state (`PROOF_PACKAGE.md`, `OPEN_PROBLEMS.md`).
- `PRIZE_ROADMAP.md` — superseded.
- `REFEREE_AUDIT.md` — folded into `PROOF_PACKAGE.md` and the Referee Layer (`PF_Lean4_Code/PF/Referee/`).
- `PARITY_REPORT.md` — superseded by `CROSS_PROVER_PARITY.md`.

### Session-tooling and ad-hoc artifacts

- `MISSION_INVENTORY/` — wave-55 session inventory and dispatch notes.
- `BRANCH_CLEANUP.sh` — one-time branch-tidy shell script.
- `fractal-synthesis (1).html` — single-file HTML artifact from an early experiment.

## How to read prior history

Every file here keeps its full pre-archival git history. To see the log of
a file from before it was moved into ARCHIVE/, use `--follow`:

```bash
git log --follow ARCHIVE/PROOF_ROADMAP.md
git log --follow 'ARCHIVE/PF_Coq/theories/Core/RH.v'
```

## Not deleted, just moved

Nothing in this directory was deleted. If a referee, reviewer, or
historian needs to reconstruct a prior state of the framework, the full
prior tree is reachable via `git log`/`git checkout` of any commit
predating the cleanup.
