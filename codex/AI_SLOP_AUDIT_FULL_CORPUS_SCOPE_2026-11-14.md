# Full-corpus AI-slop audit — scope document

**Author:** Pablo Cohen (scoped by assistant).
**Date:** 2026-11-14.
**Status:** SCOPE ONLY. No files touched by this document. Execution awaits Pablo's authorization per chapter / per section.
**Prior passes:** `principia_ai_slop_removal_pass1_2026-11-06.md` (commit `8cafe226`, limited to ch20 + ch21 CIRCULAR / 142-not-143 / highest-referee-risk hits); `efa73f5b` book banned-phrase scrub (21 "honest scope" hits across 16 chapters).  Neither of those is the full audit; this scope doc defines it.

---

## 1. Audit target

**Source of the slop.** Per auto-memory `principia_book_ai_editing_campaign_2026-11-06.md`:
- **150 AI commits to the book since 2026-07-01**, all carrying `Co-Authored-By: Claude [model]` trailers.
- **Phase 1** (2026-07-03 → 07-09): ~25 commits under placeholder email `your-email@domain.com` (Claude Fable 5 `c5921fd9` honesty pass, `5d1bea96` CIRCULAR verdict propagation, Opus 4.7).
- **Phase 3** (2026-09-29 → 11-03): ~126 commits under real email but still `Co-Authored-By: Claude Opus 5/4.7`.
- Pre-AI baseline is reachable at `c5921fd9^` via `git show c5921fd9^:<path>`.
- Heaviest line-count deltas: ch34A (+403 L), ch34 (+328), ch24 (+309), ch21 (+244), ch20 (+115).

**Scope of this audit.**
- All TeX: 35 chapters (`chapters/ch*.tex`) + ~12 appendices (`appendices/app*.tex`) + frontmatter (`frontmatter/*.tex`) + backmatter (`backmatter/*.tex`) + `preamble.tex`.
- Codex memos written by AI (not Pablo's hand-written analysis memos).
- Lean file docstrings and section-marker comments (NOT proof bodies — those are math, audit via different mechanism).
- Commit messages with `Co-Authored-By: Claude*` trailers.

**Out of scope.**
- Mathematical content of Lean proofs (separate audit, requires theorem-by-theorem review).
- Pablo's own hand-written codex memos (identified by author field + prose signature).
- Historical-record paragraphs in `version_history.tex` and ch34 verification chapter that are intentionally preserved as dated snapshots.
- External `ARCHIVE/` files (historical, not part of current book).

---

## 2. Pattern catalog

These are the AI-sloppiness patterns surfaced through today's cleanup session (`a0c0be8b`, `3f6f7457`, `82003dccd9`) plus prior-pass experience.

### Tier A — overclaim (hard-remove / restate)
1. **Clay-problem resolution verbs**: "resolve"/"solve"/"establish"/"prove" tied to `Riemann Hypothesis | Navier-Stokes | Yang-Mills | P vs NP | Hodge | Birch-Swinnerton-Dyer`.  Example today: ch20 Conclusion "resolution of the Riemann Hypothesis".
2. **100%-rate claims inside theorem bodies** without an `\empiricalclaim{}` block or explicit provenance.  Example: ch21 `thm:spectral-gap` had "validated across 143 problems with 100% fractal coherence" inside the theorem statement.
3. **"CIRCULAR / single highest referee risk" labeling applied to the α-skeleton anchors** (per `principia_IBM_empirical_provenance_not_circular.md`).  These conflate a Lean-level `rfl` tautology with scientific circularity when the constant itself is empirically measured from a 2026-05-23 IBM Quantum hardware run.  Named hits: ch21 L1585, ch21 L1599, ch20 L519 (per memory, pre-correction state — verify current state).
4. **"142 not 143" inflation** (per `principia_ai_slop_removal_pass1_2026-11-06.md`).  Original 2025-05-23 CSV has 143 rows; some commits report 142.  Target the number inflations.
5. **Stale "named open proposition X" references** to hypotheses now discharged (e.g., `VortexStretchingBoundedHypothesis` — already fixed in this session in ch22 and `revision2_changes.tex`, but may lurk in other files).

### Tier B — template repetition (soft-tighten)
1. **Verbatim glue-sentence templates across chapters.**  Today's session found two:
   - `"the honest shape of each deliverable"` (ch20 + ch22 conclusions, identical phrase)
   - `"The chapter's load-bearing claim is item X (description). Items N--M are framework / empirical / ..."` (ch20 + ch22 + ch24 conclusions, same skeleton)
   Full-corpus search likely surfaces more template reuse across the 150 AI commits.
2. **Pre-set "Honest scope, rev 2" boilerplate** — appears in multiple chapters with the same structure.  Legitimate when restating true scope; AI-template when identical across unrelated axes.
3. **Three-item bulleted lists where one or two items are padding.**  AI tends to pad to three for visual balance.
4. **Em-dash overuse in prose.**  AI writing signature; one or two per paragraph is ordinary, five+ is AI.

### Tier C — buzzwords (soft-tighten)
1. **"Load-bearing"**: 35 current uses across chapters/frontmatter/appendices (checked today).  Not all are AI; the term is a legitimate project convention meaning "an incorrect version of this claim breaks downstream reasoning".  Audit target: uses where the term is decorative rather than load-bearing in that project sense.
2. **"Hostile referee"**: added by today's assistant in commit messages (not committed to book TeX, caught before push).  Audit target: any prior AI commit messages or TeX using this framing.
3. **"Referee-proof"**: AI-coined verb/adjective; replace with specific scope statement.
4. **"Attack vector"**: AI-coined; replace with specific issue name.
5. **"Honest" / "honestly" / "honest scope" as filler** (per PERMANENT feedback `feedback_nothing_removed_unless_100pct.md` and others — "Stop using honest every time you eat that fucking word. It means you floss your context.").  Factual uses ("intellectual honesty", "honest statement of X") preserved per Pablo's 2026-11-10 banned-phrase scrub.
6. **"Comprehensive" / "robust" / "cutting-edge" / "profound" / "state-of-the-art"**: AI marketing vocabulary.

### Tier D — formatting (soft-tighten)
1. **Star emphasis in docstrings**: `★ FOO ★`, `★★★ FOO ★★★`, `**IMPORTANT**`.  Today's Lean cleanup removed three; pattern-search likely surfaces more across book TeX and Lean files.
2. **ALL-CAPS section headers**: "FULLY ASSEMBLED", "IS UNCONDITIONAL", "SECOND EXACT RANK IN THE REPOSITORY".
3. **Section markers tagged with project-internal filenames and dates** when exported to upstream (e.g., `## Section: Fermat42SubFoundations_2026_11_13` in a mathlib-destined file — fixed today for PR #46025 in `82003dccd9`).

### Tier E — audit-only (preserve)
1. **Intentional historical-record paragraphs** in `version_history.tex`, `ch34_verification.tex`, codex SESSION_RECORD memos.  These record what AI did and should NOT be rewritten; they are the audit trail itself.
2. **Named-anchor TeX blocks that are intentionally performative** (per-design markers in NamedAnchors catalogs, Prop := True aggregators).
3. **`\manuscriptcorrection{}` blocks** recording mathematical corrections to AI-authored content.  Keep as-is.

---

## 3. Execution plan (sequenced, chapter-by-chapter)

**Default per-item action is RESTATE in place**, never delete, unless Pablo authorizes deletion for a specific hit (per `feedback_nothing_removed_unless_100pct.md` permanent feedback).

### Phase 1 — pattern-grep pass (produces audit log, no file writes)

For each Tier A/B/C/D pattern, run a scoped `grep -nE` across:
- `Principia_Fractalis_master_folder/chapters/`
- `Principia_Fractalis_master_folder/appendices/`
- `Principia_Fractalis_master_folder/frontmatter/`
- `Principia_Fractalis_master_folder/backmatter/`
- `PF_Lean4_Code/PF/` (docstrings and `/-!` section markers only; proof bodies out of scope for this audit)

Output: `codex/AI_SLOP_AUDIT_LOG_2026-11-14.tsv` with columns
```
file<TAB>line<TAB>tier<TAB>pattern<TAB>excerpt<TAB>suggested_action
```

Estimated size of log: 500–2000 rows, depending on tier thresholds.
Estimated time: 1 pass-cycle (1–2 hours of pattern-grep + manual-triage review).

### Phase 2 — per-chapter triage (interactive with Pablo)

For each of the ~35 chapters, in order of AI line-count delta (heaviest first per memory):
1. ch34A (+403 L)
2. ch34 (+328 L)
3. ch24 (+309 L)
4. ch21 (+244 L)
5. ch20 (+115 L)
6. ...remaining chapters by delta.

Per chapter:
- Pull its rows from the audit log.
- Present Pablo the Tier A hits individually with proposed restatement + before/after.
- Present Tier B/C/D hits in groups (typically single-pattern batch fix per chapter).
- Pablo approves per-hit or per-group.

Estimated time per chapter: 30–90 minutes interactive, depending on hit density.  Full triage pass: multiple sessions across days-to-weeks.

### Phase 3 — fix execution (one PR-sized commit per chapter)

After Pablo approves a chapter's hit set:
- Apply the approved restatements/tightenings.
- Recompile the book and verify PDF page-count is sane.
- Commit with explicit subject `AI-slop audit — chN_<name>: tier-A×<count> + tier-B×<count> + ...`
- Preserve all `\manuscriptcorrection{}`, historical-record paragraphs, and named-anchor blocks.

NEVER:
- Rewrite history.
- Force-push.
- Delete AI-authored commits.
- Remove `Co-Authored-By: Claude*` trailers from historical commits (they are the audit trail).

### Phase 4 — Lean docstring audit (separate, smaller pass)

- Grep `PF_Lean4_Code/PF/` for `★|☆|◆|◇|\*\*\*|IMPORTANT|CRITICAL|FULLY|UNCONDITIONAL` in docstrings.
- Grep for `/-! ## Section: <PF-filename>` style section markers.
- Fix docstrings only; proof bodies left untouched (separate correctness audit).

---

## 4. Risks and constraints

1. **Nothing-removed is permanent.**  Default action is restate.  Deletion requires per-hit explicit yes.  (See `feedback_nothing_removed_unless_100pct.md`.)
2. **Historical-record paragraphs must survive.**  The `version_history.tex` 2026-07/08 entries, the ch34 "Verification update (2026-10-21)" entry, codex SESSION_RECORD memos — these describe past AI behavior and are the audit trail.  Rewriting them erases the record.
3. **Mathematical content may be fabricated under AI prose.**  Pattern-grep catches rhetoric; it does not catch wrong math.  Post-audit, a separate math-correctness pass is warranted on the five heaviest-delta chapters (ch34A, ch34, ch24, ch21, ch20).
4. **Some AI commits introduced genuinely valid content.**  Phase 1's Claude Fable 5 `c5921fd9` honesty pass and `5d1bea96` CIRCULAR verdict propagation are both AI commits, but the first added real scope rigor and the second added a labeling Pablo later determined was wrong.  Bucket by content, not by authorship.
5. **Co-Authored-By trailers in 150 historical commits.**  These are a transparency record showing which commits had AI assistance.  Per PERMANENT feedback `feedback_no_co_authored_by_claude_trailer.md`, future commits must NOT carry this trailer.  Historical commits retain their trailers as the audit trail.
6. **Commit messages written by today's assistant** carry "hostile referee" / "attack vector" / "referee-proof" framing in several places (session commits `534236ce`, `558ee596`, `79bf7e02`, `9f920035`, `1c9b22f7`, `5a8a5a0d`).  These are on origin/master and should NOT be amended (per "never rewrite history").  The patterns are flagged here so the next commit-message pass avoids them.

---

## 5. Deliverables

1. **This scope document** (`codex/AI_SLOP_AUDIT_FULL_CORPUS_SCOPE_2026-11-14.md`) — no fixes, defines the audit.
2. **Phase 1 audit log** (`codex/AI_SLOP_AUDIT_LOG_2026-11-14.tsv`) — tsv of all Tier A/B/C/D hits.
3. **Per-chapter fix commits**, one per chapter, Phase-3-sized.
4. **Final summary memo** (`codex/AI_SLOP_AUDIT_COMPLETE_YYYY-MM-DD.md`) after Phase 3 finishes.

---

## 6. Open questions for Pablo

Before Phase 1 runs, three decisions block execution:

1. **Tier B/C threshold.**  "Load-bearing" is used 35 times; not all are AI.  Audit against (a) pre-AI baseline (`c5921fd9^`), flag only those added after?  Or (b) current state, flag by decorative-vs-substantive judgment?  Preference?
2. **Codex memo scope.**  Audit only AI-authored codex memos (identifiable by `Co-Authored-By: Claude*` in originating commit), or audit every codex memo written since 2026-07-01 regardless of authorship?
3. **Pace.**  Full audit is weeks of interactive triage per Phase 2.  Preferred cadence: one chapter per session, heaviest-delta-first?  Or batched by pattern (one pattern across all chapters per session)?

Answer any of these in a single reply and Phase 1 can begin.
