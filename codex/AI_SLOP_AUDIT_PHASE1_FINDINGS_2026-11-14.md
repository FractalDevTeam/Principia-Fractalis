# AI-slop audit Phase 1 — findings

**Date:** 2026-11-14.
**Scope:** per `codex/AI_SLOP_AUDIT_FULL_CORPUS_SCOPE_2026-11-14.md`.
**Baseline:** `c5921fd9^` (= `1722ddfd`, 2026-07-24 11:24 EDT, immediately before the Claude Fable 5 "book-wide honesty pass").
**Script:** `/tmp/ai_slop_audit_phase1.py` (18 patterns across 4 tiers; factual-use exclusions).
**Log:** `codex/AI_SLOP_AUDIT_LOG_2026-11-14.tsv` (150 rows).

---

## 1. Headline reversal

**The expected pattern was wrong.**  The hypothesis going in: AI commits introduced overclaim ("resolves the Clay problem"), and pre-AI Pablo-authored content was clean.

What the data shows:

| Tier A pattern | pre-AI (Y) | AI-added (N) |
|---|---:|---:|
| `clay_resolve` | 5 | 3 |
| `proof_of_clay` | 1 | 3 |
| `100_pct_in_theorem` | 18 | 9 |

Of the **9 AI-added Tier A hits**, every single one lives inside a scope note, empirical-claim block, disclaimer, refutation, or negative-finding paragraph.  Representative:
- `ch10_hydrodynamic.tex:434` — "Scope note (2026-07-23): this establishes global regularity only for the consciousness-\textbf{modified} equations" — defensive scoping, not overclaim.
- `ch20_riemann_hypothesis.tex:435` — my own session's "\emph{Resolution} here means a \emph{conditional substrate-level reduction}" clarification.
- `revision2_changes.tex:56` — "This book does not claim to have solved any Clay Millennium Prize Problem" — the disclaimer itself trips the regex.
- `ch21_p_vs_np.tex:94, 489, 493` — my own session's `\empiricalclaim{}` block for the 143-problem 100% number.

**So the AI editing campaign added defensive scope language, not overclaim.**  That matches the memory note `principia_IBM_empirical_provenance_not_circular.md`: Phase-1 Claude Fable 5 added verification-status ledgers and honest-scope notes; the content it added was in the right direction.  Phase-3 commits added more of the same.

## 2. Where the actual overclaim lives

**Pre-AI (Pablo-authored) content that still carries overclaim**, all tagged pre_AI=Y:

| file | line | content |
|---|---|---|
| `chapters/ch10_hydrodynamic.tex` | 464 | "This resolves the Clay Millennium Prize Problem in the affirmative for consciousness-modified fluids" |
| `chapters/ch21_p_vs_np.tex` | 1543 | "This isn't just solving P vs NP—it's establishing a new foundation for quantum physics on fractal spaces" |
| `chapters/ch21_p_vs_np.tex` | 1150 | boxed "Fractal Coherence = 100% for 143/143 problems" |
| `chapters/ch21_p_vs_np.tex` | 1593 | "100% Fractal Coherence: All 143 problems achieve $\chi_P = \chi_{NP} = 1.0000$" |
| `chapters/ch21_p_vs_np.tex` | 1182 | "Based on computational experiments across 143 diverse problems with 100% fractal coherence, we conjecture: \textbf{P $\neq$ NP}" |
| `chapters/ch21_p_vs_np.tex` | 1236 | "This consciousness threshold separation is observed in 100% of tested problems (143/143)" |
| `chapters/ch24_birch_swinnerton_dyer.tex` | 436 | "Success rate: 100% in tested cases" (has empirical-claim block below) |
| `chapters/ch25_hodge_conjecture.tex` | 556 | "Success rate: 100% of tested Hodge classes have $\sigma \geq 0.95$" |
| `chapters/ch09_spectral_unity.tex` | 669 | "The spectral unity established here extends beyond P vs NP and RH" |

These are the real Tier A targets.  Phase 2 triage should present each with proposed restatement.  Nothing-removed applies: the claims get scope-qualified in place, not deleted.

## 3. Pablo's style ≠ AI slop

Tier C ("buzzwords") produced 74 hits.  **All 38 "ai_marketing" hits (profound/comprehensive/robust) are pre_AI=Y**, meaning they existed in the manuscript before the 2026-07-24 AI pass.  **All 28 "crucial_critical" hits are pre_AI=Y** too.

Pablo uses "profound" liberally in prose.  This is not AI slop; it is the author's established voice.  Leave Tier C alone unless a specific hit duplicates or inflates (none found in this pass).

**One exception**: the 2 AI-added "referee_proof" hits are session-commit artifacts of mine; those are already out of the live TeX (they only lived in commit messages).

## 4. Template repetition — confined to this session

4 Tier B hits, all pre_AI=N, all from my own 2026-11-14 session-session conclusions:

| file | line | pattern |
|---|---|---|
| `ch20_riemann_hypothesis.tex` | 576 | "What this chapter and its Lean companion do deliver:" |
| `ch21_p_vs_np.tex` | 1548 | "The Clay P versus NP statement remains open; nothing in this chapter closes it..." |
| `ch22_navier_stokes.tex` | 718 | same opener as ch20 verbatim |
| `ch24_birch_swinnerton_dyer.tex` | 822 | same opener as ch20/22 verbatim |

Judgment call: the template is accurate and functionally a disclaimer.  Legal-style boilerplate value may outweigh AI-formulaic shape.  **Recommend keeping unchanged unless you prefer per-chapter variation.**

## 5. Formatting — mostly false positives, two real

30 Tier D hits:
- 22 "star_emphasis" — virtually all are `✓` checkmarks in math-verification lines (`25 = 27 - 2 = 25 ✓`) or `✓ NEW` markers in version_history.  Standard book notation, not AI slop.  **False positives.**
- 6 "section_dated_filename" hits all in `mathlib_candidates/NotFermat42Sub.lean` — the local mathlib candidate hasn't been synced with the PR-branch descriptive-section-header cleanup (commit `82003dccd9`).
- 1 "triple_star" in the same local candidate (`**★★★ ... IS UNCONDITIONAL ★★★**`) — ditto, not synced.
- 1 "star_emphasis" `🎯` emoji in `frontmatter/howto.tex:175` — one actual AI tic.

**Actionable: sync local `mathlib_candidates/NotFermat42Sub.lean` with PR-branch polish (`82003dccd9`), and amend the one `🎯` emoji.**

## 6. What the audit did NOT find (where I expected it to)

- **No "CIRCULAR" or "single highest referee risk" labels** in the live TeX.  Those are only in `.prefix_` snapshot files, archived state.  The 2026-11-06 `8cafe226` pass already removed them from the main chapters.
- **No "142 not 143" inflations** in the live TeX.  Also already fixed.
- **No `VortexStretchingBoundedHypothesis` stale references** beyond the ones I've already updated this session.

## 7. Tier E preserves

3 hits auto-flagged as E (preserve):
- 2 "intellectual honesty" uses (ch21:1072, "we maintain intellectual honesty by labeling them as conjectures supported by strong numerical evidence") — factual, keep.
- 1 "honest statement of the building blocks" (ch25:705) — factual, keep.

All 3 are pre_AI=N but match the FACTUAL_SUBSTRINGS exclusion list — they are the AI pass's honest-scope additions, kept intentionally.

## 8. Recommended Phase 2 shape

Based on the above, Phase 2 is narrower than the scope doc anticipated:

1. **Tier A pre_AI=Y residual overclaim** (9 specific lines above).  Heaviest-delta file first means ch21:1150/1182/1236/1543/1593 first, then ch24:436, ch25:556, ch10:464, ch09:669.  Interactive triage per hit.
2. **Sync `mathlib_candidates/NotFermat42Sub.lean` with PR-branch polish.**  Mechanical.
3. **Amend `frontmatter/howto.tex` emoji use.**  Mechanical.
4. **Decide on Tier B template openers** (keep as boilerplate / vary per axis / drop).  One judgment call, all 4 occurrences at once.

Estimated: one interactive session for item 1, one commit for items 2+3+4.  Much smaller scope than initially projected.

## 9. Nothing-removed carried forward

Every Phase 2 fix follows the nothing-removed convention: the overclaim claim gets scope-qualified in place (add the empirical-claim block, add the scope line above, add the "— conditional" theorem-name suffix).  Deletion requires per-hit explicit yes.

---

**Next action.** Await Pablo's go/no-go on the 9 Tier A triage targets (which to amend, which to leave) plus the three mechanical items.
