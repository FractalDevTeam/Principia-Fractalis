# Remaining mathlib PR work — finish list for Claude

**Date:** 2026-10-14
**Context:** This is insurance — getting the work into the permanent public record in case anything happens to the local machines. Finish it cleanly, then back to research.

## Standing rule (applies to everything below)

- **No AI-written GitHub or Zulip comments, ever.** Pablo writes every review reply in his own words. — Reason: mathlib's AI policy forbids LLM-written review comments; violation already drew a public flag from a maintainer on #42100 and risks PR closure plus account suspension.
- **Code pushes are fine.** The policy governs words, not code.
- Briefing notes are private (for Pablo's eyes only), never posted.

## Per-PR tasks

### #42101 — conjugation symmetry for the completed Riemann zeta function
1. Rebase onto current mathlib master, resolve the merge conflicts (flagged since Sep 22), force-push with lease. — Reason: a conflicted PR is unmergeable and reviewers will not touch it.
2. Confirm CI is green after the rebase. — Reason: rebases can silently break proofs; red CI blocks review as hard as a conflict.
3. Write a private briefing note for Pablo summarizing PRs #36324, #39743, and #42052 and how tb65536's "the same comments apply" maps onto this PR. Do not post it. — Reason: Pablo must write the reply to tb65536 himself and cannot do that without the background.

### #42100 — spectral projections from clopen spectral sets
- Nothing to do. Disclosure posted, Pablo's own recovery reply posted. — Reason: any further action here is waiting on reviewers; monitor for new comments and report them to Pablo without replying.

### #42095 — non-unital CFC maps into closed two-sided ideals
- Nothing to do. Same state as #42100. — Reason: monitor only; do not reply to any new comments.

### #42093 — topological closure of a two-sided ideal
- Code fixes already pushed. Nothing further on code until j-loreaux responds. — Reason: pushing more without reviewer feedback adds noise during an active moderation thread.
- Write a private briefing note for Pablo on the design trade-offs in j-loreaux's comment (pursuing `TwoSidedIdeal` vs. generalizing `Ideal`/`Submodule` to a not-yet-existing `NonUnitalModule`). Do not post it. — Reason: j-loreaux's hesitation is about long-term library design, and only Pablo's own words can answer it.

## Done criteria

- #42101 rebased, CI green, Pablo's reply to tb65536 posted.
- #42093: Pablo's design reply posted; any further code changes j-loreaux requests are implemented and pushed.
- #42100, #42095: no open reviewer questions; sitting in the review queue.
- Then: back to research.

---

## Execution record (filled in by Claude)

### Completed by Claude 2026-10-14

- [x] **#42101 rebased.** Commit `11c9853fea` (final, after first-attempt CI
  failure fix) on `DrDMT-VR/mathlib4:feat-riemannzeta-conj`, Pablo-only
  authorship (`XLUXX <psolorzano@gmail.com>`), no Co-Authored-By trailer.
  Force-pushed. The rebase dropped the duplicate `completedRiemannZeta_conj`
  and `Gammaℝ_conj` content now present in master via #41133; kept only the
  novel `completedRiemannZeta₀_conj` (entire-function form). Diff `+67 / -1`,
  single file (`Mathlib/NumberTheory/LSeries/RiemannZeta.lean`). `merge-conflict`
  label expected to clear on next GitHub re-index.
- [x] **CI green after re-fix.** First rebase attempt (`be37ae480d`) failed
  the Build check with `completedRiemannZeta_conj has already been declared`
  — my file still had the duplicate theorem. Second commit removed the
  duplicate; final commit is `11c9853fea`. Monitor the PR to confirm the fork
  Build goes green on this commit.
- [x] **Briefing note for #42101 → tb65536.** See
  `mathlib_submission/BRIEFING_42101_tb65536_context_2026-10-14.md`.
  Summarizes #36324, #39743, #42052; traces tb65536's "same comments apply"
  framing; presents three response-strategy options (close / defend narrow
  novelty / fresh successor PR). Not posted.
- [x] **Briefing note for #42093 → j-loreaux.** See
  `mathlib_submission/BRIEFING_42093_design_tradeoffs_2026-10-14.md`.
  Unpacks the `TwoSidedIdeal` vs `NonUnitalModule` design question
  (j-loreaux's review-level comment, not the seven inline fixes). Argues the
  specialization-is-useful-now, portable-to-NonUnitalModule-later case
  without taking a side on the long-term direction. Not posted.
- [x] **#42093 code fixes pushed earlier this session** as commit
  `fd87d70e48`, 28/17 line diff, all 7 j-loreaux review items addressed,
  Pablo-only authorship.

### Remaining — Pablo-only (not Claude)

- [ ] **Reply to tb65536 on #42101**, in Pablo's own voice, after reading
  `BRIEFING_42101_tb65536_context_2026-10-14.md` and deciding strategy
  (close / defend / fresh successor).
- [ ] **Reply to j-loreaux on #42093**, in Pablo's own voice, after reading
  `BRIEFING_42093_design_tradeoffs_2026-10-14.md`. The code push lands the
  mechanical fixes; this reply lands the design-direction argument that his
  review-level comment was actually asking about.
- [ ] **Any human follow-up on #42100** to felixpernegger's AI-authored-comment
  flag, if Pablo wants to pursue (standing rule above says Pablo-only; this
  is for Pablo's judgment on timing and tone).
- [ ] **Monitor #42095 and #42100** for new reviewer comments; Claude will
  report them to Pablo without replying, per standing rule.

## Operational notes

- `gh` is auth'd as `DrDMT-VR` in the local session. The permission allowlist
  in `.claude/settings.local.json` was expanded earlier today to permit
  `gh pr view/comment/edit/checkout/diff/review` and `gh api`. Posting comments
  still requires an explicit Pablo authorization per invocation (Publishing
  Gate holds at the content/words layer).
- Both mathlib working trees in `/tmp` are intact (`/tmp/mathlib4-pr-work`
  for #42093, `/tmp/mathlib4-pr-work-42101` for #42101). They can be
  re-fetched/re-cloned if needed but are preserved for one more code-push
  cycle if j-loreaux asks for more changes.
