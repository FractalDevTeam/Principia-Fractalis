# mathlib PR status — VERIFIED from GitHub, 2026-10-09

Read-only verification against the live PR pages (gh token on Acer is expired —
`FractalDevTeam` 401; verified via public page reads instead). This **supersedes**
the stale status lines in `HANDOFF_2026-07-28.md`, `DO_THIS_NOW_mathlib.md`, and
`SUBMIT_MATHLIB_PRS.md`, which carry July–Sept CI snapshots ("green", "mergeable",
"DONE") that do NOT mean merged.

## The four DrDMT-VR PRs (July 2026 campaign) — ALL OPEN, NONE MERGED

| PR | title | state (2026-10-09) | note |
|---|---|---|---|
| [#42093](https://github.com/leanprover-community/mathlib4/pull/42093) | topological closure of a two-sided ideal | **Open**, awaiting-author | j-loreaux review 2026-09-01 (several change requests); 1 approval from FractalDevTeam. NOT "done/merged" — the repo's "DONE (added by maintainer)" referred to grunweg adding the AI-disclosure to the description. |
| [#42095](https://github.com/leanprover-community/mathlib4/pull/42095) | non-unital CFC maps into closed two-sided ideals | **Open**, awaiting-author | created 2026-07-25; maintainer asked to confirm AI usage. |
| [#42100](https://github.com/leanprover-community/mathlib4/pull/42100) | spectral projections from clopen spectral sets | **Open** | blocked on #42095 (stacked). |
| [#42101](https://github.com/leanprover-community/mathlib4/pull/42101) | conjugation symmetry for the **completed** Riemann zeta | **Open**, awaiting-author, **merge-conflict** (label 2026-09-22) | grunweg flagged AI + related prior attempts #36324/#39743/#42052. |

## The independent zeta landing (NOT ours)

| PR | title | state | author |
|---|---|---|---|
| [#41133](https://github.com/leanprover-community/mathlib4/pull/41133) | conjugation symmetry of `riemannZeta` (base) | **Merged 2026-07-07** (by Bors) | owenpkent |

Adds `riemannZeta_conj : riemannZeta (conj s) = conj (riemannZeta s)`.

**Nuance (do not over-correct):** #41133 is the **base** `riemannZeta_conj`. Our
#42101 is the **completed** zeta (`completedRiemannZeta₀_conj`,
`completedRiemannZeta_conj`, `Gammaℝ_conj`) — semantically **absent** from master.
So #42101's headline result is still novel; only a base-zeta lemma it may contain
is now superseded. Correct move: rebase #42101 onto #41133, not withdraw.

## Separate, unsubmitted (consistent with the Oct notes)

- **Noether–Skolem / C2 rectangular amplification** (unital `*`-homs
  `Mₙ(ℂ)→M_{kn}(ℂ)`): staged at `mathlib_candidates/NoetherSkolemAmplification.lean`
  + `mathlib_submission/body_noetherskolem.md`, **NOT submitted**. Absent from
  master (master has only the square automorphism case, PR #33017). Still novel.

## Semantic absence from master (per the cross-model audit, not independently
## re-verified here beyond #41133): the three C*-algebra results, the completed-zeta
## conjugation, and the C2 amplification are all absent from master. No merged
## master commit is credited to Pablo Cohen / DrDMT-VR / XLUXX / FractalDevTeam.

## Accurate statement for the record / the book

Real, kernel-checked upstream **candidates** and **four real, still-OPEN mathlib
PRs**; **none merged**; the novel results have **not** landed in official mathlib.
Any "N upstream mathlib contributions" phrasing must read "N submitted PRs (open),
not accepted."

## Blockers to any PR action (all Pablo-gated / external)

1. **gh token expired** on Acer (authed as `FractalDevTeam`, 401). No PR action
   possible without re-auth.
2. **Account mismatch:** the PRs are `DrDMT-VR`; local gh is `FractalDevTeam`.
3. **AI-disclosure / `Authors:` decision** pending on #42095/#42100/#42101 —
   a human (Pablo) decision per mathlib policy.
4. #42101 needs a **rebase** (merge conflict since 2026-09-22).

External actions (rebase, respond to reviewers, withdraw, disclosure) are the
author's call and were NOT taken here. This note is read-only reconciliation.
