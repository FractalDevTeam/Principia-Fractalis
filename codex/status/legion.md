# Legion status — 2026-11-27

Supersedes the 2026-11-25 entry. Every number below was measured today, not
recalled. Written because the session has been compacted repeatedly and the
project state must live in the repo, not in a context buffer.

## Branch

`lean/ns-faithful-and-vacuity-retirements-2026-11-20`

| | |
|---|---|
| local HEAD | `b78c724b` |
| origin/\<branch\> | `5c98e544` — **4 commits unpushed** |
| origin/master | `bfa02f21` — HEAD is **46 ahead** |

**Correction to an earlier claim of mine**: I reported "43 commits unpushed,
never pushed." That was computed against a *stale remote-tracking ref*. Live
`git ls-remote` puts origin's branch at `5c98e544`; only today's four commits
are unpushed. The repo is PUBLIC and the branch is already on it, so pushing
the branch is not a new publication act. **Merging to master remains
Pablo-only.**

## Today's four commits

| commit | what |
|---|---|
| `0874dee4` | the three Clay-axis `True` markers disclosed; the NS bridge proved equivalent to Fefferman's own statement |
| `559e972f` | four repairs recovered that existed only in the build tree — **two closure modules' committed source did not parse** |
| `d772db0d` | appL Phase-1: all six anchor-file citations were dead; fourteen attributions named papers the corpus does not cite |
| `b78c724b` | ch07's ledger said UNTESTED for a claim the chapter refutes; the legend had no label for refutation, so it now declares five |

## Gates, measured

| gate | result |
|---|---|
| `lake build PFClosure` (pf-legion) | **exit 0, 5,594 jobs, 0 errors, 0 sorryAx** |
| closure size | **1,769 modules** |
| book (`pf_book_gate.sh`, bibtex + 3 pdflatex) | **1,110 pages, 0 LaTeX errors, 0 undefined citations, 0 undefined refs, 0 multiply-defined labels** |

## The two-tree rule — this bit us

`~/pf-push-20261120` is the **git clone**: 36 PF oleans, 2,452 mathlib. It is
not a build tree.
`~/pf-legion-20261120` is the **build tree**: 9,854 PF oleans, 6,866 mathlib.
Same pin `v4.24.0-rc1`, same mathlib rev `eed770a434`.

**Build in pf-legion, commit in pf-push, and parity-check between them.** On
2026-11-27 `PFClosure` was green while the *committed* source of two closure
modules would not parse at all:

```
PF/PNP_Wave56CrossGaloisLockAttempt.lean:495:43  unexpected token '/-!'; expected 'lemma'
PF/Referee/SevenMillenniumUnification.lean:106:17 unexpected token '#check'; expected 'lemma'
```

Orphaned doc comments of the `35ab64dd` class. `SevenMillenniumUnification` is
a referee capstone. A gate that reads sources differing from the committed ones
is worse than no gate: it reports green. Parity is now verified — PF/ identical
on every real source file, `PF.lean`/`lakefile.toml`/`lean-toolchain`/
`lake-manifest.json` all md5-match, and **0 orphaned doc comments across all
1,769 closure modules**.

To test a committed file without disturbing the build tree:
`cd $LEGION && lake env lean $PUSH/PF/<path>.lean`

Note: WSL git cannot finalize an index write on `/mnt/d`, where this
worktree's gitdir lives. Clear `index.lock` from PowerShell, or commit with
Windows `git.exe` using `GIT_DIR` + `GIT_WORK_TREE=\\wsl.localhost\Ubuntu\...`.

## Panel compute — the long pole, and it is already running

| machine | state |
|---|---|
| Legion (WSL) | grinding `FourierPanels.Seg02Range_c59_8`; **1,052 panels remaining** of 8,717 (7,665 built) |
| Acer `192.168.0.94` | **UP** — 4 days uptime, 12 cores, 10/15 GB used, load 1.00, grinding `FourierPanels.Seg15Range_c397_32` |

Both machines are on the queue. **Do not add load.** 180 of 200 sampled panels
have no importer — they gate nothing, they are additive certificates. This is
compute, not proof.

(I briefly reported Acer down from a single `ping -c 1`. False negative —
ssh/22 is open and it has been working the whole time. Retry before reporting
a machine down.)

## THE finish-line gap — 12 book files carry no verification-status block

The rigor-ledger spec requires every chapter's central claim to carry a label,
and puts the six Millennium chapters at CONDITIONAL REDUCTION. 40 files comply.
These 12 do not, and six of them are the most referee-exposed in the book:

- **ch20_riemann_hypothesis** · **ch21_p_vs_np** · **ch24_birch_swinnerton_dyer**
  · **ch25_hodge_conjecture** — the Millennium chapters
- **ch34A_substrate_theorem** — the one load-bearing kernel-verified result
- **ch04_timeless_field** — the T_infinity chapter the spine runs through
- ch20_rev2_dirichlet_eta_inserts, appA_zeros, appJ, appL, appM_toe_diagram,
  appN_chapter_diagnostic_sheet

A referee opening ch20 or ch34A finds no ledger while 40 other files have one.
That asymmetry invites exactly the question the ledger exists to answer.
Measurement of the six is in flight; the labels are a judgement call and are
being written by hand, not generated.

## Stale items in PENDING_LEDGER_2026-11-24 — resolved, do not re-chase

- **"ch07 fine-structure retraction, Acer working tree only, NOT on Legion"** —
  it landed. ch07 body now reads "rests on a value of $R_f(1,2)$ that the
  series does not take", with $R_f(1,2)=-\pi^2/12$ machine-checked as
  `dirichletEtaExt_at_two`. The book no longer asserts a claim its author had
  determined false. What had *not* landed was the label; fixed in `b78c724b`.
- **"appL's 109 anchors each axiom-free"** — appL already carries the honest
  caveat at lines 209 and 545 (`Prop := True` is trivially axiom-free).
- **"3 files with undisclosed `Prop := True`"** — measured as **2**, not 3:
  `NumberTheory/AndrewsCurtisFrameworkAttack` and `Referee/FrontierLedger` have
  one each; `Empirical/ProblemClassTriClass_2026_06_22` has **zero**.
- `localAt` injectivity — closed at `e0b4c34d`.

## What is Pablo-only

1. Merging the branch to public `master` (46 commits).
2. mathlib PR replies — #46607 CI red on a stale fork base; #42100 needs an
   `awaiting-author` reply. Public comments are his keyboard, always.
3. Remaining book judgement calls: appB's third mass-gap figure `0.7329 GeV`,
   appC's `Tr(F Fᵀ)` sign, ch25's abelian 4-fold label, appH↔appC scale
   reconciliation, ch03:313-320's `Δ_P` vs `Δ` notation collision.
