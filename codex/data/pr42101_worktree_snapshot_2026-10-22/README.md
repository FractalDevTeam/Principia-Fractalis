# Snapshot: mathlib #42101 working-tree data, rescued 2026-10-22

**Why this exists.** These four files existed ONLY in the working tree of
`D:\CLAUDE-i9\_tmp\mathlib-pr42101-repair-20261022` on Legion — a clone that is
**shallow** (2 grafted tips) and that **intermittently fails to write git refs**
(`error: couldn't set 'refs/remotes/upstream/master'`, reproduced). Two of them
were untracked, so not even `git stash` would have covered them by default.
Pablo was mid-reply on #42101 the same day. Losing this was the one
unrecoverable outcome on the table, so it is now in the Principia repo and on
origin.

**What is NOT done here, deliberately:** nothing was committed or pushed to the
`feat-riemannzeta-conj` branch or to PR #42101. Adding commits would move the
PR head while Pablo is mid-reply, and the PR's content is his call. This is
data protection only — no side effects on the PR.

## Provenance

| | |
|---|---|
| Source clone | `D:\CLAUDE-i9\_tmp\mathlib-pr42101-repair-20261022` |
| Remote | `https://github.com/DrDMT-VR/mathlib4.git` |
| Branch | `feat-riemannzeta-conj` |
| Base commit | see `base_commit.txt` (`2a3c112c00`, the branch tip) |
| Captured | 2026-10-22 by the Legion session |

## Contents

* `files/` — the **complete post-edit content** of all four files. Full
  contents, not just a diff, so this snapshot reconstructs the work with no
  dependency on the fork, the clone, or any base commit remaining reachable.
  Path separators are flattened to `__`; the original paths are:

  | file in `files/` | original path |
  |---|---|
  | `Mathlib__NumberTheory__Harmonic__ZetaAsymp.lean` | `Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean` |
  | `Mathlib__NumberTheory__LSeries__RiemannZeta.lean` | `Mathlib/NumberTheory/LSeries/RiemannZeta.lean` |
  | `PR42101Axioms.lean` | `PR42101Axioms.lean` (untracked, repo root) |
  | `PR_DESCRIPTION.md` | `PR_DESCRIPTION.md` (untracked, repo root) |

* `pr42101_tracked_files.patch` — `git diff` of the two **tracked** files
  against the branch tip (116 lines). Verified with
  `git apply --check --reverse` against the live tree, so it is known to
  correspond exactly to the captured content.

* `SHA256SUMS` — integrity hashes for every file above.

* `base_commit.txt` — base commit and branch name.

## How to restore

Into a fresh full clone of the fork on `feat-riemannzeta-conj`:

```
# tracked files: apply the patch
git apply /path/to/pr42101_tracked_files.patch

# untracked files: copy them back
cp files/PR42101Axioms.lean  ./PR42101Axioms.lean
cp files/PR_DESCRIPTION.md   ./PR_DESCRIPTION.md
```

Or ignore the patch entirely and copy the two `Mathlib__...` files back to the
original paths in the table above — they are complete files.

Verify first: `sha256sum -c SHA256SUMS`.
