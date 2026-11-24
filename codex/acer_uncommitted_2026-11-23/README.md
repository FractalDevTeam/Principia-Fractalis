# Acer uncommitted state, captured 2026-11-23

Preservation bundle, not a merge. Nothing here has been applied to any tracked
file in this repository.

Captured from `Principia-Fractalis-ACTIVE` on Acer (192.168.0.94), branch
`lean/acer-runner-switch-2026-11-20`, which at capture time had **1 unpushed
commit** and **10 dirty entries**. See `STATUS.txt` for the verbatim
`git status --porcelain` and branch context.

Contents:

* `0001-verify.yml-switch-to-self-hosted-legion-runner.patch` — the unpushed
  commit, as a `git format-patch` series. Apply with `git am` on the right
  branch when that lane is next touched.
* `tracked_modified.patch` / `.stat` — the working-tree diff of the four
  modified tracked files, two of which are manuscript chapters
  (`ch07_constants.tex`, `ch09_spectral_unity.tex`). **These are the author's
  edits.** They are preserved as a patch deliberately rather than merged: book
  text is not mine to move between machines.
* `untracked/` — the untracked files worth keeping, including the author's own
  `.before-ch07-fix` / `.before-ch09-fix` backups.

Deliberately NOT captured: `PF_Coq_Code/Makefile.gen*` (generated), and
`codex/gravitational_reconnection_2026-11-10/`, which was landed separately and
properly at `cf7f9cfb`.

`codex/GITHUB_REPO_AUDIT_2026-11-16.md` appears under `untracked/` because it is
untracked **on Acer**; it is already tracked in this repository. Kept for
byte-level comparison in case the two copies differ.
