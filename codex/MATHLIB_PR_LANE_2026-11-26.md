# MATHLIB PR LANE — state and one new candidate, 2026-11-26

Everything below verified live today. Supersedes the status columns in
`MATHLIB_PR_ROADMAP.md`, which have been stale before.

---

## 1. The three open PRs need no code

Read live via `gh` on 2026-11-26:

| PR | title | state | mergeable | review | size |
|---|---|---|---|---|---|
| [#42093](https://github.com/leanprover-community/mathlib4/pull/42093) | `feat(Topology/Algebra/Ring)`: topological closure of a two-sided ideal | OPEN | **MERGEABLE** | **nobody has reviewed** | +127 −0 / 2 files |
| [#42095](https://github.com/leanprover-community/mathlib4/pull/42095) | `feat(Analysis/CStarAlgebra)`: non-unital CFC maps into closed two-sided ideals | OPEN | **MERGEABLE** | **nobody has reviewed** | +92 −0 / 2 files |
| [#42100](https://github.com/leanprover-community/mathlib4/pull/42100) | `feat(Analysis/CStarAlgebra)`: spectral projections from clopen spectral sets | OPEN | **MERGEABLE** | **nobody has reviewed** | +238 −0 / 3 files |

`mergeStateStatus: BLOCKED` on all three means **missing maintainer approval**,
not a conflict. Labels: `new-contributor`, `LLM-generated`, topic label.
Last activity: 11-18, 11-05, 10-28 respectively.

**So there is no code work on these.** They are blocked on human attention. Any
push now would be a warm-thread code push with no reviewer reason, which is
exactly what the standing rule says not to do.

### The one actionable item, and it is Pablo's keyboard

`#42100` carries `awaiting-author` alongside `blocked-by-other-PR`. From the
earlier thread read, the mechanics are:

* the PR **description** needs the template dependency line format rather than
  prose (`felixpernegger`'s request);
* the `awaiting-author` label is cleared by a reply carrying the
  `-awaiting-author` token.

Both are public actions on a public thread. Per the permanent rule they are
Pablo's words and Pablo's keyboard; nothing is drafted here.

### Also still true

* `grunweg` (triage) asked on all three whether AI was used. mathlib's policy
  permits it **with disclosure**, and the `LLM-generated` label is already
  applied, so triage has processed it either way. No action required.
* The PRs are authored by **DrDMT-VR**. `gh` on Legion authenticates as
  **FractalDevTeam**, which can read them but is not the author. Pushing to the
  PR branches needs the DrDMT-VR credential.
* Nothing in the book depends on any of these merging.

---

## 2. New candidate: `det_fin_three_of`, `det_fin_four`, `det_fin_four_of`

`mathlib_candidates/DetFinFour.lean`, wired into the `MathlibCandidates`
`lean_lib` roots so it is re-verified on every mathlib bump rather than rotting.

### Why this one

Chosen for **reviewability**, because reviewer attention — not code — is the
measured bottleneck in this lane. It is small, uncontroversial, extends an
existing pattern, and is need-driven: it came out of hitting the gap today while
formalising the Chern–Weil degree-4 sign fact, where the absence of a 4×4
determinant lemma forced a `simp only` + `Fin.succAbove` workaround.

`Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean` has `det_fin_one`,
`det_fin_one_of`, `det_fin_two`, `det_fin_two_of`, `det_fin_three`. Two family
members are missing:

* **`det_fin_three_of`** — the `!![...]` form, which one and two both have. An
  asymmetry rather than a decision.
* **`det_fin_four` / `det_fin_four_of`** — the next case.

Insertion point: immediately after `det_fin_three`, which is currently the last
declaration before `end Matrix` in that file.

### Verification

| check | result |
|---|---|
| standalone against mathlib master `v4.37.0-rc1` | **clean** |
| **in situ** — inserted into mathlib's own file, module rebuilt | **clean, 0 warnings** |
| downstream consumer (`Matrix.NonsingularInverse`) with the new `@[simp]` | **clean** |
| cross-toolchain: our pin `v4.24.0-rc1` | **clean** — compiles on both |
| `lake build MathlibCandidates` | **clean, 2534 jobs** |
| mathlib checkout afterwards | **0 porcelain changes, PR branch untouched, olean rebuilt from restored source** |

The 24-term right-hand side was **generated programmatically, not typed**, and
cross-checked against an independent Laplace expansion along row 0 on 500 random
rational matrices. `det_fin_four_of` is proved as `det_fin_four _`, so the
compiler verifies the letter form against the index form — the lettering is not
asserted.

### Two deliberate choices a reviewer may want to argue with

1. **`det_fin_three_of` is `@[simp]`; `det_fin_four_of` is not.**
   `det_fin_two_of` is `@[simp]` and rewrites to 2 terms; three gives 6, which is
   comparable. Four gives **24**, too large for the default simp set — so it is
   omitted deliberately, with a comment saying so, rather than by oversight.
2. **The proof pins three `succAbove` values by `decide`**, because the row-0
   expansion leaves them behind and there is an asymmetry worth making explicit:
   at the last column the `castSucc` branch is taken, so `succAbove 3 2 = 2`
   while the other two give `3`. Getting that backwards is the obvious trap.

### SUBMITTED — [#46607](https://github.com/leanprover-community/mathlib4/pull/46607)

Pablo authorised submission on 2026-11-26 and chose the **FractalDevTeam**
identity. Live state at creation: OPEN, not draft, **MERGEABLE**, `+43 −0` in one
file, label `new-contributor`, head `FractalDevTeam:det-fin-four-sub` → `master`.

The PR body carries the AI disclosure mathlib's policy requires, states the two
deliberate choices so a reviewer can disagree, and notes that the base is an
older `master` with an offer to rebase.

**Why the base is older, and why it is fine.** The push had to avoid
`.github/workflows/` because the `gh` token carries `gist, read:org, repo` and
**no `workflow` scope**, while FractalDevTeam's fork master was four months
behind — so a current-master branch would have carried workflow files and
GitHub refuses that without the scope. Basing on the fork's own master avoids it
entirely: the `det_fin_*` region is **byte-identical** between the two bases
(verified by md5), so the PR diff is only the 43 lines and it merges cleanly.
Correctness was still verified against **current** master `8ec7bd8e`, which is
what CI effectively tests.

**To remove that constraint permanently**, the token needs the `workflow` scope
(`gh auth refresh -h github.com -s workflow`). Not required for this PR.

---

## 3. Other candidates already on disk, unsubmitted

`mathlib_candidates/` also holds `GramLinearIndependent`, `TateLimit`,
`HilbertSchmidt`, `TransferOperatorCompact`, `TransferOperatorTrace`,
`NotFermat42Sub`, `NoetherSkolemAmplification`, and a `FourDouble` draft. Two
further results recorded as PR candidates elsewhere and **not** yet in this
folder:

* third-order derivative symmetry + the Laplacian sum formula — mathlib has no
  symmetry result above order 2;
* `localAt` injectivity, which would additionally make
  `modular_flow_separates_regions` unconditional on our side.

Both are larger than `det_fin_four` and so worse bets while the queue is
reviewer-bound. `det_fin_four` first; if it merges, the contributor history
makes the larger ones easier to land.

### CI STATUS — red, and the cause is the base, not the mathematics

`ci (fork) / Build` **fails at step 6, "check the cache tool is recent"**, after
which every downstream step including `build mathlib` is **skipped**. Lean never
ran, so the lemmas are not implicated. mathlib CI guards against a stale base,
and the Aug-3 base tripped that guard.

Underlying cause, measured: the submitted branch inherits the Aug-3 base's
`lean-toolchain` of **v4.33.0-rc2**, while the verification was done against
**v4.37.0-rc1**; `lakefile.lean` and `lake-manifest.json` also differ between the
two bases. So routing around the missing `workflow` scope by using a stale base
bought a configuration that had never been compiled locally. That was a bad
trade and is recorded as such rather than glossed.

**The fix is a rebase onto current master**, which is what a reviewer would ask
for anyway. It needs the `workflow` scope on the gh token, because a
current-master branch carries `.github/workflows/` and GitHub refuses such a push
without it:

    gh auth refresh -h github.com -s workflow

After that: rebase `det-fin-four-sub` onto `upstream/master` and force-push. No
proof work is expected — the lemmas already build clean in situ on current
master with 0 warnings, and on our own pin `v4.24.0-rc1`.

**Lesson for this lane.** A stale base is not a cosmetic "behind master" state on
mathlib: CI refuses it outright. Either hold the submission until the token has
the `workflow` scope, or sync the fork first. Do not trade base freshness for a
push that merely succeeds.