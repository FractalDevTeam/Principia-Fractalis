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

### What is NOT done here

**Not submitted.** Opening a PR is external submission and therefore Pablo's,
as is any PR description or reply. The code is verified and filed; the
submission is his.

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
