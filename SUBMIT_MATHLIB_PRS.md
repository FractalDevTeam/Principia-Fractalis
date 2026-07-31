# Submitting the mathlib PRs — handoff kit

Three verified, upstreamable files are staged in `PF_Lean4_Code/PF/ForMathlib/`
(all kernel-clean, root namespaces, mathlib conventions). This is the exact
procedure to get them into `leanprover-community/mathlib4`.

> **CORRECTED 2026-07-25:** only THREE of the four were absent.
> `riemannZeta_conj` ALREADY EXISTS on master (`Mathlib/NumberTheory/Harmonic/
> ZetaAsymp.lean:458`, unconditional, `@[simp]`, independent proof by another
> author). It was dropped from PR-4 to avoid a duplicate submission. The other
> three are genuine gaps and do NOT follow from it (the bridge `ζ s = Λ s / Gammaℝ s`
> cannot be inverted: `Gammaℝ` vanishes at the trivial zeros).
>
> **2026-07-25 addendum — PR-4 (zeta conjugation symmetry).** r115
> (`PF/Analytic/XiRealWitness.lean`) proved four lemmas claimed absent from mathlib:
> `Gammaℝ_conj`, `completedRiemannZeta₀_conj`, `completedRiemannZeta_conj`,
> `riemannZeta_conj` — all unconditional (no pole exclusions, `1/0 = 0`
> convention), kernel-clean, via the Dirichlet/Gamma representation on the
> halfplane + analytic identity theorem on the entire `Λ₀`. Natural upstream
> home: `Mathlib/NumberTheory/LSeries/RiemannZeta.lean` (or a small new file
> beside it). Not yet staged in `ForMathlib/` — porting is mechanical (strip the
> PF namespace, drop the §1 `cpow` helpers if master has equivalents, keep
> `pi_cpow_conj`/`natCast_cpow_conj` as private lemmas otherwise). This PR is
> independent of PR-1..3 — submit as a standalone, not stacked on them.

## STEP 1 — you do this (one interactive step I can't do headlessly)

In a terminal on this machine:

```bash
gh auth login           # choose: GitHub.com → HTTPS → login with browser
                        # (enter the one-time code it shows, in your browser)
gh auth status          # should say: Logged in to github.com as <you>
```

The current token is expired; this refreshes it. Once done, tell me "authed"
and I take it from here — the token is shared with the CLI my tools use.

## STEP 2 — I do this once you're authed

1. **Fork** `leanprover-community/mathlib4` (`gh repo fork --clone`) into a fresh
   working clone at mathlib **master** (not our pinned rc — PRs must target
   current master; I'll handle the API drift I pre-flagged in the roadmap).
2. **Port each file** to its upstream path, rewriting the `import PF.ForMathlib.*`
   lines to `import Mathlib.*` and dropping any PF-only imports:

   | staged file | → mathlib path |
   |---|---|
   | `TwoSidedIdealClosure.lean` | `Mathlib/Topology/Algebra/Ring/TwoSidedIdeal.lean` |
   | `CfcMemTwoSidedIdeal.lean` | `Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Ideal.lean` |
   | `ClopenSpectralProjection.lean` | `Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/SpectralProjection.lean` |

3. **Build + lint against master**: `lake build` the new files, run
   `scripts/lint-style.sh` / the mathlib linters, fix any drift (the flagged
   risks: `closure` → possible `topologicalClosure` rename; `mem_top` explicit-R;
   lemma relocations). Iterate until green on master.
4. **Open the PRs** as a small stacked series (PR-1 base; PR-2 on PR-1; PR-3 on
   PR-2), using the descriptions already written in `MATHLIB_PR_ROADMAP.md`.
   Add the `awaiting-review` etiquette (concise title, motivation, `#find`/no
   `sorry`, kernel-axioms note).

## Notes

- These three (WALL A) are independent of the hard WALL-B research; they stand
  as real mathlib contributions on their own. Submitting them does not depend on
  Glimm ever closing.
- mathlib review is human and can take weeks; that's normal. The value is banked
  the moment they're in review.
- If you'd rather I open them under a personal fork vs. `FractalDevTeam`, say so
  at STEP 1.

## 2026-07-25 — module-system recipe (learned from PR #42093)

mathlib master is on **Lean v4.33.0-rc1 with the module system** (our PF pin is
v4.24). Every ForMathlib file needs these FOUR adaptations before it will build on
master CI. Bake them in from the first push for PR-2/3/4:

1. After the copyright block, add a line `module` then a blank line.
2. Make every import `public import Mathlib...` (not bare `import`).
3. After the module docstring, add `@[expose] public section` (else the
   `linter.privateModule` fatal warning fires — decls are private by default).
4. Fix deprecations flagged by CI (e.g. `continuous_mul_left`→`continuous_const_mul`,
   `continuous_mul_right`→`continuous_mul_const`); the Build job treats warnings as fatal.

Keep the PF-repo `ForMathlib/*.lean` copies in the OLD (v4.24) style — they must keep
building on the PF pin. The module-adapted versions live only on the fork
`DrDMT-VR/mathlib4`. Push flow: token-in-URL (`https://x-access-token:$(gh auth token)@...`),
snap `gh` can't read files outside `$HOME` so put PR bodies there.

PR #42093 (TwoSidedIdeal.closure): Build+Lint green, MERGEABLE, labels t-topology +
new-contributor, awaiting maintainer review.

## 2026-07-25 evening — three PRs open, all green

| PR | Content | Status |
|---|---|---|
| [#42093](https://github.com/leanprover-community/mathlib4/pull/42093) | `TwoSidedIdeal.closure` | Build ✅ Test+lint ✅ MERGEABLE |
| [#42095](https://github.com/leanprover-community/mathlib4/pull/42095) | `cfcₙ` into closed two-sided ideals | Build ✅ Test+lint ✅ |
| [#42100](https://github.com/leanprover-community/mathlib4/pull/42100) | clopen spectral projections | opened; stacked on #42095 |

**Key process win: build locally before pushing.** The fork clone at
`<scratchpad>/mathlib4` has a warm cache (`lake exe cache get` already run), so
`lake build <Module>` takes ~2s and catches all drift before CI. This is how PR-3 was
staged with zero failed CI rounds, vs PR-1's four.

Additional v4.33 deprecations found beyond the earlier four-step recipe:
`continuousOn_iff_continuous_restrict` → `continuousOn_iff_continuous_domRestrict`,
`Set.restrict`/`Set.restrict_apply` → `Set.domRestrict`/`Set.domRestrict_apply`,
`push_neg` → `push Not`. Build treats ALL warnings as fatal — the build line must show
`✔`, not `⚠`.

Remaining: **PR-4** = the r115 zeta-conjugation lemmas (`Gammaℝ_conj`,
`completedRiemannZeta₀_conj`, `completedRiemannZeta_conj`, `riemannZeta_conj`), standalone,
not yet staged.


## PR-4 opened — [#42101](https://github.com/leanprover-community/mathlib4/pull/42101)

`feat(NumberTheory/LSeries): conjugation symmetry for the completed Riemann zeta function`

Ships the three genuinely-missing lemmas: `Complex.Gammaℝ_conj` (into
`Analysis/SpecialFunctions/Gamma/Deligne.lean`), `completedRiemannZeta₀_conj` and
`completedRiemannZeta_conj` (into `NumberTheory/LSeries/RiemannZeta.lean`), all
unconditional, all `@[simp]`. Verified with a FULL `lake build Mathlib` (8685 jobs,
exit 0, zero warnings) plus `lake exe lint-style`.

Touches a third file as a drive-by: golfs the pre-existing `riemannZeta_conj` in
`ZetaAsymp.lean` from ~25 lines to 4 by deriving it from the new lemmas (name,
statement and attribute unchanged) — this resolves the redundancy the PR would
otherwise create. The PR body offers to drop or relocate it if reviewers prefer.

**Open question for Pablo:** the touched files' `Authors:` headers were NOT amended.
Mathlib reviewers commonly ask contributors to add themselves. Decide the upstream
attribution name you want and it's a one-line follow-up.

Also noted: `gh auth status` shows a stale second account (`FractalDevTeam`) failing to
log in. Harmless — the active `DrDMT-VR` token is what's used — but worth clearing.

## 2026-07-31 — AI DISCLOSURE POLICY, settled by mathlib triage

Michael Rothgang (`grunweg`) asked on [#42093] whether AI was used, citing
mathlib's AI policy: **not forbidden, but must be disclosed.** He then added the
disclosure to #42093's description himself and tightened the wording.

**This settles the `Authors:` question flagged for #42101.** The two are separate:

- **Copyright header `Authors:` line — humans only.** mathlib convention lists
  human authors. Do NOT put an AI collaborator there. Our in-repo files use
  `Author: Pablo Cohen + Claude`, which is right for *this* repo; anything
  upstreamed becomes `Authors: Pablo Cohen`.
- **PR description — where the disclosure goes.** One sentence suffices.

### Action required: add to #42095, #42100, #42101

Paste-ready text (matching the information content grunweg kept on #42093):

> Parts of this contribution were developed with AI assistance (Claude). All
> statements are machine-checked by the Lean kernel; `#print axioms` on the new
> declarations reports only `[propext, Classical.choice, Quot.sound]`.

### Status

| PR | subject | disclosure |
|---|---|---|
| [#42093](https://github.com/leanprover-community/mathlib4/pull/42093) | `TwoSidedIdeal.closure` | DONE (added by maintainer) |
| [#42095](https://github.com/leanprover-community/mathlib4/pull/42095) | `cfcₙ` into closed two-sided ideals | TODO |
| [#42100](https://github.com/leanprover-community/mathlib4/pull/42100) | clopen spectral projections | TODO |
| [#42101](https://github.com/leanprover-community/mathlib4/pull/42101) | zeta conjugation symmetry | TODO (and `Authors:` = humans only) |

### Why our position is already sound

The disclosure trail predates the question, at three layers:
- **papers** — the Acknowledgements of both the Glimm/UHF paper and the
  Mordell–Weil paper state the AI collaboration and the independent-rebuild
  protocol explicitly;
- **Lean files** — every header carries `Author: Pablo Cohen + Claude`;
- **git** — every commit carries a `Co-Authored-By: Claude Opus 5` trailer.

Provenance is policy; **correctness is independently checkable.** Reproduction:
toolchain `leanprover-community/lean4:v4.24.0-rc1`, mathlib pin `eed770a4`,
`lake build PF` = 4673 jobs, zero warnings, axiom triple on every cited theorem.
