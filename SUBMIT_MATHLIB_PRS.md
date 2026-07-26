# Submitting the mathlib PRs — handoff kit

Three verified, upstreamable files are staged in `PF_Lean4_Code/PF/ForMathlib/`
(all kernel-clean, root namespaces, mathlib conventions). This is the exact
procedure to get them into `leanprover-community/mathlib4`.

> **2026-07-25 addendum — PR-4 (zeta conjugation symmetry).** r115
> (`PF/Analytic/XiRealWitness.lean`) proved four lemmas absent from mathlib:
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
