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
