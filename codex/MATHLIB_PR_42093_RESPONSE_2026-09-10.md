# Response to mathlib4 PR #42093

**Target:** [leanprover-community/mathlib4#42093](https://github.com/leanprover-community/mathlib4/pull/42093) — *feat(Topology/Algebra/Ring): topological closure of a two-sided ideal* by @DrDMT-VR

**Author of this response:** Pablo Cohen (FractalDevTeam) — as a peer contributor with parallel work on unital `StarSubalgebra` closure/direct-limit apparatus arising from a UHF-algebra classification formalization.

**Date:** 2026-09-10

---

## Draft comment (paste into the PR thread)

Congratulations on this contribution and thanks for the AI-use disclosure — that discipline sets a useful precedent for the LLM-assisted-formalization category the community is now navigating.

I'm writing as a peer contributor with a directly adjacent gap-filling result: while formalizing Glimm's 1960 UHF classification specialized to supernatural number `3^∞` in Lean 4 ([FractalDevTeam/Principia-Fractalis@r331b-provenance](https://github.com/FractalDevTeam/Principia-Fractalis/tree/r331b-provenance), commit `22cb48e2`, 2026-09-10), we needed the analog for `StarSubalgebra`:

> ```lean
> private lemma coe_iSup_of_directed_starSubalgebra
>     {ι : Type*} [Nonempty ι] {K : ι → StarSubalgebra ℂ A}
>     (dir : Directed (· ≤ ·) K) :
>     ((⨆ i, K i : StarSubalgebra ℂ A) : Set A) = ⋃ i, (K i : Set A)
> ```

Mathlib currently ships the corresponding result only for `NonUnitalStarSubalgebra` (via `Subalgebra.coe_iSup_of_directed`). The unital-star case is a straightforward extension using `Subalgebra.copy` and pointwise-`star_mem`, but the lemma is not currently there. If you (or the reviewers here) are interested, I can prepare a standalone PR immediately upstream of this one, mirroring the naming and namespacing conventions this PR is establishing.

We are also queuing four more mathlib-PR candidates from the same formalization work, all following the pattern this PR sets:

1. **`conjByUnitary`** — for a unitary `U : Matrix (Fin n) (Fin n) ℂ`, the map `x ↦ U * x * star U` as a `StarAlgEquiv`. Currently absent; useful in matrix-algebra automorphism arguments (Noether–Skolem).
2. **`reindexStarAlgEquiv`** — upgrading `Matrix.reindexAlgEquiv` to preserve `star` via `Matrix.conjTranspose_reindex` (which is definitionally `rfl` when the same reindex is applied to both row and column axes). Matches the pattern of `Matrix.reindexAlgEquiv` and `Matrix.reindexLinearEquiv`.
3. **`IsDenseInducing.extendStarAlgHom`** — the star-upgraded analog of the existing `UniformSpace.Completion.extensionHom` / `IsDenseInducing.extendRingHom` pattern (mathlib `Topology/Algebra/UniformRing.lean:282-304`). We currently do this specialized to a concrete UHF-algebra completion; the general version would mirror the `RingHom` pattern.
4. **`IsTracialLinearFunctional`** and its uniqueness apparatus — mathlib currently has no named `TracialState` class (`PositiveContinuousLinearMap` is the closest). Even a minimal `structure IsTracial` + a handful of API lemmas would fill a real gap.

Regarding the reviewer feedback:

- @j-loreaux's points 1–5 are exactly the pattern I'd want reviewers to apply to our submissions too. Point 4 (`IsOpenUnits` typeclass over explicit hypothesis) is particularly worth generalizing — I'll draft our `IsDenseInducing.extendStarAlgHom` with an analogous typeclass hypothesis where a Banach-algebra assumption isn't needed.
- @grunweg's requirement that AI use be disclosed up front is one we support unconditionally. Our substrate-rigidity work was farmed via a coordinated series of Claude Opus 4.7 sessions under an explicit statement-card discipline; all mathematical decisions (theorem specification, proof-strategy pivots, semantic scoping) were human-authored, and every declaration audits to `[propext, Classical.choice, Quot.sound]`. We plan to include a disclosure of the same form in every PR body.

Happy to coordinate: if @j-loreaux or another maintainer would find it useful, I can (a) prepare `coe_iSup_of_directed_starSubalgebra` as a small PR before this one merges, then (b) queue the other four as a chain following #42093's naming and disclosure conventions. Let me know which cadence works best for review.

---

## Notes for our own PR submissions (internal to Principia Fractalis)

**Disclosure paragraph, standardized:** include in every PR body, following the pattern @grunweg required here.

> *AI-generated content notice: This PR was drafted with the assistance of Claude Opus 4.7, following the coordinated statement-card / kernel-audit discipline described in [FractalDevTeam/Principia-Fractalis codex/FLT_LESSONS_FOR_PF_2026-09-08.md](https://github.com/FractalDevTeam/Principia-Fractalis/blob/r331b-provenance/codex/FLT_LESSONS_FOR_PF_2026-09-08.md) and modeled on Anthropic's September 2026 FLT formalization run. All theorem statements, semantic scoping, and mathematical decisions are human-authored (P. Cohen). Every declaration in this PR passes `#print axioms` = `[propext, Classical.choice, Quot.sound]`.*

**Naming pattern from PR #42093:**
- `TwoSidedIdeal.closure` (protected, no `_root_` prefix)
- `TwoSidedIdeal.coe_closure`, `mem_closure_iff`, `le_closure`, `closure_mono`, `closure_minimal`, `isClosed_closure`, `closure_eq_of_isClosed`, `closure_closure`, `closure_top`, `closure_ne_top`
- Discussion around `closure` vs `topologicalClosure` still open; watch for the maintainer's decision and mirror it.

**Reviewer conventions to preemptively apply:**
- No `_root_.` prefix on protected declarations.
- Extract inline `have` statements as separate lemmas (each with its own name and docstring).
- Prefer `instance` over `theorem` for structural closure facts.
- Prefer typeclass hypotheses over explicit hypotheses where a general instance exists (`IsOpenUnits`, `IsClosed`, etc.).
- Attach `@[gcongr]` to monotonicity lemmas.
- Attach `@[simp]` sparingly; prefer named-lemma explicit rewriting when the LHS could be ambiguous.

**PR submission order (proposed):**
1. `coe_iSup_of_directed_starSubalgebra` — smallest, fills a direct symmetry gap with the non-unital case.
2. `conjByUnitary` + `reindexStarAlgEquiv` — matrix-algebra helpers, low controversy, useful independently.
3. `IsDenseInducing.extendStarAlgHom` — the more delicate structural PR; discuss naming and scope on Zulip first.
4. `IsTracialLinearFunctional` (or `IsTracialFunctional`) — broadest scope; benefits from Zulip design discussion before PR.

**Cross-referencing:** every PR body should cite the parent formalization (this Principia Fractalis substrate-rigidity paper, GitHub-hosted, DOI to follow) as the motivating context.

---

## What this response also does

It notifies the mathlib community that a next contribution chain is forthcoming, associated with a concrete formalization result (`T_infinity_rigidity`) that is already kernel-verified on a public branch. That establishes standing for the chain before it lands and lets reviewers plan bandwidth. It also builds continuity with the existing LLM-assisted-formalization thread — PR #42093 is not the first such PR, but the community norms are still forming, and each contribution should honour them.

*Location: `codex/MATHLIB_PR_42093_RESPONSE_2026-09-10.md`. Ready to paste into PR #42093 discussion thread on Pablo's authorization.*
