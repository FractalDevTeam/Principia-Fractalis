# Mathlib PR Series — C\*-Algebra Ideal & Spectral-Projection Theory

**Goal:** build, upstream-first, the missing mathlib theory identified by the r107a wall map
(`PF/SubstrateSpectralBump.lean` header) — the exact API whose absence blocks kernel-closure of
`SubstrateCompletionTraceDetectsIdeals`, i.e. Glimm-1960 simplicity of UHF algebras and hence
unconditional faithfulness of the substrate UHF trace.

**Method:** each PR is developed as a mathlib-style file under `PF_Lean4_Code/PF/ForMathlib/`
(root namespaces, mathlib conventions, kernel-verified against the pinned mathlib
`eed770a4` / v4.24.0-rc1), then ported to a mathlib4 fork branch and submitted upstream.
Standard staging convention; nothing here uses PF-specific definitions.

**Submission prerequisite:** `gh auth login` (current token expired) + fork of
`leanprover-community/mathlib4` under FractalDevTeam or a personal account.

## The series

| PR | Content | Wall | Status |
|----|---------|------|--------|
| 1 | `TwoSidedIdeal.closure` — closure of a two-sided ideal in a topological ring is a two-sided ideal; basic API (`le_closure`, `closure_minimal`, `isClosed_closure`, idempotence); `closure_ne_top` (proper ideals have proper closure when units are open) | A1 | **file complete & kernel-verified** (`PF/ForMathlib/TwoSidedIdealClosure.lean`, 11 decls); awaiting `gh auth` to fork/submit |
| 2 | `cfcₙ f a ∈ I` for closed two-sided `I` with `a ∈ I` — proved unconditionally on `f` (junk value 0 ∈ I) via `ContinuousMapZero.induction_on_of_compact`; + `smul_mem_of_isClosed`, `cfcₙHom_mem_of_isClosed`, `cfcₙ_mem_closure` | A2 | **file complete & kernel-verified** (`PF/ForMathlib/CfcMemTwoSidedIdeal.lean`, 4 decls) |
| 3 | `spectralProjection a U := cfcₙ (U.indicator 1) a`; selfadjoint + idempotent for clopen `U ∌ 0`, `∈ I` (PR-2), nonzero iff `U ∩ σₙ ≠ ∅`; finite-spectrum corollary `spectralProjection_singleton_ne_zero` (nonzero selfadjoint + finite σₙ ⇒ nonzero projection in `I`) | B1 (partial) | **file complete & kernel-verified** (`PF/ForMathlib/ClopenSpectralProjection.lean`, 9 decls). **WALL A now fully discharged for finite-spectrum algebras.** |
| 4 | Hereditary subalgebras and corners `pAp`; basic order/ideal correspondence | B2 | queued |
| 5 | Murray–von Neumann equivalence and subequivalence of projections; comparison in finite/matrix settings | B2 | queued |
| 6 | AF-specific: finite-spectrum elements have polynomial spectral projections; level-k projection trace-scaling `τ(q) ≥ n⁻¹` for the normalized trace | B3 | queued |

## Strategy notes

- **PR-3 sidesteps full Borel calculus.** General discontinuous cfc is a large project; but the
  indicator of a *clopen* spectral subset is already continuous on the spectrum, which `cfc`
  handles today. In AF/UHF algebras every level element has finite spectrum, so clopen-set
  projections + PR-6 may suffice for Glimm — the Borel route can stay future work.
- **Hypothesis rephrasing (PF-side, not a PR):** restating `SubstrateCompletionTraceDetectsIdeals`
  over *closed* ideals removes the unital-Pedersen component of WALL A entirely (r107a report).
  Do this in the PF repo once PR-1's closure API exists.
- Each PR is independently useful to mathlib regardless of PF — that is what makes the series
  upstreamable.

## PR-1 submission package (ready to paste)

**Title:** `feat(Topology/Algebra/Ring): topological closure of a two-sided ideal`

**Summary:** The topological closure of a two-sided ideal in a topological ring is a two-sided
ideal. Defines `TwoSidedIdeal.closure` with basic API, mirroring the one-sided `Ideal.closure`
(`Mathlib/Topology/Algebra/Ring/Ideal.lean`) but in the greater generality of non-unital
non-associative topological rings, where one-sided ideals are unavailable.

**Motivation:** mathlib has no topological-closure API for `TwoSidedIdeal`/`RingCon`. Closed
two-sided ideals are the basic objects of C\*-algebra ideal theory and groundwork for hereditary
subalgebras and spectral-projection arguments via cfc. `closure_ne_top` (units open ⟹ proper
ideals have proper closure, e.g. Banach algebras via `Units.isOpen`) is the standard first step
toward "maximal two-sided ideals are closed".

**Declarations:** `closure`, `coe_closure`, `mem_closure_iff`, `le_closure`, `closure_mono`,
`closure_minimal`, `isClosed_closure`, `closure_eq_of_isClosed`, `closure_closure`,
`closure_top`, `closure_ne_top`. Suggested location:
`Mathlib/Topology/Algebra/Ring/TwoSidedIdeal.lean`.

**Reviewer-risk notes:** may be asked to rename `closure` → `topologicalClosure` (modern
subobject convention; mechanical). `TwoSidedIdeal` API is actively developed — `mem_top`
explicit-`R` wart and lemma locations may have shifted on master (one-token fixes). The
`map_mem_closure` unification in `mk'` is elaborator-order sensitive; the `Set.MapsTo.closure`
form used is the robust one.

---

*Maintained by the r-numbered substrate arc; see `PF/SubstrateSpectralBump.lean` for the wall map,
and the full paper (`Papers/uhf_faithful_trace_glimm_2026-07-23.tex`) for the mathematical context.*
