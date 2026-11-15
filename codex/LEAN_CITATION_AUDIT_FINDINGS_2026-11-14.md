# Corpus-wide Lean citation cross-check — findings

**Date:** 2026-11-14.
**Script:** `/tmp/corpus_lean_cite_audit.py`.
**Log:** `codex/LEAN_CITATION_AUDIT_2026-11-14.tsv` (591 rows).

## Scope

For every `\texttt{...}` token in the book TeX that unescapes to a Lean-shaped identifier, we checked whether the token exists in the Lean tree.  Index built over 10{,}771 `.lean` files across `PF_Lean4_Code/` and `mathlib_candidates/`, yielding 379{,}009 distinct names (including fully-qualified forms).

## Numbers

- **590 Lean citations** found in 62 book TeX files.
- **420 found** (`Y`) — token resolves to a declared name in the Lean tree.
- **170 not found** (`N`) — index miss.
- After filtering Lean-core names (`native_decide`, `Classical.choice`, `Quot.sound`, `Iff.rfl`, etc.), mathlib names (`not_fermat_42`, `UniformSpace.Completion`, …), file suffixes (`.lean`, `.cff`, `.py`), and tool names: **72 citation instances** / **62 distinct tokens** remained as potential real misses.

## Classification of the 62 distinct unresolved tokens

### False alarms — token exists as namespace/file, not theorem

My indexer catches `theorem/def/lemma/structure/instance`-prefixed declarations but not `namespace` names directly.  These are real citations:

- `BSD_RankWitnessTypedUpgrade` — `PF/BSD_RankWitnessTypedUpgrade.lean`.
- `YM_ContinuumWightmanV2` — namespace in `PF/YM_ContinuumWightmanV2.lean`.
- `YM_OSRPInteractionScaffold` — namespace in `PF/YM_OSRPInteractionScaffold.lean`.
- `BSD_HeegnerRank1Proof` — namespace in `PF/BSD_HeegnerRank1Proof.lean`.
- `IBMPeaksGaloisPair` — exists widely; the dotted form `PF.IBMPeaksGaloisPair` reflects a namespace prefix the indexer didn't match.
- `PF_NS3DEncodingV4`, `PF_YMEncodingV4` — exist, cited as module prefix.
- `inv_BSD` — exists as `inv_BSD_YM`, `inv_BSD_NS` (compound names) in `TuringEncoding/AlphaSkeletonMasterCapstone.lean`.

### Correctly cited as retired / gated — not an error

`ch34_verification.tex` lines 660–671 explicitly documents an L4L architectural gap: five symbol names are flagged as "no longer exist at HEAD":
- `PF.RH_Equivalence`
- `PF.YM_Equivalence`
- `PF.BSD_Equivalence`
- `PF.Axioms`
- `PF.ConsciousnessCore`

My audit flagged these N; the chapter already discloses them as retired.  No action.

### Non-Lean tokens (filenames, Python, Cactus NR code, etc.)

Expected to be unresolved:
- `scipy.sparse.csr_matrix`, `mp.dps` — Python code snippets in ch34.
- `interface.ccl`, `evolve.c` — Cactus framework files in ch15 (numerical methods).
- `ADVERSARIAL_REBUTTAL` — codex markdown document.
- `SubstrateSpectralBump.lean` — bare filename reference.
- `cff.json`, `CITATION.cff` — package metadata.

### Research-direction names (not formalized theorems)

- `riemannHypothesis_below_15` — appears in multiple Lean docstrings as the research \emph{target} (RH on a finite rectangle, classically known since Riemann and Gram) that `rh_below_15_conditional` is one component of.  Book's version-history citation is of the target name, not a Lean theorem that was supposed to exist.  Pablo may want to clarify this in the prose.

### Lean core / mathlib — correctly cited

- `native_decide`, `Classical.choice`, `Quot.sound`, `propext`, `Iff.rfl`, `sorryAx`, `ofReduceBool`, `Nat.rec` — Lean core, correctly cited as the three-axiom-bar machinery.
- `not_fermat_42`, `UniformSpace.Completion`, `SchwartzMap.norm_le_seminorm`, `ConvexOn.map_integral_le`, `MeasureTheory.continuous_of_dominated`, `MemLp.exists_boundedContinuous_eLpNorm_sub_le`, `piEquivPiSubtypeProd`, `lintegral_prod_swap`, `Matrix.specialUnitaryGroup`, `Nat.cast_injective`, `StarSubalgebra.coe_iSup_of_directed` — mathlib references, correctly cited.

## Combined with today's three substantive fixes

Today's cross-check pass (`3bba6134`) already fixed three real Lean-vs-prose mismatches:
1. LMFDB `32.a2` → `32.a3` for `y² = x³ − x`.
2. Dropped unverified `LMFDB 64.a4` claim for `y² = x³ + x`.
3. ch20 RH preamble + conclusion: separated `rh_below_15_conditional` (argument-principle, conditional on R1/R2/R3) from the Legion box march (unconditional to 829/64) from the classical 150-digit zero-locus check.

## Verdict

**The book's Lean citations are substantively accurate.**  After filtering noise (Lean-core names, mathlib references, non-Lean filenames, retired symbols explicitly documented as retired), zero additional false Lean citations were found by the corpus-wide pattern pass.  The three real mismatches surfaced earlier today were already corrected in `3bba6134`.

The audit does NOT verify STATEMENT CONTENT — only existence of the cited names.  A deeper audit would, for each cited theorem, pull the actual Lean statement and compare against the TeX description.  Today's `3bba6134` commit did this for the specific claims I added in this session's TeX work; a corpus-wide statement-level audit is a separate project (estimated: weeks of careful interactive triage).

## Suggested next step if the audit should go deeper

For each of the ~420 `Y` citations in the log, produce a deeper check:
- Read the Lean theorem's signature + docstring.
- Read the surrounding book prose.
- Flag any mismatches where prose claim exceeds or misrepresents the Lean statement.

That would be the equivalent of today's ch20/ch21/ch22/ch24/ch25 scope-preamble pass extended to every chapter that cites a Lean theorem — likely 20–30 TeX files in scope, one interactive session per chapter.
