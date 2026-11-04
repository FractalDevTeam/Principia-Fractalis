# `P_NP_Axiom_Elimination.lean` — retired from `PF/` on 2026-11-03

**Nothing was deleted.** The file is here byte-for-byte; `git` records the
rename. Its content sha256 is identical on both sides of the move:

```
1349156c0a7141695d6a9917ef84e32f661ae592a09f23d37b5d3d2dec4a14de
```

Only the extension changed — `.lean` → `.lean.retired` — so it is no longer
Lean source and no longer answers a `grep --include=*.lean`. It can be restored
with a single `git mv`.

## Why it was retired

This executes the standing prescription in
`codex/SEMANTIC_PARITY_MAP_2026-10-06.md`, item (i):

> *"Relocate byte-for-byte out of `PF/` with a note; do not delete."*

The parity map's stated reason was that the file's `theorem P_NEQ_NP` carries
**no hypothesis**, has no `olean`, no importers, is not in the closure, and that
its proof would require `π/10/√2 = π/10/(φ+¼)`, which is false.

**Measured on 2026-11-03, which settles it more plainly than that inference.**

1. **The file cannot be built at the pinned mathlib (v4.24.0-rc1).** Its import
   `Mathlib.Analysis.SpecialFunctions.Gamma` does not exist at this pin — that
   module was split into `Gamma/Basic`, `Gamma/Beta`, `Gamma/BohrMollerup`,
   `Gamma/Deligne` and `Gamma/Deriv`. It was the **only** file among all 9,492
   `PF/*.lean` sources importing it, which is exactly why no build had ever
   surfaced it.

2. **Repairing that single import and rebuilding gives 20 errors**, among them:
   - `spectral_gap_positive_proof` is an **unknown identifier** at line 245 —
     and it is one of the two results the `P_NEQ_NP` proof cites;
   - `alpha_P`, `alpha_NP` and `certificate_forces_higher_frequency` are
     *"already declared"*: the file duplicates declarations it imports;
   - `List.enum` and `List.toTM3` do not exist at this pin;
   - plus type mismatches, two failed `calc` steps, unsolved goals, a failed
     `rfl`.

3. **So the live `#print axioms P_NEQ_NP` command inside the file has never
   executed, and that theorem has never been kernel-checked.** The file's
   comments say `MAIN THEOREM: P ≠ NP (COMPLETE PROOF WITHOUT AXIOMS)` and
   `#check P_NEQ_NP -- Main Result: ✓ PROVEN`. Nothing certified any of it.

4. **Nothing depended on it.** Zero importers, no `olean`, and its
   uniquely-owned `spectral_gap_positive_proof` occurred in no other file in the
   corpus. Last content commit 2025-11-29; the August 2026 touch was a
   tree-wide registry rebuild.

## What the corpus actually claims about P vs NP

This retirement removes a dead artifact. It does not remove a claim, because
the live claims were already conditional and said so **in their types**. After
the move, every `P_NEQ_NP`-shaped theorem in `PF/` carries its hypothesis in
its signature:

| declaration | hypothesis, in the type |
|---|---|
| `P_NP_Complete_Proof.lean:340` `P_NEQ_NP` | `(hpoly : PolylogEigenvalueConjecture)` |
| `P_NP_Equivalence.lean:298` `P_neq_NP_via_spectral_gap` | `(hpoly : PolylogEigenvalueConjecture)` |
| `TuringEncoding/Operators.lean:393` `P_neq_NP_from_spectral_gap` | `(hpoly : PolylogEigenvalueConjecture)` |
| `EmpiricalPostulateDischarge.lean:201` | `ClassP ≠ ClassNP → …` |
| `EmpiricalPostulateDischarge.lean:230` | `EmpiricalCH2Postulate → …` |
| `EmpiricalPostulateDischarge.lean:274` | `(PolylogEigenvalueConjecture ∨ EmpiricalCH2Postulate) → …` |

`PolylogEigenvalueConjecture` is a `def … : Prop` (`Operators.lean:250`), not an
axiom, and `P_NP_Complete_Proof.lean`'s docstring records the refactor that made
it explicit: *"Refactor 2026-05-20: now takes the `PolylogEigenvalueConjecture`
hypothesis explicitly."* That is the same shape as the Riemann chain's two
undischarged hypotheses — a named, explicit, undischarged premise carried in
the type. **No Clay result is claimed, here or anywhere in the live tree.**

The five other files in the repository containing a hypothesis-free
`theorem P_NEQ_NP : P_neq_NP_def` were already in `ARCHIVE/` before this move
(`2026-06-08-cleanup/`, `2026-06-16-orphans/`). This was the last one in the
live Lean tree.

## One naming issue left standing, reported not acted on

`PF/SpectralGap.lean:77` declares `theorem P_neq_NP : spectral_gap ≠ 0` under
the docstring *"P and NP are topologically distinct."* The **statement** is a
true fact about a real number; the **name and docstring** describe a complexity
separation. That file is also outside the closure (zero importers). Renaming a
theorem is the kind of change the project's own rules reserve, so it is
recorded here rather than made.

## Provenance

- Prescribed: `codex/SEMANTIC_PARITY_MAP_2026-10-06.md` item (i)
- Measured and executed: 2026-11-03
- Book record: `appendices/appL_substrate_bundle_closure_2026-06-18_19.tex`,
  the P-vs-NP bridge bullet
- Restore with: `git mv ARCHIVE/2026-11-03-pnp-axiom-elimination-retired/P_NP_Axiom_Elimination.lean.retired PF_Lean4_Code/PF/P_NP_Axiom_Elimination.lean`
