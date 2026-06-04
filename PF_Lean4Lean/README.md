# PF_Lean4Lean — Meta-Verification Layer

**Status (2026-06-03):** Surfaced from `experimental/PF_L4L_future/` for visibility. Build participation is gated on a known refactor (see Status below); the canonical Lean 4 build at `PF_Lean4_Code/` is independent and unaffected.

## Purpose

PF_Lean4Lean is the **third formalization layer** of Principia Fractalis:

```
PF_Lean4_Code/        — canonical Lean 4 source (machine-verified, 0 project axioms)
        |
        v
   Lean 4 kernel      — Lean 4's built-in type-checker
        |
        v
PF_Lean4Lean/         — meta-level external re-verification of Lean 4 kernel output
        |
        v
PF_Coq_Code/          — independent cross-prover parity (Coq)
```

The L4L layer's purpose is **bit-for-bit agreement proofs** between Lean 4 expressions and an independent external type-checker. It is a verification layer, not a parallel formalization.

## Current Status

- **Source files present:** `PF_L4L/Ch20/RH.lean`, `Ch21/PNP.lean`, `Ch23/YM.lean`, `Ch24/BSD.lean`, plus `Core/{AxiomAudit, Resonance, SpectralGap, Zeta}.lean`.
- **Build participation:** GATED. The `rfl`-based agreement proofs require refactoring to keep up with post-2026-04-28 manuscript and canonical Lean 4 revisions (Ch 20 transfer operator, Ch 22 topological stability, Ch 23 mass gap, Ch 24 BSD operator, Ch 25 Hodge concentration).
- **Lakefile path:** updated to `../PF_Lean4_Code` (was `../PF_canonical/2_LEAN_SOURCE_CODE`, which referenced a now-empty submodule).
- **CI:** does NOT currently run L4L's build. An explicit `cd PF_Lean4Lean && lake build` is required.

## Architectural Decision

The full architectural rationale for keeping L4L verification-only (Path B) versus folding it into the canonical 8-axiom budget (Path A) is recorded in [`L4L_ARCHITECTURAL_DECISION.md`](L4L_ARCHITECTURAL_DECISION.md).

**Path B is selected**, with the explicit constraint that L4L remains verification-only and does NOT inflate the canonical project-axiom count tracked by `AXIOM_AUDIT.md`.

## Quick Start (advisory — not currently buildable end-to-end)

```bash
cd PF_Lean4Lean
lake exe cache get
lake build
# Expected (after refactor): Build participates in cross-prover parity audit.
# Current state: requires source-level updates to track 2026-04-28+ manuscript edits.
```

## Open Work

1. Rewrite `rfl`-based agreement proofs using `decide`, `Decidable.decide`, `norm_num`, `linarith`, `Eq.mpr`/`congr` for the agreement-witness pattern.
2. Synchronize `Ch20/RH.lean`, `Ch21/PNP.lean`, `Ch23/YM.lean`, `Ch24/BSD.lean` with the corresponding post-2026-04-28 canonical Lean 4 statements.
3. Where an L4L statement requires an axiom outside the canonical 8, attribute it in L4L's own namespace (`PF_L4L.Ch20.lemma_X_axiomatized_in_L4L_only`) — never in `PF_Lean4_Code/PF/`.
4. Re-enable L4L participation in the project axiom audit (`tools/audit.sh`) once the rewrite lands.

## Why It Is Surfaced

Even quarantined, the L4L layer is the documented mechanism by which Principia Fractalis proposes to satisfy a third-party verification step beyond Lean 4 itself. Hiding it under `experimental/` understated the framework's verification architecture; the three-layer story (canonical Lean 4 → L4L meta-checker → Coq cross-prover) is referee-relevant.
