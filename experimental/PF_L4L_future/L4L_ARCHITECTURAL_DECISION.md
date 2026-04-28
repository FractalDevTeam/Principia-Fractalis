# Lean4Lean (L4L) Architectural Decision

*Decision recorded: 2026-04-28. Tracks REVISION_GUIDE.md tier 🟡 task #17.*

## Background

Lean4Lean (L4L) is the third formalization layer of Principia Fractalis,
sitting alongside the canonical Lean 4 layer (`PF_Lean4_Code/PF/`) and the
Coq layer (`PF_Coq/theories/`). L4L is currently quarantined under
`experimental/PF_L4L_future/`. The lakefile path was repaired at commit
`e0ab8f7 → 2e511f7` so the build infrastructure points correctly to the
canonical Lean 4 library, but the L4L source files themselves have not
been restored to active build participation.

## The architectural fork

Restoring L4L to active build participation has two paths:

### Path A: Expand the canonical `PF_Lean4_Code/PF/` scope

Pull L4L's framework-level statements into the canonical library. This
would put L4L's claims under the `PF/` namespace and into the official
build. **Cost**: the 8-axiom canonical count (the rev 2 manuscript's
referee-visible claim) inflates because L4L statements include
framework-level postulates that are presently axiomatized at L4L's own
level. The manuscript's Lean status section would need to be rewritten
to reflect a larger axiom count, which weakens one of the rev 2 cycle's
key empirical achievements.

### Path B: Rewrite L4L's `rfl`-based agreement proofs

L4L's design intent is to provide *bit-for-bit agreement proofs* between
Lean 4 expressions and an independent Lean4Lean type-checker — these are
typically `rfl`-based (definitional equality) and serve as a third-party
verification step. Rewriting these proofs changes the design intent of
L4L itself: instead of being a verification layer, L4L would become a
parallel formalization. This loses the third-party-verification value
that motivated L4L's separation from the canonical Lean 4 library in
the first place.

## Decision (2026-04-28)

**Path B is selected, with the explicit constraint that L4L remains
verification-only and does NOT inflate the canonical 8-axiom count.**

### Specifically

1. **L4L stays under `experimental/PF_L4L_future/`** in the current
   manuscript / formalization release cycle. Its build participation is
   gated on the rewrite below being completed without compromising the
   canonical 8-axiom claim.

2. **The `rfl`-based agreement proofs are to be incrementally rewritten**
   to use:

   * `decide` and `Decidable.decide` for finitely-checkable claims
   * `Tactic.norm_num` and `Tactic.linarith` for arithmetic claims
   * Mathlib's `Eq.mpr` / `congr` for the agreement-witness pattern
     where definitional equality fails but propositional equality
     holds modulo a lemma chain

3. **Where an L4L statement requires an axiom that is not in the canonical
   8**, that axiom is to be *attributed in L4L's own namespace*
   (e.g., `PF_L4L.Ch20.lemma_X_axiomatized_in_L4L_only`) rather than
   added to `PF_Lean4_Code/PF/`. This preserves the canonical 8-axiom
   claim while letting L4L's investigations proceed independently.

4. **L4L participates in the build at `experimental/` priority** — the
   `lake build` command at the repository root continues to refer
   exclusively to the canonical `PF_Lean4_Code/PF/`; an explicit
   `cd experimental/PF_L4L_future && lake build` is required to build
   L4L. The CI does not currently run L4L's build; this is intentional
   pending the rewrite.

5. **The L4L source files (`Ch20/`, `Ch21/`, `Ch23/`, `Ch24/`, `Core/`)
   that depend on now-revised manuscript theorems** (in particular,
   the post-V01-2026-04-27/28 manuscript edits to Ch 20 transfer operator,
   Ch 22 topological stability, Ch 23 mass gap, Ch 24 BSD operator,
   Ch 25 Hodge concentration) require their L4L counterparts to be
   updated to match the new manuscript / canonical-Lean-4 statements.
   This is a separate multi-day refactor and is tracked in this directory
   as future work.

6. **PARITY_REPORT.md** at the repository root continues to track the
   axiom counts in PF (Lean 4), PF_Coq, and PF_L4L separately, with the
   PF_L4L column reflecting the experimental status. As L4L files
   come back online they are added to PARITY_REPORT.md's enumeration.

## Status as of 2026-04-28

- L4L is quarantined under `experimental/PF_L4L_future/`.
- Lakefile path (`../../PF_Lean4_Code`) is correct.
- L4L source files exist but are not in the canonical build path.
- The eight (8) canonical axioms in `PF_Lean4_Code/PF/` are the
  referee-claimed count; L4L's axiomatization is independent and
  documented separately.
- Path B (preserve L4L design intent + canonical count) is the
  selected architectural direction.
- Full L4L restoration is a future-work item, not blocking the rev 3
  manuscript / formalization release.

## Cross-references

- `frontmatter/rev2_formalization_status.tex` (Lean 4 status section):
  the 8-axiom claim is the canonical `PF_Lean4_Code/PF/` count, with
  scope explicitly disclosed (commit `0b3829f`).
- `PARITY_REPORT.md` at repository root: per-layer axiom enumeration.
- `REVISION_GUIDE.md` at repository root: tier 🟡 task #17, "L4L
  Architectural Decision", recorded as RESOLVED by this document.
