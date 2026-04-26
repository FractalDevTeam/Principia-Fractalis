# experimental/

This directory holds work that exists in the repository for historical
preservation but is **not** part of the Revision 2 claim. None of it
is built, tested, or verified during the canonical `lake build` /
`make` commands. A referee should treat the contents of this
directory as future work, not as evidence of completed verification.

## Current contents

### `PF_L4L_future/`

A skeletal Lean4Lean meta-verification layer (~9 `.lean` files,
~566 lines). It was begun in earlier revisions with the intent of
providing a third independent formalization layer (Lean 4 → Coq →
Lean4Lean), but it never reached a working build state:

- The `lakefile.toml` requires a canonical-source directory
  (`../PF_canonical/2_LEAN_SOURCE_CODE`) that does not exist in the
  current repo layout.
- The L4L `import PF.Axioms` / `import PF.YM_Equivalence` /
  `import PF.RH_Equivalence` / `import PF.BSD_Equivalence` /
  `import PF.ConsciousnessCore` declarations expect a Lean file
  organization where these modules live under a `PF/` subdirectory,
  but the current Lean codebase has them at the top level of
  `PF_Lean4_Code/`.

Restoring L4L to a working state would require either restructuring
the Lean code organization or rewriting the L4L imports against the
current layout. Both are tracked as future work in
`/RESEARCH_ROADMAP.md` at the repository root.
