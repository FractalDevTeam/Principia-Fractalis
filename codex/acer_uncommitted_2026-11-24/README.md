# Acer uncommitted state, preserved 2026-11-24

Preserved, NOT merged. `acer_working_tree.patch` is `git diff` from Acer's
`Principia-Fractalis-ACTIVE` at HEAD `21f7bf8b` (branch
`lean/acer-runner-switch-2026-11-20`), 4 modified tracked files, 79 insertions
/ 22 deletions.

**The load-bearing one is ch07_constants.tex (+95 lines): it RETRACTS the fine
structure constant claim.** The superseded theorem text reads "rests on a value
of R_f(1,2) that the series does not take." That retraction is on Acer only —
not on Legion, not on origin — so the book as published still asserts
`α_EM = R_f(1,2)·π/10`.

Landing it withdraws a claim, which is Pablo-only. Hence preserved here rather
than merged, following the 2026-11-23 precedent in
`codex/acer_uncommitted_2026-11-23/`.

The two Lean diffs are `/--` → `/-!` on docstrings that precede no declaration
— the correct repair for the 35ab64dd orphan-doc-comment break — and both
already match Legion's copies, so nothing is at risk there.
