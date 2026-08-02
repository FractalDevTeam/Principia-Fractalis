# The Paper Gate — what "100% sure, referee-proof, not AI slop" means operationally

**Standing policy, 2026-08-02.** No manuscript leaves this repository unless
every gate below passes. Distilled from `codex/GLIMM_PAPER_STYLE_CHARTER.md`,
the grunweg disclosure precedent (#42093), and this project's own audit history.

## Gate 1 — Correctness: the kernel, not confidence
- Every mathematical claim in the paper maps to a NAMED Lean theorem.
- Transitive `#print axioms` = `[propext, Classical.choice, Quot.sound]` for
  every cited theorem; no `sorry`, no `native_decide`, no project axioms.
- One-command reproduction (`./verify.sh` or equivalent) stated in the paper
  with measured runtime; toolchain + mathlib pin + HEAD hash printed.
- Verification data (job counts, HEAD) measured on the DAY of submission,
  never carried forward from a draft.
This is what "100% sure" means. A referee cannot dispute a kernel-checked
theorem; the only remaining surfaces are novelty, interest, and presentation.

## Gate 2 — Scope: claim exactly what is proved
- A "What is not proved" section, mandatory, load-bearing, specific.
- No Millennium-problem language unless the theorem statement is the literal
  Clay statement (it never is; so: never).
- Rank bounds are lower bounds; conditional results name their hypotheses in
  the theorem, not the prose; numerics are labeled evidence, never proof.
- The framework (substrate, α, consciousness, r-numbers) appears NOWHERE in a
  mainstream paper except one matter-of-fact provenance sentence.

## Gate 3 — Provenance: disclose once, factually
- Acknowledgements: one sentence — formalization carried out in collaboration
  with Claude (Anthropic) under the author's direction; all claims
  independently rebuilt and axiom-audited. (Settled form; already public on
  mathlib #42093 with maintainer sign-off.)
- `Authors:`/author lines: humans only. Git trailers carry the co-authorship.
- Never hide it, never dramatize it. The kernel does not care who wrote the
  proof; that is the entire point, and it is our strongest anti-slop argument.

## Gate 4 — Anti-slop signals (what referees actually pattern-match on)
- Every citation verified against the actual source (the book once cited
  Mayer 1991 for the wrong zeta; the c1-c12 correction round exists because
  of this class).
- No generation artifacts, no "150-digit precision" conflations, no
  unexplained constants, no tables without provenance.
- The mathematics must contain IDEAS a referee can see are ideas: in the MW
  paper these are the Jordan-von Neumann route to bi-additivity, the torsion
  bound needing no curve equation, the index-2 sublattice margin trick, the
  Z-encoding of kernel checks, Res(phi,psi) = Delta^2. Slop has no ideas.
- Internal consistency pass: every number appearing twice appears identically.

## Gate 5 — External adjudication before or alongside
- mathlib PRs are the gold standard: hostile expert review of the actual code,
  in public, with merge as the certificate. Keep candidates flowing.
- arXiv before journal; the repository public; referees can run everything.

## Current status against the gate
| Manuscript | Gate status |
|---|---|
| `uhf_faithful_trace_glimm` (+ short version) | PASSES (re-measure data at submission) |
| `formal_mordell_weil_rank` | PASSES after verification-data refresh (this commit) |
| Substrate/framework papers | DO NOT SUBMIT until repair queue P4-P9 lands |
| Framework-attempt results (e.g., T3 spectrum) | numerics -> proof -> Lean -> only then paper |
