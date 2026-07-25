# PF_Real — real Coq proofs

Everything in this directory is **genuine machine-checked mathematics**, in contrast to
the legacy `PF/` tree, whose 761 files all prove `True` by `exact I` and contain no
mathematical content (see `../COQ_REALIZATION_PLAN.md`).

Invariants enforced here:

- No `Admitted`, no `Axiom`, no `Parameter`, no `exact I`, no `: True`.
- Every file ends with `Print Assumptions` on its main results, and the output must read
  **"Closed under the global context"** (Rocq's equivalent of a clean `#print axioms`).
- Each file names the Lean theorem it corresponds to, and states its scope honestly.

## Contents

| File | Proves | Lean counterpart | Axioms |
|---|---|---|---|
| `MatrixTraceFaithful.v` | `(\tr (M *m M^T) == 0) = (M == 0)` over a real domain | `normalized_matrix_trace_star_mul_self_eq_zero_iff` | none |
| `MatrixTracialUnique.v` | any additive, homogeneous, tracial, unital `phi : 'M[F]_n.+1 -> F` equals `\tr M / n.+1%:R`; plus the non-vacuity/uniqueness bundle | `matrix_tracial_state_unique` (r113) | none |

`MatrixTracialUnique.v` is in one respect *stronger* than the Lean original: it holds over
an arbitrary `fieldType`, and the needed `n.+1%:R != 0` is **derived** from unitality
rather than assumed.

## Scope, stated plainly

These are the **finite-dimensional** core of the r102–r113 UHF arc. The completion-tier
results (faithfulness of `tau_UHF` on `T_infinity`, Glimm simplicity, uniqueness of the
trace on the completion) are **not** mirrored here: Rocq/mathcomp has no C*-algebra
theory, which is the same wall mathlib presented before that infrastructure was built.
Nothing in this directory should be read as verifying those results.

Build: `coqc -Q PF_Real PFReal PF_Real/<file>.v` (Rocq 9.1.0, mathcomp 2.5.0 with
algebra/field).
