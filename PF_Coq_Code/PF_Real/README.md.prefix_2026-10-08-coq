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
| `Base3Tower.v` | the level bijection `'I_(3^k) * 'I_3 ~ 'I_(3^(k+1))`; the embedding `A |-> A (x) I_3` (additive, multiplicative, unital); `\tr (emb3 A) = 3 * \tr A` and normalized-trace preservation; the partial trace `ptr3` with the retraction `ptr3 (emb3 A) = A` | `substrateEmbedMatrix` (r28) + `partialTraceStep_*` (r109) | none |
| `WeylAveraging.v` | character-sum orthogonality; clock/shift matrices with explicit inverses; the Weyl commutation `S C = w (C S)`; the clock average = diagonal part; and the FULL two-index average `weyl_average : (1/n^2) . sum_{a,b} S^b C^a X C^(n-a) S^(n-b) = (\tr X / n) . 1` | `matrix_unitary_average_eq_trace_smul_one` (r104) | none |

`MatrixTracialUnique.v` is in one respect *stronger* than the Lean original: it holds over
an arbitrary `fieldType`, and the needed `n.+1%:R != 0` is **derived** from unitality
rather than assumed.

## Scope, stated plainly

### Additional scope limits (Base3Tower, WeylAveraging)

- **No star/adjoint structure.** The base is an arbitrary `comRingType`/`fieldType`, which
  carries no involution, so the Lean `*_star` lemmas have no counterpart here.
- **Single tower step only.** `emb3`/`ptr3` go level `k` <-> `k+1`; the iterated
  `partialTraceDown` / `condExp` are not built.
- **"Unitary" is realised as "invertible".** mathcomp has no unitary group / operator norm /
  positivity over an abstract field, so inverses are written concretely as `C^(n-a)`,
  `S^(n-b)` and *proved* to be inverses.
- The Weyl algebra is not connected to the base-3 tower; that bridge does not exist here.

These are the **finite-dimensional** core of the r102–r113 UHF arc. The completion-tier
results (faithfulness of `tau_UHF` on `T_infinity`, Glimm simplicity, uniqueness of the
trace on the completion) are **not** mirrored here: Rocq/mathcomp has no C*-algebra
theory, which is the same wall mathlib presented before that infrastructure was built.
Nothing in this directory should be read as verifying those results.

Build: `coqc -Q PF_Real PFReal PF_Real/<file>.v` (Rocq 9.1.0, mathcomp 2.5.0 with
algebra/field).
