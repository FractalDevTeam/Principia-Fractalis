# PF_Real — real Coq proofs

Everything in this directory is **genuine machine-checked mathematics**, in contrast to
the legacy `PF/` tree, which is a declaration-name and dependency-shape index. Measured
2026-10-08 over all 9,973 proof obligations in `PF/`: **6,428 are literally `: True`**
and a further **808 are vacuous by reduction** (their statements are built only from
`Definition … : Prop := True` aliases, or `Record`s all of whose fields are such
aliases), so **7,236 (72.6%) verify nothing**. Of the 2,737 obligations whose statements
do mention a real object, 1,665 are closed ground arithmetic over hand-chosen literals
and only **439 are quantified general statements** — 104 of those 439 are in *this*
directory. See `../PF/README.md` and `../COQ_REALIZATION_PLAN.md`.

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
| `Base3Tower.v` | the level bijection `'I_(3^k) * 'I_3 ~ 'I_(3^(k+1))`; the embedding `A \|-> A (x) I_3` (additive, multiplicative, unital); `\tr (emb3 A) = 3 * \tr A` and normalized-trace preservation; the partial trace `ptr3` with the retraction `ptr3 (emb3 A) = A` | `substrateEmbedMatrix` (r28) + `partialTraceStep_*` (r109) | none |
| `WeylAveraging.v` | character-sum orthogonality; clock/shift matrices with explicit inverses; the Weyl commutation `S C = w (C S)`; the clock average = diagonal part; and the FULL two-index average `weyl_average : (1/n^2) . sum_{a,b} S^b C^a X C^(n-a) S^(n-b) = (\tr X / n) . 1` | `matrix_unitary_average_eq_trace_smul_one` (r104) | none |
| `SubstrateSpine_2026_10_08.v` | the **iterated** tower maps `embIter k j : 'M[F]_(3^k) -> 'M[F]_(3^(k+j))` and `ptrIter k j` in the other direction; `embIter` is a unital algebra map at every jump length; `\tr (embIter k j A) = (3^j)%:R * \tr A` and normalized-trace preservation across arbitrarily many levels; **subsequence invariance** `embIter (k+j) i o embIter k j = embIter k (j+i)`; the retraction `ptrIter k j (embIter k j A) = A`; tracial uniqueness at **arbitrary** positive dimension; and the capstone `substrate_tower_trace_coherent` — every tracial unital functional at any level `3^(k+j)` restricts, through the tower, to the normalized trace at level `3^k` | iterated `substrateEmbedMatrix` (r28), `partialTraceDown` / `condExp` (r109), `matrix_tracial_state_unique` (r113), `Substrate3Inf.trace_unique` (r337, finite skeleton only) | none |

**Totals: 5 files, 141 theorem-class declarations, 141 `Qed`, 1,648 lines.** Every one of
the 141 reports `Closed under the global context` under `Print Assumptions`.

`MatrixTracialUnique.v` is in one respect *stronger* than the Lean original: it holds over
an arbitrary `fieldType`, and the needed `n.+1%:R != 0` is **derived** from unitality
rather than assumed. `SubstrateSpine_2026_10_08.v` carries that further: its
`tracial_dim_neq0` derives invertibility of the dimension at arbitrary positive `d`, and
`tower_char3_forced` shows that the existence of one tracial unital functional at a level
`3^(m+1)` of the tower **forces** `3%:R != 0` in `F` — so `substrate_tower_trace_coherent`
assumes no characteristic condition at all.

## Scope, stated plainly

### Additional scope limits (Base3Tower, WeylAveraging, SubstrateSpine)

- **No star/adjoint structure.** The base is an arbitrary `comRingType`/`fieldType`, which
  carries no involution, so the Lean `*_star` lemmas have no counterpart here.
- **Iterated tower steps: now built, finite only.** `Base3Tower.v` covers the single step
  `k <-> k+1`. `SubstrateSpine_2026_10_08.v` builds the iterated maps `embIter` / `ptrIter`
  for an arbitrary jump length `j`, proves they compose correctly (the cocycle law, i.e.
  *subsequence invariance* for the finite tower), and proves the trace is coherent along
  the whole finite tower. What is still absent is the **limit**: there is no inductive
  limit, no completion, and therefore no `T_infinity` object anywhere in this directory.
- **Subsequence invariance is covered only in the finite, same-prime sense.** The
  remaining half of that bridge — non-isomorphism **across distinct supernatural numbers**
  — needs a `K_0` functor for C\*-algebras. Rocq/mathcomp has none. That is an open
  research lane, not a gap in the proofs here, and nothing in this directory should be
  read as addressing it.
- **"Unitary" is realised as "invertible".** mathcomp has no unitary group / operator norm /
  positivity over an abstract field, so inverses are written concretely as `C^(n-a)`,
  `S^(n-b)` and *proved* to be inverses.
- The Weyl algebra is not connected to the base-3 tower; that bridge does not exist here.

These are the **finite-dimensional** core of the r102–r113 UHF arc, plus (as of
2026-10-08) its finite tower-coherence layer. The completion-tier results (faithfulness of
`tau_UHF` on `T_infinity`, Glimm simplicity, uniqueness of the trace on the completion,
and `T_infinity_rigidity` itself) are **not** mirrored here: Rocq/mathcomp has no
C\*-algebra theory, which is the same wall mathlib presented before that infrastructure was
built. Nothing in this directory should be read as verifying those results.

Build: `coqc -Q PF_Real PFReal PF_Real/<file>.v` (Rocq 9.1.0, mathcomp 2.5.0 with
algebra/field). **`eval $(opam env)` first** — `/usr/bin/coqc` is Coq 8.18.0, has no
mathcomp, and silently shadows the opam switch; see `../TOOLCHAIN.md`.
