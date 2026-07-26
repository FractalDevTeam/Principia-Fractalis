# Making the Coq layer real (started 2026-07-25)

## The finding that forced this

Every one of the 761 `.v` files in this directory currently proves `True`:

```coq
Theorem ..._parity : True.
Proof. exact I. Qed.
```

The 9,844 "Theorem / 9,844 Qed / 0 Admitted" statistic is measuring nothing — every
`Qed` closes the trivial goal. The 3,989 declarations that are not literally `: True`
prove `honest_scope_coq_parity_only`, which is itself `:= True`. So the layer contains
**zero mathematical content**. The README's "structural-shape mirror, not an independent
mathematical verification" is accurate but too gentle: a reader who opens one file and
finds `exact I` will reasonably distrust the rest of the corpus, including the genuinely
kernel-verified Lean results.

Directive (Pablo, 2026-07-25): make it real, "no ifs, ands or buts."

## What that can and cannot mean — honestly

| Group | Files | Can it be made real? |
|---|---|---|
| **A. UHF arc (r102–r113)** — finite-dimensional core | ~14 | **YES, now.** Real mathcomp proofs. This is genuine mathematics: level-k trace faithfulness, tracial-functional uniqueness (commutator argument), Weyl clock/shift averaging, base-3 tower combinatorics. |
| **B. UHF arc — completion tier** | (same files, upper half) | **Not yet.** Rocq/mathcomp has no C\*-algebra theory (the same wall mathlib had). Building it is a months-long project of its own. Until then these state the finite-dimensional content and say plainly what is not covered. |
| **C. Mirrors of conditional/open Lean content** (Millennium, `Conjecture`, `Attempt`, `Frontier`) | ~496 | **Cannot be made real, in any prover.** The underlying mathematics is unproven. The honest Coq version encodes the *implication* ("IF ⟨named open prop⟩ THEN claim"), which verifies the reduction, not the claim. |
| **D. Capstones/aggregators over A–C** | remainder | Inherit the status of what they aggregate. |

**The deliverable, therefore:** no file in this directory states `True` while implying
verification. Group A becomes real proofs. Groups B–D state exactly and only what they
establish, with the gap named. That is achievable in full, and it is what rigor means
here. Coq proofs of open problems are not on the table for anyone.

## Toolchain

- Rocq 9.1.0, mathcomp 2.5.0 (`boot`, `order`, `ssreflect`, `fingroup`; **`algebra` +
  `field` installed 2026-07-25** for matrices/trace/fields), Coquelicot 3.4.4 for real
  analysis.
- Real proofs live in `PF_Real/` (new); the legacy shape-index files stay in `PF/`
  until each is either replaced or explicitly relabelled.

## Order of work

1. `PF_Real/MatrixTraceFaithful.v` — `\tr (M *m M^T) = 0 -> M = 0` (foundation stone;
   the Coq counterpart of `normalized_matrix_trace_star_mul_self_eq_zero_iff`).
2. `PF_Real/MatrixTracialUnique.v` — any additive, homogeneous, unital, tracial
   functional on `'M[F]_n` is the normalized trace (commutator argument; the Coq
   counterpart of r113's `matrix_tracial_state_unique`).
3. `PF_Real/WeylAveraging.v` — clock/shift unitaries and the averaging identity (r104).
4. `PF_Real/Base3Tower.v` — the `3^k` tower embeddings and trace compatibility (r109).
5. Relabel Groups B–D: rename `*_parity` → `*_ShapeIndex`, and put a header on every
   file stating "declaration-name and dependency-shape index; contains no mathematical
   content" — so nothing can be mistaken for verification.

Progress is tracked by a single invariant: **`grep -c 'exact I' PF_Real/` must stay 0.**

---

## Status 2026-07-26

### Done — four real Coq files exist and compile

All four Group-A targets are built, compile under Rocq 9.1.0 + mathcomp 2.5.0
(algebra/field), and every `Print Assumptions` reports *"Closed under the global context"*.
`grep -c 'exact I' PF_Real/` = **0**. No `Admitted`, no `Axiom`, no `Parameter`. (The
`Hypothesis` lines in `MatrixTracialUnique.v`, `Base3Tower.v` and `WeylAveraging.v` are
`Section` hypotheses — they become explicit premises of the resulting theorems, not
axioms, which is why `Print Assumptions` stays clean.)

| File | Theorem+Lemma | `Qed` | Lines |
|---|---:|---:|---:|
| `PF_Real/MatrixTraceFaithful.v` | 2 | 2 | 50 |
| `PF_Real/MatrixTracialUnique.v` | 14 | 14 | 187 |
| `PF_Real/Base3Tower.v` | 48 | 48 | 427 |
| `PF_Real/WeylAveraging.v` | 46 | 46 | 439 |
| **total** | **110** | **110** | **1,103** |

### Done — step 5, the legacy tree is now banner-labelled

Every one of the 761 `.v` files in `PF/` was given a prepended comment banner (script-
driven, idempotent, nothing deleted — verified by md5: the concatenation of all original
file bytes is bit-identical to the concatenation of the post-banner suffixes). `PF/README.md`
was written to state the tree's status plainly. Spot-compiles confirm the banners are inert:
21 files compiled pre- and post-banner produced identical exit codes.

### Correction to the finding at the top of this document

The claim above — *"Every one of the 761 `.v` files in this directory currently proves
`True`"* — is **overstated**, and the 2026-07-26 audit corrected it. Actual measurement over
9,860 `Proof … Qed` blocks:

- **7,367 (74.7%)** are `True` / `exact I`-class. Zero content. This is the bulk, and the
  central finding stands.
- **2,481 (25.2%)** are closed with real tactics (`lra`, `reflexivity`, `lia`, `nra`,
  `vm_compute`, `field`, `rewrite`, induction). Kernel-checked, but overwhelmingly
  arithmetic over hand-chosen literals, definitional unfoldings of framework constants, or
  `hypothesis -> claim` reductions over an assumed `Prop`. A minority (notably
  `PF/IntervalArithmetic.v`, parts of `PF/Analytic/`) is genuine but narrow mathematics.
- **12** are `Admitted`/`Abort` across 5 files — so the tree's advertised **"0 Admitted" is
  false**. `Admitted` still emits a `.vo`, so those files compile while assuming their
  conclusions.
- **244** axiom-like declarations (`Axiom`/`Parameter`/`Hypothesis`) across 37 files.

By file: **477** are pure shape index (no substantive proof, no `Admitted`, no axiom) and
carry the `SHAPE INDEX ONLY — NO MATHEMATICAL CONTENT` banner verbatim. The other **284**
carry a `LEGACY PARITY TREE — MIXED CONTENT` banner that prints that file's own
trivial/substantive/`Admitted`/axiom counts. Stamping the blanket "everything here is
`True`" text on those 284 would have replaced one inaccuracy with another, so it was not
done.

### Also found

The checked-in `.vo` artifacts in `PF/` are **stale**: built under Coq 8.18 (`.vo` version
`81800`) against an installed Rocq 9.1.0 (expects `90100`). `PF/MillenniumSixReductions.v`
fails to compile for this reason alone — it compiles cleanly once its `TuringEncoding/*`
dependencies are rebuilt. A full `make clean && make` is needed before any build statistic
about `PF/` is meaningful.

`PF_Coq_Code/README.md` (the top-level one) still says the Coq layer *"Provides independent
cross-prover verification of the same theorems"* and targets *"0 sorries / 0 admits"*. That
is now contradicted by `PF/README.md` and should be rewritten; it was left untouched in this
pass to keep the change surface small.

### What remains

1. **Group B — completion tier: still impossible in Rocq.** No C\*-algebra theory exists in
   Rocq/mathcomp: no C\*-norm, no involution on an abstract completion, no GNS
   construction, no Glimm/UHF machinery. So faithfulness of `tau_UHF` on `T_infinity`,
   Glimm simplicity, and uniqueness of the trace on the completion **cannot** be mirrored.
   This is the same wall mathlib presented before its operator-algebra infrastructure was
   built, and clearing it is a months-long project in its own right. `PF_Real/README.md`
   states this scope limit explicitly; nothing in `PF_Real/` should be read as covering it.
2. **Groups C and D remain shape-index only** and are now labelled as such. Group C cannot
   be made real in any prover — the underlying mathematics is open. The available upgrade is
   to encode the *implications* explicitly rather than `True`; the banners make the current
   status unmistakable in the meantime.
3. **Optional next real targets**, if the arc continues: star/adjoint structure over an
   involutive base ring; iterated tower steps (`partialTraceDown`, `condExp`) beyond the
   single `k -> k+1` step; connecting the Weyl algebra to the base-3 tower. None of these
   need C\*-theory.
4. **Rename pass** (`*_parity` -> `*_ShapeIndex`) from step 5 was **not** done — only the
   header banners. Renaming 9,808 declarations would break every dependent file in the tree
   and is a separate, riskier operation.
