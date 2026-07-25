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
