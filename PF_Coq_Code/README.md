# Principia Fractalis — Coq Port

Coq mechanization work for Principia Fractalis, alongside the Lean 4
formalization in `../PF_Lean4_Code/`.

> **CORRECTED 2026-07-26 — this file previously claimed "independent
> cross-prover verification of the same theorems". That claim was false and is
> withdrawn.** Measured over all 9,860 `Proof … Qed` blocks in `PF/`:
> **6,749 are the one-liner `Proof. exact I. Qed.`** proving `True` — zero
> mathematical content. The remainder are closed with real tactics, but
> overwhelmingly arithmetic over hand-chosen literals, definitional unfoldings of
> framework constants, or `hypothesis → claim` reductions over an assumed `Prop`.
> A narrow minority (notably `PF/IntervalArithmetic.v`) is genuine but elementary
> mathematics.
>
> **Any citation of cross-prover verification must point at `PF_Real/`, never at
> `PF/`.** `PF_Real/` contains 110 real theorems across 4 files, every
> `Print Assumptions` reporting *"Closed under the global context"*, zero
> `exact I`, zero `Admitted`, zero `Axiom`. Its scope is the finite-dimensional
> core only — Rocq/mathcomp has no C\*-algebra theory, so the completion-tier
> results (faithfulness of `tau_UHF` on `T_infinity`, Glimm simplicity, uniqueness
> of the trace) are **not** mirrored there and must not be claimed.
>
> See `PF/README.md` and `COQ_REALIZATION_PLAN.md` for the full audit.

## Status

**Phase C — initialization**: directory structure + project config +
first port target (`PF/IntervalArithmetic.v` from
`../PF_Lean4_Code/PF/IntervalArithmetic.lean`).

## Dependencies

* **Coq 8.19+** (or compatible)
* **Coq stdlib `Reals`** — real-number arithmetic, `sqrt`, `PI`, trig
* **Coquelicot** (optional, for cleaner analysis API)
* **`coq-mathcomp-analysis`** (optional, for category-theoretic
  alignment with Lean mathlib)

Recommended installation via `opam`:

```sh
opam install coq coq-coquelicot coq-mathcomp-analysis
```

## Directory Structure

```
PF_Coq_Code/
├── README.md               (this file)
├── _CoqProject             (Coq project config, lists all .v files)
├── Makefile                (generated; or use coq_makefile)
├── PF/
│   ├── Basic.v             (foundation; minimal)
│   ├── IntervalArithmetic.v (port of IntervalArithmetic.lean)
│   └── ... (further ports)
```

## Build

```sh
cd PF_Coq_Code
coq_makefile -f _CoqProject -o Makefile
make
```

## Porting Strategy

Mirroring the Lean module layout 1-to-1:

| Lean (`PF_Lean4_Code/PF/...`) | Coq (`PF_Coq_Code/PF/...`) | Status |
|-------------------------------|----------------------------|--------|
| `Basic.lean`                  | `Basic.v`                  | ported |
| `IntervalArithmetic.lean`     | `IntervalArithmetic.v`     | in progress |
| `IntegralKernel/`             | `IntegralKernel/`          | pending |
| `TuringEncoding/`             | `TuringEncoding/`          | pending |
| `Analytic/`                   | `Analytic/`                | pending |
| ... (full list)               | ...                        | pending |

**Order of porting** (smallest-leaves first):
1. ✓ `Basic.v` (trivial)
2. → `IntervalArithmetic.v` (foundational; bounds on π, √2, φ)
3. `IntegralKernel/Basic.v`, `IntegralKernel/SelfAdjoint.v`,
   `IntegralKernel/FractalKernel.v`, etc.
4. `TuringEncoding/Basic.v`, `TuringEncoding/Operators.v`
5. `Analytic/Polylog.v`, `Analytic/Jonquieres.v`, etc.
6. The 29-module polylog-route framework, layer by layer.

## Goal

Match the Lean state's axiom-count discipline:
* Target: **0 sorries (axioms)**, **0 admits**.
  **NOT MET in `PF/` as of 2026-07-26.** Actual: **12 `Admitted.`** across 5
  files (`Wave16/YangMillsLevelKSpectrum.v`, `Wave20/HodgeDim4CY4Substrate.v`,
  `Wave15/ConsciousnessRHBridge.v`, `Wave15/PerelmanBackward.v`,
  `Wave18/NS3DVortexStretchingObstruction.v`) and **235 `Axiom`/`Parameter`**
  declarations across 37 files. `Admitted` still emits a `.vo`, so those files
  compile while assuming their conclusions. The target IS met in `PF_Real/`.
* The single mathematical axiom `alpha_class_polylog_eigenvalue_conjecture`
  (declared identically in both provers).
* Headline theorems' axiom dependencies traceable via `Print Assumptions`.

## Independent Verification

Both Lean 4 and Coq mechanizations are intended as independent
referee-grade verifications of the same mathematical claims. Discrepancies
between the two ports would indicate either a formalization bug or a
mathematical subtlety worth investigating.

---

## Scope and coverage statement (2026-08-04)

**What this layer is.** The Coq layer is a declaration-level
structural-shape mirror, not independent mathematical verification.
The parity pattern is:

```coq
Theorem name : True. Proof. exact I. Qed.
```

The correct one-line description is the one in the top-level
`README.md`:

> Coq 8.18 cross-prover structural-shape parity. The load-bearing
> mathematical verification lives in the Lean 4 + Lean4Lean kernels;
> the Coq layer is a declaration-level structural-shape mirror, not
> an independent mathematical verification

**Coverage cutoff.** The last shape-mirror `.v` files were added
2026-07-08 (Lean arc r101; the task-era estimate was ~2026-06-24 —
git history shows r101/2026-07-08 as the true cutoff). Everything
after that in the Lean tree has NO Coq counterpart of any kind.
In particular, nothing from r120 onward is mirrored here:

- Hardy RH on-line-zero atom (r120)
- BSD / Mordell–Weil rank arcs (r129–r182)
- Transfer-operator / Lefschetz arc (r183–r194)
- Friedmann (r187)

(The `BSD*` and `RH*Mayer*` files present in `PF/` are earlier
capstone-wave shape mirrors, dated ≤ 2026-07-08; they are not
counterparts of the r129+ arcs despite similar names.)

The only post-cutoff Coq work is `PF_Real/` (real, zero-axiom,
finite-dimensional theorems; see the 2026-07-26 correction above)
and the 2026-07-26 banner-labelling pass. Neither extends
shape-mirror coverage.
