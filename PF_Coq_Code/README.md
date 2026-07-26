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
