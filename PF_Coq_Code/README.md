# Principia Fractalis — Coq Port

Coq mechanization of Principia Fractalis, mirroring the Lean 4
formalization in `../PF_Lean4_Code/`. Provides independent cross-prover
verification of the same theorems.

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
* The single mathematical axiom `alpha_class_self_adjointness_canonical`
  (declared identically in both provers).
* Headline theorems' axiom dependencies traceable via `Print Assumptions`.

## Independent Verification

Both Lean 4 and Coq mechanizations are intended as independent
referee-grade verifications of the same mathematical claims. Discrepancies
between the two ports would indicate either a formalization bug or a
mathematical subtlety worth investigating.
