# PF_Lean4Lean — Meta-Verification Layer

**Status (2026-06-04):** PARTIAL BUILD CLEAN — flagship theorem
`PF.Referee.PrincipiaFractalisSubstrateTheorem` is re-verified as an
independent-package import with `[propext, Classical.choice, Quot.sound]`-only
axiom dependence. Six per-pillar contract modules remain GATED on an
architectural gap; see Section "Architectural Gap" below.

For the full audit see
[`../REFEREE_PROOF_LEAN4LEAN_AUDIT_2026-06-04.md`](../REFEREE_PROOF_LEAN4LEAN_AUDIT_2026-06-04.md).

## Purpose

PF_Lean4Lean is the **third formalization layer** of Principia Fractalis:

```
PF_Lean4_Code/        — canonical Lean 4 source (machine-verified, 0 project axioms)
        |
        v
   Lean 4 kernel      — Lean 4's built-in type-checker
        |
        v
PF_Lean4Lean/         — external-import re-verification of canonical theorems
        |
        v             — (future: Mario Carneiro's external lean4lean program)
        v
PF_Coq_Code/          — independent cross-prover parity (Coq)
```

The L4L layer's purpose is to re-import canonical theorems into a separate
lake package (with an independent build hash) and confirm the axiom-list
via build-time `#print axioms` reports. Any drift away from the three
foundational Lean axioms surfaces at L4L build time. The strongest form
(running Mario Carneiro's external `lean4lean` program against produced
`.olean` files) is future work; the current package provides the
import-side scaffolding required for that step.

## L4L External-Kernel Certification (2026-06-04)

The flagship single-citation theorem
`PF.Referee.PrincipiaFractalisSubstrateTheorem` is re-verified from the
independent `PF_L4L` lake package as
`PF_L4L.Referee.flagshipReverified : PFSubstrateAntecedents → PFSubstrateConsequences`,
with build-time `#print axioms` reporting only
`[propext, Classical.choice, Quot.sound]` — zero project axioms. The
unconditional consequences inhabitation
`PF_L4L.Referee.flagshipConsequencesReverified` carries the same axiom
list. The spectral-gap apparatus (`PF.SpectralGap`) and the P vs NP
conditional bridge (`PF.P_NP_Equivalence.P_neq_NP_via_spectral_gap`) are
re-verified as `PF_L4L.Core.spectralGapSpecPF` and
`PF_L4L.Ch21.pnpContractPF`, with the same axiom list. See
[`../REFEREE_PROOF_LEAN4LEAN_AUDIT_2026-06-04.md`](../REFEREE_PROOF_LEAN4LEAN_AUDIT_2026-06-04.md)
for the full protocol.

## Current Status

- **Source files present:** `PF_L4L/Ch20/RH.lean`, `Ch21/PNP.lean`,
  `Ch23/YM.lean`, `Ch24/BSD.lean`, plus
  `Core/{AxiomAudit, Resonance, SpectralGap, Zeta}.lean`. New (2026-06-04):
  `Referee/FlagshipReverification.lean`.
- **Build participation:**
  - REACHABLE (build clean, depend only on
    `propext, Classical.choice, Quot.sound`): `PF_L4L.Core.SpectralGap`,
    `PF_L4L.Ch21.PNP`, `PF_L4L.Referee.FlagshipReverification`.
  - GATED (6 modules): `PF_L4L.Core.{Resonance, Zeta, AxiomAudit}`,
    `PF_L4L.{Ch20.RH, Ch23.YM, Ch24.BSD}` — architectural gap, see below.
- **Lakefile path:** `../PF_Lean4_Code` (correct).
- **Toolchain:** `leanprover/lean4:v4.24.0-rc1`, mathlib4 `v4.24.0-rc1`.
- **CI:** does NOT currently run L4L's build. An explicit
  `cd PF_Lean4Lean && lake build` is required.

## Architectural Gap (2026-06-04)

Six L4L source files import modules under the `PF.*` namespace that do not
exist in the current `PF_Lean4_Code/` layout:

| L4L module                   | Bad import (file not in PF lake library)                                          |
|------------------------------|-----------------------------------------------------------------------------------|
| `PF_L4L.Core.Resonance`      | `PF.YM_Equivalence`                                                                |
| `PF_L4L.Core.Zeta`           | `PF.RH_Equivalence`                                                                |
| `PF_L4L.Core.AxiomAudit`     | `PF.Axioms`, `PF.RH_Equivalence`, `PF.YM_Equivalence`, `PF.BSD_Equivalence`, `PF.ConsciousnessCore` |
| `PF_L4L.Ch20.RH`             | `PF.RH_Equivalence`                                                                |
| `PF_L4L.Ch23.YM`             | `PF.YM_Equivalence`                                                                |
| `PF_L4L.Ch24.BSD`            | `PF.BSD_Equivalence`                                                               |

The corresponding `.lean` files exist on disk at `PF_Lean4_Code/` top level
(e.g., `PF_Lean4_Code/RH_Equivalence.lean`), but they are **not** exposed
via the `PF` lake library. `PF_Lean4_Code/lakefile.toml` declares
`[[lean_lib]] name = "PF"`, which only exposes files under
`PF_Lean4_Code/PF/`. The top-level orphans are not module roots of any
lake library.

Additionally, `RH_Equivalence.lean` declares
`axiom riemann_zeta : ℂ → ℂ` — an axiom in conflict with the current PF
framework's zero-axiom policy. The L4L `Core/Zeta.lean` `rfl`-based
agreement proof would fail even if the import were reachable, because
`riemann_zeta` is an opaque axiom in the source, not a `def` that reduces
to `riemannZeta`.

### Architectural Decision

See [`L4L_ARCHITECTURAL_DECISION.md`](L4L_ARCHITECTURAL_DECISION.md) for
the full rationale. The 2026-04-28 decision (Path B: rewrite `rfl`-based
agreement proofs) remains in effect for the GATED modules. The 2026-06-04
audit adds a third path:

**Path C (selected for the flagship module):** re-verify theorems that
**are already exposed by `PF/`**. The single most load-bearing capstone
(`PF.Referee.PrincipiaFractalisSubstrateTheorem`) is now re-verified
under this path, demonstrating the pattern. Future work can extend the
same pattern to other PF-exposed theorems (e.g., `PF.Wave58MasterCapstone`,
`PF.Referee.CrossMillenniumMetaClosure`).

## Quick Start

```bash
cd PF_Lean4Lean
export PATH="$HOME/.elan/bin:$PATH"
lake update
lake exe cache get
lake build
```

Expected: `Build completed successfully (3897 jobs).`

Confirm zero project axioms in the `#print axioms` info-messages emitted
during build:

```
'PF_L4L.Core.spectralGapSpecPF'                  depends on axioms: [propext, Classical.choice, Quot.sound]
'PF_L4L.Ch21.pnpContractPF'                      depends on axioms: [propext, Classical.choice, Quot.sound]
'PF_L4L.Referee.flagshipReverified'              depends on axioms: [propext, Classical.choice, Quot.sound]
'PF_L4L.Referee.flagshipConsequencesReverified'  depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Open Work

1. **(External program wire-in):** add Mario Carneiro's
   `mario-carneiro/lean4lean` as a lake dependency, run
   `lean4lean check` against produced `.olean` files as a post-build step.
   This is the strict third-prover form of L4L verification.
2. **(Extend Path C pattern):** add re-verification modules for the
   remaining flagship capstones (`PF.Wave58MasterCapstone`,
   `PF.Referee.CrossMillenniumMetaClosure`,
   `PF.NavierStokes.LerayHopfGlobalExistenceBootstrap`, etc.) using the
   same `def T_reverified := T; #print axioms T_reverified` pattern.
3. **(Resolve GATED modules):** either modify
   `PF_Lean4_Code/lakefile.toml` to expose the top-level orphan files as
   a second `[[lean_lib]]`, OR rewrite the 6 GATED L4L files to bind only
   against the `PF.*` namespace. The first is a one-line change but
   touches the canonical framework; the second is a multi-day refactor.
4. **(CI):** re-enable L4L participation in the project axiom audit
   (`tools/audit.sh`) once the external program wire-in lands.

## Why It Is Surfaced

Even partially built, the L4L layer is the documented mechanism by which
Principia Fractalis proposes to satisfy a third-party verification step
beyond Lean 4 itself. The flagship single-citation theorem is
machine-verified through this layer at this HEAD; six pillar contracts
are documented as future work with the precise architectural gap recorded
above. The three-layer story (canonical Lean 4 → L4L meta-checker → Coq
cross-prover) is referee-relevant.
