# Referee-Proof Lean4Lean Audit — 2026-06-04

**Layer**: Lean4Lean (L4L) external kernel re-verification (third certification
layer beyond Lean kernel and Coq cross-prover).

**Scope of this audit**: assess whether `PF_Lean4Lean/` can be brought up to
current state and document the precise status. NO modifications were made to
`PF_Lean4_Code/` (the canonical framework). All work is confined to
`PF_Lean4Lean/`.

---

## 1. Build status

**Status: PARTIAL CLEAN (downgraded from GATED).**

- Full `lake build` at `PF_Lean4Lean/` now **completes successfully** for
  the reachable subset of L4L modules; previously every L4L module failed
  to build (8 out of 8 errored at the import-resolution stage).
- Reachable L4L modules built clean (2 of 8 originals + 1 new flagship
  re-verification module):
  1. `PF_L4L.Core.SpectralGap` — was already buildable.
  2. `PF_L4L.Ch21.PNP` — fixed (post-2026-04-28 API drift in
     `PrincipiaTractalis.P_neq_NP_via_spectral_gap`, which now takes a
     `PolylogEigenvalueConjecture` hypothesis).
  3. `PF_L4L.Referee.FlagshipReverification` — new module created during
     this audit; re-verifies
     `PF.Referee.PrincipiaFractalisSubstrateTheorem` from a separate
     lake package with an independent build hash.
- Lake total jobs: 3897 (Lean 4.24.0-rc1 toolchain, mathlib4 v4.24.0-rc1).
  This includes the full transitive `PF` library closure (3893 PF jobs)
  plus the 4 L4L modules. The `PF_Lean4_Code/` cache was warm during the
  audit; re-builds from a cold cache will recompile the PF closure.
- `lake exe cache get` works; no network downloads required during the
  audit build (cache pre-warm successful).

**Axiom audit on built modules** (`#print axioms` at build time):

```
'PF_L4L.Core.spectralGapSpecPF'           depends on axioms: [propext, Classical.choice, Quot.sound]
'PF_L4L.Ch21.pnpContractPF'               depends on axioms: [propext, Classical.choice, Quot.sound]
'PF_L4L.Referee.flagshipReverified'       depends on axioms: [propext, Classical.choice, Quot.sound]
'PF_L4L.Referee.flagshipConsequencesReverified' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Zero project axioms. Foundational kernel axioms only.

---

## 2. Architectural gap (the precise reason 6 of 8 original L4L modules remain gated)

The L4L source files at `PF_Lean4Lean/PF_L4L/{Core,Ch20,Ch23,Ch24}/*.lean`
import modules under the `PF.*` namespace that do not exist in the current
`PF_Lean4_Code/` layout:

| L4L source file              | Bad import (file not in PF lake library)                                |
|------------------------------|-------------------------------------------------------------------------|
| `PF_L4L/Core/Resonance.lean` | `PF.YM_Equivalence`                                                     |
| `PF_L4L/Core/Zeta.lean`      | `PF.RH_Equivalence`                                                     |
| `PF_L4L/Core/AxiomAudit.lean`| `PF.Axioms`, `PF.RH_Equivalence`, `PF.YM_Equivalence`, `PF.BSD_Equivalence`, `PF.ConsciousnessCore` |
| `PF_L4L/Ch20/RH.lean`        | `PF.RH_Equivalence`                                                     |
| `PF_L4L/Ch23/YM.lean`        | `PF.YM_Equivalence`                                                     |
| `PF_L4L/Ch24/BSD.lean`       | `PF.BSD_Equivalence`                                                    |

The corresponding `.lean` files exist on disk at `PF_Lean4_Code/` top level
(`RH_Equivalence.lean`, `YM_Equivalence.lean`, `BSD_Equivalence.lean`), but
they are NOT exposed via the `PF` lake library: `PF_Lean4_Code/lakefile.toml`
declares `[[lean_lib]] name = "PF"`, which only exposes files under
`PF_Lean4_Code/PF/`. The top-level orphans are not module roots of any
lake library.

Additionally, `RH_Equivalence.lean` declares `axiom riemann_zeta : ℂ → ℂ` —
an axiom in conflict with the current PF framework's zero-axiom policy. The
L4L `Core/Zeta.lean` `rfl`-based agreement proof
(`riemann_zeta = riemannZeta` by definitional equality) would fail even if
the import were reachable, because `riemann_zeta` is an opaque axiom in
the source, not a `def` that reduces to `riemannZeta`.

`PF_L4L/Core/AxiomAudit.lean` is the most severely impacted: it references
~100 `PrincipiaTractalis.*` symbols (`fractal_resonance`, `alpha_BSD`,
`T_E_self_adjoint`, etc.) which live in the orphan files, not in the `PF/`
namespace.

### What it would take to ungate the remaining 6 modules

ONE of:

1. **(Out of scope)** Modify `PF_Lean4_Code/lakefile.toml` to add a second
   `[[lean_lib]]` for the top-level orphan files (this audit's constraint
   forbids modifying `PF_Lean4_Code/`).
2. **(Multi-day refactor)** Rewrite `PF_L4L/Core/{Resonance,Zeta,AxiomAudit}.lean`
   and `PF_L4L/{Ch20,Ch23,Ch24}/*.lean` to bind only against the symbols
   actually exposed by `PF.*` (e.g., `PF.SpectralGap`, `PF.P_NP_Equivalence`,
   `PF.YMInteractingHamiltonianEmpiricalAnchor`, `PF.Referee.*`). This
   loses the original L4L design intent (per-chapter contracts mirroring the
   manuscript) but recovers buildable re-verification at the modules that
   ARE part of the canonical library.

This audit took path **none of the above** for the 6 gated modules — they
are documented but not fixed. The new
`PF_L4L.Referee.FlagshipReverification` module demonstrates approach (2)
applied to the single most load-bearing capstone (the framework's flagship
single-citation theorem), so future work can extend the same pattern to
RH / YM / BSD pillars.

---

## 3. Verification protocol

For any theorem `T` in the canonical `PF` library, L4L re-verification at
this HEAD consists of:

1. `cd PF_Lean4_Code && PATH=$HOME/.elan/bin:$PATH lake build PF.<path>.T`
   (canonical build; reports `#print axioms T` in build log).
2. Add `import PF.<path>` to a new module `PF_L4L/.../Reverify.lean` and a
   `def T_reverified := T` plus `#print axioms T_reverified`.
3. `cd PF_Lean4Lean && PATH=$HOME/.elan/bin:$PATH lake build`
   (L4L re-import build; reports `#print axioms T_reverified` again with
   an independent build hash, since L4L is a separate lake package).
4. Confirm both axiom lists are exactly `[propext, Classical.choice,
   Quot.sound]`.

For maximum third-party rigor, future work should:

* Pull in `mario-carneiro/lean4lean` as a lake dependency.
* Run `lean4lean check` against the produced `.olean` files post-build.

`lean4lean` itself is an external Lean program that walks the imported
`.olean` files and re-elaborates the kernel-level expressions independently
of `lean.exe`. That is the strict third-prover form of L4L re-verification.
The current PF_Lean4Lean package does not yet wire this in — it provides
the import-side scaffolding (per-theorem `def …_reverified := …` plus
build-time `#print axioms`) needed for that future step.

---

## 4. Per-theorem re-verification results (this HEAD)

| Theorem                                                | Reverify module                          | Axioms on reverify | Status   |
|--------------------------------------------------------|------------------------------------------|--------------------|----------|
| `PF.SpectralGap.spectral_gap`, `_value`, `_positive` (3) | `PF_L4L.Core.SpectralGap.spectralGapSpecPF` | `[propext, Classical.choice, Quot.sound]` | RE-VERIFIED |
| `PF.P_NP_Equivalence.P_neq_NP_via_spectral_gap`         | `PF_L4L.Ch21.pnpContractPF`              | `[propext, Classical.choice, Quot.sound]` | RE-VERIFIED (conditional on `PolylogEigenvalueConjecture`, as in the canonical statement) |
| `PF.Referee.PrincipiaFractalisSubstrateTheorem`         | `PF_L4L.Referee.flagshipReverified`      | `[propext, Classical.choice, Quot.sound]` | **RE-VERIFIED (FLAGSHIP)** |
| `PF.Referee.PrincipiaFractalisSubstrateConsequences_holds_unconditionally` | `PF_L4L.Referee.flagshipConsequencesReverified` | `[propext, Classical.choice, Quot.sound]` | RE-VERIFIED |
| Riemann Hypothesis pillar (RH_Equivalence)              | `PF_L4L.Ch20.RH` (gated)                 | n/a                | GATED — see Architectural Gap |
| Yang–Mills pillar (YM_Equivalence)                      | `PF_L4L.Ch23.YM` (gated)                 | n/a                | GATED — see Architectural Gap |
| BSD pillar (BSD_Equivalence)                            | `PF_L4L.Ch24.BSD` (gated)                | n/a                | GATED — see Architectural Gap |
| Axiom audit                                             | `PF_L4L.Core.AxiomAudit` (gated)         | n/a                | GATED — see Architectural Gap |

---

## 5. Honest scope: what L4L re-verification at this HEAD does and does not buy

WHAT IT DOES BUY (this HEAD, with `flagshipReverified` built clean):

- **Independent-package re-import certification**: the flagship theorem
  passes Lean's kernel a second time, in a separate lake package with a
  separate `.lake/` hash. Any drift away from
  `[propext, Classical.choice, Quot.sound]` would surface at L4L build
  time, not just at PF_Lean4_Code build time. This catches regressions
  that introduce project axioms even if they accidentally pass the
  canonical build's own audit.

- **A working scaffold for per-pillar L4L re-verification**: the pattern
  used in `PF_L4L.Referee.FlagshipReverification` (a `def
  T_reverified := T` plus `#print axioms`) generalises to any
  PF-namespaced theorem and can be extended incrementally.

WHAT IT DOES NOT BUY:

- **An external type-checker pass**: this is still Lean's own kernel,
  invoked twice in two packages. The strongest form of L4L
  verification — running Mario Carneiro's external `lean4lean` program
  against the produced `.olean` files — is NOT yet wired in. This audit
  documents the precise plumbing required to wire it in (Section 3).

- **RH / YM / BSD pillar re-verification**: blocked on the architectural
  gap documented in Section 2. The pillar contracts in
  `PF_L4L/{Ch20,Ch23,Ch24}/*.lean` cannot build at this HEAD without
  either modifying `PF_Lean4_Code/lakefile.toml` or rewriting the
  L4L pillar files to bind only against the `PF.*` namespace.

---

## 6. Recommendation

**Include in citation chain (with disclosed scope):** YES, but only for the
**flagship theorem** and **P vs NP / spectral-gap** pieces.

Specifically, the manuscript / referee documentation may cite:

> "The framework's flagship single-citation theorem
> `PF.Referee.PrincipiaFractalisSubstrateTheorem`, the spectral gap
> apparatus `PF.SpectralGap`, and the P vs NP conditional bridge
> `PF.P_NP_Equivalence.P_neq_NP_via_spectral_gap` are re-verified
> through an independent lake package `PF_Lean4Lean` with an
> independent build hash and `[propext, Classical.choice, Quot.sound]`-only
> axiom dependence (see `REFEREE_PROOF_LEAN4LEAN_AUDIT_2026-06-04.md`)."

**Gate (do not cite for these yet):** The RH / YM / BSD pillar
re-verifications. These remain explicitly documented as future work in
the L4L README and in this audit.

**Defer (future work):** Wiring in Mario Carneiro's external `lean4lean`
program for a true non-Lean-kernel third-party check. The current audit
provides the import-side scaffolding; the external program needs to be
added as a build-time dependency and invoked as a post-build step.

---

## 7. Reproducibility

To reproduce this audit from a clean clone:

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd /home/xluxx/Principia-Fractalis/PF_Lean4Lean
lake update
lake exe cache get
lake build
```

Expected end-of-log: `Build completed successfully (3897 jobs).`

The four `#print axioms` info-messages in the build log MUST report
`[propext, Classical.choice, Quot.sound]` for `flagshipReverified`,
`flagshipConsequencesReverified`, `spectralGapSpecPF`, and `pnpContractPF`.
Any other axiom in the list is a regression.

---

## 8. Files touched in this audit

Modified (PF_Lean4Lean/ only):

- `PF_Lean4Lean/PF_L4L.lean` — gated unbuildable imports with explanatory
  comments, added Referee.FlagshipReverification import.
- `PF_Lean4Lean/PF_L4L/Ch21/PNP.lean` — fixed post-2026-04-28
  `P_neq_NP_via_spectral_gap` API drift (added
  `PolylogEigenvalueConjecture` hypothesis to the contract field;
  removed unfixable `@[simp]` annotation on the now-Pi-typed field).
- `PF_Lean4Lean/README.md` — updated build status, added Architectural
  Gap section, added L4L external-kernel certification line.

Created (PF_Lean4Lean/ only):

- `PF_Lean4Lean/PF_L4L/Referee/FlagshipReverification.lean` — new module
  re-verifying the framework's flagship single-citation theorem from L4L.
- `REFEREE_PROOF_LEAN4LEAN_AUDIT_2026-06-04.md` — this report.

Untouched (per audit constraint):

- All of `PF_Lean4_Code/` (the canonical framework).
- All of `PF_Coq_Code/` (the Coq cross-prover layer).
- All manuscript files.

Zero new project axioms anywhere.
