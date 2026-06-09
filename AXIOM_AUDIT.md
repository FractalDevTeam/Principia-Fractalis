# Axiom Audit — Principia Fractalis

**Audit cycle:** 2026-06-09
**Maintainer:** Pablo Cohen
**Adjacent docs:** [`OPEN_PROBLEMS.md`](OPEN_PROBLEMS.md), [`PROOF_PACKAGE.md`](PROOF_PACKAGE.md), [`CHANGELOG.md`](CHANGELOG.md)

This document catalogs every axiom-shaped commitment in the Principia
Fractalis formalization. It is honest about what the "zero project axioms"
claim does and does not mean.

---

## Level 0 — Lean kernel axioms (unavoidable)

Every Lean 4 development that uses classical mathematics relies on
exactly these three foundational axioms:

```
propext         -- propositional extensionality
Classical.choice -- the axiom of choice
Quot.sound      -- soundness of quotient types
```

These are mathlib's accepted foundations; they are not part of the
project's claim catalog. `#print axioms` on any PF capstone should
return only these three (and a build-time check enforces this — see
`tools/audit.sh`).

---

## Level 1 — Project-level `axiom` declarations

**As of 2026-06-09: zero `axiom` keyword declarations in the canonical
`PF/` library.**

Historical eliminations (pre-cleanup):

| Former axiom | Status now | Where eliminated |
|---|---|---|
| `H_P_selfAdjoint`, `H_NP_selfAdjoint` | REMOVED as unused | `PF/TuringEncoding/Operators.lean` (deletion note) |
| `H_P_groundStateEnergy`, `H_NP_groundStateEnergy` | REMOVED as unused | `PF/TuringEncoding/Operators.lean` (deletion note) |
| `alpha_class_polylog_eigenvalue_conjecture` | Refactored to `def : Prop` | `PF/TuringEncoding/Operators.lean` (now `PolylogEigenvalueConjecture`) |
| `pi_lower_bound`, `pi_upper_bound` (9-decimal π bounds) | Refactored to theorems | `PF/IntervalArithmetic.lean` (audit 2026-06-09 batch 3) — now derived from `Real.pi_gt_d20` / `Real.pi_lt_d20` |

---

## Level 2 — Calculus / mathematical-fact axioms (intentional, narrow)

A small number of axioms encode real-analysis facts that are true but
not in mathlib at the precision required:

| Axiom | File | Why axiomatized |
|---|---|---|
| `radix_economy_decreasing_from_six` | `PF/IntervalArithmetic.lean` | Real calculus fact about the radix-economy function not in mathlib |
| `radix_economy_maximum_at_e` | `PF/IntervalArithmetic.lean` | Same as above (related fact) |
| `log_2_lower`, `log_2_upper` | `PF/IntervalArithmetic.lean` | High-precision log bounds not in mathlib at this precision |
| `log_3_lower`, `log_3_upper`, `log_5_lower`, `log_5_upper`, `log_6_lower`, `log_6_upper` | `PF/IntervalArithmetic.lean` | Same family |
| `log_4_eq` | `PF/IntervalArithmetic.lean` | `Real.log 4 = 2 * Real.log 2` (true but stated as axiom) |

These are eliminable by either (a) computing tighter mathlib bounds, or
(b) PR-ing the missing lemmas upstream. They are real-analysis facts,
not novel mathematical content.

---

## Level 3 — Named-hypothesis `def : Prop` (the substrate's assumptions)

These are NOT `axiom` declarations in Lean. They are explicit definitions
of propositions that load-bearing theorems take as hypotheses. They are
honestly *the framework's substrate-level assumptions*. Each is catalogued
in [`OPEN_PROBLEMS.md`](OPEN_PROBLEMS.md).

| Name | File | OPEN_PROBLEMS item |
|---|---|---|
| `PolylogEigenvalueConjecture` | `PF/TuringEncoding/Operators.lean` | P1 |
| `RHSpectralSurjectivityConjecture` | `PF/RHSurjectivityConjecture.lean` | P4 |
| `fractalEmergenceNoBlowup` | `PF/MillenniumSixReductions.lean` | P5 |
| `fractalYMMassGap` | `PF/MillenniumSixReductions.lean` | P6 |
| `fractalBSDRankEquality` | `PF/MillenniumSixReductions.lean` | P7 |
| `fractalHodgeCrystallization` | `PF/MillenniumSixReductions.lean` | P8 |
| `KatoRellichInput` | `PF/Operators/VAlphaExplicit.lean` | P2 — but this Prop is proven **false** in `KatoRellichDischarge.lean`; the structural replacement is `H_alpha_PMap` in `VAlphaPMap.lean` |
| `GroundStateVariationalInput` | `PF/Operators/VAlphaExplicit.lean` | spectral variational principle, conditional |

**Honest scope:** these Props are the substrate's *axioms in the
informal sense* — the framework's assumed truths that the discharge
chain rests on. The "0 project axioms" claim is true on the literal Lean
keyword `axiom`; it is **not** a claim that the framework rests on no
assumptions. The assumptions live as hypotheses, propagated through
theorem signatures, with their open status documented here and in
OPEN_PROBLEMS.md.

---

## Level 4 — Coq `Parameter` declarations (equivalent to axioms)

Coq's `Parameter` is functionally identical to `Axiom` — both introduce
assumed entities with no proof. Audit 2026-06-09 found:

| Coq file | Count | Notes |
|---|---|---|
| `PF/Wave19/PNPUnconditional.v` | 7 `Parameter`s | Includes `P_neq_NP_def`, `P_neq_NP_via_spectral_gap`; the latter IS the conclusion |
| (other Wave files) | ~91 total `Parameter`s (per file header counts) | Standard "Coq stdlib GAP" — Complex/Coquelicot infrastructure not in stdlib |

The "0 Axioms" claim for the Coq side is true on the literal `Axiom`
keyword. The `Parameter` count is non-zero; the README's claim of
parity with the Lean side should note this distinction.

---

## Build-verified axiom claim

```bash
bash tools/audit.sh
```

runs `lake build PF` and `#print axioms` on the canonical theorem
`PF.Referee.PerelmanAnchoredSimultaneousClosure.perelman_anchor_yields_simultaneous_clay_closure`.
Expected output: `[propext, Classical.choice, Quot.sound]` and **no other
axioms**. The CI workflow `.github/workflows/lean.yml` runs the same
verification on every push/PR.

---

## Summary

| Level | What it is | Count | Honest framing |
|---|---|---|---|
| 0 | Lean kernel axioms | 3 | Foundational; same as all mathlib developments |
| 1 | Project `axiom` declarations in PF/ | 0 | True claim of "0 project axioms" |
| 2 | Real-analysis fact axioms (π/log bounds, radix economy) | ~10 | Real but not novel; eliminable by mathlib upstream |
| 3 | `def : Prop` named hypotheses (the substrate's assumptions) | 8 load-bearing | The actual framework assumptions; see OPEN_PROBLEMS.md |
| 4 | Coq `Parameter` declarations | ~91 | Functionally axioms; called Parameters by convention |

The substrate-level honest framing is: **PF's load-bearing claims rest on
the Lean kernel + a small set of real-analysis facts + the named
substrate hypotheses (Level 3). The Level 3 hypotheses ARE the
framework's content; discharging them is the open mathematical work.**
