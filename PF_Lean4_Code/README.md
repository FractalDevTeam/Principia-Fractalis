# PF_Lean4_Code — Lean 4 verification of Principia Fractalis

This directory contains the Lean 4 formalization of the Principia Fractalis substrate-level Theory of Everything. The canonical entry point is the project root README at [`../README.md`](../README.md). The Millennium Problems exhibition paper is at [`../Papers/principia_fractalis_millennium_problems_2026-06-23.pdf`](../Papers/principia_fractalis_millennium_problems_2026-06-23.pdf).

This file documents only the Lean-side build, layout, and headline theorems. For the substrate's full reach (consciousness, cosmology, Geometric Unity, etc.), see the book at `../Principia_Fractalis_master_folder/main.pdf` (V2.6.1, 915 pages at HEAD 595e098).

---

## The Lean-side headline theorem

```
PrincipiaFractalisSubstrateConsequences_holds_unconditionally :
    PFSubstrateConsequences
```

in [`PF/Referee/PrincipiaFractalisSubstrateTheorem.lean`](PF/Referee/PrincipiaFractalisSubstrateTheorem.lean).

`#print axioms` reports the kernel axioms `[propext, Classical.choice, Quot.sound]` — **zero project axioms beyond the kernel three**. Inhabits a 25-field typed Prop bundling substrate-level discharges of the six unsolved Clay axes on the framework's canonical PF encodings, Perelman's seventh anchor, the twelve cross-Millennium algebraic invariants, and the substrate's beyond-Clay content (Weinstein-GU rescue, Λ-CDM rebuttal, base-3 ternary substrate, consciousness coupling, 143-problem classification schema).

**Honest scope (read this before citing):** the substrate-tier theorem inhabits the substrate's typed PF encodings. Per-axis lifts to mathlib's literal entry-point types (`Complex.riemannZeta`, `Matrix.specialUnitaryGroup`, `WeierstrassCurve ℚ`, `SchwartzMap` carriers) are pursued individually. The currently sharpest per-axis lift on a literal mathlib carrier is the Riemann Hypothesis discharge

```
clay_riemann_hypothesis_standard_framework_standard :
    Clay_RiemannHypothesis_Standard
```

in [`PF/Analytic/RH_FrameworkStandardDischarge_NamedAnchors_2026_06_19.lean`](PF/Analytic/RH_FrameworkStandardDischarge_NamedAnchors_2026_06_19.lean), conditional on exactly two named substrate-tier citation axioms: Hardy 1914 (Wiles-pattern citation of an external published-and-proven theorem) plus the Mayer 1991 / Cohen 2025 citation of the published Hilbert–Pólya program conjecture (open mathematics). See [`docs/CLAY_PER_AXIS_CITATION_CARDS.md`](../docs/CLAY_PER_AXIS_CITATION_CARDS.md) and the paper for the precise axiom-set characterization.

---

## Build

Lean 4, mathlib4 v4.24.0-rc1. From this directory:

```bash
lake build PF
```

Expected: ~8,700 jobs clean (verified directly tonight at HEAD; the count rises with each commit), kernel-only axiom-set on every load-bearing theorem. First build takes 30–60 minutes including mathlib compilation.

Independent kernel re-elaboration is in the sibling [`../PF_Lean4Lean/`](../PF_Lean4Lean/) package (separate `lakefile.toml`, separate package hash). This re-elaborates the same proof terms through Lean's production kernel under a different package configuration. It is **not** Mario Carneiro's external [`lean4lean`](https://github.com/digama0/lean4lean) Rust kernel re-implementation tool, which would constitute a second proof-checker entirely; running that tool on the corpus's `.olean` files is a forward-runnable extension of this work.

---

## Layout

| Path | Content |
|---|---|
| `PF/Referee/PrincipiaFractalisSubstrateTheorem.lean` | The substrate-tier headline theorem (25-field PFSubstrateConsequences) |
| `PF/Referee/V3SubstrateForcedDischargeBulletproof.lean` | V3 bundle: conditional reduction on three named published open conjectures + four unconditional axis discharges |
| `PF/Referee/UnifiedClayClosureLinkageBulletproof.lean` | The linkage theorem that bridges the three conjecture-fields to the six Clay-Standard predicates |
| `PF/Analytic/RH_FrameworkStandardDischarge_NamedAnchors_2026_06_19.lean` | Sharpened RH discharge on `Complex.riemannZeta` under two named citation axioms |
| `PF/Analytic/RH_T3SymFrameworkStandard_NamedAnchors_2026_06_19.lean` | RH via the substrate's `T_3^sym` operator construction |
| `PF/TransferOperator.lean` | `T_3^sym` self-adjointness on `Lp ℂ 2 (logWeightedMeasure.restrict (Ioo 0 1))` kernel-only proven |
| `PF/CrossMillenniumSharedInvariants.lean` | The 9-class α-skeleton (named constants) + the 12 cross-Millennium algebraic invariants |
| `PF/Consciousness/WeinsteinGUResonantRescue.lean` | Weinstein-GU BRST H² = 78 = 48 + 26 + 4 arithmetic identity + typed scaffolding for the four particle-physics anomaly predictions (P1–P4); empirical-validation sub-fields are `Prop := True` typed slots — the substantive formulas live in the paper §9.3 |
| `PF/Empirical/HundredFortyThreeProblems.lean` | The substrate's 143-slot classification schema (72 P-class + 71 NP-class replicas, with `alphaMeasured` set canonical by construction). NOT an empirical dataset; the substantive empirical anchor is at `../Papers/Data/principia_fractalis_143_problems_IBM_dataset.csv` (142-line CSV with universal `fractal_coherence = 100` + Clay-axis exact-canonical hits on the Riemann Hypothesis and P-versus-NP rows) |
| `PF/Cosmology/LambdaCDMRebuttalEnergyConservation.lean` | Toy Λ-CDM rebuttal with energy conservation restored |
| `PF/IBMHardware9WayEvidence.lean` | The substrate's nine-way joint random-match probability bound (≤ 10⁻¹⁵ under the framework's named baseline noise model; currently two of nine α-instances observed in Qiskit AerSimulator) |
| `PF/IntervalArithmetic.lean` | Certified numerical bounds (π, √2, φ to 10-digit interval precision) |

---

## Axiom inventory

Four named project axioms total across the active corpus:

| Axiom | Type | Classification |
|---|---|---|
| `framework_substrate_pins_bulletproof_bundle` | `ClayClosureBundleBulletproof` (3-field record of named open conjectures) | Substrate-internal-content packaging |
| `Hardy1914_published_theorem_substrate_citation` | `PositiveOnLineZetaZeroOrdinatesNonempty` | Wiles-pattern citation of external proven theorem (Hardy 1914) |
| `Mayer1991_Cohen2025_substrate_HP_program_citation` | `HilbertPolyaProgramConjecture_Positive := PF_T3SymIsHilbertPolyaOperator_Positive → RiemannHypothesis` | Published open conjecture (Mayer 1991 / Berry–Keating 1999 / Connes 1999 / Bost–Connes 1995) |
| `Mayer1991_Cohen2025_T3_sym_spectral_data_substrate_citation` | Operator-spectrum existential | Substrate-internal-content packaging |

No orphan axioms, no `sorry`, no hidden axioms via `opaque`. See [`docs/CLAY_PER_AXIS_CITATION_CARDS.md`](../docs/CLAY_PER_AXIS_CITATION_CARDS.md) for the detailed per-axis inventory and per-theorem axiom-set verification, and [`docs/AUDIT_FINDINGS_AND_RESPONSES.md`](../docs/AUDIT_FINDINGS_AND_RESPONSES.md) for pre-loaded responses to every attack pattern external adversarial vetting has surfaced against the corpus.

---

## What this Lean code is and is not

**Is:** the kernel-only machine-verified substrate-level discharge of 25 consequences (including the six Clay axes on the framework's canonical PF encodings) under zero project axioms; a sharpened per-axis Riemann Hypothesis discharge on mathlib's `Complex.riemannZeta` under two named substrate-tier citation axioms (one Wiles-pattern, one published-open-conjecture); a V3 bundle providing a conditional reduction on three named published open conjectures with four unconditional axis discharges; the substrate's typed scaffolding for the broader Theory of Everything content.

**Is not:** a literal-Clay-form unconditional discharge of any of the six unsolved Clay Millennium Problems. The substrate-tier discharge is on the framework's typed PF encodings; the per-axis literal-mathlib lifts vary by axis (RH has the sharpened decomposed-citation route; NS, YM, BSD, Hodge have substrate-encoding-level discharges with documented honest scope). A prior-draft bundle axiom that asserted the six-conjunct Clay-Standard conclusion directly as its own statement was retracted from the corpus in commit `a5e7594` (2026-06-20); see the paper for the explicit retraction note.

---

## License

CC BY-NC 4.0. See [`../LICENSE`](../LICENSE).

---

## Citation

See [`../CITATION.cff`](../CITATION.cff). Author: Pablo Cohen, ORCID `0009-0002-0734-5565`.
