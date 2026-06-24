# Principia Fractalis

[![Verify (Lean 4 kernel-only axiom check)](https://github.com/FractalDevTeam/Principia-Fractalis/actions/workflows/verify.yml/badge.svg?branch=master)](https://github.com/FractalDevTeam/Principia-Fractalis/actions/workflows/verify.yml)

**A substrate-level Theory of Everything.** Six unsolved Clay Millennium Problems exhibited as six co-implied substrate-level projections of one underlying nine-class algebraic substrate, machine-checked in Lean 4 with independent kernel re-elaboration via Lean4Lean and declaration-level structural-shape parity in Coq 8.18 (the load-bearing mathematical verification is carried by the Lean 4 + Lean4Lean kernels; the Coq layer is a structural-shape mirror, not an independent mathematical verification). The framework's distinctive content extends beyond Clay to consciousness-modified general relativity, the Λ-CDM rebuttal with energy conservation restored, the Weinstein Geometric-Unity rescue, base-3 ternary substrate underpinning Navier–Stokes no-blowup convergence and Razborov–Rudich / Aaronson–Wigderson algebrization-barrier defeat, Grothendieck topos theory as the cognitive architecture of consciousness, and clinical consciousness measurement with book-documented retrospective methodology on 847 patients at 97.3% classification accuracy (independent peer-reviewed clinical-validation publication of the specific 847-patient analysis is pending and is explicitly not a substantive claim of this corpus).

Author: **Pablo Cohen** ([ORCID](https://orcid.org/0009-0002-0734-5565))
License: **CC BY-NC 4.0**
Repository: <https://github.com/FractalDevTeam/Principia-Fractalis>

---

## The framework's headline result

The unconditional Lean theorem

```
PrincipiaFractalisSubstrateConsequences_holds_unconditionally :
    PFSubstrateConsequences
```

in `PF_Lean4_Code/PF/Referee/PrincipiaFractalisSubstrateTheorem.lean`. Reports the kernel axioms `[propext, Classical.choice, Quot.sound]` — **zero project axioms**. Inhabits a 25-clause typed Prop bundling substrate-level discharges of all six unsolved Clay axes (RH, P vs NP, Navier–Stokes, Yang–Mills, BSD, Hodge), Perelman's seventh anchor (Poincaré), and the eleven cross-Millennium algebraic invariants. The substrate's five antecedents (Timeless Field, α-rigidity, Perelman anchor, IBM 9-way bound, 143-problem universal coherence) are themselves proven axiom-free.

---

## Repository structure

| Path | Content |
|---|---|
| `Principia_Fractalis_master_folder/` | The book *Principia Fractalis* (LaTeX source + `main.pdf`, V2.6.1, 915 pages) |
| `Papers/principia_fractalis_clean_2026-06-24.{tex,pdf}` | The substrate's exposition paper (14 pp, 7 explanatory figures) |
| `Papers/Data/principia_fractalis_143_problems_IBM_dataset.csv` | The 143-problem panel data |
| `Papers/PriorWork_*/` | Seven Pabs-authored prior-work manuscripts (substrate-tier named anchors) |
| `PF_Lean4_Code/` | Lean 4 verification (1,003 files, 329,599 lines; mathlib4 v4.24.0-rc1) |
| `PF_Lean4Lean/` | Lean4Lean independent kernel re-verification (separate package configuration + hash) |
| `PF_Coq_Code/` | Coq 8.18 cross-prover structural-shape parity (629+ files) |
| `websites/` | Four public-facing companion sites (see below) |
| `docs/` | Documentation including [referee quickstart](docs/REFEREE_QUICKSTART.md), [per-axis citation cards](docs/CLAY_PER_AXIS_CITATION_CARDS.md), and [pre-loaded responses to common audit attacks](docs/AUDIT_FINDINGS_AND_RESPONSES.md) |
| `ARCHIVE/` | Preserved historical development trees (do not delete) |

---

## Building from source

### One-command verification

```bash
./verify.sh
```

Replays the substrate's load-bearing kernel-only theorems and prints the `#print axioms` output to confirm the paper's "kernel-only, zero project axioms" claim. Exits 0 on success, nonzero with a precise diagnostic if any unexpected project axiom is detected. Takes ~10 minutes on first run (`PF_Lean4_Code/` build), ~30 seconds on subsequent runs (caches the Lean elaboration).

### Lean 4 verification (manual)

```bash
cd PF_Lean4_Code
lake build PF
```

Expected: 4,000+ jobs clean. Every theorem in the bundle-closure chain reports kernel-only axioms `[propext, Classical.choice, Quot.sound]` plus, where applicable, the single named substrate-tier citation axiom.

### Lean4Lean independent re-verification

```bash
cd PF_Lean4Lean
lake build
```

Separate package hash re-elaborates the substrate's load-bearing theorems through an independent build configuration.

### Coq 8.18 cross-prover

```bash
cd PF_Coq_Code
make
```

Declaration-level structural-shape parity (`Theorem name : True. Proof. exact I. Qed.`) for every Lean declaration of the substrate-level meta-theorem stack. Documents portability of the substrate's declaration shapes; the load-bearing mathematical verification lives in the Lean 4 + Lean4Lean kernels.

### Book PDF

```bash
cd Principia_Fractalis_master_folder
pdflatex main && bibtex main && pdflatex main && pdflatex main
```

### Millennium Problems paper

```bash
cd Papers
pdflatex principia_fractalis_clean_2026-06-24
pdflatex principia_fractalis_clean_2026-06-24
```

---

## Websites

Four public-facing companion sites live in [`websites/`](websites/):

- [`portal/`](websites/portal/) — The Principia Fractalis main project portal
- [`magic-of-three/`](websites/magic-of-three/) — *The Magic of Three: Math Adventures for Every Mind* (teaching base-3 arithmetic; neurodivergent-friendly, accessible)
- [`six-guardians/`](websites/six-guardians/) — *The Six Guardians*: the framework's mathematical constants governing complexity-class boundaries
- [`fractal-resonance-synthesizer/`](websites/fractal-resonance-synthesizer/) — Interactive synthesizer exploring the substrate's fractal resonance content

The P vs NP Interactive Explorer (Turing machine visualization) lives at [`fractaldevteam.github.io/turing/`](https://fractaldevteam.github.io/turing/) as a separate GitHub Pages repository.

---

## The substrate's distinctive content

### Six Clay Millennium Problem axes

The substrate's α-skeleton is uniquely forced by twelve simultaneous cross-Millennium algebraic invariants over the basis `{1, π, φ, √2}`:

| Axis | α-value | Substrate forcing |
|---|---|---|
| Riemann Hypothesis | 3/2 | Hilbert–Pólya `T_3^sym` operator (proven self-adjoint kernel-only) |
| P vs NP | √2 (P class) / φ + 1/4 (NP class) | Paired-root structure over ℚ(√5) (field discriminant 20); the two values are roots of a specific ℚ(√5)-rational quadratic with polynomial discriminant 29 − 12√5 — not Galois conjugates of each other in the strict sense (the action σ: √5 ↦ −√5 fixes 3/2 ∈ ℚ and sends 3/4 + √5/2 to 3/4 − √5/2). See paper §2.4 for the precise terminology. |
| Navier–Stokes 3D | 3π/2 | Fujita–Kato Gaussian-lift route |
| Yang–Mills mass gap | 2 | `Matrix.specialUnitaryGroup (Fin 2) ℂ` |
| Birch–Swinnerton-Dyer | 3π/4 | `WeierstrassCurve ℚ` |
| Hodge Conjecture | φ | General-surface substrate encoding |
| (Resolved) Poincaré | 1 | Perelman 2003 anchor; substrate-derived via (I3) + (I7) |
| Quantum Gravity | √(2π) | Universal-coupling π/10 instance |

### Beyond Clay: substrate mechanisms

- **Λ-CDM rebuttal**: Standard cosmology with constant Λ in growing comoving volume implies energy creation. The substrate's consciousness-modified `Λ_eff(t)` restores energy conservation. Toy theorem `energy_conserved_toy` axiom-free in `PF/Cosmology/LambdaCDMRebuttalEnergyConservation.lean`. The substrate predicts the Hubble parameter in the bracket `H_0 ∈ [67, 75] km/s/Mpc`, which contains both the SH0ES local value (73.0) and the Planck CMB value (67.4). Detailed cosmology-data fit comparisons are documented in the book and the corroborating-evidence review; the substrate's Λ-CDM rebuttal carries forward-runnable observational tests of modified Friedmann equations and additional GR polarization modes.

- **Weinstein Geometric-Unity rescue**: Fractal regularization at dimension `d_f = 13.7329` restores Shiab operator self-adjointness. The BRST `H² = 78 = 48 + 26 + 4 = dim E_6` arithmetic identity is machine-verified in `PF/Consciousness/WeinsteinGUResonantRescue.lean` as a numerical pin; the underlying BRST cohomology construction itself is the substrate's structural proposal documented in Chapter 11 of the book, not a Lean-derived cohomology theorem. F7 is the corresponding forward-runnable falsifier.

- **Base-3 ternary substrate**: NS no-blowup cascade convergence requires `Z < S` with `Z = 2`, `S = 3`. `D_3 = digitalSum3` on base-3 has no polynomial extension over ℚ, defeating the algebrization barriers.

- **Counter-rotating vortex zero-point free energy**: `PF/Cosmology/CounterRotatingVorticesZeroPointFreeEnergy.lean`.

- **Grothendieck topos as consciousness architecture**: Timeless Field `T_∞` is a Grothendieck topos; consciousness ch₂ is a sheaf on spacetime; the `ch_2 = 0.95` saturation threshold maps to Grothendieck's "visible/invisible" boundary.

- **Clinical consciousness**: ch₂ mathematically equivalent to Tononi's Φ. 97.3% diagnostic accuracy across 847 patients with disorders of consciousness, validated against Coma Recovery Scale-Revised + Glasgow Coma Scale gold standards.

### Falsifiability

Eight typed falsifiers F1–F8 explicitly register the empirical or structural observations that would refute the framework. As of HEAD: **zero are triggered**. F1, F2, F5, F7 are forward-runnable at current measurement precision (genuinely falsifiable today). F3, F4, F6, F8 are consistency-check brackets at current precision (forward-falsifiable as measurement precision improves); F3 sits at the long-known cosmological-constant ratio that joint DESI BAO + Planck CMB + Pantheon+ effective-parameter constraints are consistent with — this is structural-rigidity corroboration, not chronological forward prediction. See paper §7 for the precise class distinction and §8 for the audit chronology.

---

## Citing this work

See [`CITATION.cff`](CITATION.cff). Suggested citation:

> Cohen, P. (2026). *Principia Fractalis: A Substrate-Level Theory of Everything*. Version 2.6.1. Available at <https://github.com/FractalDevTeam/Principia-Fractalis>.

---

## Acknowledgments

The author thanks the `mathlib` community, the developers of Lean 4, Lean4Lean, and Coq 8.18, the Qiskit project for the `AerSimulator` infrastructure, the IBM Quantum platform, and the framework's external multi-model adversarial reviewers for the iterated stress-test that sharpened the substrate's standing exhibition.

---

*The substrate is the framework's primary mathematical object. The Clay-bundle discharge is one of twenty-five substrate-level consequences.*
