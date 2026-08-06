# Principia Fractalis

[![Verify (Lean 4 kernel-only axiom check)](https://github.com/FractalDevTeam/Principia-Fractalis/actions/workflows/verify.yml/badge.svg?branch=master)](https://github.com/FractalDevTeam/Principia-Fractalis/actions/workflows/verify.yml)

Author: **Pablo Cohen** ([ORCID](https://orcid.org/0009-0002-0734-5565))
License: **CC BY-NC 4.0**
Repository: <https://github.com/FractalDevTeam/Principia-Fractalis>

---

## Headline result (kernel-verified, unconditional)

A machine-checked construction of the uniformly hyperfinite (UHF) C\*-algebra $M_{3^\infty}$ —
realized as the metric completion $T_\infty$ of the inductive limit of the matrix tower
$M_{3^k}(\mathbb{C})$ under the unital \*-embeddings $A \mapsto A \otimes I_3$ — together with
a canonical tracial state $\tau_{\mathsf{UHF}}$ on $T_\infty$ that is verified in the Lean 4 kernel
to be additive, unital, 1-Lipschitz, tracial, Hermitian, positive, and **faithful**:

$$\tau_{\mathsf{UHF}}(x^{*}x)=0 \implies x=0 \quad \text{for every } x \in T_\infty.$$

As a corollary, $T_\infty$ is **algebraically simple** — every two-sided ideal is $\bot$ or $\top$.
To our knowledge this is the first formalization of Glimm's 1960 simplicity theorem for a UHF
algebra in any proof assistant, and the first machine-checked construction of a UHF algebra with
a faithful tracial state in any proof assistant.

**Summit theorem.**

```
r112_substrate_completion_faithful_capstone
```

in [`PF_Lean4_Code/PF/SubstrateCompletionFaithful.lean`](PF_Lean4_Code/PF/SubstrateCompletionFaithful.lean).
Reports kernel axioms `[propext, Classical.choice, Quot.sound]` — **zero project axioms, zero sorries**.
Discharges the previously named `SubstrateUHFCompletionPositiveFaithfulnessSubstrateConjecture`.

**One-command reproduction.**

```bash
./verify.sh
```

Replays the load-bearing kernel-only theorems and prints the `#print axioms` output for the
summit chain (`r107a` → `r108` → `r109` → `r110` → `r111` → `r112`). Exits 0 on success, nonzero
with a precise diagnostic if any unexpected project axiom is detected. ~10 min on first run
(`PF_Lean4_Code/` build), ~30 s on subsequent runs.

**Verified build data at HEAD `ff4c50f2` (2026-07-23):**

| | |
|---|---|
| `lake build PF` | 4,471 jobs clean |
| `lake build` (full) | 8,928 jobs clean |
| Sorries | 0 |
| Project axioms | 0 |
| mathlib pin | `eed770a4` |
| toolchain | `leanprover/lean4:v4.24.0-rc1` |

**Update (2026-08-04):** HEAD has advanced (see `git log`); `lake build PF` = 4,701 jobs
clean at r194. The arc list since this block was written: Mordell–Weil ranks r129–r182
(paper: [`Papers/formal_mordell_weil_rank_2026-07-30.pdf`](Papers/formal_mordell_weil_rank_2026-07-30.pdf)),
transfer-operator/Lefschetz arc r183–r194, Friedmann r187. Figures elsewhere in this
README dated 2026-07-23 are historical.

**Update (2026-08-05):** `lake build PF` = 4,724 jobs clean at HEAD `13369b35`. Arcs added
since: the universal rank pipeline (rank lower bounds for any elliptic curve over ℚ from
its coefficients, r193–r203) and Hausdorff dimension (Moran/Falconer bounds; the Cantor
function; `dimH cantorSet = log₃2`; certified enclosures for the continued-fraction Cantor
sets, r205–r209).

Paper: [`Papers/uhf_faithful_trace_glimm_2026-07-23.pdf`](Papers/uhf_faithful_trace_glimm_2026-07-23.pdf) (14 pp).

---

## Framework context: what this theorem lives inside

The UHF construction above is the completion tier of the **Timeless Field** substrate — the
central algebraic object of *Principia Fractalis*. The wider corpus proposes this substrate as
the shared source from which the six Clay Millennium axes (RH, P vs NP, Navier–Stokes,
Yang–Mills, BSD, Hodge) plus Perelman's Poincaré anchor and a Quantum-Gravity instance emerge
as **substrate-level projections** of a single nine-class $\alpha$-skeleton over the basis
$\{1,\pi,\varphi,\sqrt{2}\}$.

We state the current standing precisely and without inflation:

- The **Clay-axis discharges** in the corpus are Lean 4 **substrate-level reductions**: each
  axis's headline classical statement is reduced, kernel-only, to a small named set of
  substrate-tier conjectures (spectral bijection, Hardy 1914 non-degeneracy, an HP-program
  surjectivity conjecture, and so on) that are explicitly enumerated in the paper. The
  substrate-tier conjectures are the remaining deductive load. They are **not** claimed to be
  proven in this repository.
- The **α-skeleton uniqueness** — that the tuple $(3/2,\,\sqrt{2},\,\varphi+1/4,\,3\pi/2,\,2,\,3\pi/4,\,\varphi,\,1,\,\sqrt{2\pi})$
  is uniquely forced by twelve simultaneous cross-Millennium algebraic invariants — is a
  substrate-level typed claim in Lean 4 with the invariants themselves axiom-free, conditional
  on the same substrate-tier conjectures above.
- The **Extremal-Trace Conjecture 8.X.2** is the single remaining deductive gap between the
  substrate bundle and its classical-side realizations, and is stated as such in the paper.
- The **beyond-Clay content** — consciousness-modified Λ-CDM with energy conservation, the
  Weinstein Geometric-Unity BRST arithmetic pin ($H^2 = 78 = 48+26+4 = \dim E_6$), the base-3
  ternary substrate underpinning Navier–Stokes cascade convergence and the
  Razborov–Rudich / Aaronson–Wigderson barrier defeat, and Grothendieck-topos consciousness
  architecture — is presented as the substrate's structural proposals with named forward
  falsifiers, not as derived theorems of this repository.
- The **clinical consciousness** figure (97.3% classification accuracy on 847 patients with
  disorders of consciousness against CRS-R + GCS) is a book-documented retrospective analysis;
  independent peer-reviewed clinical validation of the specific 847-patient analysis is
  pending and is not treated as a substantive claim of this corpus.

The **verified, unarguable** content of the repository at HEAD is the UHF faithfulness + Glimm
simplicity summit above. Everything else in the corpus is either (a) axiom-free at its
declared tier or (b) explicitly conditional on the named substrate-tier conjectures listed in
the papers.

---

## Repository structure

| Path | Content |
|---|---|
| `Principia_Fractalis_master_folder/` | The book *Principia Fractalis* (LaTeX source + `main.pdf`, V2.6.1, ~918 pp) |
| `Papers/uhf_faithful_trace_glimm_2026-07-23.{tex,pdf}` | **Today's headline paper.** Full ITP-style presentation of the UHF $M_{3^\infty}$ faithful-trace + Glimm-simplicity result (14 pp; kernel-verified at HEAD `d5ad2881`) |
| `Papers/principia_fractalis_alpha_skeleton_2026-07-13.{tex,pdf}` | Canonical framework paper (Wiles-pattern skeleton, 17 pp): the α-skeleton, the twelve invariants, and the substrate-level reductions of the Clay axes to the enumerated substrate-tier conjectures |
| `Papers/principia_fractalis_millennium_problems_2026-07-13.{tex,pdf}` | Extended companion (73 pp): the full substrate-level Theory-of-Everything paper — Clay-bundle substrate reductions, ΛCDM rebuttal, Weinstein-GU $H^2=78$, base-3 ternary, Grothendieck-topos consciousness, $T_3^{\mathsf{sym}}$ N=25000 spectral resonance data, Filtration Theorem 8.X.1, Extremal-Trace Conjecture 8.X.2 |
| `Papers/RETIRED/2026-07-23-itp-notes-superseded/` | Retired short ITP notes (07-11, 07-20), superseded by the full paper above |
| `Papers/principia_fractalis_clean_2026-06-29.{tex,pdf}` | Back-pocket algebraic-skeleton-only exposition (20 pp, companion) |
| `Papers/Data/principia_fractalis_143_problems_IBM_dataset.csv` | The 143-problem panel data |
| `Papers/PriorWork_*/` | Seven Pabs-authored prior-work manuscripts (substrate-tier named anchors) |
| `PF_Lean4_Code/` | Lean 4 verification (mathlib4 pin `eed770a4`; `lake build PF` = 4,471 jobs, full = 8,928 jobs, kernel-clean) |
| `PF_Lean4Lean/` | Lean4Lean independent kernel re-verification (separate package configuration + hash) |
| `PF_Coq_Code/` | Coq 8.18 cross-prover structural-shape parity. The load-bearing mathematical verification lives in the Lean 4 + Lean4Lean kernels; the Coq layer is a declaration-level structural-shape mirror, not an independent mathematical verification |
| `websites/` | Four public-facing companion sites (see below) |
| `docs/` | [Referee quickstart](docs/REFEREE_QUICKSTART.md), [per-axis citation cards](docs/CLAY_PER_AXIS_CITATION_CARDS.md), and [pre-loaded responses to common audit attacks](docs/AUDIT_FINDINGS_AND_RESPONSES.md) |
| `ARCHIVE/` | Preserved historical development trees (do not delete) |

---

## Building from source

### One-command verification

```bash
./verify.sh
```

Replays the substrate's load-bearing kernel-only theorems (including the r107a–r112 summit
chain) and prints the `#print axioms` output. Exits 0 on success, nonzero with a diagnostic if
any unexpected project axiom is detected.

### Lean 4 verification (manual)

```bash
cd PF_Lean4_Code
lake build PF
```

Expected: 4,471 jobs clean at HEAD. Every theorem in the summit chain reports kernel-only
axioms `[propext, Classical.choice, Quot.sound]`.

### Lean4Lean independent re-verification

```bash
cd PF_Lean4Lean
lake build
```

Separate package hash re-elaborates the substrate's load-bearing theorems through an
independent build configuration.

### Coq 8.18 cross-prover

```bash
cd PF_Coq_Code
make
```

Declaration-level structural-shape parity (`Theorem name : True. Proof. exact I. Qed.`) for
every Lean declaration of the substrate-level meta-theorem stack. Documents portability of the
declaration shapes; the load-bearing mathematical verification remains in the Lean 4 +
Lean4Lean kernels.

### Book PDF

```bash
cd Principia_Fractalis_master_folder
pdflatex main && bibtex main && pdflatex main && pdflatex main
```

### Papers

```bash
cd Papers
pdflatex uhf_faithful_trace_glimm_2026-07-23
pdflatex uhf_faithful_trace_glimm_2026-07-23

pdflatex principia_fractalis_alpha_skeleton_2026-07-13
pdflatex principia_fractalis_alpha_skeleton_2026-07-13

pdflatex principia_fractalis_millennium_problems_2026-07-13
pdflatex principia_fractalis_millennium_problems_2026-07-13
```

---

## Websites

Four public-facing companion sites live in [`websites/`](websites/):

- [`portal/`](websites/portal/) — The Principia Fractalis main project portal
- [`magic-of-three/`](websites/magic-of-three/) — *The Magic of Three: Math Adventures for Every Mind* (teaching base-3 arithmetic; neurodivergent-friendly, accessible)
- [`six-guardians/`](websites/six-guardians/) — *The Six Guardians*: the framework's mathematical constants governing complexity-class boundaries
- [`fractal-resonance-synthesizer/`](websites/fractal-resonance-synthesizer/) — Interactive synthesizer exploring the substrate's fractal resonance content

The P vs NP Interactive Explorer (Turing machine visualization) lives at
[`fractaldevteam.github.io/turing/`](https://fractaldevteam.github.io/turing/) as a separate
GitHub Pages repository.

---

## The substrate's α-skeleton (reference table)

The nine α-values, uniquely forced (in the substrate framework) by twelve simultaneous
cross-Millennium algebraic invariants over the basis $\{1,\pi,\varphi,\sqrt{2}\}$. Substrate-level
reductions in Lean 4 are kernel-only; classical-side realizations are conditional on the
substrate-tier conjectures enumerated in the paper.

> **Correction (2026-08-04).** Two honesty notes on this table.
> (1) The α_NP = φ + 1/4 pin is an **empirical calibration, not a
> derivation**: the kernel-verified theorem `alphaNP_unconstrained`
> proves the framework's invariants do not force α_NP, and the
> "empirical validation" theorem (`alpha_rigidity_empirically_validated`)
> is a definitional `rfl` tautology, not a check that could fail. The
> corresponding referee instruction in `docs/REFEREE_QUICKSTART.md` §6
> is retired as of this date.
> (2) The spectral-peak data referred to as "IBM" in theorem names comes
> from Qiskit `AerSimulator` runs, not IBM hardware.
> See `OPEN_PROBLEMS.md` and `docs/ALPHA_DICTIONARY.md` (canonical
> α-dictionary, 2026-08-04).

| Axis | α-value | Substrate encoding |
|---|---|---|
| Riemann Hypothesis | $3/2$ | Hilbert–Pólya $T_3^{\mathsf{sym}}$ operator (self-adjoint kernel proven axiom-free) |
| P vs NP | $\sqrt{2}$ (P) / $\varphi + 1/4$ (NP) | Paired-root structure over $\mathbb{Q}(\sqrt{5})$; the pair is not Galois-conjugate in the strict sense (the action $\sigma: \sqrt{5}\mapsto -\sqrt{5}$ fixes $3/2\in\mathbb{Q}$). See paper §2.4 for precise terminology |
| Navier–Stokes 3D | $3\pi/2$ | Fujita–Kato Gaussian-lift route |
| Yang–Mills mass gap | $2$ | `Matrix.specialUnitaryGroup (Fin 2) ℂ` |
| Birch–Swinnerton-Dyer | $3\pi/4$ | `WeierstrassCurve ℚ` |
| Hodge Conjecture | $\varphi$ | General-surface substrate encoding |
| (Resolved) Poincaré | $1$ | Perelman 2003 anchor; substrate-derived via (I3) + (I7) |
| Quantum Gravity | $\sqrt{2\pi}$ | Universal-coupling $\pi/10$ instance |

---

## Falsifiability

Eight typed falsifiers **F1–F8** register the empirical or structural observations that would
refute the framework. As of HEAD: **zero are triggered**. F1, F2, F5, F7 are forward-runnable
at current measurement precision (genuinely falsifiable today). F3, F4, F6, F8 are
consistency-check brackets at current precision. See paper §7 for the class distinction and §8
for the audit chronology.

**Correction (2026-08-04):** all eight falsifiers in
`FrameworkFalsifiabilityConditions.lean` are structurally vacuous. Each has the shape
`∃ m : ℝ, |m − predicted| > ε` with `m` unconstrained — inhabited by arbitrary reals, so
each is true independent of any experiment. See
[`codex/FALSIFIABILITY_REGISTRY_DEFECT_2026-07-28.md`](codex/FALSIFIABILITY_REGISTRY_DEFECT_2026-07-28.md).
A rebuilt registry on a Measurement/Refutes pattern is in progress. Do not cite F1–F8 as
kernel-verified falsifiability.

---

## Citing this work

See [`CITATION.cff`](CITATION.cff). Suggested citations:

For the UHF faithful-trace + Glimm-simplicity result:

> Cohen, P. (2026). *A Machine-Checked Construction of the UHF Algebra $M_{3^\infty}$ with a Faithful Tracial State: Formalizing Glimm Simplicity in Lean 4.* Available at <https://github.com/FractalDevTeam/Principia-Fractalis>.

For the wider framework:

> Cohen, P. (2026). *Principia Fractalis: A Substrate-Level Theory of Everything.* Version 2.6.1. Available at <https://github.com/FractalDevTeam/Principia-Fractalis>.

---

## Acknowledgments

The author thanks the `mathlib` community, the developers of Lean 4, Lean4Lean, and Coq 8.18,
the Qiskit project for the `AerSimulator` infrastructure, the IBM Quantum platform, and the
framework's external multi-model adversarial reviewers for the iterated stress-test that
sharpened the substrate's standing exhibition.
