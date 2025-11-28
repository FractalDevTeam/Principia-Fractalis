# Principia Fractalis

Formalization and verification of the Principia Fractalis framework in Lean 4.

This repository is the public companion to the book **"Principia Fractalis"** by Pablo Cohen.  It contains:

- The **canonical Lean formalization** of the framework (PF_canonical).
- The **Lean-for-Lean layer** (PF_L4L) that exposes minimal contracts for each pillar and tracks which axioms are used.
- Supporting data, numerical certificates, and documentation referenced in the book.

The book already points to this GitHub repository as the place where all formal code and verification artifacts live.

---

## Repository layout

- `PF_canonical/`
  - `1_BOOK_LATEX_SOURCE/` – LaTeX source for the full book (chapters, appendices, figures, scripts).
  - `2_LEAN_SOURCE_CODE/` – canonical Lean 4 formalization of the Principia Fractalis framework.
    - Top-level Lean files (e.g. `UniversalFramework.lean`, `IntervalArithmetic.lean`, `YM_Equivalence.lean`, `RH_Equivalence.lean`, `BSD_Equivalence.lean`, `NavierStokesConsciousness.lean`, `ChernWeil.lean`).
    - `PF/` – internal library of PF modules (P vs NP, RH, YM, BSD, resonance, Turing encoding, consciousness core, toy models, etc.).
- `PF_L4L/`
  - `PF_L4L/` – Lean-for-Lean layer:
    - For each pillar (P vs NP, RH, YM, BSD, etc.) there is a small "contract" module (e.g. `Ch21/PNP.lean`, `Ch20/RH.lean`, `Ch23/YM.lean`, `Ch24/BSD.lean`).
    - `Core/AxiomAudit.lean` – collects and classifies which canonical axioms each pillar uses. PF_L4L **introduces no new axioms**; it only tags and re-exports canonical ones.
- `Evidence_and_Data_for_GitHub/` – numerical data, plots, and certificates supporting the interval and spectral bounds used in the Lean code.
- `Principia_Fractalis_FINAL_SUBMISSION_2025-11-18/` – final book submission material and related artifacts.

The root folder also contains many PDF versions of the book and related technical reports.  The authoritative current text is whatever version is referenced in the book itself.

---

## Building the Lean projects

### Requirements

- Lean 4 (>= 4.24) installed via `elan`.
- `lake` build tool (comes with Lean 4).

### Build PF_L4L (Lean-for-Lean layer)

From this repository root:

```bash
cd PF_L4L
lake update
lake build
```

This command type-checks both PF_L4L and all canonical Lean code it depends on.  A successful build means all Lean files are syntactically and semantically consistent with the current axiom set.

### Build PF_canonical directly (optional)

The canonical Lean project is organized under `PF_canonical/2_LEAN_SOURCE_CODE`.  In most workflows you do **not** need to build it separately, because PF_L4L already depends on it.  If you wish to, you can initialize a separate Lake project there and build its sources, but the supported entry point for verification is PF_L4L.

---

## Axiom audit

Principia Fractalis is explicit about all non-logical assumptions used in the Lean formalization.

- All axioms in the Lean code are declared with the keyword `axiom` in `PF_canonical/2_LEAN_SOURCE_CODE`.
- PF_L4L never introduces new axioms; it only references and tags canonical ones.
- A structured **axiom audit** (grouping axioms by theme: universal framework, P vs NP, RH, YM, BSD, Navier–Stokes, Hodge, topology, numeric certificates, etc.) is maintained in a separate document and in `PF_L4L/Core/AxiomAudit.lean`.

For each major theorem (e.g. P≠NP via spectral gap, RH spectral bijection, YM mass gap equivalence, BSD equivalence), PF_L4L identifies which subsets of canonical axioms are being used.  This makes it possible for external projects to attempt to **replace axioms by theorems** over time (e.g. Minlos theorem, rigorous YM measure construction, fully formal spectral bijections, verified interval arithmetic).

---

## Relationship to the book

- The LaTeX chapters in `PF_canonical/1_BOOK_LATEX_SOURCE/chapters` are the primary human-readable exposition of the framework.
- The Lean files in `PF_canonical/2_LEAN_SOURCE_CODE/` are a kernel-checked reflection of the mathematical content of the book.
- PF_L4L exposes a minimal, pillar-wise interface suitable for formal verification, automation, and meta-analysis.

Each major chapter (numbers, resonance, Timeless Field, consciousness, field equations, operator theory, spectral measures, P vs NP, RH, Navier–Stokes, Yang–Mills, BSD, Hodge, cosmology, clinical consciousness, etc.) has corresponding Lean modules where its core mathematics lives.  Where some chapter material is not yet fully formalized, this is explicitly documented in the ongoing axiom and coverage audit.

---

## For referees and formal verification

If you are evaluating Principia Fractalis as a referee or as part of a formal-math project, a typical workflow is:

1. **Check that the code builds**
   - Run `lake build` in `PF_L4L` as described above.
2. **Inspect the axiom audit**
   - Consult the separate axiom-audit document (and `PF_L4L/Core/AxiomAudit.lean`) to see the full list of non-logical axioms, grouped by theme.
3. **Match chapters to Lean modules**
   - Use the chapter-to-Lean mapping (maintained in documentation) to locate the Lean definitions and theorems corresponding to each chapter.
4. **Trace dependencies for key results**
   - For each central theorem (e.g. spectral gap ↔ P≠NP, spectral bijection ↔ RH, mass gap ↔ YM equivalence, BSD equivalence), use PF_L4L to see exactly which axioms and intermediate lemmas it depends on.

This setup is designed so that future work (in Lean or other provers) can gradually **replace axioms by theorems** while keeping the overall framework and interfaces stable.

---

## Contributing / extending the formalization

Contributions are welcome in several directions:

- **Formal proofs of currently axiomatized results**, such as:
  - Bochner–Minlos theorem for nuclear spaces.
  - Existence of Yang–Mills-type measures.
  - Deep spectral bijection results in the RH and BSD pillars.
  - Verified interval arithmetic and real-analytic bounds to replace numeric certificate axioms.
- **Extensions of the existing toy models** (Navier–Stokes, Hodge, Poincaré, etc.) to stronger theorems.
- **Improvements to PF_L4L** to make axiom usage and theorem dependencies even more transparent.

Any pull requests should preserve the existing **axiom surface** (no new axioms) unless explicitly justified and documented in the axiom audit.

---

## License and authorship

- Mathematical content and conceptual framework: Pablo Cohen.
- Lean 4 code: AI-assisted translation and structuring of the book’s mathematics into a machine-checkable form.

Please refer to the book and accompanying PDFs in this repository for the full narrative, physical interpretations, and empirical evidence supporting the framework.
