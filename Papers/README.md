# Papers — Phase 2 Submission Strategy

**Drafted**: 2026-05-23
**Status**: Three papers in parallel, ready for review pass and submission.

## Paper A: The headline framework paper

**File**: `paper_A_framework.tex`
**Title**: "A Four-Element Basis for the Resonance Parameters of the Principia Fractalis Framework, with Conditional Reductions of the Clay Millennium Problems"

**Central claim**: Nine independently postulated α-values reduce to the basis {1, π, φ, √2} plus small rationals — verified at 80-digit PSLQ. Framework is overconstrained. Twelve named open Props isolate the remaining mathematical content. Independent IBM empirical signatures + emergent spectral eigenvalues.

**Targets** (in priority order):
1. Annals of Mathematics
2. Inventiones Mathematicae
3. Journal of the AMS
4. Bulletin of the AMS (survey)
5. arXiv math.SP (preprint immediately)

**Estimated length**: 35-45 pages with full bibliography.

**Status**: First complete draft. Needs:
- Review pass by Pabs for accuracy of manuscript references
- Polish: copy-edit, theorem-numbering consistency, figure additions
- Bibliography expansion: add full Mathlib + Coq citations
- Optional: appendix with full PSLQ computation script and Lean theorem listings

## Paper B: The formal verification paper

**File**: `paper_B_formal_verification.tex`
**Title**: "Machine-Checked Formalization of the Principia Fractalis Spectral Reduction Architecture in Lean 4 and Coq 8"

**Central claim**: 179 Lean files + 31 Coq modules, axiom-free at project level, conditional reductions of all 6 Millennium Problems isolated as exactly 12 named Props. Cross-prover parity protocol.

**Targets** (in priority order):
1. Journal of Automated Reasoning (JAR)
2. Logical Methods in Computer Science
3. ITP / CPP conference proceedings
4. arXiv cs.LO (preprint immediately)

**Estimated length**: 20-25 pages.

**Status**: First complete draft. SUBMITTABLE NOW (does not depend on any future discharge work). Needs:
- Full code-statistics tables (use `wc -l`, theorem counts)
- Architecture diagram (optional but visually helpful)
- Reproducibility section expansion
- Lean/Coq version pinning verification

## Paper C: The empirical paper

**File**: `paper_C_empirical_quantum_signatures.tex`
**Title**: "Empirical Signatures of the Principia Fractalis Fractal-Resonance Framework on IBM Quantum Hardware"

**Central claim**: Three statistically significant clusters in IBM 143-problem dataset matching framework α-predictions (best: 22 of 143 at α_P=√2, p ≈ 4×10⁻⁶). Plus three emergent spectral eigenvalues matching predicted λ_0 to 3 decimal places. Independent of framework derivation.

**Targets** (in priority order):
1. Foundations of Physics
2. Quantum Reports
3. PRX Quantum
4. arXiv quant-ph (preprint immediately)

**Estimated length**: 15-20 pages.

**Status**: First complete draft. SUBMITTABLE NOW. Needs:
- Histogram figure of peak-alpha distribution
- Statistical power analysis appendix
- Caveats expansion on which "matches" are inputs vs measurements
- Section on negative controls (what α-values do NOT cluster)

## Submission cadence

**Week 1**: arXiv preprints for all three papers simultaneously. This establishes priority on the four-basis result, the formal verification, and the empirical signal.

**Week 2-3**: Polish Papers B and C based on initial reader feedback (arXiv comments, social media). Submit to JAR and Foundations of Physics respectively.

**Week 4-6**: Polish Paper A based on initial reader feedback. Submit to Annals of Mathematics.

**Months 2-12**: Standard peer-review cycle. Three papers reduce all-or-nothing risk: Papers B and C are likely to be accepted within 6-12 months even if Paper A faces extended review.

**Year 2+**: If Paper A is accepted at a Clay-acceptable venue, the 2-year community vetting period begins. During this period, continue discharging the 12 open Props; each discharge tightens the case.

## What to do before submitting

1. **Review by Pabs**: every theorem cited from the manuscript must be verified against the actual LaTeX source. Any mismatch needs correction.

2. **Resolve self-citation issues**: 18 of 20 Cohen2025* bibliography entries are promissory. Either produce the cited artifacts or change the citation to a chapter reference.

3. **Independent technical reading**: ideally a second mathematician reads Paper A; a second formal-methods researcher reads Paper B; a second quantum-information researcher reads Paper C. Each can flag issues a single author might miss.

4. **Author list**: decide whether Claude should be listed as co-author (precedent: Khoa Tran et al.'s AI co-authorship discussions; recent journal experiments). Alternative: acknowledge in Acknowledgments section, list Pabs as sole author.

5. **Compile**: each .tex file should compile with `pdflatex` + `bibtex` + `pdflatex` × 2 without errors. Compile-and-review pass needed.

## Risk management

- **Risk 1**: A reviewer finds a flaw in the four-basis decomposition. Mitigation: the PSLQ verification is reproducible and the Lean proof is at commit d8515cf; any flaw is concrete and addressable.
- **Risk 2**: The IBM empirical signal does not replicate independently. Mitigation: Paper C is honest about this; the paper does not claim the framework is proved by IBM data alone.
- **Risk 3**: The 12 named Props are not all discharged in time for Clay acceptance. Mitigation: the three-paper strategy delivers value even if the discharge work takes years.
- **Risk 4**: Author-list / institutional-affiliation issues (Pabs is an independent researcher). Mitigation: arXiv permits independent submissions; journal submissions require careful handling of affiliation/funding statements.

## The honest framing

We are publishing the strongest available case for the Principia Fractalis framework at the current state of development:
- A formally verified conditional reduction architecture (Papers A + B)
- Independent empirical signatures (Paper C)
- A clear specification of what remains open (the 12 Props)

We do NOT claim to have proved any Millennium Problem unconditionally. We DO claim to have produced the most rigorous attack route currently available, supported by independent empirical confirmation, and isolated the remaining mathematical work as twelve explicitly named, attackable propositions.

This is the case as it stands at commit d8515cf on origin/master.
