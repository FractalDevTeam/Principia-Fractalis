# NAVIGATION MAP - Principia Fractalis

**PURPOSE**: Know exactly where everything is
**FOR**: Quick reference without searching
**FORMAT**: Clear lists, no dense paragraphs

---

## TOP-LEVEL STRUCTURE

```
Principia_Fractalis/
├── book/                           ← The 1,084-page textbook
├── lean_formalization/             ← Formal proofs (Lean 4)
├── verification_reports/           ← Status & verification docs
├── numerical_evidence/             ← Data & reproducible scripts
├── documentation/                  ← This file + guides
├── COMPLETE_MANIFEST.md            ← Full inventory
├── QUICK_START_GUIDE.md            ← Start here!
├── README.md                       ← GitHub homepage
└── LICENSE                         ← Legal stuff
```

---

## BOOK FOLDER (`book/`)

### Main Files
```
book/
├── main.pdf                        ← COMPILED BOOK (1,084 pages, 9.4 MB)
├── main.tex                        ← Main LaTeX file
├── bibliography.bib                ← All references
└── compile.sh                      ← Build script
```

### Chapters (`book/chapters/`)
41 chapter files:

**Foundation (Chapters 1-9)**
- ch01_introduction.tex
- ch02_complex.tex
- ch03_resonance.tex (CRITICAL: fractal resonance R_f)
- ch04_timeless_field.tex (CRITICAL: T_∞ automorphisms)
- ch05_base3.tex
- ch06_consciousness.tex (CRITICAL: ch_2 = 0.95 threshold)
- ch07_constants.tex (π/10 universal coupling)
- ch08_unity.tex
- ch09_spectral_unity.tex (CRITICAL: framework unification)

**Millennium Problems (Chapters 20-29)**
- ch20_riemann_hypothesis.tex (150-digit bijection)
- ch21_computational_complexity.tex (P vs NP)
- ch22_yang_mills.tex
- ch23_navier_stokes.tex
- ch24_bsd.tex
- ch25_hodge.tex
- ch26_poincare.tex (SOLVED by Perelman)
- (More problem-specific chapters)

**Applications (Chapters 30-41)**
- ch30_neural.tex (consciousness measurement)
- ch31_cosmology.tex (CMB predictions)
- ch32_particle.tex (Standard Model)
- (Additional applications)
- ch41_conclusion.tex

### Appendices (`book/appendices/`)
23 appendix files:

**Critical Appendices**
- appA_zeros.tex - Riemann zero computations
- appH_numerical_validation.tex - Numerical evidence
- appI_lean_formalization.tex - Formal verification status (UPDATED Nov 10)
- appJ_bijection_analysis.tex - RH bijection roadmap

**Specialized Topics**
- appB_brst.tex - BRST quantization
- appC_clinical.tex - Clinical validation
- appD_software.tex - Implementation
- appE_weinstein.tex
- appF_solutions.tex
- appG_notation.tex
- appK_continuum_limit_COMPLETE.tex - Yang-Mills continuum
- appK_measure_theory.tex
- appL_os_reconstruction.tex
- appM_spectral_heights.tex
- appM_yang_mills_research_roadmap.tex
- appN_sha_finiteness.tex - BSD Sha finiteness
- appO_motivic_spectral.tex
- appP_explicit_cycles.tex
- appQ_bsd_rank2_COMPLETE.tex - BSD rank ≥2

**Multiple Bijection Appendices**
- appJ_bijection_COMPLETE_PROOF.tex
- appJ_partial_bijection_results.tex
- appJ_research_roadmap.tex
- appJ_riemann_convergence.tex

### Frontmatter (`book/frontmatter/`)
```
frontmatter/
├── preface.tex                     ← UPDATED Nov 10 (honest scope)
├── abstract.tex
├── acknowledgments.tex
└── dedication.tex
```

### Figures (`book/figures/`)
All images, diagrams, plots used in book.

---

## LEAN FORMALIZATION (`lean_formalization/`)

### Configuration Files
```
lean_formalization/
├── lakefile.lean                   ← Build configuration
├── lean-toolchain                  ← Lean version spec
└── BUILD_INSTRUCTIONS.md           ← How to compile
```

### Proof Files (`lean_formalization/PF/`)

**Core Theorems (Stage 0 - Nov 8, 2025)**
```
PF/
├── Basic.lean                      ← 4 theorems (foundations)
├── IntervalArithmetic.lean         ← 9 theorems (certified computation)
├── RadixEconomy.lean               ← 8 theorems (base-3 optimality)
├── SpectralGap.lean                ← 7 theorems (P vs NP gap)
├── SpectralEmbedding.lean          ← 3 theorems (gauge emergence)
└── ChernWeil.lean                  ← 2 theorems (consciousness threshold)
```
**Status**: 33 theorems, 0 sorries, 100% VERIFIED

**Bridge Formalization (Stages A, B - Nov 10, 2025)**
```
PF/
├── TuringEncoding.lean             ← Stage A: Turing machines (0 sorries)
│   └── TuringEncoding/             ← Subdirectory with modules
│       ├── Basic.lean
│       ├── Operators.lean
│       └── Complexity.lean
│
├── P_NP_Equivalence.lean           ← Stage B: Spectral to Turing (0 sorries)
└── P_NP_EquivalenceLemmas.lean     ← Supporting lemmas (0 sorries)
```
**Status**: ALL SORRIES ELIMINATED (Stages A, B)

**Millennium Problem Bridges (Stage C - Nov 10, 2025)**
```
PF/
├── RH_Equivalence.lean             ← Riemann Hypothesis bridge (partial)
├── BSD_Equivalence.lean            ← BSD Conjecture bridge (partial)
├── YM_Equivalence.lean             ← Yang-Mills bridge (partial)
└── UniversalFramework.lean         ← Unifying structure (partial)
```
**Status**: PARTIAL (work in progress, sorries present)

### Documentation
```
lean_formalization/
├── README.md                       ← Contribution guidelines
├── VERIFICATION_CERTIFICATE_2025-11-08.md
├── VERIFICATION_REPORT.md
├── STAGE_C_FORMALIZATION_REPORT.md
└── STAGE_C_QUICK_REFERENCE.md
```

---

## VERIFICATION REPORTS (`verification_reports/`)

### CRITICAL REPORTS (READ THESE FIRST)
```
verification_reports/
├── VERIFICATION_COMPLETE_2025-11-10.md          ← Overall status
├── FRAMEWORK_AWARE_BIJECTION_VERIFICATION.md    ← RH bijection analysis
├── STAGES_ABC_COMPLETE_VERIFICATION_2025-11-10.md ← Lean progress
└── TURING_PNP_COMPLETION_2025-11-10.md          ← P vs NP Turing
```

### STATUS REPORTS
```
├── FINAL_STATUS_AFTER_FIXES_2025-11-10.md
├── ALL_CONTRADICTIONS_RESOLVED_FINAL_2025-11-10.md
├── VERSION_3.4_COMPLETE_STATUS.md
└── MILLENNIUM_PROBLEMS_VERIFICATION.md
```

### SPECIALIZED REPORTS (90+ files)
Categories:
- Bijection analysis (10+ files)
- BSD research (5+ files)
- Yang-Mills progress (5+ files)
- Numerical validation (10+ files)
- Guardian assessments (15+ files)
- Historical status (20+ files)
- Lean formalization (15+ files)

**TIP**: Use `grep` to find specific topics:
```bash
cd verification_reports/
grep -l "Riemann" *.md          # Find RH-related reports
grep -l "P vs NP" *.md          # Find P vs NP reports
grep -l "sorry" *.md            # Find Lean sorry discussions
```

---

## NUMERICAL EVIDENCE (`numerical_evidence/`)

### Python Scripts
```
numerical_evidence/python_scripts/
├── riemann_zeros.py                ← Compute Riemann zeros
├── eigenvalues.py                  ← Compute spectral eigenvalues
├── bijection_verification.py      ← Verify 150-digit correspondence
├── statistical_analysis.py        ← Compute p-values
└── consciousness_eeg.py            ← EEG signal processing
```

### Data Files
```
numerical_evidence/data/
├── riemann_zeros_10000.txt         ← First 10,000 zeros (150 digits)
├── eigenvalues_N1000.txt           ← Eigenvalues (N=1000)
├── bijection_map.txt               ← λ_k ↔ ρ_k mapping
└── clinical_eeg_data/              ← Patient EEG recordings
```

### Results
```
numerical_evidence/results/
├── precision_analysis.txt          ← 150-digit precision verification
├── statistical_significance.txt   ← P < 10^(-1,520,000)
└── clinical_accuracy.txt           ← 97.3% consciousness measurement
```

---

## DOCUMENTATION (`documentation/`)

```
documentation/
├── QUICK_START_GUIDE.md            ← THIS IS WHERE YOU START
├── NAVIGATION_MAP.md               ← This file
├── PUBLICATION_STATUS.md           ← arXiv/peer review status
├── GITHUB_UPLOAD_CHECKLIST.md      ← Step-by-step upload guide
└── COMPLETE_INTEGRITY_2025-11-10.txt  ← All checksums
```

---

## KEY FILES BY TOPIC

### Want to understand the Riemann Hypothesis approach?
1. `book/chapters/ch20_riemann_hypothesis.tex`
2. `book/appendices/appJ_bijection_analysis.tex`
3. `verification_reports/FRAMEWORK_AWARE_BIJECTION_VERIFICATION.md`
4. `numerical_evidence/results/precision_analysis.txt`

### Want to verify P vs NP claims?
1. `book/chapters/ch21_computational_complexity.tex`
2. `lean_formalization/PF/SpectralGap.lean`
3. `lean_formalization/PF/P_NP_Equivalence.lean`
4. `verification_reports/TURING_PNP_COMPLETION_2025-11-10.md`

### Want to check Lean proofs?
1. `lean_formalization/BUILD_INSTRUCTIONS.md`
2. `lean_formalization/PF/` (all .lean files)
3. `lean_formalization/VERIFICATION_CERTIFICATE_2025-11-08.md`

### Want to understand the framework?
1. `book/chapters/ch03_resonance.tex` (fractal resonance R_f)
2. `book/chapters/ch04_timeless_field.tex` (T_∞ automorphisms)
3. `book/chapters/ch06_consciousness.tex` (ch_2 = 0.95)
4. `book/chapters/ch09_spectral_unity.tex` (unification)

### Want numerical evidence?
1. `book/appendices/appH_numerical_validation.tex`
2. `numerical_evidence/` (all scripts and data)
3. `verification_reports/FRAMEWORK_AWARE_BIJECTION_VERIFICATION.md` (150-digit analysis)

---

## SEARCH TIPS

### Find specific files
```bash
# Find all files mentioning "bijection"
find . -type f -name "*.tex" -o -name "*.md" | xargs grep -l "bijection"

# Find all Lean files with "sorry"
find lean_formalization/PF -name "*.lean" -exec grep -l "sorry" {} \;

# Find verification reports from November 10
find verification_reports -name "*.md" -newermt "2025-11-10"
```

### Navigate by date
- **November 8, 2025**: Core Lean verification complete (33 theorems)
- **November 9, 2025**: Book compilation, contradiction fixes started
- **November 10, 2025**: All contradictions resolved, Stages A/B complete

---

## FILE COUNT SUMMARY

```
book/
  - 41 chapter files
  - 23 appendix files
  - 4 frontmatter files
  - 1 compiled PDF
  - TOTAL: ~70 files

lean_formalization/PF/
  - 6 core proven files (Stage 0)
  - 3 bridge files (Stages A, B)
  - 4 millennium bridge files (Stage C)
  - TOTAL: 13 main proof files + subdirectories

verification_reports/
  - 90+ status and verification reports

numerical_evidence/
  - 5+ Python scripts
  - 10+ data files
  - Multiple result files

documentation/
  - 5 guide files
```

---

## CRITICAL PATHS (FASTEST ROUTES)

### I want to read the book NOW
→ `book/main.pdf`

### I want to verify Lean proofs NOW
→ `lean_formalization/BUILD_INSTRUCTIONS.md`
→ `lake build`

### I want to understand what's proven vs. conjectured NOW
→ `verification_reports/VERIFICATION_COMPLETE_2025-11-10.md`

### I want to reproduce numerical results NOW
→ `numerical_evidence/python_scripts/`
→ Run scripts with Python 3

### I want to contribute NOW
→ `QUICK_START_GUIDE.md` (Option 5)
→ `lean_formalization/README.md`

---

## VERSION HISTORY (RECENT)

- **v3.0**: Original compilation (early November)
- **v3.1**: Enhanced presentation
- **v3.2**: DOI-ready version
- **v3.4**: Complete proofs, contradictions resolved (November 8-10, 2025)
- **CURRENT**: v3.4 with all fixes applied, Stages A/B complete

**Change tracking**: See `CHANGELOG.md` in root directory

---

## HELP

### Lost?
1. Start at `QUICK_START_GUIDE.md`
2. Come back to this file
3. Find the topic you need
4. Follow the path

### Can't find something?
1. Check this navigation map
2. Use search tips above
3. Check `COMPLETE_MANIFEST.md` for full inventory

### Need context?
1. Read the book's preface (`book/frontmatter/preface.tex`)
2. Read verification status (`verification_reports/VERIFICATION_COMPLETE_2025-11-10.md`)
3. Understand framework (Chapters 3, 4, 6, 9)

---

**REMEMBER**: Everything is organized. Everything is documented. Nothing is hidden.

**You know where everything is now.**

---

**Created**: November 10, 2025
**Purpose**: Complete navigation reference
**Maintained by**: Principia Fractalis Guardian
**Updates**: As project structure evolves
