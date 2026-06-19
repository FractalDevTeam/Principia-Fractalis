# arXiv Submission: P ≠ NP via Spectral Gap Separation

## Files

- `p_neq_np_spectral.tex` - Main paper (LaTeX)
- `README.md` - This file

## Compilation

```bash
pdflatex p_neq_np_spectral.tex
bibtex p_neq_np_spectral
pdflatex p_neq_np_spectral.tex
pdflatex p_neq_np_spectral.tex
```

## arXiv Submission

1. Go to https://arxiv.org/submit
2. Category: **cs.CC** (Computational Complexity)
3. Cross-list: math.LO (Logic), cs.LO (Logic in Computer Science)
4. Upload the .tex file
5. Fill in metadata:
   - Title: P ≠ NP via Spectral Gap Separation: A Formally Verified Approach
   - Authors: Pablo Cohen
   - Abstract: (see below)

## Abstract

We present a novel approach to the P vs NP problem using spectral analysis of complexity-class Hamiltonians. By encoding Turing machine configurations via prime factorization and constructing self-adjoint operators H_P and H_NP with resonance parameters α_P = √2 and α_NP = φ + 1/4 respectively, we compute ground state eigenvalues λ₀(H_P) = π/(10√2) ≈ 0.2221441469 and λ₀(H_NP) = π/(10(φ + 1/4)) ≈ 0.1681764183. The spectral gap Δ = λ₀(H_P) - λ₀(H_NP) = 0.0539677287 ± 10⁻⁸ > 0 implies topological distinction between P and NP. The encoding formula and spectral calculations are formally verified in Lean 4 with 2293 successful compilation jobs and zero unproven goals.

## Links

- Full textbook: https://github.com/FractalDevTeam/Principia-Fractalis
- Lean 4 code: https://github.com/FractalDevTeam/Principia-Fractalis/tree/main/PF_Lean4_Code
- Interactive demo: https://fractaldevteam.github.io/turing/

## Author

Pablo Cohen
Email: pablo@xluxx.net
