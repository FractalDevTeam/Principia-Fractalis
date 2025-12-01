# Contributing to Principia Fractalis

Thank you for your interest in contributing to Principia Fractalis. This document outlines how you can participate in this project.

## Types of Contributions

### 1. Peer Review and Verification

The most valuable contribution is **rigorous mathematical review**:

- Verify proof chains in the Lean 4 or Coq formalizations
- Check axiom classifications and their justifications
- Validate numerical computations independently
- Identify potential gaps or areas needing clarification

**To submit a review:**
1. Open an Issue with the `[REVIEW]` prefix
2. Specify which section/file you reviewed
3. Provide detailed, mathematically precise feedback

### 2. Bug Reports

If you find errors in:
- Proof formalization (wrong type, logical gap)
- Numerical computations
- Documentation inconsistencies
- Build issues

**Open an Issue with:**
- `[BUG]` prefix
- File path and line numbers
- Expected vs. actual behavior
- Environment details (Lean version, Coq version, OS)

### 3. Documentation Improvements

- Clarify mathematical exposition
- Fix typos or grammatical errors
- Improve build instructions
- Add examples or explanations

### 4. Formalization Extensions

If you want to extend the Lean 4 or Coq proofs:
- Discuss first via an Issue
- Follow existing code style and naming conventions
- Ensure zero sorrys/admits in your contribution
- Document any new axioms thoroughly

## Code of Conduct

1. **Maintain scientific rigor** - All feedback must be mathematically precise
2. **Be respectful** - Disagree with ideas, not people
3. **Be constructive** - Criticism should include suggestions for improvement
4. **Stay on topic** - This is a mathematics project, not a philosophy forum

## Review Standards

This project maintains peer-review level scrutiny:

- All mathematical claims require proof or explicit axiom citation
- Informal arguments are not accepted where rigor is needed
- Numerical claims require certified bounds
- Cross-references between sections must be verified

## Getting Started

1. **Read the Documentation**
   - Start with `README.md` for an overview
   - Read `VERIFICATION_STATUS.md` for formalization details
   - Review `AXIOM_AUDIT.md` for axiom classifications

2. **Set Up Development Environment**

   **Lean 4:**
   ```bash
   # Install elan (Lean version manager)
   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

   # Build the project
   cd PF_Lean4_Code
   lake update && lake build
   ```

   **Coq:**
   ```bash
   # Install Coq (via opam recommended)
   opam install coq

   # Build the project
   cd PF_Coq
   coq_makefile -f _CoqProject -o Makefile
   make -j4
   ```

3. **Explore the Codebase**
   - `PF_Lean4_Code/PF/SpectralGap.lean` - Core P vs NP proof
   - `PF_Coq/theories/Core/P_NP_Proof.v` - Coq equivalent
   - `Principia_Fractalis_master_folder/` - Book LaTeX source

## Pull Request Process

1. Create a feature branch from `master`
2. Make your changes with clear commit messages
3. Ensure all builds pass (zero sorrys/admits)
4. Update relevant documentation
5. Submit PR with detailed description of changes

## Questions?

Open an Issue with the `[QUESTION]` prefix for:
- Clarification on mathematical content
- Help understanding the framework
- Discussion of theoretical implications

---

*Principia Fractalis demands the highest standards of mathematical rigor. Contributors are expected to uphold these standards.*
