# Contributing to Principia Fractalis

Thank you for your interest in contributing to this research.

## Ways to Contribute

### Mathematical Review (Most Valuable)

The most valuable contribution is **rigorous peer review**:

1. Open a [Mathematical Review](https://github.com/FractalDevTeam/Principia-Fractalis/issues/new?template=mathematical_review.md) issue
2. Identify the specific theorem, axiom, or proof you're examining
3. Provide detailed analysis with references

We welcome:
- Axiom validity questions
- Proof correctness concerns
- Numerical precision issues
- Logical gap identification
- Alternative approach suggestions

### Bug Reports

Found a compilation error or inconsistency?

1. Open a [Bug Report](https://github.com/FractalDevTeam/Principia-Fractalis/issues/new?template=bug_report.md)
2. Include the file, line number, and prover (Lean 4 / Coq)
3. Provide steps to reproduce

### Questions

Have a question about the mathematics or framework?

1. Open a [Question](https://github.com/FractalDevTeam/Principia-Fractalis/issues/new?template=question.md)
2. Provide context about what you're trying to understand

### Code Contributions

For code contributions (proof improvements, new formalizations):

1. Fork the repository
2. Create a feature branch
3. Ensure all proofs compile:
   ```bash
   # Lean 4
   cd PF_Lean4_Code && lake build

   # Coq
   cd PF_Coq && make
   ```
4. Submit a pull request with clear description

**Important:** Do not introduce `sorry` (Lean) or `Admitted` (Coq) statements.

## Code of Conduct

- Be respectful and constructive
- Focus on mathematical rigor, not personal criticism
- Cite sources when referencing prior work
- Acknowledge that this is ongoing research

## Contact

- **Email:** psolorzano@gmail.com
- **ORCID:** [0009-0002-0734-5565](https://orcid.org/0009-0002-0734-5565)

---

*All contributions are appreciated. Even a starred repository helps with visibility.*
