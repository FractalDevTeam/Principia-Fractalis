# Chapter 9 (Spectral Unity) — survey before charter, 2026-09-12

*Survey performed after the R_f Priority 1 + Priority 2 (α = 0) arc closed
at HEAD `2ad1d880` on `r331b-provenance`. Recorded per the standing rule
adopted after the R_f charter mistake: "Every new Lean campaign starts
with a SURVEY file that grep-inventories the existing tree for adjacent
identifiers before proposing new modules."*

## §1. What the book says (ch09_spectral_unity.tex, verified read)

Chapter 9's central definitional content:

- **Definition 9.1** (`def:comp_operators`, ch09 lines 76-86) defines
  **two separate operators** `H_P` and `H_{NP}` on Hilbert spaces
  `H_P = L^2(X_P, μ_P)` and `H_{NP} = L^2(X_{NP}, μ_{NP})`:
  ```
  (H_P f)(L) = Σ_x (1/2^{|x|}) e^{iπα_P D_3(encode_{M_L}(x))} E_P(M_L, x) f(L ⊕ {x})
  ```
  and similarly for `H_{NP}` with `α_{NP}` and `E_{NP}`. The book does
  **not** present these as instances of a unified parametric family
  `H_α : ℂ → Operator`. They are parallel constructions.

- **Theorem 9.1** (`thm:self_adjoint_fractal`, ch09 lines 90-102):
  "H_P and H_{NP} are self-adjoint on their respective domains if and
  only if α_P = √2 and α_{NP} = φ + 1/4." **Proof is a "Proof Sketch"
  that defers to `\cite{cohen2025pvsnp}`** — an external paper. The
  book itself does not prove this theorem.

- **Theorem 9.2** (`thm:pvsnp_spectral`, ch09 lines 110-125): ground
  state energies `λ_0(H_P) = π/(10√2)` and closed-form
  `λ_0(H_{NP}) = π/(10(φ + 1/4))`. Includes a 2026-05-18 correction
  note: the empirical value `≈ 0.1330` does NOT match the closed
  form `≈ 0.1682`; the spectral separation is conditional on the
  empirical measurement.

- The **energy functionals `E_P(M_L, x)` and `E_{NP}(M_L, x)`** are
  undefined in the book text. They are referenced but never specified.

## §2. What is already in the Lean tree (verified grep, 2026-09-12)

`PF/SpectralGap.lean` (274 lines):

| Lean identifier | what it actually formalizes |
|---|---|
| `lambda_0_P : ℝ := pi_10 / Real.sqrt 2` | a **real-number** definition; NOT an operator ground state |
| `lambda_0_NP : ℝ := pi_10 / (phi + 1/4)` | same — a real-number definition |
| `spectral_gap : ℝ := lambda_0_P - lambda_0_NP` | arithmetic difference |
| `spectral_gap_value` | `|Δ - 0.0539677287| < 1e-8` — pure numerical claim |
| `spectral_gap_positive` | `Δ > 0` — trivial from the arithmetic |
| `pvsnp_spectral_separation` | `∃ Δ > 0, Δ = lambda_0_P - lambda_0_NP ∧ |Δ - 0.0539677287| < 1e-8` |

**Critical honest scope:** `PF/SpectralGap.lean` does not define `H_P`
or `H_{NP}` as operators. It computes the arithmetic difference of
two real numbers. It does not establish that these numbers are
ground state energies of any actual self-adjoint operator. The
"P ≠ NP" claim is exclusively at the level of the numerical
separation `π/(10√2) − π/(10(φ+1/4)) > 0`.

This matches (and sharpens) the fractal-architecture doc's note:
"P vs NP (ch21) apparently faithful — needs `Machine` /
`turingTimeComplexity` audit."

## §3. What the 2026-09-12 single-agent survey recommended, and why it is wrong

The `Explore` agent recommended a "unified operator template
`H_α : ℂ → Operator`" as the highest-leverage gap, with the claim
"self-adjoint iff α ∈ {√2, φ+1/4}, ground state energies
λ₀(H_α) ∝ sin(πα/√2)/α".

**Verification against the book (§1 above) shows:**

1. The book does NOT unify H_P and H_{NP} into a parametric H_α family.
   The unification is a natural mathematical generalization, but it is
   not book-guided — it is extrapolation.
2. The `sin(πα/√2)/α` formula does NOT appear in ch09. The book gives
   only the two specific closed-form values.
3. The self-adjointness result is book-deferred to an external paper.
   Any Lean proof of it would either import that paper's argument
   (currently outside the corpus) or be first-principles work.
4. The energy functionals `E_P`, `E_{NP}` are undefined in the book.
   No faithful Lean definition of H_P or H_{NP} is possible using only
   book-level content.

The survey's recommendation is therefore rejected as insufficiently
book-guided. Adopting it would repeat the R_f-charter mistake at
larger scale.

## §4. What IS a legitimate ch09 formalization campaign

Book-guided targets that would advance the fractal:

### Target A — honest per-axis operator scaffold (~150-250 lines)

Define `H_P` and `H_{NP}` as noncomputable Lean objects **taking
their energy functionals as abstract parameters** (since the book
leaves them abstract). State — but do NOT prove — self-adjointness
as a Prop, following the discipline of `PF/Consciousness/FractalResonance.lean`
§8 (which encodes `rh_resonance_at_three_halves` etc. as Props,
not axioms, not theorems).

**Deliverable:** a Lean file `PF/SpectralUnityOperators.lean` (name
suggested; verify no conflict) with:
- `noncomputable def H_P (E_P : ...) : ...`
- `noncomputable def H_NP (E_NP : ...) : ...`
- `def self_adjoint_at_alpha_P : Prop := IsSelfAdjoint (H_P ...)`
- `def self_adjoint_at_alpha_NP : Prop := IsSelfAdjoint (H_NP ...)`
- Bridge lemma: if the Props hold and the ground-state hypothesis
  holds, then `pvsnp_spectral_separation` follows.

This would upgrade `PF/SpectralGap.lean` from a real-number arithmetic
file to a substrate-level operator-theoretic statement, matching the
book's own scope (the book proof-sketches the operator claims).

**Scope estimate:** 150-250 lines. **Risk:** low — nothing is proven
that isn't already in the tree; the Props are honest research markers.

### Target B — sector-interface theorem for P/NP (~300-500 lines)

Per Direction B of the fractal-architecture doc: an interface theorem
```
sector_interface_PvsNP : SubstrateAt (√2) ∧ SubstrateAt (φ + 1/4)
                       → SolvedClayProblem_PvsNP
```
without either side containing the other in disguised form.

Currently the "SolvedClayProblem_PvsNP" statement in the tree
(`enum_to_class_separation_bridge_iff_literal_P_neq_NP`) is at the
type-level; a substrate-level interface would connect substrate
rigidity to the numerical spectral separation.

**Scope estimate:** larger (300-500 lines). **Risk:** medium —
requires a careful honest scope statement, per directive §5.

## §5. Recommendation

Do not launch a new Lean campaign this session. The R_f arc's two
priorities are closed; the appI cross-reference is updated; the
ch09 survey exists. The right next-session move is Pablo-directed:

- If continuing the atomic-level fractal expansion: Target A above.
- If moving to Direction B: BSD sector (`rfl`-tautology, worst
  faithfulness per the ledger) is the highest-yield honest rewrite.
- If pausing Lean and moving to publication: submit the mathlib PRs
  from `codex/MATHLIB_PR_42093_RESPONSE_2026-09-10.md`.

Do not adopt the single-agent H_α unification recommendation. It
extrapolates beyond the book text and would recapitulate the R_f
charter mistake.

*Charter policy reminder:* Every new Lean campaign starts with a
survey. Every survey is verified against the book source, not just
against agent output. Book-guides-Lean is the acceptance test.
