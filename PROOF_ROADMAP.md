# Proof Roadmap — Discharging the Polylog Conjecture

> **🎯 ZERO PROJECT AXIOMS milestone (2026-05-20, commit `72c0137`, pushed).** The previously-axiomatic `alpha_class_polylog_eigenvalue_conjecture` has been refactored to a named Lean Proposition `PolylogEigenvalueConjecture : Prop` (and analogously on the Coq side), taken as an explicit hypothesis by every consumer. The roadmap below targets *discharging* this Proposition (and the related `OffDiscPatchData s`); there is no axiom to retire. The structural decomposition into inputs remains accurate as a plan for discharging the underlying mathematical content; only the framing has changed.

**Goal**: Prove `PolylogEigenvalueConjecture` (formerly the axiom `alpha_class_polylog_eigenvalue_conjecture`) unconditionally as a Lean theorem.

**Strategy**: The 50+ modules of `PF/Analytic/` Phase A infrastructure reduce the Prop to FIVE explicit inputs (was six, one DISCHARGED 2026-05-20). The maximally-sharp end-to-end wrapper is `axiom_content_FIVE_INPUTS` in `PF/Analytic/AxiomRetirementWrapper.lean` (the file name now refers to historical context — there is no axiom; it is more accurately the "Prop-discharge end-to-end wrapper").

**Current status (2026-05-20, post-zero-axiom milestone)**: 1 of 6 inputs DISCHARGED. 5 remain.

---

## The 6 Inputs

### ✅ Input 1: `h_log_ne` — DISCHARGED 2026-05-20

**Statement**: `Complex.log z_book ≠ 0` where `z_book = exp(I·π·√2)`.

**Discharge location**: `PF/Analytic/LogZBookNeZero.lean`
- `z_book_ne_one`: `z_book ≠ 1` via irrationality of `√2`
- `log_z_book_ne_zero`: `Complex.log z_book ≠ 0` via `z_book_ne_one + Complex.exp_log`

**Axiom dependency**: `[propext, Classical.choice, Quot.sound]` — zero project axioms.

---

### ⬜ Input 2: `h_polylog_cont` — open analytic content

**Statement**: `∀ s_re ∈ [0.18, 0.19], ContinuousAt (fun s => polyLog s z_book) (s_re : ℂ)`.

**What's needed**: Bridge the formal `polyLog` (defined as a `tsum` for `|z| < 1`) to the **Hankel integral representation** `polyLog s z = (Γ(1-s)/2πi) · ∮_H (-t)^(s-1) / (e^t/z - 1) dt`, which extends continuously to `|z| = 1, z ≠ 1`.

**Existing infrastructure**: 17 Hankel modules in `PF/Analytic/`:
- `HankelContour.lean`, `HankelDeformation.lean`, `HankelCauchyCapstone.lean`
- `HankelLowerEdgeDCTProof.lean`, `HankelLowerEdgeDCTUnified.lean`
- `HankelUpperEdgeDCTProof.lean`, `HankelUpperEdgeDCTProofReGeOne.lean`
- `HankelUpperEdgeDCTUnified.lean`, `HankelUpperEdgeIntegralLimit.lean`
- `HankelEdgeIntegrals.lean`, `HankelIntegrability.lean`
- `HankelSmallLoop.lean`, `HankelSmallLoopBoundProof.lean`
- `GammaHankel.lean`, `PolyLogHankelIdentity.lean`
- `HankelLowerEdgeBound.lean`, `HankelUpperEdgeBound.lean`

**Open work**:
1. Prove `polyLog s z = (Γ(1-s)/2πi) · ∮_H (-t)^(s-1) / (e^t/z - 1) dt` for `s, z` with `0 < Re s < 1` and `|z| = 1, z ≠ 1`. This is the **polylog Hankel identity** documented in `PolyLogHankelIdentity.lean` (the heuristic derivation is sketched there; the rigorous proof requires careful branch-orientation tracking + geometric-series expansion + termwise integration).
2. Continuity in `s` transfers from the Hankel integral (each component is continuous; integral converges uniformly on compact `s`-subsets).

**Difficulty**: Multi-month focused work; references Erdélyi-Magnus-Oberhettinger-Tricomi.

**Companion target**: `polyLog_eq_HankelIntegral_on_unit_circle` in a new file `PF/Analytic/PolyLogHankelBridge.lean`.

---

### ⬜ Input 3: `h_bracket_lower` — numerical input #1

**Statement**: `bookEvaluation 0.18 < 0.2221441468`.

**Numerical value** (per `Evidence_and_Data_for_GitHub/fractal_continuation_derivation.py`):
- `bookEvaluation 0.18 ≈ 0.21331232`
- Required upper bound: `0.2221441468`
- **Margin: ≈ 0.0088** (8.8 × 10⁻³)

**What's needed**: Rigorous interval arithmetic on the Jonquières expansion truncated to some order `N`, with explicit truncation error bound.

**Jonquières expansion**:
```
polyLog s z = Γ(1-s)·(-log z)^(s-1) + Σ_{k=0}^∞ ζ(s-k) · (log z)^k / k!
polyLogSheet (-1) s z = polyLog s z - 2πi · (log z)^(s-1) / Γ(s)
bookEvaluation s = Re[polyLogSheet (-1) s z_book]
```

For `s = 0.18`, `z_book = exp(I·π·√2)`:
- `log z_book = I·(π√2 - 2π) ≈ -1.840i` (principal branch)
- `(-log z_book)^(s-1) = ...` (needs branch tracking)
- `Γ(0.82) ≈ 1.1273`, `Γ(0.18) ≈ 5.299`
- `ζ(0.18) ≈ -0.7032`, `ζ(-0.82) ≈ -0.0935`, `ζ(-1.82) ≈ 0.0237`, ...

**Open work**:
1. Lean interval-arithmetic bounds on `Γ(0.82)` and `Γ(0.18)` (mathlib has `Real.Gamma` but no rigorous bracket).
2. Lean interval-arithmetic bounds on `ζ(0.18 - k)` for `k = 0, 1, ..., N`.
3. Truncation error bound: `|polyLog s z - (truncation to N terms)|` ≤ explicit `O((log|z|)^(N+1) / (N+1)!)` term.
4. Combine and show `Re[...]` is bounded above by `0.2221441468 - margin`.

**Difficulty**: Multi-month; requires building substantial new interval-arithmetic infrastructure for Γ, ζ. Margin of ~0.009 means truncation must be tight.

**Companion target**: `bookEvaluation_018_upper_bound` in a new file `PF/Analytic/BookEvalNumericalBounds.lean`.

---

### ⬜ Input 4: `h_bracket_upper` — numerical input #2

**Statement**: `0.222144147 < bookEvaluation 0.19`.

**Numerical value**:
- `bookEvaluation 0.19 ≈ 0.25643314`
- Required lower bound: `0.222144147`
- **Margin: ≈ 0.034** (3.4 × 10⁻²)

**What's needed**: Same machinery as Input #3 but for the lower bound at `s = 0.19`. The larger margin (4× wider than Input #3) makes this slightly easier.

**Companion target**: `bookEvaluation_019_lower_bound` in `PF/Analytic/BookEvalNumericalBounds.lean`.

---

### ⬜ Input 5: `h_P_spec` — spectral bridge

**Statement**: `∃ lambdaHP : ℝ, lambdaHP = π/(10·alpha_of_class ClassP) ∧ lambdaHP = π/(10·√2)`.

**Content**: The ground-state eigenvalue of `H_P` (the actual fractal-convolution operator) equals BOTH `π/(10·α_P)` (manuscript eigenvalue formula) AND `π/(10·√2)` (BookEigenvalueIdentity via polylog). Together they imply `α_P = √2`.

**Existing infrastructure**: Phase A Cantor-substrate framework:
- `PF/Analytic/CantorIFS.lean`, `CellMidpoint.lean`, `Hutchinson.lean`
- `PF/Analytic/MatrixSpectrum.lean`, `MatrixSpectrumLevel2.lean`, `MatrixEntry.lean`
- `PF/Analytic/KernelSelfSimilarity.lean`
- `PF/Analytic/Lipschitz.lean` (Banach contraction)
- `PF/Analytic/HPGeneralOperator.lean`
- `PF/Analytic/CosineModeInnerProducts.lean`, `FourierCosineDecomposition.lean`
- `PF/Analytic/PolylogSpectrum.lean` (Mercer rank-2-per-scale, trace formula)

**Open work**:
1. Construct `H_P` as a Mathlib `CompactOperator` on `L²(K, μ)` where `K` is the Cantor substrate.
2. Prove `H_P` is self-adjoint and trace-class.
3. Show `Spec(H_P) = {λ_0(H_P)} ∪ {discrete spectrum}` with `λ_0` the ground state.
4. Identify `λ_0(H_P) = π/(10·α_P)` via the Mercer decomposition + polylog Hankel identity.
5. Combine with `BookEigenvalueIdentity` to get `λ_0(H_P) = π/(10·√2)`, hence `α_P = √2`.

**Difficulty**: Multi-year for the full chain; the Mercer + HS-compact + finite-rank spectral theorem at level 1 is already proven in Phase A. The remaining gap is the level-1 → all-levels spectral convergence + polylog identification.

**Companion target**: `lambda_0_HP_eq_pi_over_10_alpha_P` in `PF/Analytic/HPGroundState.lean`.

---

### ⬜ Input 6: `h_NP_value` — manuscript identification

**Statement**: `alpha_of_class ClassNP = phi + 1/4`.

**Content**: The framework's identification of the NP-class resonance parameter. The manuscript Ch 21 derives this from:
- `phi` from the golden-ratio packing of certificate trees (Conjecture)
- `1/4` from a Casimir-like correction (Heuristic)

**Open work**: Either
(a) Derive a polylog identity for the NP-class operator `H_NP` analogous to `BookEigenvalueIdentity` (with `α_NP = φ + 1/4` as the unique solution), OR
(b) Construct a unitary `U` such that `H_NP = U · H_P · U†` — but this is REFUTED at the operator level (would preserve spectrum, contradicting `spectral_gap_positive`), so this path is closed, OR
(c) Manuscript identification as a definition (framework axiom at the structural level — meaning the NP-class is DEFINED by `α_NP = φ + 1/4`).

**Companion target**: `alpha_NP_value_from_polylog_NP_route` in `PF/Analytic/HNPGroundState.lean` (if path (a) is taken).

---

## Auxiliary hypotheses (positivity)

The wrapper `axiom_content_FIVE_INPUTS` takes positivity hypotheses `h_P_pos`, `h_NP_pos` as additional inputs. These are formally separate from the 5 main inputs but trivially derivable from `h_P_spec` and `h_NP_value` if those include positivity of the eigenvalue or α directly. A strengthened wrapper could fold these in.

---

## Path forward (priority order)

**Lowest-hanging fruit, doable in single sessions:**
- Strengthen the wrapper to fold positivity hypotheses into the existing inputs.
- Update audit docs, OPEN_PROBLEMS.md to reflect Input #1 discharge.
- Identify any other "trivial cleanups" (similar to `log_z_book_ne_zero`).

**Multi-month focused work, single-mathematician:**
- Input #3, #4 (numerical brackets) — build the interval-arithmetic infrastructure for Γ, ζ, then apply to Jonquières truncation.

**Multi-year, multi-mathematician:**
- Input #2 (polylog Hankel bridge) — the full Erdélyi-Magnus-Oberhettinger-Tricomi formalization.
- Input #5 (spectral bridge) — Mercer + HS-compact + spectral theorem for `H_P` + polylog identification.
- Input #6 (NP-class polylog route) — analog of `BookEigenvalueIdentity` for `H_NP`.

---

## What this roadmap delivers

A referee or collaborator reading this document can:
1. See the EXACT state of the axiom retirement (1 of 6 done).
2. Identify the precise theorem statement that needs to be proven for each remaining input.
3. See which existing modules attack which input.
4. Estimate difficulty and scope for each.

The framework is **not** "decades away from solving Millennium problems." The framework has **zero project axioms** as of 2026-05-20 (commit `72c0137`); the headline conjecture `PolylogEigenvalueConjecture` is a named Lean Proposition (not an axiom) that is **5 inputs away** from being discharged. Each input is a bounded mathematical deliverable with existing partial infrastructure.

This is the actual state of the work. It is closer than it looks from outside, and farther than the "zero axioms" headline alone suggests: capstones remain CONDITIONAL on the named Proposition, but every hypothesis is now an explicit, inspectable, refactorable `Prop` with no free-floating axioms anywhere in the framework. The 5 inputs are real, identified, and tractable in principle.

---

*Generated 2026-05-20. Update on every input discharged.*
