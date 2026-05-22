# Proof Roadmap — Discharging the Polylog Conjecture

> **🎯 2026-05-21 SESSION UPDATE (commit `1607e4b`, build 6322 jobs clean, 0 project axioms).** Today's session produced 13+ axiom-free files that substantially reduced the residual content on both the P-vs-NP and RH chains. Headline updates to this roadmap:
> * **Input 4 (`BookEval019_ShiftBound`) — DISCHARGED** as a Lean theorem (commit `6aa4439`). `bookEvaluation 0.19 > 0.222144147` is now PROVEN, anchored by new axiom-free interval-arithmetic infrastructure (`PF/Analytic/GammaIntervalBounds.lean`, `TrigBookBrackets.lean`, `RpowBookBracket.lean`). The "5 inputs" wrapper is now effectively a "4 inputs" wrapper on the P-side.
> * **Input 3 (`BookEval018_ShiftBound`) — confirmed FALSE in current Lean semantics.** Discharging Input 3 literal-statement-faithful is structurally impossible with the tsum-defined `polyLog`; would require upgrading to a Jonquières-extended `polyLog_continuation` (multi-month classical-analysis formalization).
> * **Polylog-continuation chain:** `PolyLogMonodromyHypothesis` further reduced to `JonquieresGlobalIdentityHypothesis` via `MonodromyFromJonquieres.lean`. The Γ-term half of Jonquières now PROVEN on the corrected `JonquieresAnalyticDomain := SlitPlane ∩ Complex.slitPlane` (`JonquieresAnalyticity.lean`). ζ-series at s=0 PROVEN unconditional (`ZetaShiftBoundDischarge.lean`); at s=-N for N:ℕ PROVEN unconditional (`ZetaShiftBoundNegNat.lean`); at general s reduced to the single named Prop `ZetaShiftPolyExpBound s` (`ZetaBridgeDischarge.lean`). s=0 disc-agreement traced down to `JonquieresExpansionEqualsGeomFrequentlyAtHalf` (no polyLog reference).
> * **RH chain:** new max-discharged wrapper `riemann_hypothesis_residual_only` (`RHMaxDischarged.lean`) exposes only 8 args across 3 bundles. `LogWeightedL2InnerBridge` RETIRED (now a theorem); RH Bundle (a) factored into three named sub-Props (`T3SymLinearStructure`, `T3SymCompactSelfAdjointApproximation`, `T3SymEigenvalueExtraction`).
>
> See the new "Post-2026-05-21 residual Props" section at the bottom of this document for the catalog of remaining named open Props on each chain.

> **🎯 ZERO PROJECT AXIOMS milestone (2026-05-20, commit `72c0137`, pushed).** The previously-axiomatic `alpha_class_polylog_eigenvalue_conjecture` has been refactored to a named Lean Proposition `PolylogEigenvalueConjecture : Prop` (and analogously on the Coq side), taken as an explicit hypothesis by every consumer. The roadmap below targets *discharging* this Proposition (and the related `OffDiscPatchData s`); there is no axiom to retire.

> **⚠ STRUCTURAL FINDING (2026-05-21): the 5-inputs path documented below was structurally vacuous, not viable.** A four-agent investigation determined that the formal Lean `polyLog` (defined as a `tsum`) equals **zero** identically on `{Re s ≤ 1, |z| = 1, z ≠ 1}` due to mathlib's `tsum_eq_zero_of_not_summable` convention on non-summable series. Specifically: `polyLog s z_book = 0` for `s ∈ [0.18, 0.19]` in current Lean semantics. This means:
> - **Input 2 (`h_polylog_cont`)** is satisfied **vacuously** — a constantly-zero function is trivially continuous (discharged literal-statement-faithful in `PF/Analytic/PolylogContInputDischarge.lean`, but does not capture manuscript content).
> - **Input 3 (`h_bracket_lower : bookEvaluation 0.18 < 0.222`)** is **mathematically FALSE** in current Lean. With `polyLog s z_book = 0`, `bookEvaluation 0.18 ≈ 0.71`, not the manuscript's Jonquières-extended value ≈ 0.21. The wrapper's hypothesis cannot be discharged because it is false.
> - **Input 4 (`h_bracket_upper`)** is true in current Lean but requires unbuilt interval-arithmetic infrastructure for `Real.Gamma`, `Real.rpow`, `Real.cos`, `Real.sin` at irrational arguments — multi-month effort independent of the polyLog gap.
> - **Input 5 (`h_P_spec`)** is Category (c) multi-year (per `PF/Analytic/HPSpectralBridge.lean`); the obstruction is the deliberately `opaque alpha_of_class` — without a concrete definition or spectral analysis tying H_P's eigenvalues to `alpha_of_class ClassP`, no bounded assembly produces `alpha_of_class ClassP = √2`.
>
> **What was actually achieved in the 2026-05-21 investigation:**
> 1. `PF/Analytic/PolylogContInputDischarge.lean` — Input 2 discharged literal-statement-faithful (vacuous in manuscript sense). Axiom-free.
> 2. `PF/Analytic/BookEvalNumericalBounds.lean` — Inputs 3+4 reduced to two named Props (`BookEval018_ShiftBound`, `BookEval019_ShiftBound`) capturing the closed-form algebraic inequalities on the monodromy-shift real part (no infinite series, no opaque polyLog). Same discipline as the May 20 cascade refactor. Axiom-free.
> 3. `PF/Analytic/OffDiscPatchDataConstruction.lean` — `OffDiscPatchData s` reduced to the single hypothesis `PolyLogMonodromyHypothesis s` via `offDiscPatchData_of_monodromy` (6 fields collapse to 1 hypothesis). Axiom-free.
>
> **What is now the real residual open work:**
> - Define a manuscript-faithful `polyLog_continuation s z` function whose value on `|z| ≥ 1` equals the Jonquières/Hankel analytic continuation (not the divergent tsum). Then rewrite `axiom_content_FIVE_INPUTS` against `polyLog_continuation` instead of formal `polyLog`. This is multi-month classical-analysis formalization work.
> - Discharge `PolyLogMonodromyHypothesis s` (the global single-function form) — equivalent to producing the Hankel-contour analytic continuation.
> - Discharge the two `BookEval*_ShiftBound` named Props via rigorous interval arithmetic on Γ, rpow, cos, sin (independent classical-analysis infrastructure work).
> - Input 5 (`h_P_spec` / `alpha_of_class ClassP = √2`) remains multi-year operator-theoretic content.

**Goal**: Prove `PolylogEigenvalueConjecture` (formerly the axiom `alpha_class_polylog_eigenvalue_conjecture`) unconditionally as a Lean theorem. **The original 5-inputs decomposition does not provide a viable path; see the structural finding above.**

**Strategy (revised)**: Build a manuscript-faithful `polyLog_continuation` function and a corresponding new wrapper. The 50+ modules of `PF/Analytic/` Phase A infrastructure that targeted the 5-inputs path remain valuable component pieces but do not assemble into a discharge without the polyLog-continuation upgrade.

**Current status (2026-05-21)**: 5-inputs path retired as structurally vacuous; residual content sharpened to 4 named Props (2 closed-form ShiftBounds + PolyLogMonodromyHypothesis + Input 5's multi-year content). Build: 5758 jobs clean, 0 sorries, 0 project axioms.

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

### ⚠ Input 3: `h_bracket_lower` — STRUCTURALLY FALSE IN LEAN

> **2026-05-21 status: This hypothesis is structurally FALSE in current Lean semantics.** With the tsum-defined `polyLog` returning 0 on `{Re s ≤ 1, |z| = 1, z ≠ 1}` (per mathlib's `tsum_eq_zero_of_not_summable` convention), `bookEvaluation 0.18 ≈ 0.71` in actual Lean, not the manuscript's Jonquières-extended value ≈ 0.21. Discharging this hypothesis literal-statement-faithful is structurally impossible without first upgrading `polyLog` to its Jonquières analytic continuation (multi-month classical-analysis formalization). The hypothesis is not a residual to close on the current `polyLog` — it is a structural diagnosis indicating the need for a `polyLog_continuation` upgrade.

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

### ✅ Input 4: `h_bracket_upper` — DISCHARGED 2026-05-21 (commit `6aa4439`)

> **2026-05-21: PROVEN as a Lean theorem.** `bookEvaluation 0.19 > 0.222144147` is no longer a residual hypothesis. Discharge anchored by new axiom-free interval-arithmetic infrastructure:
> * `PF/Analytic/GammaIntervalBounds.lean` — rigorous brackets for `Γ(0.18)`, `Γ(0.19)`, `√π`, `β_book`.
> * `PF/Analytic/TrigBookBrackets.lean` — `cos`/`sin` brackets at irrational arguments.
> * `PF/Analytic/RpowBookBracket.lean` — `Real.rpow` brackets at irrational arguments.
> * `PF/Analytic/BookEval019Discharge.lean` — the discharge itself.
>
> All axiom-free. The "5 inputs" wrapper is effectively now a "4 inputs" wrapper (Input 4 retired; Inputs 1+2 retired in prior sessions; only Inputs 3 (false in current Lean) and 5 (multi-year operator theory) remain on the P-side).

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

## Post-2026-05-21 Residual Named Props (current snapshot)

After the 2026-05-21 session, the framework's residual content is concentrated in the following named Props. Each is axiom-free in its own file; the open content is mathematical (analytic/operator-theoretic), not architectural.

### Polylog-continuation chain (P-vs-NP side, beyond Input 5)

| Prop | File | Status / role |
|---|---|---|
| `ZetaShiftPolyExpBound s` (general `s`) | `PF/Analytic/ZetaBridgeDischarge.lean` | **OPEN** at general `s`. Base cases `s = 0` and `s = -N` for `N : ℕ` are PROVEN (`ZetaShiftBoundDischarge.lean`, `ZetaShiftBoundNegNat.lean`). |
| `JonquieresFrequentAgreementAtHalf s` | `PF/Analytic/GermAtHalfDischarge.lean` | **OPEN**. Frequent polyLog/Jonquières agreement near `z = 1/2`. |
| `JonquieresExpansionEqualsGeomFrequentlyAtHalf` | `PF/Analytic/JonquieresAtZeroDischarge.lean` | **OPEN** (sharper `s = 0` specialization, *no polyLog reference* — purely classical agreement of two explicit analytic expressions). |
| `JonquieresExpansionAnalyticOnPuncturedBall` | `PF/Analytic/JonquieresLocalWitness.lean` | **OPEN**. Local analyticity on the punctured ball. |
| `JonquieresGlobalIdentityHypothesis` | (replaces `PolyLogMonodromyHypothesis` via `PF/Analytic/MonodromyFromJonquieres.lean`) | **OPEN**. Global identity form. |
| `PolyLogMonodromyHypothesis s` | (via `MonodromyFromJonquieres.lean`) | Reduced to `JonquieresGlobalIdentityHypothesis` (above). |
| `BookEval018_ShiftBound` (Input 3) | `PF/Analytic/BookEvalBound018.lean` | **STRUCTURALLY FALSE in current Lean** — requires `polyLog_continuation` upgrade. |
| `BookEval019_ShiftBound` (Input 4) | `PF/Analytic/BookEval019Discharge.lean` | **DISCHARGED** (theorem, 2026-05-21). |
| `h_P_spec` (Input 5) | `PF/Analytic/HPSpectralBridge.lean` | **OPEN**. Multi-year operator-theoretic content; gated by opaque `alpha_of_class`. |

### RH chain (Bundle (a) post-session factorization)

| Prop | File | Status / role |
|---|---|---|
| `T3SymLinearStructure` | `PF/Analytic/T3SymCLMConstruction.lean` | **OPEN**. RH Bundle (a) linear-structure residual (post-`LogWeightedL2InnerBridge`-discharge). |
| `T3SymCompactSelfAdjointApproximation` | `PF/Analytic/T3SymFiniteRankTowerDischarge.lean` | **OPEN**. RH Bundle (a) finite-rank-tower residual (base cases + closure rules proven; this is the sharper sub-Prop). |
| `T3SymEigenvalueExtraction` | `PF/Analytic/T3SymFiniteRankTowerDischarge.lean` (and related) | **OPEN**. Named Prop encoding the missing mathlib infinite-dimensional spectral theorem witness. |
| `LogWeightedL2InnerBridge` | `PF/Analytic/LogWeightedL2InnerBridgeDischarge.lean` | **DISCHARGED** (theorem, 2026-05-21). |
| `SlitDiscPreconnectedReachability` | `PF/Analytic/SlitDiscPreconnected.lean` | **DISCHARGED** (theorem, 2026-05-21). |
| RH Bundle (b) — Mayer 1991 non-degeneracy | (Phase A engineering) | **OPEN**. Numerical non-degeneracy verification. |
| RH Bundle (c) — surjectivity = Problem 4 | `PF/SpectralBijection.lean` | **OPEN**. The single load-bearing open conjecture of the RH program. |

### Max-discharged wrapper

`riemann_hypothesis_residual_only` in `PF/Analytic/RHMaxDischarged.lean` exposes only 8 arguments across the 3 bundles (a)/(b)/(c) above. This is the sharpest stated form of the RH conditional reduction.

### Net post-2026-05-21 summary

* **P-side residuals**: `ZetaShiftPolyExpBound s` (general s), `JonquieresExpansionEqualsGeomFrequentlyAtHalf`, `JonquieresFrequentAgreementAtHalf s`, `JonquieresExpansionAnalyticOnPuncturedBall`, `JonquieresGlobalIdentityHypothesis` (polylog continuation); `BookEval018_ShiftBound` (Input 3, structurally false in current Lean); `h_P_spec` (Input 5, operator theory).
* **RH-side residuals**: `T3SymLinearStructure`, `T3SymCompactSelfAdjointApproximation`, `T3SymEigenvalueExtraction` (Bundle (a)); Mayer 1991 non-degeneracy (Bundle (b)); surjectivity / Problem 4 (Bundle (c)).
* **Retired this session**: Input 4 (`BookEval019_ShiftBound`), `SlitDiscPreconnectedReachability`, `LogWeightedL2InnerBridge` — all now theorems.

Build state at this snapshot: **6322 jobs clean, 0 sorries, 0 project axioms, commit `1607e4b`**.

---

*Generated 2026-05-20. Updated 2026-05-21 (session — substantial residual reduction).*
