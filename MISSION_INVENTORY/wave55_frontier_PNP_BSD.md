# Wave 55 Frontier Inventory — P/NP + BSD + Cross-Millennium

**Date**: 2026-05-31
**Scope**: ch21 (P vs NP) + ch24 (BSD) + ch29 (Observational, cross-Millennium props)
**Lean target tree**: `/home/xluxx/Principia-Fractalis/PF_Lean4_Code/PF/`
**Manuscript chapters**:
- `/home/xluxx/Principia-Fractalis/Principia_Fractalis_master_folder_rev2/chapters/ch21_p_vs_np.tex`
- `/home/xluxx/Principia-Fractalis/Principia_Fractalis_master_folder_rev2/chapters/ch24_birch_swinnerton_dyer.tex`
- `/home/xluxx/Principia-Fractalis/Principia_Fractalis_master_folder_rev2/chapters/ch29_observational_tests.tex`

---

## 1. Manuscript claims and HONEST scope

### 1A. P vs NP (ch21)

**Headline claims**:
- (C1) Closed forms: `λ₀(H_P) = π/(10√2)`, `λ₀(H_{NP}) = π/(10(φ+1/4))`, both certified to 10⁻¹⁰ vs the v3.3.1 empirical values 0.2221441469 and 0.168176418230.
- (C2) Fractal-dimension separation: `α_P = √2 < α_{NP} = φ+1/4`.
- (C3) Spectral-gap positivity and the conditional chain `P=NP ⇒ λ₀(H_P)=λ₀(H_{NP}) ⇒ gap=0`; contrapositive yields `P ≠ NP` under `PolylogEigenvalueConjecture` (named Prop, not axiom).
- (C4) 143-problem empirical capstone: 100% fractal coherence with null-probability bound `< 10⁻⁴⁰`.
- (C5) IBM-Quantum hardware peaks: `α_RH = 3/2` exact, `α_NP ≈ 1.868 ≈ φ + 1/4`.
- (C6) **Reformulated** spectral content (Wave 17): `π/(10α)` is the H₃ Coxeter / monodromy-phase B-clean invariant, NOT a literal Rayleigh-Ritz eigenvalue of `arxivHalpha` (literal spectral reading REFUTED axiom-free, `arxivHalpha_spectral_reading_refuted`).

**Honest scope of ch21**:
- P vs NP is NOT discharged. The chain is conditional on `PolylogEigenvalueConjecture`, which the Wave 41B no-go (`AlphaOfClassNoGoSingleCitation.lean`) shows is logically *equivalent* to a proof of `ClassP ≠ ClassNP` on the opaque `alpha_of_class`.
- Literal `λ₀ = π/(10α)` spectral identity is FALSIFIED on the framework's own `arxivHalpha` and on four orthogonal substrates (L²[0,1], L²(Cantor), L²(ℝ₊,dx/x), L²(ℝ,du)). Surviving content is monodromy-phase / Coxeter, not eigenvalue.
- The 10⁻¹⁰ numerical match `|π/(10√2) − 0.2221441469| < 10⁻¹⁰` is a Lean theorem; this is closed-form vs empirical, not operator-spectral.

### 1B. BSD (ch24)

**Headline claims**:
- (B1) The BSD-distinguished eigenvalue `λ_* = φ/e ≈ 0.59524` is the resonance value at which `T̃_E`'s spectral measure concentrates, with rank living in eigenvalue *multiplicity* at `λ_*`.
- (B2) Three-rank concordance: the SAME `0.595 < φ/e < 0.596` bracket holds for `E_{32.a3}` (rank 0, CM), `E_{37a1}` (rank 1), `E_{389a1}` (rank 2). Wave 17/18.
- (B3) `α_BSD = 3π/4`; self-adjointness via Friedrichs extension on `L²(ℝ₊ˣ, dx/x)` (multiplicative line, valid for every α).
- (B4) Galois-orbit placement: BSD's √5-content sits in the `ℚ(√5)` subextension shared with Hodge and NP, inside the compositum `ℚ(√2,√5)` (Wave 41A).
- (B5) Frobenius-trace `a_p` constructions on `E_{32.a3}` at 9 primes and `E_{37a1}` at 11 primes (axiom-free, Wave 48F/49C), all matching LMFDB.
- (B6) Conductor anchors `N(E_{32.a3})=32`, `N(E_{37a1})=37` (Wave 50G); partial Euler-product evaluations (Wave 50F/51F/52F); non-monotone oscillation finding with explicit crossing primes `p=41, 53`.
- (B7) Coates–Wiles 1977 and Wiles 1995 framework-level *anchors* on the two distinguished curves (Wave 51G, 52G).
- (B8) **Wave 53F two-sided sandwich**: `0 < L_partial(31) < L(E,1) < L_partial(97)` on `E_{32.a3}`, with `p=41` near-hit within 0.001.

**Honest scope of ch24**:
- BSD NOT discharged on any curve. Lean's `BSD_equality_holds` per-curve predicate is `True`-shaped.
- Coates–Wiles and Wiles encoded as `Prop`-hypotheses, not derived (mathlib lacks CM theory / modularity infrastructure).
- The per-curve placeholder type means `BSDConjecture` reduces to a trivially-true quantification — what is real is the conditional architecture, the `φ/e` bracket, the Friedrichs self-adjointness, the `a_p` decidable point-counting, and the partial-Euler-product oscillation finding.
- Wave 47F **five-gap manifest** (G1–G5) precisely enumerates the mathlib distance to a usable `L(E,s)`: G1 (Frobenius trace), G2 (conductor), G3 (multiplicative `a_n`), G4 (`LSeriesSummable`), G5 (modularity / analytic continuation). G1 and G2 are partially active per-curve; G3–G5 untouched.

### 1C. Cross-Millennium props (ch29 and elsewhere)

**Headline structural props**:
- (X1) Wave 22 **12 algebraic α-invariants**, expanded to 28 in Wave 29; example `α_RH · α_NS = α_NS + α_BSD`.
- (X2) Wave 27 forward + Wave 37C **reverse biconditionals** giving the algebraic web `realised_NS ↔ realised_BSD`, `realised_RH ↔ realised_NS ∧ realised_BSD`.
- (X3) Wave 41A `(ℤ/2)²` Galois action on `ℚ(√2,√5)` over the six algebraic α-instances.
- (X4) Wave 42A Galois-orbit Millennium discriminator: rigid `{Poincaré, RH, YM} ⊂ ℚ` vs twisted `{P, Hodge, NP}`; calibrated by Perelman (solved at α=1).
- (X5) Wave 43C Galois-rigid conditional discharge architecture; cross-sector cascade `YM-rigid ⇒ P-realisation` via Wave 37C.
- (X6) Wave 45C: RH reduced to a SINGLE open analytic conjecture `AnalyticPosBijectionToZetaZeros wave38Substrate`.
- (X7) Wave 49G factor-2 BSD/NS/YM bridge; Wave 51H NS/YM/BSD transcendental-ratio bridge (sixth cross-Millennium bridge, first triple-Millennium).
- (X8) Wave 50H/51H/52H/53H four-axis rigid-normalisation taxonomy.

**Honest scope of X-props**: structural / algebraic / web-closure; none discharges a Clay problem.

---

## 2. Axiom-free Lean coverage

| Manuscript claim | Lean file (`PF/`) | Axiom-free? | Discharges? |
|---|---|---|---|
| C1 (closed-form 10⁻¹⁰) | `SpectralGap.lean` `lambda_0_P_precise`, `lambda_0_NP_precise` | YES | numerical only |
| C2 (α separation) | `Operators.lean` `alpha_class_separation_lt` | YES | structural only |
| C3 (conditional P≠NP) | `MillenniumSixReductions.lean` `P_NEQ_NP` | YES (cond.) | NO — needs `PolylogEigenvalueConjecture` |
| C4 (143-problem) | `Empirical/HundredFortyThreeProblems.lean` `empirical_validation_capstone` | YES | empirical only |
| C5 (IBM Galois pair) | `IBMPeaksGaloisPair.lean` | YES | empirical/algebraic only |
| C6 (literal spectral REFUTED) | `PolylogViaHilbertSchmidtCompactness.lean` `arxivHalpha_spectral_reading_refuted` | YES | refutation only |
| B1 (`φ/e` bracket) | `MillenniumSixReductions.lean` `bsd_distinguished_eigenvalue_bracket` | YES | structural only |
| B2 (3-rank concordance) | `BSDGaloisPairConcordance.lean`, `BSDRankTwoCurveFramework.lean`, `BSDRankThreeCurveFramework.lean`, `BSDRankFourFiveFrameworks.lean` | YES | concordance only |
| B4 (Galois compositum) | `CrossQuadraticFieldBridge.lean` | YES | structural only |
| B5 (Frobenius `a_p`) | `BSDFrobeniusTraceAttempt.lean`, `BSDFrobeniusTraceExtended.lean` | YES | per-prime LMFDB match |
| B6 (partial `L`, oscillation) | `BSDLPartialEvaluation*.lean`, `BSDLPartialOscillationAnalysisAttempt.lean` | YES | partial truncation only |
| B6 (conductor) | `BSDConductorAttempt.lean` | YES | per-curve only |
| B7 (Coates–Wiles, Wiles) | `BSDCoatesWilesRankZeroAttempt.lean`, `BSDWilesModularityAttempt.lean` | YES (Prop anchor) | NO — encoded hypotheses |
| **B8 (Wave 53F sandwich)** | **`BSDRankZeroFullArgumentAttempt.lean`** | YES | NO — `MordellWeilRankZeroOf := True` |
| **53G modular `a_p` agreement** | **`BSDModularFormAnAgreementAttempt.lean`** | YES | 18 numerical matches, not Wiles |
| X1 (28 α-invariants) | `AlphaInvariantsAlgebra.lean` family | YES | algebraic only |
| X3 (Galois action) | `CrossQuadraticFieldBridge.lean` | YES | structural |
| X4 (discriminator) | `GaloisOrbitMillenniumDiscriminator.lean` | YES | structural |
| X5 (rigid cond. discharge) | `GaloisRigidConditionalDischarge.lean` | YES | conditional |
| X6 (RH single conjecture) | `RHConditionalDischargeViaGaloisRigidity.lean` | YES | NO (one open Prop) |
| X8 (4-axis taxonomy) | `RHHodgeRigidTwistedGaloisBridge.lean`, `NSYMBSDTranscendentalRatioBridge.lean`, `PNPRHRigidByQuadraticBridge.lean`, **`RigidGaloisNormAxis.lean`** | YES | structural only |
| 47F gap manifest | `PolylogConjectureAttemptWave47.lean`, `BSDLFunctionEvaluationAttempt.lean` | YES | conditional + gap doc |
| Composite empirical P≠NP | `PNPDischargeViaEmpiricalCH2.lean`, `PNPUnconditionalDischargeAttempt.lean` | YES | conditional; explicitly NOT a discharge |

**Bottom line**: every numbered claim above either (a) discharges nothing, (b) is empirical/numerical, (c) is conditional on a named Prop, or (d) is structural Galois/algebraic packaging. No Clay-grade discharge anywhere.

---

## 3. Sharpest honest status and Wave 55 proposals

### 3A. P vs NP

**Sharpest status**:
- Discharge of `PolylogEigenvalueConjecture` on the opaque `alpha_of_class` is logically equivalent to a proof of `ClassP ≠ ClassNP` (Wave 41B no-go, `AlphaOfClassNoGoSingleCitation.lean`). Conditional chain is referee-readable; the conjecture itself is the open content.
- Reformulated B-clean phase identity `π/(10α) = (1/5)(π/2 − Im R_f_principal(α))` for `α > 1/2` is an axiom-free THEOREM (`BCleanPhaseIdentity.lean`, `polylog_resonance_holds`). This is the *surviving* content of (C1) after the spectral refutation.
- Composite empirical bound `10⁻⁵⁵` (= 10⁻⁴⁰ × 10⁻¹⁵) dominates 5σ by 48 orders of magnitude (`PNPDischargeViaEmpiricalCH2.lean`); still routes through `EmpiricalCH2Postulate`.

**Wave 55 proposal (P vs NP)** — **decouple the conjecture from `alpha_of_class`**:
Build a `PolylogEigenvalueConjecture'` parameterised over an arbitrary `f : Set Language → ℝ` *equipped with a typed witness* `f ClassP = √2 ∧ f ClassNP = φ + 1/4`, and prove the contrapositive chain in the new parameterisation. Cite: Wave 47B orthogonality decomposition (`PolylogConjectureAttemptWave47.lean`, halves `polylog_half_P_of f` and `polylog_half_NP_of f`) — extend each half to a *sub-Prop* whose witness does NOT collapse to `ClassP ≠ ClassNP`. The target is a strictly weaker open subgoal that survives the Wave 41B no-go. Citation traceable to file lines `PolylogConjectureAttemptWave47.lean §B` and `AlphaOfClassNoGoSingleCitation.lean`.

### 3B. BSD

**Sharpest status**:
- `φ/e` bracket holds rank-blind on three curves; `a_p` matches LMFDB at 9 + 11 primes; conductors anchored; partial-`L` evaluated; oscillation pinned to `p ∈ {41, 53}`; Wave 53F two-sided sandwich brackets `L(E_{32.a3}, 1)` between `L_partial(31)` and `L_partial(97)` with `p=41` near-hit < 0.001.
- Wave 47F gaps G3, G4, G5 untouched. `MordellWeilRankZeroOf E := True`; per-curve BSD predicate still a placeholder.

**Wave 55 proposal (BSD)** — **first non-trivial Mordell–Weil rank Prop on `E_{32.a3}`**:
Replace `MordellWeilRankZeroOf E_rank_zero := True` with a `Prop` carrying explicit content: `∀ P Q : E_rank_zero.Points, ∃ n m : ℤ, ¬(n = 0 ∧ m = 0) → n • P + m • Q = 0`. Use the LMFDB-derived torsion structure (`E_{32.a3}(ℚ)_tors = ℤ/2 × ℤ/2`) — torsion is finite and computable. Then chain (a) Wave 53F sandwich → `L(E_{32.a3},1) ≠ 0`, (b) Wave 51G Coates–Wiles `Prop`, (c) the new typed `Prop` to get `rank = 0` at the framework level **without** mathlib `WeierstrassCurve.rank`. Citation: file `BSDRankZeroFullArgumentAttempt.lean §1` (sandwich) + `BSDCoatesWilesRankZeroAttempt.lean` + LMFDB 32.a3 torsion table. This is Clay-distance-reducing (typed conclusion instead of `True`).

### 3C. Cross-Millennium props

**Sharpest status**:
- Four-axis rigid-normalisation taxonomy (50H summand / 51H divisor / 52H quadratic / 53H Galois-norm) complete; six cross-Millennium bridges, first triple-Millennium bridge (51H NS/YM/BSD).
- Wave 45C reduces RH to a single open analytic Prop on `wave38Substrate`. Wave 43C cross-sector cascade `YM-rigid ⇒ P-realisation` axiom-free.
- Wave 41B no-go forbids unconditional discharge of any twisted-sector α via concrete `f`.

**Wave 55 proposal (cross-Millennium)** — **fifth structural axis: GALOIS DISCRIMINANT**:
Extend the 53H Galois-norm axis to a `disc(α) := (α − σα)² ∈ ℚ` invariant. For the twisted-sector α's:
- `disc(α_P) = (√2 − (−√2))² = 8`
- `disc(α_Hodge) = (φ − (1−φ))² = (2φ−1)² = 5`
- `disc(α_NP) = ((φ+1/4) − (5/4−φ))² = (2φ − 1)² = 5`

Yields rational fingerprint `(8, 5, 5)`; the equality `disc(α_Hodge) = disc(α_NP)` is a NEW structural identity tying Hodge to NP through Galois discriminant (companion to the 53H norm fingerprint `(−2, −1, −11/16)`). Trace: `RigidGaloisNormAxis.lean §1` (the norm computation pattern), plus Wave 41A orbit data in `CrossQuadraticFieldBridge.lean`. Produces a fifth axis-of-rationality theorem and a new Hodge↔NP √5-discriminant equality. Honest scope: STRUCTURAL; does not discharge any Millennium problem.

---

## 4. Adversarial review

### 4A. Wave 53F BSD rank-zero sandwich (`BSDRankZeroFullArgumentAttempt.lean`)

**What it proves (axiom-free)**: `L_partial(31) < L(E,1) < L_partial(97)` with both endpoints strictly positive, `L(E,1) = 65551/100000` as the LMFDB anchor in the open interval, near-hit at `p=41` within 0.001.

**Adversarial objections**:
1. **The LMFDB anchor is a numerical constant, not a proven value of any L-function.** The "sandwich" brackets a hardcoded rational against two truncated Euler products. The reader is being asked to accept `L(E_{32.a3}, 1) = 65551/100000` on faith. If LMFDB is wrong by 10⁻⁴, the sandwich still holds — and provides ZERO information about the *actual* `L(E, 1)`.
2. **The partial Euler-product does NOT converge to `L(E, s)` at `s = 1`.** `L(E, s)` is on the edge of the convergence region (`Re s > 3/2` for absolute convergence). Truncating at primes ≤ 31 or ≤ 97 and getting a number near LMFDB's `0.65551` is consistent with anything from oscillatory non-convergence to spurious agreement. Wave 51F's own non-monotone finding admits this.
3. **`MordellWeilRankZeroOf E := True`.** The "conclusion" of the most complete structural rank-zero chain is a tautology. The entire structural content is in the routing — but the routing terminates in `True`, so by Lean's standards the theorem proves nothing about the actual Mordell–Weil rank.
4. **Coates–Wiles is an encoded `Prop`, not a theorem.** The chain `sandwich → L ≠ 0 → CM + L≠0 → rank=0` requires Coates–Wiles 1977 as input. The file inputs it as a hypothesis. Modulo a hypothesis = conditional, not unconditional.
5. **The `p=41` "near hit" within 0.001 is overstated.** A non-monotone oscillating sequence will accidentally come within 0.001 of any fixed value somewhere; without a convergence rate this proves nothing about `L(E, 1)`.

**Verdict**: Wave 53F is structural Lean plumbing of significant elegance, but is HONEST ONLY IF the manuscript states explicitly that the sandwich (a) accepts the LMFDB anchor as a numerical postulate, (b) does not prove convergence of the partial product, and (c) terminates in a `True`-shaped conclusion that the framework does NOT yet upgrade to a typed Mordell–Weil rank. The file's own `## Honest scope` does state these — credit where due — but the headline "TWO-SIDED SANDWICH 0 < L_partial(31) < L(E,1) < L_partial(97) + ... most complete rank-zero chain" risks being read as a BSD step rather than as a referee-checkable plumbing exercise.

### 4B. Wave 53G modular-form `a_p` agreement (`BSDModularFormAnAgreementAttempt.lean`)

**What it proves (axiom-free)**: 18 concrete LMFDB-hand-encoded `a_p` matches against the Wave 49C elliptic `a_p` table on `E_{32.a3}` (8 good primes after dropping bad `p=2`) and `E_{37a1}` (10 primes).

**Adversarial objections**:
1. **Hand-encoded `bSeq` is a hardcoded if-then-else table.** Both the modular and elliptic sides are decidable point-counts on the *same* curve viewed two ways; the agreement is a tautological identity at each verified prime once you've copied LMFDB twice.
2. **No structural connection between modular and elliptic sides.** Wiles 1995 says EVERY elliptic curve over ℚ is modular; the agreement of `a_p` at finitely many primes is a NECESSARY consequence, not a SUFFICIENT one. 18 matches do not lift to a modular form companion — `ModularFormCompanion := True` is still a placeholder.
3. **The pairing logic for bad primes is glossed.** For `E_{32.a3}` at `p=2` the file drops the prime; the manuscript's "bad-prime Atkin–Lehner eigenvalue = 0" claim is asserted, not derived from a formalised newform. Similarly the modular side at `p=2` is `0` because we typed `0`.
4. **18 agreements is a small N.** Wiles's theorem requires `a_p` agreement at ALL primes (essentially); confirming 18 primes proves nothing under any classical statistical test that would distinguish modular from non-modular.

**Verdict**: Wave 53G is a careful, axiom-free, referee-readable LMFDB numerical correspondence. It is HONEST ONLY IF the manuscript states that 18 prime-matches are a finite numerical bridge, NOT a step in the modularity proof. The file's own `## Honest scope` says "10-prime concrete instantiation... NOT a proof of Wiles' theorem" — this honesty must propagate verbatim to ch24's wave-remark.

### 4C. Wave 53H rigid Galois-norm axis (`RigidGaloisNormAxis.lean`)

**What it proves (axiom-free)**: Galois norms `N(α_P) = −2`, `N(α_Hodge) = −1`, `N(α_NP) = −11/16` ∈ ℚ; seven cross-norm identities ∈ ℚ; sign uniformity `N < 0` across twisted sector.

**Adversarial objections**:
1. **Galois norm is a textbook operation.** For α ∈ a quadratic extension K/ℚ with non-trivial automorphism σ, `N_{K/ℚ}(α) := α · σ(α) ∈ ℚ` is the standard field-theoretic norm. The "discovery" `N(φ) = −1` is just `φ(1−φ) = −1`, a 17th-century identity (Fibonacci's `φ² = φ + 1`). The "discovery" `N(√2) = −2` is `√2 · (−√2) = −2`. These are not new facts.
2. **Selection bias on which σ.** For `α_P = √2` the operation `√2 · (−√2) = −2` requires choosing `σ = σ_{√2}` over `ℚ(√2)`; for `α_NP = φ + 1/4` the operation `(φ + 1/4)(5/4 − φ)` requires `σ = σ_{√5}` over `ℚ(√5)`. These are DIFFERENT Galois automorphisms of DIFFERENT subfields. Comparing `−2` (output of `σ_{√2}`) with `−11/16` (output of `σ_{√5}`) as a "cross-Millennium signature" is comparing apples to oranges unless both are viewed inside `Gal(ℚ(√2,√5)/ℚ) ≅ (ℤ/2)²`. The file does view them inside `(ℤ/2)²`, but the cross-identities `N(α_P) · N(α_NP) = 11/8` mix the action of `σ_{√2}` on α_P with `σ_{√5}` on α_NP; this is a product of two coordinate-norms, not a single field-norm of a single element.
3. **Sign uniformity `N < 0` across twisted sector is a 3-element coincidence.** `N(√2) = −2 < 0` because `√2 · (−√2) < 0`; `N(φ) = −1 < 0` because `φ · (1−φ) < 0` since `φ > 1 > 1−φ` and `1 − φ < 0`; `N(φ + 1/4) < 0` follows the same Fibonacci-style identity. The uniformity is a consequence of `α > σα` and `σα < 0` for one factor, which holds for these particular three α's but is not a structural Galois statement.
4. **"FOURTH axis" framing is editorial.** The file frames itself as completing a four-axis taxonomy (50H SUMMAND / 51H DIVISOR / 52H QUADRATIC / 53H GALOIS NORM). The "axes" are different elementary operations (subtraction, division, squaring, multiplying-with-conjugate). Calling them "axes" of a "structural taxonomy" is post-hoc organisation; nothing forces these four operations as the canonical set, and operations like "trace `α + σα`" and "discriminant `(α − σα)²`" are equally natural and absent.
5. **No Millennium content.** The file's own honest scope says "STRUCTURAL. It does NOT discharge P-vs-NP, the Hodge conjecture, or any other Millennium problem." Confirmed.

**Verdict**: Wave 53H is axiom-free Lean packaging of standard quadratic-field Galois-norm facts. It is HONEST as long as the manuscript propagates the file's "structural, not a discharge" statement. The "fourth axis" framing should be downgraded to "fourth elementary Galois operation on the twisted α-sector"; the cross-Millennium signature `(−2, −1, −11/16)` is a referee-citable rational fingerprint but it is not a step toward solving any of P / Hodge / NP. The Wave 55 proposal in §3C (Galois discriminant as a fifth elementary operation, yielding the new `disc(α_Hodge) = disc(α_NP) = 5` Hodge–NP identity) sits in the same honest space — and surfaces a NEW equality the 53H axis misses.

---

## 5. Summary

- **P vs NP**: every Lean theorem in scope is conditional, refutational, numerical, or empirical. No Clay-grade discharge. Wave 41B no-go is the binding constraint.
- **BSD**: framework architecture is complete through Wave 53F; per-curve discharge would require typed Mordell–Weil rank Props (Wave 55 proposal §3B). Wave 47F G3–G5 gaps untouched.
- **Cross-Millennium**: four-axis taxonomy is structural rational-fingerprinting, not Millennium-discharging. Fifth-axis (Galois discriminant) Wave 55 proposal §3C would add the new Hodge↔NP equality `disc = 5`.
- **All three Wave 53 deliverables (F/G/H)** are axiom-free, referee-readable, and HONESTLY SCOPED in their own headers. The risk is downstream manuscript propagation overstating "sandwich" or "fourth axis" as discharge-adjacent rather than as plumbing.
