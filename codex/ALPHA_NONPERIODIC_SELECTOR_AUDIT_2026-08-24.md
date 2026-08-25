# PRINCIPIA FRACTALIS — α-NONPERIODIC SELECTOR AUDIT

**Date:** 2026-08-24
**HEAD:** `2533ddaf` (r322 landing, local; `origin/master` at `9fae5cac`)
**Companion to:** `codex/I9_TERNARY_BRANCH_FACTOR_ORIGIN_AUDIT_2026-08-24.md`, `codex/R220_R222_LOG_FREQUENCY_ORIGIN_AUDIT_2026-08-24.md`
**Deliverable:** the READ-ONLY audit mandated by the post-r322 directive Part VIII.

The question this document answers:

> **r322 (`omega_add_two`, `invariant_factors_through_omega_add_two`) proves that no invariant factoring through the character map `ω(α) = e^{iπα}` can distinguish α from α + 2·k. Does PF contain any canonical, α-independent invariant that IS α-selective — i.e., that lives OUTSIDE the ω / χ / σ character sector and can distinguish α from α + 2?**

If yes, that invariant plus an ω-side orbit-class characterization (like r224's `2·ℤ` or r221's `½ℤ+½ ∪ 2ℤ+1`) could compose into a genuine substrate derivation of a specific α-value.

If no, the α-skeleton's specific α-values are fundamentally external inputs; the substrate can classify orbits but cannot select representatives.

---

## 1. HEAD

`2533ddaf9bfb5b8a8fdc78f68a97ffff43ea01a6` (local); `origin/master` = `9fae5cac`.

## 2. Corpus scope

- Total PF `.lean` files: **1410** (including the just-landed r322).
- 12 candidate object classes surveyed (listed below).
- Priority areas per DIRECTIVE Part VIII: literal RH data; literal YM data; transfer operator spectra; K-theory beyond trace range; monodromy / branch data; Coxeter / geometric data; functional equations / modular; dimensions / ranks / indices; analytic invariants; bounds / interval data.

## 3. Selector criteria per DIRECTIVE Part VIII

For each candidate:
1. Is α already an input to the object's definition?
2. Does it factor through `omega(α) = e^{iπα}` (or through `chi ∘ omega`, or through `sigma`)?
3. Is it 2-periodic in α?
4. Is it even in α?
5. Can it distinguish `α = 0` from `α = 2`?
6. Can it distinguish `α = 3/2` from `α = 7/2`?
7. Is the object canonical BEFORE knowing the target α?
8. Is its connection to the RH/YM/etc. axis LITERAL or narrative?

An α-selector must satisfy (7), FAIL (1) (α should not be an input), and PASS at least one of (5) or (6) (distinguish some orbit representatives).

## 4. Candidates surveyed — table

| # | Object | File:line | α-input? | ω-factor? | 2-periodic? | Distinguishes 0 vs 2? | Distinguishes 3/2 vs 7/2? | Canonical? | Axis link |
|---|---|---|---|---|---|---|---|---|---|
| C1 | `chi_norm_unity_iff_half_or_odd_integer` (r221) | `PF/ChiNormUnity_r221.lean:~170` | No | **Yes** | Yes (r322) | No | No | Yes | RH orbit-class match (α_RH ∈ ½ℤ+½) |
| C2 | `chi_norm_three_iff_even_integer` (r224) | `PF/ChiNormLevelThree_r224.lean:134` | No | **Yes** | Yes (r322) | No | No | Yes | YM orbit-class match (α_YM ∈ 2ℤ) |
| C3 | `sigma α := logb 3 ‖χ(ω α)‖` (r212) | `PF/SigmaAbscissa_r212.lean:235` | Yes (param) | **Yes** | Yes (r240) | No | No | Yes | Abscissa function of α |
| C4 | `sin_pi_div_ten = 1/(2φ)` (H_3) | `PF/H3CoxeterOrigin.lean:~110` | No | No | N/A (α-independent) | N/A | N/A | Yes (Coxeter) | Narrative link to φ; does NOT select α |
| C5 | `eigenvalueToT α λ := 10/(π·λ·α)` | `PF/SpectralBijection.lean:~60` | **Yes (input)** | No | N/A | N/A | Yes if α ≠ 0 (parametric) | No (tool) | Tool, requires α as input |
| C6 | T3_sym spectral surjectivity attempt | `PF/T3SymCanonicalAlphaCarrierAttempt.lean` | Yes (α=3/2 hardcoded) | No | N/A | N/A | N/A | No (fixed α) | Route-C reformulation; T3 literal eigenvalues UNFORMALIZED |
| C7 | RH dimension-2 truncation `α_truncation` | `PF/RHDimensionTwoTruncation.lean:~30` | Yes (target-encoded) | No | N/A | N/A | N/A | No (chosen to fit t_1) | Engineering demo, not selector |
| C8 | `α_RH := 3/2`, `α_YM := 2` defs | `PF/CrossMillenniumSharedInvariants.lean:73,79` | N/A (defines α) | No | No | Yes (0 ≠ 2) | Yes (3/2 ≠ 7/2) | Definitional | THESE ARE THE INPUTS |
| C9 | Galois-orbit discriminator (α_RH ↔ α_NP) | `PF/IBMPeaksGaloisPair.lean` | Uses α-pair | No | No | N/A | N/A (Galois pair, not single α) | Yes (over ℚ(√5)) | Characterises PAIR, not selects α within pair |
| C10 | BSD rank / class number machinery | `PF/BSD_*.lean` | Mixed | No | No | N/A | N/A | Canonical per curve | Orthogonal to α-selection |
| C11 | YM cluster-fixing witnesses | `PF/YangMills*.lean` | Yes (input) | No | N/A | N/A | N/A | No (requires α as input) | Orthogonal to α-selection |
| C12 | α_NS = 3π/2 (transcendental) | Def in CrossMillennium; used in r221 §7 | Def input | No | No (transcendental) | Yes globally | Yes globally | Definitional | Not derived from NS problem |

## 5. Genuine α-selectors — result

**ZERO.**

No candidate simultaneously satisfies:
1. Canonical, α-independent, defined BEFORE the target α is chosen (row 7 = Yes).
2. Does NOT require α as an input (row 1 = No).
3. Does NOT factor through `ω` (row 2 = No).
4. Distinguishes α from α + 2·k for at least some α, k (row 5 or row 6 = Yes).
5. Is formalized (theorem present, not merely conjectured or open problem).

All candidates fail at least one of the five conditions. Detailed breakdown:

| Failure mode | Candidates | Interpretation |
|---|---|---|
| Fail (2) — factor through ω | C1, C2, C3 | r322 obstruction applies. Orbit-class match, not exact selector. |
| Fail (4) — α-universal (no α distinction at all) | C4 (H_3 identity) | Constant identity valid for all α; not a selector. |
| Fail (1) — require α as input | C5, C6, C7, C11 | Tool, not canonical invariant. |
| Fail (7)+(5) — definition IS the α-value | C8 | The definitions are external inputs. |
| Fail (2) partially, orthogonal to α | C9, C10 | Characterises pair / orthogonal to selection. |
| Fail (5) — transcendental input, no derivation | C12 | Definitional. |

## 6. Domain-restriction / interval candidates — result

Per DIRECTIVE Part VIII, interval bounds like `1 < α_RH < 2` or `0 < α_YM ≤ 2` are potential selectors IF independently derived.

**Findings:**

| # | Interval | Source | Independent derivation? | Verdict |
|---|---|---|---|---|
| I1 | `α_truncation = 5/(3π · 1413/100)` chosen so `t_1 = 14.13` | `RHDimensionTwoTruncation.lean:33` | **NO** — reverse-engineered from desired ζ-zero output | Target-encoded, rejected. |
| I2 | Level set `α ∈ ½ℤ+½ ∪ 2ℤ+1` for RH tier | `ChiNormUnity_r221.lean` | Not an interval, but a discrete lattice | Not an interval; already ω-factored (fails (2)). |
| I3 | Level set `α ∈ 2ℤ` for YM tier | `ChiNormLevelThree_r224.lean` | Not an interval, but a discrete lattice | Not an interval; ω-factored. |
| I4 | Implicit `1 < α_RH < 2` in some cosmology comments | Not formalized as a Lean theorem | N/A | Not a theorem; docstring narrative only. |

**No interval bound in the corpus is independently derived AND α-selective within an ω-orbit.**

## 7. Literal RH data — status

Per DIRECTIVE Part VIII priority. Does the corpus have any canonical RH-axis invariant (ζ zero location, functional equation constant, class number, regulator, ...) that distinguishes α_RH = 3/2 from α_RH + 2 = 7/2?

**NO.**

Concrete evidence:
- **Hardy 1914 first ζ-zero:** `t_1 ≈ 14.1347...` is referenced by name in `RHDimensionTwoTruncation.lean` but **not defined as a computed real**. Only bounds `14 < t_1 < 15` are asserted, and even those are used only as consistency checks.
- **Functional equation `ξ(s) = ξ(1-s)`:** Not formalized. `MillenniumRHSubstratePositionCapstone_r255.lean` treats mathlib's `completedRiemannZeta` as a black-box.
- **L-function zero data beyond ζ:** No formalization of Dirichlet, Dedekind, or Artin L-function zero data.
- **RH-side substrate invariant matching α_RH = 3/2:** None found. r221's ‖χ‖ = 1 orbit contains α_RH but also contains α = 5/2, 7/2, 9/2, ..., 3, 5, 7, ..., and does NOT select 3/2.

The only α-linked RH data in the corpus (`SpectralBijection.lean`, `T3SymCanonicalAlphaCarrierAttempt.lean`, `RHDimensionTwoTruncation.lean`) takes α as an INPUT.

## 8. Literal YM data — status

Same question for α_YM = 2 vs α_YM + 2 = 4.

**NO.**

Concrete evidence:
- **QCD Hilbert space / OS reconstruction:** Not formalized.
- **Bochner-Minlos measure `YM_BochnerMinlosR4Witness_Axiomatic`:** An axiomatic placeholder, not derived.
- **Mass-gap Δ(α):** Not defined as an α-indexed function anywhere in the corpus. Cluster-fixing witnesses (`YangMillsUniformGapViaRepulsion.lean`) work under a hypothesis of Δ > 0; they do not derive Δ nor its α-dependence.
- **Canonical H_YM operator:** Not defined. `SpectralGap.lean` discusses gap concepts abstractly without instantiating a YM Hamiltonian.

r224's ‖χ‖ = 3 orbit contains α_YM = 2 but also α = 0, 4, -2, ..., and does NOT select 2 uniquely.

## 9. K-theory beyond ℤ[1/3] — status

Per DIRECTIVE Part VIII: is any K-theoretic invariant beyond the tracial K-theory formalized?

**NO.**

Not referenced anywhere:
- `K_1(T_∞)` — absent.
- Chern character `ch_* : K_*(X) → H_*(X)` — absent.
- Atiyah-Singer style index pairing — absent.
- Bott periodicity — absent.
- Rotation algebras `A_θ` with K-theory `ℤ + θℤ` — absent.
- Crossed products `T_∞ ⋊_α G` — absent.

The tracial K-theory `τ_*(K_0(T_∞)) = ℤ[1/3]` (r123) is the ONLY K-theoretic invariant of the substrate formalized. r320 (`memZ13_ratio_ne_pi`) already ruled out ratios of `ℤ[1/3]` elements as π-carriers. There is no analogous "K-theory beyond `ℤ[1/3]`" scaffolding to derive `3/2` from.

## 10. Coxeter / geometric data — status

Per DIRECTIVE Part IX (special RH/YM question). H_3 Coxeter data (`sin(π/10) = 1/(2φ)`, `cos(π/5) = φ/2`) is CANONICAL and non-ω-factored (candidate C4). But:

- The H_3 identities are **α-independent** — they yield fixed real constants (φ, integer 10, exponents {1,5,9}), not α-values.
- The narrative connection `α_RH = 15/10 = (sum of H_3 exponents)/Coxeter number` is CITED in `H3CoxeterOrigin.lean`, but no theorem DERIVES α_RH from H_3 data non-circularly. The value `3/2` is INSERTED via `α_RH := 3/2` in `CrossMillenniumSharedInvariants.lean:73`; the "H_3 explanation" is an interpretive gloss, not a formal derivation.

**Verdict.** H_3 provides real substrate-native constants (φ, 10, exponent set) but no α-selector. Any use of H_3 to "explain" α_RH = 3/2 is currently narrative.

## 11. Interpretation

**The substrate can CLASSIFY α into orbit classes:**
- σ = 0 tier (via r221): `(½ℤ+½) ∪ (2ℤ+1)` — contains α_Poincaré, α_RH.
- σ = 1 tier (via r224): `2·ℤ` — contains α_YM (and α = 0, 4, ...).
- σ ∈ (0, 1) tier (from r212's sigma_alpha*_ne_zero_one): all irrational α (φ, √2, φ+1/4, 3π/4, 3π/2, √(2π)).

**The substrate cannot by ω/χ/σ alone SELECT a specific representative** within an orbit class. r322 formalized this obstruction generically.

**No non-ω-factored canonical selector exists elsewhere in the corpus.** Every candidate outside the ω/χ/σ sector either:
- takes α as an input (C5, C6, C7, C11),
- is α-universal (C4),
- IS the α-value definition (C8),
- is orthogonal to α-selection (C9, C10),
- is transcendental input without derivation (C12).

**Consequence.** The α-skeleton's specific α-values (α_RH = 3/2, α_YM = 2, α_Hodge = φ, α_P = √2, ...) are **fundamentally external inputs** to the current substrate. The substrate contributes:
- Orbit-class characterisations (r221, r224 for two tiers).
- 2-periodicity obstructions (r240 for σ, r322 for ω).
- Integer-tier ceilings (r241 `sigma_le_one`).

These are real substrate content. But no invariant selects the specific representative within the orbit.

## 12. Recommendation

Per DIRECTIVE Part XI. Priority order:
- (A) genuine problem-native selector breaking α → α+2 ambiguity for RH or YM
- (B) theorem connecting literal RH/YM canonical invariant to existing χ/σ orbit class
- (C) precise negative theorem proving broad, explicitly quantified class of PF invariants factors through the period-2 quotient

### Assessment

- **(A) not tractable in the current corpus.** Would require formalizing (RH) the Riemann functional equation + Hardy-Littlewood zero density with numerical bounds, or (YM) the QCD Hilbert space + mass-gap Δ(α) as an α-indexed function. Both are Clay-grade research.
- **(B) not tractable.** Same underlying obstacle — no literal RH/YM invariant is formalized to bridge to.
- **(C) already accomplished.** r240 (σ side) + r322 (ω side) together give the generic negative theorem: any invariant factoring through `ω` or `sigma` is 2-periodic in α. Extending this to "every corpus χ-based invariant" would be an enumeration exercise, not new mathematics.

### **Recommendation: NO NEW THEOREM.**

Per DIRECTIVE Part XI's own filter (rejecting redundant or too-weak theorems), the current best move is:

**PRIMARY — Semantic reconciliation only.** Document the α-skeleton status honestly in the codex-level status ledger:

- α_RH = 3/2 is currently an **external input** (definition in `CrossMillenniumSharedInvariants.lean:73`), consistent with a substrate orbit-class match (r221's ‖χ‖ = 1 tier) but not selected by any substrate invariant. Selecting 3/2 requires either a literal RH invariant (not formalized) or an intrinsic non-ω substrate object (not present).
- α_YM = 2 is currently an **external input** (line 79), consistent with r224's ‖χ‖ = 3 tier but not selected by any substrate invariant. Selecting 2 within `2·ℤ` currently uses I7 + Perelman anchor, both of which trace to external inputs.
- The five other rational-orbit-forbidden α's (α_Hodge = φ, α_P = √2, α_NP = φ+1/4, α_BSD = 3π/4, α_QG = √(2π), α_NS = 3π/2) are **external inputs** with no substrate orbit-class characterisation at all (all irrational, all miss r221 and r224 tiers).

No new Lean theorem is required to document this state; the theorems (r240 `sigma_add_two_int`, r322 `omega_add_two_int`, r221, r224, r212's `sigma_alpha*_ne_zero_one`) already say it.

### Optional — enumeration lemma

If a small landing is desired to make the enumeration explicit in Lean, the smallest non-circular candidate is:

```lean
/-- **α-skeleton substrate orbit-class summary (r322 corollary).**  Each of the
9 canonical α-values either sits in an r221/r224 orbit-class (α_Poincaré, α_RH,
α_YM) or is irrational and misses all rational orbit classes (α_Hodge, α_P,
α_NP, α_BSD, α_QG, α_NS).  In neither case is the specific real value selected
by any invariant factoring through `omega`. -/
theorem alpha_skeleton_substrate_orbit_summary :
    (‖chi (omega α_Poincare)‖ = 1) ∧
    (‖chi (omega α_RH)‖ = 1) ∧
    (‖chi (omega α_YM)‖ = 3) ∧
    (‖chi (omega α_Hodge)‖ ≠ 1 ∧ ‖chi (omega α_Hodge)‖ ≠ 3) ∧
    (‖chi (omega α_P)‖ ≠ 1 ∧ ‖chi (omega α_P)‖ ≠ 3) ∧
    (‖chi (omega α_NP)‖ ≠ 1 ∧ ‖chi (omega α_NP)‖ ≠ 3) ∧
    (‖chi (omega α_BSD)‖ ≠ 1 ∧ ‖chi (omega α_BSD)‖ ≠ 3) ∧
    (‖chi (omega α_QG)‖ ≠ 1 ∧ ‖chi (omega α_QG)‖ ≠ 3) ∧
    (‖chi (omega α_NS)‖ ≠ 1 ∧ ‖chi (omega α_NS)‖ ≠ 3)
```

Each conjunct exists already in r221/r224/r212 — this would just bundle them. Type C in DIRECTIVE terms. Whether this is worth landing is a stylistic choice; the substantive content is already proved.

### Rejected recommendations

- **Any theorem assuming `1 < α_RH < 2` or `0 < α_YM ≤ 2`.** No independent derivation of such bounds exists. Would be circular per DIRECTIVE Part XI.
- **Formalizing ζ functional equation.** Real research; not "smallest testable" and beyond current infrastructure scope.
- **Formalizing YM mass gap Δ(α).** Clay-grade.
- **Any "α-selector := smallest positive representative"** rule. Not justified by any substrate principle.
- **A theorem defining a new invariant that equals α_RH or α_YM.** Explicitly forbidden per DIRECTIVE Part X.

## 13. Status lock

Per DIRECTIVE Part XII:

| Result | Status |
|---|---|
| r128 conditional one-anchor rigidity | PROVED |
| Structural-law provenance | 0/8 laws intrinsically PF-derived |
| r320 trace-range ratio for L5 | FORMALLY RULED OUT |
| r220/r222 phase frequency uniqueness from base | REVOKED (r321) |
| Transcendental-carrier audit | 0 class-A/B π-generators formalized; ω-inversion candidate REVOKED |
| I9 substrate bridge — YM side | PARTIAL via r224 (orbit-class match, r322 ambiguity) |
| I9 substrate bridge — RH side | MISSING |
| r240 σ period-2 | PROVED |
| **r322 ω period-2 + factorisation obstruction** | **PROVED (this landing)** |
| **Genuine α-nonperiodic selector in corpus** | **NONE (this audit)** |
| α_RH = 3/2 selection within ½ℤ+½ ∪ 2ℤ+1 orbit | EXTERNAL INPUT (definition) |
| α_YM = 2 selection within 2·ℤ orbit | EXTERNAL INPUT (definition) |

**Present frontier.** The substrate can CLASSIFY α into orbit classes (r221, r224, r241 ceiling). The substrate cannot by any ω-factoring invariant SELECT a specific representative within an orbit. r240 + r322 formalize this obstruction generically.

**Consequence for the α-skeleton architecture.** The α-skeleton's specific α-values are external inputs. r128 rigidity + orbit-class characterisation + external anchors (Perelman, definitional) together give the current mathematical status. No substrate mechanism currently selects the specific reals `3/2`, `2`, `3/2 · 2 = 3`, `φ`, `√2`, etc.

---

## Summary

Twelve candidate object classes surveyed. **Zero canonical, α-independent, non-ω-factored, α-selective, formalized invariants exist in the corpus.**

Every candidate fails at least one of the selector criteria:
- ω-factoring obstruction (C1, C2, C3): orbit-class match only.
- α-universal (C4 H_3 identity): does not depend on α at all.
- Requires α as input (C5, C6, C7, C11): tool, not invariant.
- Definition itself (C8): the α-values are external inputs.
- Orthogonal to α-selection (C9, C10, C12).

No literal RH invariant (formalized ζ FE, class number, computed zero) exists. No literal YM invariant (formalized mass gap, canonical H_YM) exists. No K-theory beyond `ℤ[1/3]` is formalized. No independently derived interval bound exists.

**Recommended landing (READ-ONLY; NOT implementing):** NO NEW THEOREM. Semantic reconciliation only — document that the specific α-values `3/2`, `2`, φ, √2, φ+1/4, `3π/4`, `3π/2`, √(2π) are currently external inputs to the substrate, with r221/r224/r212 providing orbit-class matches (rational tiers only) and r240/r322 providing the 2-periodicity obstruction. All content is already in the kernel; the reconciliation is at the codex/status-ledger level.

**Optional enumeration lemma** (Type C bundle): `alpha_skeleton_substrate_orbit_summary` — bundles r221/r224/r212's existing per-α facts into a single 9-conjunct summary theorem. Type C in DIRECTIVE terms. Content is not new.

**Rejected:** any interval restriction (`1 < α_RH < 2`, etc.) lacking independent derivation; any new function defined to equal α_RH or α_YM; any "smallest positive" rule.

**Correct scientific status.** The α-skeleton's specific α-values are fundamentally external inputs to the current substrate. r220 + r212 + r224 + r221 characterise the ORBIT CLASSES; r240 + r322 characterise the corresponding periodicity OBSTRUCTIONS to selection. Neither literal RH data nor literal YM data is formalized to a level that could bridge to specific α-values. The substrate CLASSIFIES; it does not currently SELECT.

**Not implementing without your authorization.** Per DIRECTIVE Part XI.10: STOP after producing this audit.

---

**End of audit.**
