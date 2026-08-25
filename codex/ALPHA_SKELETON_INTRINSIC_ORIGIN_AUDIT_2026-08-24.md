# PRINCIPIA FRACTALIS — α-SKELETON INTRINSIC-ORIGIN AUDIT

**Date:** 2026-08-24
**HEAD:** `7509accdb89b69e7aebb8bf443e37be63ab463b5` (r319 on origin/master)
**Deliverable:** the READ-ONLY intrinsic-origin audit mandated by the post-r319 directive. No mathematical definitions modified. No new proof wrappers created. No theorem attack started.

The question this document answers:

> **Is there any object already present in Principia Fractalis from which one or more canonical α-values can be derived WITHOUT placing those α-values, equivalent equations, or selected spectra into the construction?**

Sharpening the earlier "does the substrate produce the α-values?" question with the r123-post distinction between (a) *relations among assigned α's* and (b) *intrinsic derivation of α's*.

---

## 1. HEAD

`7509accdb89b69e7aebb8bf443e37be63ab463b5`

## 2. Surviving exact α-skeleton relations (kernel-proved)

The nine α-values, all `def` in `PF/CrossMillenniumSharedInvariants.lean`:

```
α_Poincaré = 1        α_Hodge = φ           α_BSD = 3π/4
α_P        = √2       α_NP    = φ + 1/4     α_NS  = 3π/2
α_YM       = 2        α_RH    = 3/2         α_QG  = √(2π)
```

The ELEVEN base invariants (from `CrossMillenniumSharedInvariants.lean` §§ 95–208), all kernel-verified:

| # | Invariant | Kernel proof method |
|---|---|---|
| I1 | `α_P² = α_YM` | `unfold + norm_num` |
| I2 | `α_RH² = 9/4` | `norm_num` |
| I3 | `α_QG² = 2π` | `unfold + Real.sq_sqrt` |
| I4 | `α_Hodge² = α_Hodge + 1` | `φ` identity |
| I5 | `α_NS = 2·α_BSD` | `ring` |
| I6 | `α_NS = α_YM · α_BSD` | `ring` |
| I7 | `α_YM = α_Poincaré + 1` | `norm_num` |
| I8 | `α_RH · α_NS = α_NS + α_BSD` | `ring` |
| I9 | `α_RH · α_YM = 3` | `norm_num` |
| I10 | `α_NP − α_Hodge = 1/4` | `ring` |
| I11 | `α_QG² = α_YM · π` | consequence of I3 |

**All 11 are TRIVIALLY DEFINITIONAL** (unfold + ring on the α-defs). They are *consequences of the definitions*, not constraints forcing the definitions.

**r124's redundancy discoveries** (`AlphaWebDegreesOfFreedom_r124.lean`):
- I2 is redundant given {I3, I11, I9}.
- I8 is redundant given {I3, I11, I9, I5}.
- The 11 invariants have **9 unknowns and Gröbner-effective rank 8** → **1-parameter family** with `α_BSD` as the free parameter.

## 3. Every known proposed α-generation mechanism

Complete list from the corpus survey:

| # | Mechanism | Source | Kernel-verified? |
|---|---|---|---|
| M1 | 9 extremal tracial states of `π(T_∞)″` ↔ 9 α-values | r26 Conjecture 8.X.2 | **FALSIFIED** by r113+r123 (`no_nine_distinct_tracial_states`) |
| M2 | K-theoretic membership `α ∈ ℤ[1/3] = τ_*(K_0(T_∞))` | r123.A | Kernel-verified; **excludes 7 of 9 α-values** |
| M3 | Substrate spectral realizability | r123.B (`substrate_level_realizes_arbitrary_spectrum`) | Kernel-verified; realizes ANY real vector |
| M4 | Unique tracial state of `T_∞ = 3^∞` UHF factor | r113 (`substrate_UHF_trace_unique`) | Kernel-verified; **singleton**, not nine |
| M5 | `π/10 ↔ H_3` universal coupling `λ_0(α)·α = π/10` | r123.D + `H3CoxeterOrigin` | Identity `sin(π/10)=1/(2φ)` holds; but coupling **holds for every α** |
| M6 | Bare ternary reality condition on `G_3(e^{iπα})` | r123.F | Kernel-verified; forces `α ∈ ℤ[1/3]` (same exclusions as M2) |
| M7 | H_3 exponent set {1, 5, 9} + Coxeter number 10 organize α-skeleton | r25 + `H3CoxeterOrigin` | Individual identities kernel-verified; **unification via 9-trace bijection refuted** by r123 |
| M8 | Perelman anchor cascade: `α_Poincaré = 1 → …` | r126–r128 | Kernel-verified; **conditional** on 8 structural laws + 3 corpus invariants |
| M9 | Galois trace/norm structure over `ℚ(√5)`, `ℚ(√2)` | r125 | Kernel-verified; **descriptive of assigned constants** |
| M10 | Substrate oscillator abscissa `σ(α) = log_3|1 + 2cos(πα)|` | `SubstrateOscillator_r223` | Kernel-verified; `σ` is a FUNCTION OF α, not an intrinsic value |
| M11 | Transfer matrix Cauchy bound `‖A(m,n)‖ ≤ …` | `TransferMatrixCauchy_r186` | Kernel-verified; parameters are inputs |
| M12 | Polylog eigenvalue identity NP → `α_NP = φ + 1/4` | `EigenvalueIdentityNP` | **Conditional** on unproved polylog sign-change + Jonquières monodromy; `z_book_NP := exp(iπ(φ+1/4))` inserts α_NP definitionally |
| M13 | B-clean phase monodromy | `BCleanPhaseIdentity` | Relates α to monodromy quantity; **does not determine α** |
| M14 | IBM peaks Galois pair `4a² − (9+2√5)a + (9+6√5)/2 = 0` | `IBMPeaksGaloisPair` | Kernel-verified; both α_RH, α_NP defined outright and confirmed as roots |
| M15 | 4-basis generator `{1, π, φ, √2}` combinations | `AlphaBasisGenerators` | Basis is intrinsic; **combination assignment stipulated** |

## 4. Classification A–G

| ID | A intrinsic | B conditional | C rigidity of assigned | D definitional | E encode-and-recover | F non-selective | G falsified |
|---|---|---|---|---|---|---|---|
| M1 | | | | | | | ✓ |
| M2 | | | | | | | ✓ (excludes) |
| M3 | | | | | | ✓ | |
| M4 | | | | | | | ✓ (uniqueness) |
| M5 | | | | | | ✓ | |
| M6 | ✓ (but negative) | | | | | | (yields M2 exclusions) |
| M7 | | | | | ✓ | | (via r123 refutation of 9-trace) |
| M8 | | ✓ | ✓ | | | | (requires anchor) |
| M9 | | | ✓ | ✓ | | | |
| M10 | | | ✓ | | | ✓ | |
| M11 | | | | ✓ | | | |
| M12 | | ✓ | | ✓ | ✓ | | |
| M13 | | ✓ | | | | ✓ | |
| M14 | | | ✓ | ✓ | | | |
| M15 | | | | ✓ | ✓ | | |

**Zero mechanisms in column A that positively derive an α-value.** M6 is intrinsic but delivers only an *exclusion*.

## 5. Explicitly circular routes

- M12 (`EigenvalueIdentityNP`): `z_book_NP := exp(I·π·(φ + 1/4))` inserts α_NP into the definition, then "recovers" α_NP as the argument of z. Classic encode-and-recover. Documented in `codex/ALPHA_NP_DERIVABILITY_2026-07-25.md` as Circle 1.
- M14 (IBM peaks Galois pair): both `alpha_RH` and `alpha_NP` are `noncomputable def` outright; the joint quadratic is CONFIRMED to vanish on them (post-hoc structural fact), not derived from them.
- M15 (basis generators): `α_QG := √(2π)` is presented as "radical × √π" — the combination is CHOSEN because it equals the pre-declared α_QG; no derivation of why THIS combination is the QG-class α rather than any other.
- The α-skeleton's "9-of-9 rigidity" claim in codex materials: proved by `unfold α_NP α_Hodge; ring` on `α_NP − α_Hodge = 1/4`. `codex/ALPHA_NP_DERIVABILITY_2026-07-25.md` documents THREE closed loops in the α_NP derivation.

## 6. Explicitly falsified routes

- M1 (nine extremal tracial states): FALSIFIED by r113 + r123. `T_∞` has ONE tracial state; `no_nine_distinct_tracial_states` is a kernel-clean proof.
- M4 as an α-selector: FALSIFIED — single tracial state gives no partition into 9.
- M7 as unification: FALSIFIED — the four-facet 9-count architectural claim was tied to nine tracial states which don't exist. Individual arithmetic pieces remain valid.
- α-skeleton gauge invariance under `α ↦ α + 2` (the framework's own resonance-phase symmetry): FALSIFIED by `alpha_P_sq_eq_alpha_YM_not_mod_two_invariant` (r123.E).

## 7. Genuinely intrinsic candidates

**None deliver a positive derivation of any α-value.**

The genuinely intrinsic pieces that DO exist:

- **H_3 arithmetic** — `H_3_Coxeter_number = 10`, exponent set `{1, 5, 9}`, exponent gap = 4, `sin(π/10) = 1/(2φ)`. These are real classical mathematics (`Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic` + `H3CoxeterOrigin`). They intrinsically produce the constant **φ** (as icosahedral quadratic irrational) and the integer **1/4** (as reciprocal of the exponent gap).
- **Base-3 substrate K-theory** — `τ_*(K_0(T_∞)) = ℤ[1/3]` intrinsically. Contains 1 and 2 (namely α_Poincaré and α_YM) and excludes all 7 other α-values.
- **Base-3 rank-2 period-2 count** — `|Fin 3 × Fin 3| = 9`. Intrinsic combinatorial fact.
- **Ternary reality condition** (M6) — intrinsically forces `α ∈ ℤ[1/3]` via `G_3(e^{iπα})` reality. Independent K-theoretic corroboration.
- **Perelman anchor** — `α_Poincaré = 1` from an EXTERNAL SOLVED Millennium result (Perelman 2003). Not PF-substrate-intrinsic; classical mathematics.

The pattern: **PF has real intrinsic pieces, but none of them positively selects an α-value from a canonical construction.**

## 8. α-skeleton dependency graph (kernel-proved edges)

Nodes: nine α-values. Edges: kernel-proved algebraic equations relating them.

```
                        α_Poincaré = 1   (external anchor: Perelman 2003)
                              │
                     I7: +1   │
                              ▼
                         α_YM = 2 ─────── I1 (√·) ────► α_P = √2
                          │
                  I9: /   │  ─ I6 ────► α_BSD = 3π/4 ─── I5 (×2) ──► α_NS = 3π/2
                          ▼                  ▲                          │
                     α_RH = 3/2 ─── I8 ──────┘                          │
                          │                                             │
                          │ L3 (Galois trace on φ+ℚ)                    │
                          ▼                                             │
                     α_NP = α_RH − α_Hodge ────► α_NP = φ + 1/4         │
                          ▲                                             │
                          │ L1 (φ minpoly, positive root)               │
                     α_Hodge = φ                                        │
                                                                        │
                     α_QG = √(2π) ◄─── L4 (Galois norm α_YM · π) ───────┘
```

Auxiliary structural laws (assumptions, not corpus invariants):
- **L1**: `α_Hodge² = α_Poincaré · α_Hodge + α_Poincaré` (Galois minpoly of φ)
- **L2**: `α_P² = α_YM` (Galois norm on √2) — same content as I1
- **L3**: `α_Poincaré + 2(α_NP − α_Hodge) = α_RH` (Galois trace on `φ + ℚ`)
- **L4**: `α_QG² = α_YM · π` (Galois norm on √(2π)) — same content as I3+I11
- **L5**: `α_NS = α_RH · π` (**the π-scaling law**; not derived from anything)

## 9. Minimum independent seed-set analysis

**Definition.** The smallest set of α-values that must be supplied as independent seeds so that the remaining α-values are uniquely determined by (i) the eight structural laws {L1, L2, L3, L4, L5, I6, I7, I9} + (ii) positivity of every α.

### Minimum seed size = 1

**Proof (from `AlphaSkeletonUniqueness_r128.lean`, theorem `forced_from_poincare` at line 190):**

Given `α_Poincaré = 1` and the eight structural laws + positivity, the following forward cascade uniquely determines the other 8 α-values:

1. `α_YM = 2` from I7 + anchor.
2. `α_P = √2` from L2 (`α_P² = α_YM`) + positivity.
3. `α_RH = 3/2` from I9 (`α_RH · α_YM = 3`) + `α_YM = 2`.
4. `α_Hodge = φ` from L1 (positive root of `x² = x + 1`).
5. `α_NP = φ + 1/4` from L3 + `α_RH = 3/2` + `α_Hodge = φ`.
6. `α_QG = √(2π)` from L4 (`α_QG² = α_YM · π`) + positivity.
7. `α_NS = 3π/2` from L5 + `α_RH = 3/2`.
8. `α_BSD = 3π/4` from I6 (`α_NS = α_YM · α_BSD`) + `α_YM = 2` + `α_NS = 3π/2`.

### Alternative single-seed anchors

r128 §5 (`AlphaSkeletonUniqueness_r128.lean:327`) proves the analogous BACKWARD result:

- **Seed = {α_BSD = 3π/4}** + structural laws + positivity ⇒ all 9 α-values (no Perelman needed).

By symmetry of the same laws, any one of {α_Poincaré, α_YM, α_RH, α_BSD, α_NS, α_QG, α_P, α_Hodge, α_NP} would similarly suffice as a seed. The eight laws + positivity are algebraically **rigid** in the sense that they have exactly ONE positive solution (the canonical skeleton), so specifying ANY ONE α uniquely determines the other eight.

### What is NOT reducible

- The **eight structural laws** are **not substrate-derived**. They are algebraic assertions inserted alongside the α-definitions. They remain external inputs.
- **Positivity** must be asserted for at least four α-values (α_P > 0, α_Hodge > 0, α_QG > 0, and one of α_BSD/α_NS > 0).

## 10. Do exact relations uniquely determine the rest?

**Yes, from ONE seed + 8 laws + positivity.** The eight-law system is rigid in the sense proved by r128.

**But:** the eight laws are *chosen* to be exactly the equations that hold for the pre-declared α-values. This is r124's honest observation: the 11 canonical invariants form a **1-parameter family** — 8 rigid + 1 free (`α_BSD`). The r128 uniqueness result *closes* that freedom by adding L5 (the π-scaling law `α_NS = α_RH · π`), which is not among the 11 canonical invariants and not derived from anything.

**Net status:** the skeleton has *effective* dimension 1 (one seed) *after* accepting the eight structural laws as inputs; but the eight structural laws themselves are not intrinsic PF theorems — they are inserted along with the α-definitions.

## 11. Best candidate for deriving ONE seed intrinsically

Given r123's exclusion result, the *only* two α-values that could conceivably lie in `τ_*(K_0(T_∞)) = ℤ[1/3]` are:

- **`α_Poincaré = 1`**
- **`α_YM = 2`**

Both are trivial integers in K-theory (unit and 2·unit). No canonical PF invariant is currently proved to equal specifically 1 or 2 in a nontrivial way — the multiplicative identity of a C*-algebra is always 1, so saying "the substrate produces 1" is not selective.

The other seven α-values (`√2`, `φ`, `φ + 1/4`, `3π/4`, `3π/2`, `√(2π)`, `3/2`) are **PROVABLY OUTSIDE** the substrate's intrinsic invariant range. Any derivation of them requires **structure beyond the current substrate**.

### Best available candidate: derive an anchor from H_3 arithmetic

H_3 icosahedral Coxeter data intrinsically produces φ:

- `cos(π/5) = φ/2` (mathlib `Real.cos_pi_div_five`)
- `sin(π/10) = 1/(2φ)` (`H3CoxeterOrigin`)

So the constant **φ appears in PF via a genuinely-intrinsic H_3 identity, NOT via `α_Hodge := φ` insertion**.

If PF could prove that **H_3 (rather than an arbitrary rank-3 Coxeter group) is the intrinsic symmetry group of a canonical base-3 substrate object**, then `φ` would inherit intrinsic PF origin, and `α_Hodge = φ` would become a substantive derivation (up to the label assignment).

Currently NO such theorem exists. r25's "four convergent facets" of the 9-count (base-3 rank-2 = 9, H_3 top exponent = 9, Coxeter number 10, π/10 half-argument) is an **arithmetic coincidence collection**, not a proof of H_3-forcing from base-3.

## 12. Exact theorem that would constitute the next real PF breakthrough

Per DIRECTIVE Part XI: the breakthrough would be a theorem of the shape

```
theorem canonical_substrate_invariant_eq_alpha_X :
    CanonicalInvariant(T_∞) = α_X
```

with `CanonicalInvariant` defined without α_X, no coefficient chosen to encode α_X, no target spectrum inserted, no equivalent polynomial selected because α_X solves it, uniqueness proved, zero project axioms.

### The recommended specific target

**`theorem h_three_is_substrate_symmetry :
    SymmetryGroup(base_3_substrate) ≃ CoxeterGroup H_3`** — or the sharper form

**`theorem alpha_hodge_from_h3_intrinsic :
    ∃ (I : PF-substrate-object), Intrinsic(I) ∧ I = φ`**

where `I` does not include `α_Hodge`, φ, √5, or any polynomial whose root is φ in its definition; and `Intrinsic` means the object is canonically constructed from base-3 substrate data alone.

**Concrete route to attempt** (the most tractable of the possible next attacks):

Consider the base-3 substrate's period-2 dynamics on `{0,1,2}^ℕ`. r25 kernel-proves `basethree_period2_fixed_points.card = 9`. If the automorphism group of this period-2 fixed set (or a canonical enrichment) can be proved to *contain* or *equal* the icosahedral group `H_3` (order 120), then `φ` becomes PF-intrinsic via `cos(π/5) = φ/2` on the resulting spherical fundamental domain.

**Alternative concrete route:** prove that the transfer operator of the full 3-shift, restricted to a canonical natural subspace, has eigenvalue φ. Currently `TransferMatrixCauchy_r186` provides only bounds; a genuine spectral computation of φ from an α-free construction would qualify.

**Alternative honest-negative route:** prove a *companion no-go to r123* — that **no** canonical invariant of the current substrate equals any of the seven non-integer α-values. That would formally close the intrinsic-origin question in the negative and force PF to either extend the substrate or accept the α-web as classical inputs.

## 13. What that theorem would imply for the rest of the skeleton

Combining a substrate derivation of ANY ONE α-seed with r128's uniqueness (§9 above), all 8 remaining α-values would follow — but only *conditional* on the 8 structural laws {L1, L2, L3, L4, L5, I6, I7, I9} + positivity.

Specifically:

- Substrate derivation of `α_Hodge = φ` → via L1, I7, L2, I9, L3, L4, I6 → `(α_Poincaré, α_YM, α_P, α_RH, α_NP, α_QG, α_NS, α_BSD)` all forced.
- Substrate derivation of `α_Poincaré = 1` → r128's forward cascade → 8 others.
- Substrate derivation of `α_YM = 2` → same, since α_Poincaré = α_YM − 1.

The **π-scaling law L5** (`α_NS = α_RH · π`) is the one law with least existing motivation; it is currently the "least justified" structural assumption. A separate substrate derivation of L5 (from, say, base-3 continuum scaling) would further strengthen the architecture.

## 14. Would it affect any literal Millennium residual?

**Directly, no.** The α-skeleton is not part of the literal RH / NS / YM / BSD / Hodge / P-vs-NP statements. The Xi(15) discharge (r315), the r120 on-line zero, and the r280 countability result — the actual PF contributions to RH — do not depend on the α-skeleton at all.

**Indirectly, yes.** The α-skeleton is PF's proposed universal architecture. If ONE α is intrinsically derived from the substrate, the framework's claim "the substrate governs the cross-Millennium constants" acquires genuine content instead of remaining an assignment. That materially changes the scientific-truth valuation of every substrate-based bridge (r287–r302, `UnifiedClayClosureViaRouteBSpecificXiAndFullPinning`, etc.) in the corpus.

Conversely, if the *companion no-go* is proved (no substrate invariant equals any nontrivial α), the framework's cross-Millennium bridges have to be re-honesty-scoped: the α-skeleton is external input, and the substrate provides infrastructure but not universal constants.

Either resolution is scientifically valuable.

---

## Summary

The α-skeleton contains **eleven kernel-proved algebraic invariants** that jointly form a **1-parameter family**; adding **five auxiliary structural laws** {L1, L2, L3, L4, L5} to the corpus invariants {I6, I7, I9} yields a rigid system with **minimum seed size = 1**. Given any one α-value + positivity + the eight-law rigidity, all other eight α-values are uniquely determined.

**Zero mechanisms in the corpus positively derive any α-value from a nontrivially-canonical substrate invariant.** All substrate-side attempts are either FALSIFIED (nine-trace bijection), NON-SELECTIVE (spectral realizability, π/10 coupling), CIRCULAR (α inserted in weights/polynomials), or DEFINITIONAL (α-values inserted as `def`). The bare ternary route (M6) is intrinsic but only excludes — it does not select.

The **best candidate** for the next PF breakthrough is a theorem showing that **H_3 (icosahedral)** is the intrinsic symmetry of a canonical base-3 substrate object, which would give `φ` intrinsic PF origin via `cos(π/5) = φ/2`, and cascade via r128 to force the rest of the skeleton.

The **alternative honest-negative** would be a *companion no-go* to r123 proving that no substrate invariant equals any nontrivial α, formally closing the intrinsic-origin question in the negative.

**Not implementing either without your authorization.** Per DIRECTIVE: STOP after producing this audit.

---

**End of audit.**
