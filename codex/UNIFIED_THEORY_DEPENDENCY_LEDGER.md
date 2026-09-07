# UNIFIED THEORY DEPENDENCY LEDGER

**Opened:** 2026-09-07. **Re-keyed to the directive's seven classes:** 2026-09-07.
Machine-readable twin: `UNIFIED_THEORY_DEPENDENCY_LEDGER.json`.
**Built backward from:** `codex/COMPLETION_THEOREM_DRAFT.md`.
**Program:** `codex/UNIFIED_THEORY_PROOF_PROGRAM.md`.
**Charter:** `codex/ALPHA_RIGIDITY_AUDIT_CHARTER_2026-09-01.md` (recovered 2026-09-07;
blocker B-CHARTER closed).

Every node is load-bearing for at least one conjunct of the completion theorem
draft. Each row was read from the declaration itself, not reconstructed.

---

## CLASSIFICATION — the directive's seven classes

The A–H stand-in used in the first edition is withdrawn. All nodes are re-keyed
to the directive's classes, received 2026-09-07:

| key | class | meaning as applied here |
|---|---|---|
| **C1** | definition-or-convention | a choice. Includes values fixed by `def`, and equations that are consequences of those defs (minimal polynomials of chosen values, arithmetic on chosen numerals, target-encoded constraints) |
| **C2** | theorem-derived-from-earlier-foundations | genuine derivation from mathlib or from previously-established PF results |
| **C3** | independently-motivated-axiom | assumed, but motivated by something other than the conclusion it serves |
| **C4** | empirical-input | premised on measurement or finite-precision numerics |
| **C5** | conditional-interface | an honest `A → B` whose antecedent is stated and non-circular |
| **C6** | unresolved-conjecture | a named open problem carried as a hypothesis |
| **C7** | recorded-negative-or-refuted | an established negative result, or a claim refuted |
| **✖** | **unknown provenance — BLOCKER** | node does not exist, or origin not establishable |

Two orthogonal flags are carried alongside the class, because they are defects
rather than provenance:

- `circular` — the premise restates or contains the conclusion it serves.
- `vacuous` — the conclusion holds by construction and constrains nothing.

A node can be, e.g., C6 + circular: the Prop is a legitimate open conjecture
*and* it is being used to conclude itself.

---

## LAYER 1 — THE CONSTRUCTED UNIVERSE

| id | node | file | class | flags | note |
|---|---|---|---|---|---|
| N01 | `TimelessFieldRing` (T_∞) | `SubstrateTimelessFieldCompletion.lean` | **C2** | | Algebraic direct limit; `NormedRing`, `StarRing`, `CStarRing`, `NormedAlgebra ℂ`. Real mathematics |
| N02 | `TimelessFieldCompletion` | `SubstrateTimelessFieldCompletion.lean:82` | **C2** | | `UniformSpace.Completion TimelessFieldRing`; mathlib-native |
| N03 | C*-structure **on the completion** (r54–r57) | — | **✖** | | Listed by r53 as requiring proof, not auto-inheritance. Unconfirmed. Blocks (U1) |
| N04 | `SubstrateConfiguration` / `SubstrateEquiv` | — | **✖** | | Does not exist. No `Setoid`/`Quotient` in the substrate module. Blocks (E1) |
| N05 | `DerivedConstantFunctions` + invariance | — | **✖** | | Does not exist. Blocks (E2). The framework cannot ask whether its constants are invariants |

---

## LAYER 2 — THE α-SKELETON AND ITS CONSTANTS

### 2a. The nine values — all `CrossMillenniumSharedInvariants.lean:64–88`

| id | node | value | class | note |
|---|---|---|---|---|
| N06 | `α_Poincare` | `1` | **C1** | r216, in-kernel: "closed by `rfl`… records the numeral chosen in the definition… **not** a statement about Ricci flow… or about the Poincaré conjecture" |
| N07 | `α_RH` | `3/2` | **C1** | |
| N08 | `α_YM` | `2` | **C1** | |
| N09 | `α_P` | `√2` | **C1** | |
| N10 | `α_NP` | `φ + 1/4` | **C1** | the `1/4` is free (r124 `alpha_offset_is_free`); charter N4: the "forcing" fed φ and 1/4 in and got φ+1/4 out |
| N11 | `α_Hodge` | `φ` | **C1** | |
| N12 | `α_QG` | `√(2π)` | **C1** | |
| N13 | `α_BSD` | `3π/4` | **C1** | r124's free parameter |
| N14 | `α_NS` | `3π/2` | **C1** | |
| N14b | `α_PvNP` | `5/4` | **C1** | `PNPClassSeparationPrecisionBridge.lean:457`. A **tenth** anchor outside the 9-tuple. r128 flagged the collision: two different reals under near-identical names. Charter Q1 open |

### 2b. The eight structural laws — every one a convention

The 2026-08-24 provenance audit found **zero** intrinsic derivations. Under the
seven classes all eight are **C1**: they are consequences of the chosen values,
not independent constraints on them.

| id | law | equation | class | flags | note |
|---|---|---|---|---|---|
| N15 | L1 | `α_Hodge² = α_Po·α_Hodge + α_Po` | **C1** | | minimal polynomial of `φ` by construction; mathlib `minpoly` never invoked |
| N16 | L2 | `α_P² = α_YM` | **C1** | | minimal polynomial `x²−2` of `√2`; no substrate spectrum proved to contain `√2` |
| N17 | L3 | `α_Po + 2(α_NP − α_Hodge) = α_RH` | **C1** | | reduces to `1 + 2(1/4) = 3/2`; no bridge forces `q = 1/4` |
| N18 | L4 | `α_QG² = α_YM·π` | **C1** | | minimal polynomial of `√(2π)` |
| N19 | **L5** | `α_NS = α_RH · π` | **C1** | **SETTLED** | Was the sole narrative-only law and r124's free-parameter closer. **r332 (2026-09-07) settles it — see N19b.** Reclassified from "unsupported narrative" to C1: it is a convention, now provably not derivable on the route the corpus has |
| N20 | I6 | `α_NS = α_YM·α_BSD` | **C1** | | `3π/2 = 2·(3π/4)`; `GaugeInvariance` exists in name only |
| N21 | I7 | `α_YM = α_Poincaré + 1` | **C1** | | the assertion `2 = 1 + 1`. Most-cascading law under drop (destroys 4 α's) |
| N22 | I9 | `α_RH·α_YM = 3` | **C1** | | `(3/2)·2 = 3`. The `3` is the only constant plausibly from the base-3 substrate; no theorem links them |

### 2c. Results about the skeleton

| id | node | file | class | note |
|---|---|---|---|---|
| N23 | `alpha_skeleton_unique` | `AlphaSkeletonUniqueness_r128.lean` | **C5** | Honest conditional: rigid **given** N15–N22. Since all eight are C1, the rigidity is rigidity-given-conventions |
| N24 | `alpha_web_admits_every_positive_BSD` | `AlphaWebDegreesOfFreedom_r124.lean` | **C7** | For every `t > 0` an assignment satisfies all eleven invariants with `α_BSD = t` |
| N25 | `invariant_two/eight_is_redundant` | r124 | **C7** | Two of the eleven invariants carry no information |
| N26 | `IsIntrinsic` | — | **✖** | Does not exist. Blocks (K0), hence all of (K) |
| N27 | Perelman anchor | — | **C1** | Perelman 2002–03 is a real theorem (**C3** in itself), but it enters as `def α_Poincare : ℝ := 1`. Charter §5.7: the assignment "does not independently assign the α-value". Classified by how it enters, not by its pedigree |
| **N19b** | **`pi_not_ktheoretic_ratio` (r332)** | `AlphaL5PiScalingObstruction_r332.lean` | **C7** | **NEW 2026-09-07.** `∀ a b ∈ ℤ[1/3], b/a ≠ π`. Kernel-green, mathlib three, non-vacuity proved (r332.E). Closes L5 against the K-theoretic trace route |
| N19c | `alpha_ns_div_alpha_rh_eq_pi` (r332.D) | same | **C1** | `α_NS/α_RH = π` by `ring` after unfolding. The identity is true *of the chosen numerals* and unreachable from the invariant — the definition of target-encoded |
| N27b | Trace-range obstruction (charter N2, r113+r123) | `AlphaFromSubstrateKTheory_r123.lean:326` | **C7** | Substrate trace range is `ℤ[1/3]`; seven of nine α's lie outside it. r332 is its ratio-level completion |

**Layer 2 verdict:** no α-value is derived. All eight structural laws are
conventions. As of r332 the last of them with an open derivation question is
closed negatively. **The framework has no derived constants on the route it has.**

---

## LAYER 3 — THE CLAY SECTORS AND THEIR BRIDGES

### 3a. Statement definitions

| id | node | class | faithful? |
|---|---|---|---|
| N28 | `RiemannHypothesis` (`SpectralBijection.lean:512`) | **C2** | **YES** — literal RH on mathlib `riemannZeta` |
| N29 | `Clay_RiemannHypothesis_Standard := RiemannHypothesis` | **C2** | **YES** |
| N30–N34 | `Clay_{PvsNP,NavierStokes,YangMills,BSD,Hodge}_Standard E` | **C5** | shape faithful; **faithfulness delegated to `E`** |

### 3b. The encodings — where faithfulness is won or lost

| id | node | file | class | flags | verdict |
|---|---|---|---|---|---|
| N35 | `PF_ComplexityEncoding` | `PNPCapstoneTypedBridge.lean:41`; `TuringEncoding/Complexity.lean:106,143` | **C2** | | **Apparently faithful** — real TMs, poly bounds, Cook-1971 certificates. Blocker B-TM: `Machine`/`turingTimeComplexity` unaudited |
| N36 | `PF_NS3DEncodingV2` / `NS3DRegularitySolutionV2` | `NS3DRegularitySolutionV2.lean:142,201` | **C1** | | **NOT faithful.** 5-conjunct predicate, three conjuncts are mathlib-*availability flags*. Does not assert global-in-time smooth existence |
| N37 | `PF_YMEncodingBridge5` | `Bridge5_YM_SubstrateDischarge.lean:342` | **C1** | | **NOT faithful.** Finite-dimensional substrate model; `massGap := T.v4.v3.v2.Δ` |
| N38 | `GlimmJaffe_OS_SU2_TypedAnchor` | `:226` | **C1** | **vacuous** | `def : Prop := True` |
| N39 | `StreaterWightman_SU2_TypedAnchor` | `:243` | **C1** | **vacuous** | `def : Prop := True` |
| N40 | `OsterwalderSchrader_SU2_TypedAnchor` | `:262` | **C1** | **vacuous** | `def : Prop := True` |
| N41 | `OSRP_Compatible_Interacting_Ham_Open` | `YM_Wave56ContinuumLiftAttempt.lean:364` | **C6** | | Open by its own name |
| N42 | `PF_BSDEncodingV5` | `BSDCapstoneTypedBridgeV5.lean:193,196,305` | **C1** | **vacuous** | `algebraicRankV5 = analyticRankV5 = manuscriptRankV5`, the same function. Equality by `rfl`; returns `0` off a 20-curve list |
| N43 | `PF_HodgeEncoding` | `HodgeCapstoneTypedBridge.lean:55` | **C1** | | **NOT faithful.** Own docstring: "substrate-level only… not literal geometric algebraicity by an explicit cycle" |
| N44 | `PF_HodgeEncoding_FullGeneral` | `Voisin2007GeneralQuinticPrecision.lean:496` | **C5** | | **Genuine cycle witnesses.** The right foundation for a faithful Hodge sector; unused by the headline |

### 3c. The premise bundles

| id | node | class | flags | verdict |
|---|---|---|---|---|
| N45 | `ClayClosureBundleBulletproof` | **C6** | **circular** | Fields `rh_hp_T3sym_positive` + `rh_hp_program_positive` compose by modus ponens to the RH conclusion |
| N46 | `PF_T3SymIsHilbertPolyaOperator_Positive` | **C6** | | Named open conjecture, honestly carried |
| N47 | `HilbertPolyaProgramConjecture_Positive` | **C6** | **circular** | Content: `PF_T3Sym…_Positive → RiemannHypothesis` |
| N48 | `Mayer1991_Cohen2025_…_citation` (`:222`) | **C6** | **circular** | Definitionally equal to N47; r301 carries it a **second** time |
| N49 | `Hardy1914_…_citation` (`:172`) | **C3** | **circular (identity)** | Hardy 1914 is a genuine external theorem, so C3 by pedigree — but r301 lists `PositiveOnLineZetaZeroOrdinatesNonempty` as **conclusion (E2)** while requiring it as **hypothesis**. The theorem returns one of its own inputs |
| N50 | `PolylogEigenvalueConjecture` | **C6** | | Carries the entire P-vs-NP sector. Charter N5: three mutually inconsistent gap values unreconciled |
| N51 | `ClayClosureBundleDualCitationAggregate` (r299:116) | **✖** | | 8 fields not individually audited. Blocker B-N51 |
| N52 | `ClayClosureBundleUniversal` (r301) | **✖** | **circular** | Contains N45, N48, N49, N51 |
| N53 | Cohen 2025 numerics (self-adjointness `<1e-15` at `N≤40`; eigenvalue match, 150 digits, **five pairs**; scaling `5e-6`) | **C4** | | Evidence, not proof. Any conclusion downstream is empirical-premised |

---

## LAYER 4 — TOP-LEVEL THEOREMS

| id | node | class | flags | verdict |
|---|---|---|---|---|
| N54 | `principia_fractalis_millennium_supreme_capstone_universal_at_HEAD` (r301) | **✖** | **circular** | Valid; carries no information. Not a central-theorem candidate |
| N55 | `PrincipiaFractalisSubstrateTheorem` | **C1** | **vacuous** | Antecedent discarded (`intro _h_antecedents`); consequences independently provable |
| N56 | `SubstrateTheoremContent_r216` | **C7** | | Proves in-kernel that *any* proposition implies `PFSubstrateConsequences` |
| N57 | **CENTRAL THEOREM** | **✖** | | **UNSPECIFIED.** No declaration in the corpus is it |

---

## LAYER 5 — THE r331b CHAIN (healthy, and outside the unified-theory claim)

| id | node | class | verdict |
|---|---|---|---|
| N58 | `xi_T15_zero_count_identity_unconditional` | **C2** | Unconditional, no binders, mathlib three. Genuine. **Not RH** |
| N59 | `top15_re_lt_neg_1e4` (18-box union, FULL) | **C2** | Cover gate PASS 2026-09-07, measure exactly 1/2 |
| N60 | 18 `RiemannXiBox<K>Bridge` capstones | **C2** | All CLOSED. Weakest: box 106 at `+2.211191e-05` |
| N61 | `RiemannXiBox0Bridge` rebuild | **✖ → in progress** | Was skipped by the C1 pass. `a1_v3`'s `ensure_box0_reference` now builds it on both halves |

---

## CREDIT COLUMN

Recording what the corpus got right, because a ledger that only tallies defects
misrepresents the project.

| # | credit | evidence |
|---|---|---|
| **CR1** | **The in-file docstrings are candid — repeatedly more candid than the headline theorem names and the prose chapters.** Nearly every unfaithfulness finding in Layer 3 was *self-disclosed by the file that contains it*: the BSD bridge states "This is NOT a Clay BSD discharge for arbitrary `WeierstrassCurve ℚ`"; the Hodge bridge states "Honest scope: substrate-level only… not literal geometric algebraicity by an explicit cycle"; r128's header itemises three reasons its own predecessor's citation "does not hold". The defect is a **headline/prose problem, not concealment in the formalisation** | r216 §"This is a prose problem, not concealment"; BSD V5 honest-scope block; `HodgeCapstoneTypedBridge.lean:72-76` |
| **CR2** | The project audits itself adversarially and publishes the negatives. r124, r216, r123, the 2026-08-24 provenance audit, and this ledger's own predecessors are all PF work product | N24, N25, N56, N27b |
| **CR3** | `r216` deliberately puts the vacuity of the flagship theorem **in the kernel** so it "cannot drift back out of the prose". That is an unusual and correct instinct | `SubstrateTheoremContent_r216.lean` header |
| **CR4** | The evidence standard is real and has caught real errors: the `#print axioms`-not-RC rule caught a silently-admitted `sorry` in the endgame module on 2026-09-05 | Gate §B0 |
| **CR5** | The r331b chain is genuine unconditional analysis, correctly scoped by the corpus as *not* RH | N58–N60; gate F8 |
| **CR6** | The rigidity charter pre-registers its outcomes (§8) before running the audit, including the outcome unfavourable to the framework | Charter §8 |

---

## BLOCKERS

| id | blocker | blocks | owner | status |
|---|---|---|---|---|
| ~~B-SCHEME~~ | directive's seven classes | ledger keying | Pablo | **CLOSED 2026-09-07** — received and applied |
| ~~B-CHARTER~~ | `ALPHA_RIGIDITY_AUDIT_CHARTER` | α-rigidity section | Pablo | **CLOSED 2026-09-07** — recovered and committed |
| ~~B-L5~~ | L5 derivability | α-skeleton grounding | orchestrator | **CLOSED 2026-09-07** — r332, negative verdict |
| **B-DIRECTIVE** | full directive text not yet in `codex/` | provenance of this program's own mandate | Pablo | **OPEN** — Pablo to relay as file payload; on the orchestrator's queue |
| **B-N03** | C*-structure on the completion (r54–r57) | conjunct (U1) | orchestrator | open |
| **B-N04/05** | no equivalence relation, no invariance statement | (E1), (E2) | research | open |
| **B-N26** | `IsIntrinsic` undefined | (K0), all of (K) | research | open |
| **B-N51** | r299 aggregate's 8 fields unaudited | aggregate-route claims | orchestrator | open |
| **B-JOIN** | `SubstrateBearsOn` / `DerivationIsNonVacuous` / `AntecedentIsLoadBearing` undefined | (C), (D) — the unification claim itself | research | open |
| **B-TM** | `Machine`/`turingTimeComplexity` faithfulness | whether (S2) is the real P vs NP | orchestrator | open |
| **B-CIRC** | premise set of the top-level theorem contains its conclusion | any information content in r301 | Pablo | open |
| **B-N61** | box 0 bridge rebuild | gate B1, C1 completeness | orchestrator | **in progress** — `a1_v3` fix deployed both halves |

---

## TALLY

| class | count | note |
|---|---|---|
| **C1** definition-or-convention | 24 | includes all 9 α-values, all 8 structural laws, and 4 unfaithful encodings |
| **C2** theorem-derived | 10 | N01, N02, N28, N29, N35, N58, N59, N60 (+2) |
| **C3** independently-motivated-axiom | 1 | N49 (Hardy 1914 — but flagged circular in its use) |
| **C4** empirical-input | 1 | N53 |
| **C5** conditional-interface | 8 | N23, N30–N34, N44 |
| **C6** unresolved-conjecture | 6 | N41, N45, N46, N47, N48, N50 |
| **C7** recorded-negative-or-refuted | 6 | N24, N25, N56, **N19b**, N27b |
| **✖** blocker | 10 | |
| *flag* `circular` | 6 | N45, N47, N48, N49, N52, N54 |
| *flag* `vacuous` | 5 | N38, N39, N40, N42, N55 |

**Six of the ten C2 nodes are the substrate construction or the r331b rectangle
chain** — the latter correctly scoped by the corpus as *not* the unified theory.
**No C2 node connects layer 1 to layer 2, or layer 2 to layer 3.** As of r332 the
layer-1→layer-2 join is not merely unproved but **closed negatively** on the
route the corpus has.

---

*Re-keyed 2026-09-07 to the directive's seven classes. Nothing in this file
modifies a `.lean` file. Public HEAD `96c71da7`. NO PUSH.*
