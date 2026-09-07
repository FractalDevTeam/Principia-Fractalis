# UNIFIED THEORY DEPENDENCY LEDGER

**Opened:** 2026-09-07. Machine-readable twin: `UNIFIED_THEORY_DEPENDENCY_LEDGER.json`.
**Built backward from:** `codex/COMPLETION_THEOREM_DRAFT.md`.
**Program:** `codex/UNIFIED_THEORY_PROOF_PROGRAM.md`.

Every node below is load-bearing for at least one conjunct of the completion
theorem draft. Nodes were found by reading the declarations, not by reconstructing
them from memory; each row carries the file and, where read, the line.

---

## CLASSIFICATION SCHEME — DECLARED STAND-IN

**The directive's seven classes could not be located.** Searched: the entire
`codex/` tree and repo root on the Acer, `D:\CLAUDE-i9`, `D:\Principia-Fractalis-Repo`,
`C:\Users\psolo`. Neither the Unified-Theory Proof Directive text nor
`ALPHA_RIGIDITY_AUDIT_CHARTER` exists on any accessible filesystem.

This ledger therefore uses the corpus's own eight-code scheme, from
`codex/ALPHA_SKELETON_STRUCTURAL_LAW_PROVENANCE_2026-08-24.md` §3, which was
itself produced under an earlier directive. **If the directive's seven classes
differ, every `class` field below must be re-keyed.** That is recorded as
blocker `B-SCHEME`.

| code | meaning |
|---|---|
| **A** | intrinsic PF theorem — derived inside the framework |
| **B** | conditional — holds given a stated, non-circular hypothesis |
| **C** | rigidity of assigned values |
| **D** | definitional — the equation is the minimal polynomial of a chosen value |
| **E** | trivial arithmetic on chosen numerals |
| **F** | target-encoded — chosen because the assigned values satisfy it |
| **G** | unsupported narrative — docstring motivation, no formal counterpart |
| **H** | external classical theorem, cited |
| **∅** | **UNKNOWN PROVENANCE — BLOCKER.** Node does not exist, or its origin could not be established from the filesystem |

Per the standing rule, **`∅` is a blocker**, not a low grade.

---

## LAYER 1 — THE CONSTRUCTED UNIVERSE

| id | node | file | class | note |
|---|---|---|---|---|
| N01 | `TimelessFieldRing` (T_∞) | `PF/SubstrateTimelessFieldCompletion.lean` (imported) | **A** | Genuine algebraic direct limit; carries `NormedRing`, `StarRing`, `CStarRing`, `NormedAlgebra ℂ`. Real mathematics. |
| N02 | `TimelessFieldCompletion := UniformSpace.Completion TimelessFieldRing` | `SubstrateTimelessFieldCompletion.lean:82` | **A** | mathlib-native metric completion. `CompleteSpace`, `MetricSpace`, `Ring`, `NormedRing`, `NormedSpace ℂ` all auto-inherited. |
| N03 | `Star` / `StarRing` / `CStarRing` / `NormedAlgebra ℂ` **on the completion** | r54–r57, per r53 docstring | **∅** | Listed by r53 as work items requiring proof rather than automatic inheritance. Not confirmed present. **Blocks completion conjunct (U1).** |
| N04 | `SubstrateConfiguration`, `SubstrateEquiv` | — | **∅** | **Does not exist.** No `Setoid` or `Quotient` in the substrate completion module. **Blocks (E1).** |
| N05 | `DerivedConstantFunctions` + invariance under the equivalence | — | **∅** | **Does not exist.** **Blocks (E2).** Consequence: the framework cannot currently ask whether its constants are invariants or artefacts of representative choice. |

**Layer 1 verdict:** the construction is real and is the healthiest layer. The
equivalence relation — required for any claim that the constants are intrinsic —
is entirely absent.

---

## LAYER 2 — THE α-SKELETON AND ITS CONSTANTS

### 2a. The nine values

All at `PF/CrossMillenniumSharedInvariants.lean:64-85`, all `noncomputable def`.

| id | node | value | class | note |
|---|---|---|---|---|
| N06 | `α_Poincare` | `1` | **F** | r216 (kernel): "closed by `rfl`. It records the numeral chosen in the definition. It is **not** a statement about Ricci flow… or about the Poincaré conjecture." |
| N07 | `α_RH` | `3/2` | **F** | |
| N08 | `α_YM` | `2` | **F** | |
| N09 | `α_P` | `√2` | **F** | |
| N10 | `α_NP` | `φ + 1/4` | **F** | the `1/4` offset is a free parameter of the web (r124 `alpha_offset_is_free`) |
| N11 | `α_Hodge` | `φ` | **F** | |
| N12 | `α_QG` | `√(2π)` | **F** | |
| N13 | `α_BSD` | `3π/4` | **F** | r124: the unique maximal independent variable of the system |
| N14 | `α_NS` | `3π/2` | **F** | |

### 2b. The eight structural laws

Classifications taken verbatim from the corpus's own provenance audit, which
found **zero laws of class A**.

| id | law | equation | class | note |
|---|---|---|---|---|
| N15 | L1 | `α_Hodge² = α_Po·α_Hodge + α_Po` | **D + F** | minimal polynomial of `φ` by construction; mathlib `minpoly` never invoked |
| N16 | L2 | `α_P² = α_YM` | **D + F** | minimal polynomial `x²−2` of `√2`. No substrate operator's spectrum is proved to contain `√2` |
| N17 | L3 | `α_Po + 2(α_NP − α_Hodge) = α_RH` | **E + F** | reduces to `1 + 2(1/4) = 3/2`. The "Galois trace" narrative has no bridge forcing `q = 1/4` |
| N18 | L4 | `α_QG² = α_YM·π` | **D + F** | minimal polynomial of `√(2π)` |
| N19 | **L5** | `α_NS = α_RH · π` | **G** (F on canonical) | **THE LOAD-BEARING GAP.** "No substrate route from `α_RH` to `α_NS` via π-scaling exists. No corpus theorem justifies the multiplicative factor `π`." Closes r124's free parameter |
| N20 | I6 | `α_NS = α_YM·α_BSD` | **E + F** | `3π/2 = 2·(3π/4)`. Cited as "gauge invariant"; `GaugeInvariance` exists "in name only" |
| N21 | I7 | `α_YM = α_Poincaré + 1` | **E + F** | the assertion `2 = 1 + 1`. Most-cascading law under drop (destroys 4 α's) |
| N22 | I9 | `α_RH·α_YM = 3` | **E + F** | `(3/2)·2 = 3`. The `3` is the only constant that could plausibly come from the base-3 substrate; no theorem links them |

### 2c. Skeleton results

| id | node | file | class | note |
|---|---|---|---|---|
| N23 | `alpha_skeleton_unique` (nine-tuple rigidity) | `AlphaSkeletonUniqueness_r128.lean` | **B** | Genuinely conditional and honestly stated: rigid **given** N15–N22. Since none of those is class A, the rigidity does not ground the values |
| N24 | `alpha_web_admits_every_positive_BSD` | `AlphaWebDegreesOfFreedom_r124.lean` | **A** | **A genuine intrinsic theorem — and it is negative.** For every `t > 0` an assignment satisfies all eleven invariants with `α_BSD = t` |
| N25 | `invariant_two_is_redundant`, `invariant_eight_is_redundant` | r124 | **A** | Two of the eleven invariants carry no information |
| N26 | `IsIntrinsic` (predicate forbidding target-value insertion) | — | **∅** | **Does not exist.** **Blocks completion conjunct (K0).** Without it, any lookup-table functional satisfies (K1)–(K9) |
| N27 | Perelman anchor `α_Poincaré = 1` | — | **H → F** | Perelman 2002–03 is a real theorem, but it enters as `def α_Poincare : ℝ := 1`, not as a citation with content. The audit records: "External classical, cited via `def`, not a theorem" |

**Layer 2 verdict:** no α-value is derived. Eight of eight structural laws are
target-encoded; L5 is pure narrative. The framework has no predicted constants.

---

## LAYER 3 — THE CLAY SECTORS AND THEIR BRIDGES

### 3a. Statement definitions

| id | node | file | class | faithful? |
|---|---|---|---|---|
| N28 | `RiemannHypothesis := ∀ s, 0<s.re → s.re<1 → riemannZeta s = 0 → s.re = 1/2` | `PF/SpectralBijection.lean:512` | **A** | **YES** — the literal RH on mathlib `riemannZeta` |
| N29 | `Clay_RiemannHypothesis_Standard := RiemannHypothesis` | `PF/Referee/StandardClayStatements.lean:36` | **A** | **YES** |
| N30 | `Clay_PvsNP_Standard E := ¬ Surjective E.inclusion` | `StandardClayStatements.lean:55` | **B** | shape faithful, depends on `E` |
| N31 | `Clay_NavierStokes_Standard E` | `StandardClayStatements.lean:~72` | **B** | shape faithful, depends on `E` |
| N32 | `Clay_YangMillsMassGap_Standard E` | `StandardClayStatements.lean:~95` | **B** | shape faithful, depends on `E` |
| N33 | `Clay_BSD_Standard E` | `StandardClayStatements.lean:~118` | **B** | shape faithful, depends on `E` |
| N34 | `Clay_Hodge_Standard E` | `StandardClayStatements.lean:~138` | **B** | shape faithful, depends on `E` |

### 3b. The encodings — where faithfulness is won or lost

| id | node | file | class | verdict |
|---|---|---|---|---|
| N35 | `PF_ComplexityEncoding` (`ClassP`/`ClassNP` from `Machine`, `turingTimeComplexity`, Cook-1971 certificates) | `PF/Referee/PNPCapstoneTypedBridge.lean:41`; `PF/TuringEncoding/Complexity.lean:106,143` | **A?** | **Apparently faithful.** Real TM definitions. Needs a dedicated audit of `Machine`/`turingTimeComplexity` — recorded as open |
| N36 | `PF_NS3DEncodingV2`, `hasGlobalSmoothSolution := NS3DRegularitySolutionV2` | `PF/NavierStokes/NS3DRegularitySolutionV2.lean:142,201` | **F** | **NOT faithful.** The predicate is `UniformHadamardBoundAllN ∧ MathlibSobolevDivFreeAvailable ∧ MathlibPMath1 ∧ MathlibPMath2 ∧ (divFree → BKM ∧ FiniteVorticityIntegral)`. Three conjuncts are mathlib-availability flags. It does not assert global-in-time smooth existence |
| N37 | `PF_YMEncodingBridge5` | `PF/YangMills/Bridge5_YM_SubstrateDischarge.lean:342` | **F** | **NOT faithful.** Finite-dimensional substrate model; `massGap T := T.v4.v3.v2.Δ` |
| N38 | `GlimmJaffe_OS_SU2_TypedAnchor` | `Bridge5_YM_SubstrateDischarge.lean:226` | **E** | **`Prop := True`.** Vacuous conjunct of N37's `satisfiesClayAxioms` |
| N39 | `StreaterWightman_SU2_TypedAnchor` | `Bridge5_YM_SubstrateDischarge.lean:243` | **E** | **`Prop := True`.** Vacuous |
| N40 | `OsterwalderSchrader_SU2_TypedAnchor` | `Bridge5_YM_SubstrateDischarge.lean:262` | **E** | **`Prop := True`.** Vacuous |
| N41 | `OSRP_Compatible_Interacting_Ham_Open` | `PF/YM_Wave56ContinuumLiftAttempt.lean:364` | **B** | Open by its own name; carried as a conjunct |
| N42 | `PF_BSDEncodingV5`, `algebraicRankV5 = analyticRankV5 = manuscriptRankV5` | `PF/Referee/BSDCapstoneTypedBridgeV5.lean:193,196,305` | **E** | **VACUOUS BY CONSTRUCTION.** Both ranks are the same function; equality is `rfl`; off a 20-curve list both return `0`. The file states this itself |
| N43 | `PF_HodgeEncoding`, `isAlgebraic := HodgeAlgebraicRepresentation` | `PF/Referee/HodgeCapstoneTypedBridge.lean:55` | **F** | **NOT faithful.** Own docstring: "substrate-level only… not literal geometric algebraicity by an explicit cycle" |
| N44 | `PF_HodgeEncoding_FullGeneral` with `AlgebraicCycleOnQuinticWitness` | `PF/AlgebraicGeometry/Voisin2007GeneralQuinticPrecision.lean:496` | **B** | **Genuine cycle witnesses.** The right foundation for a faithful Hodge sector; not used by the headline |

### 3c. The premise bundles

| id | node | file | class | verdict |
|---|---|---|---|---|
| N45 | `ClayClosureBundleBulletproof` | `PF/Referee/UnifiedClayClosureLinkageBulletproof.lean:56` | **∅ CIRCULAR** | Three fields, two of which compose by modus ponens to the RH conclusion |
| N46 | `PF_T3SymIsHilbertPolyaOperator_Positive` | same | **B** | Named open conjecture, honestly carried |
| N47 | `HilbertPolyaProgramConjecture_Positive` | same | **∅ CIRCULAR** | Content: `PF_T3SymIsHilbertPolyaOperator_Positive → RiemannHypothesis`. With N46 in the same structure, yields the conclusion |
| N48 | `Mayer1991_Cohen2025_substrate_HP_program_citation := HilbertPolyaProgramConjecture_Positive` | `RH_FrameworkStandardDischarge_NamedAnchors_2026_06_19.lean:222` | **∅ CIRCULAR** | Same Prop as N47, carried a second time by r301 |
| N49 | `Hardy1914_published_theorem_substrate_citation := PositiveOnLineZetaZeroOrdinatesNonempty` | same file, `:172` | **∅ IDENTITY** | r301 lists this Prop as **conclusion (E2)** while requiring it as **hypothesis**. Premise and conclusion are the same Prop. (Hardy 1914 is genuine — but assumed here, not proved here) |
| N50 | `PolylogEigenvalueConjecture` | `PF/TuringEncoding/…` | **B** | Named open conjecture; carries the entire P-vs-NP sector |
| N51 | `ClayClosureBundleDualCitationAggregate` | `PF/Analytic/UnifiedClayClosureDualCitationAggregate_r299.lean:116` | **∅** | 8-field aggregate; **fields not individually audited this session.** Recorded as unknown provenance |
| N52 | `ClayClosureBundleUniversal` | `…SupremeCapstoneUniversal_r301.lean` | **∅ CIRCULAR** | Contains N45, N48, N49, N51 |

---

## LAYER 4 — TOP-LEVEL THEOREMS

| id | node | class | verdict |
|---|---|---|---|
| N53 | `principia_fractalis_millennium_supreme_capstone_universal_at_HEAD` (r301) | **∅ CIRCULAR** | Valid but carries no information: hypothesis contains conclusion. Not a central-theorem candidate |
| N54 | `PrincipiaFractalisSubstrateTheorem : PFSubstrateAntecedents → PFSubstrateConsequences` | **∅ VACUOUS** | Antecedent discarded (`intro _h_antecedents`); consequences independently provable |
| N55 | `SubstrateTheoremContent_r216` | **A** | **Genuine intrinsic theorem — negative.** Proves in-kernel that any proposition implies `PFSubstrateConsequences` |
| N56 | **CENTRAL THEOREM** | **∅** | **UNSPECIFIED.** No declaration in the corpus is it |

---

## LAYER 5 — THE r331b CHAIN (healthy, and outside the unified-theory claim)

| id | node | class | verdict |
|---|---|---|---|
| N57 | `xi_T15_zero_count_identity_unconditional` | **A** | Unconditional, no binders, mathlib three. **Genuine.** Not RH |
| N58 | `top15_re_lt_neg_1e4` (18-box union, FULL) | **A** | Cover gate PASS 2026-09-07, measure exactly 1/2 |
| N59 | 18 `RiemannXiBox<K>Bridge` capstones | **A** | All CLOSED; margins in `FULL_STATUS_REPORT_2026-09-06.md` §1.3 |
| N60 | `RiemannXiBox0Bridge` rebuild | **∅ OPEN** | Skipped by the running C1 pass; no olean. Operational, not mathematical |

---

## BLOCKERS — UNKNOWN PROVENANCE

Per the standing rule, each of these halts anything downstream of it.

| id | blocker | blocks | owner |
|---|---|---|---|
| **B-SCHEME** | The directive's seven classes not on any filesystem | correct keying of this entire ledger | Pablo |
| **B-CHARTER** | `ALPHA_RIGIDITY_AUDIT_CHARTER` not on any filesystem | the α-rigidity section's mandated form | Pablo |
| **B-N03** | C*-structure on the completion (r54–r57) unconfirmed | completion conjunct (U1) | orchestrator |
| **B-N04/05** | No equivalence relation, no invariance statement | conjuncts (E1), (E2); the whole "intrinsic constants" claim | open research |
| **B-N26** | `IsIntrinsic` undefined | conjunct (K0), hence all of (K) | open research |
| **B-N51** | r299 aggregate's 8 fields not individually audited | any claim resting on the aggregate route | orchestrator |
| **B-JOIN** | `SubstrateBearsOn`, `DerivationIsNonVacuous`, `AntecedentIsLoadBearing` undefined | conjuncts (C), (D) — the unification claim itself | open research |
| **B-TM** | `Machine` / `turingTimeComplexity` faithfulness unaudited | whether (S2) is the real P vs NP | orchestrator |

---

## TALLY

| class | count | nodes |
|---|---|---|
| **A** — intrinsic PF theorem | 10 | N01, N02, N24, N25, N28, N29, N55, N57, N58, N59 |
| **B** — conditional, honest | 11 | N23, N30–N34, N41, N44, N46, N50 |
| **D** — definitional | 3 | N15, N16, N18 |
| **E** — trivial arithmetic / vacuous | 8 | N17, N20, N21, N22, N38, N39, N40, N42 |
| **F** — target-encoded | 14 | N06–N14, N19, N27, N36, N37, N43 |
| **G** — unsupported narrative | 1 | **N19 (L5)** |
| **H** — external classical | 1 | N27 (degraded to F by its `def` form) |
| **∅** — blocker | 13 | N03, N04, N05, N26, N45, N47, N48, N49, N51, N52, N53, N54, N56 |

**Of the ten class-A nodes, three are negative results about the framework**
(N24, N25, N55) and four are the r331b rectangle chain (N57–N60), which the
corpus correctly scopes as *not* the unified theory. The substrate construction
(N01, N02) is the remaining genuine positive contribution.

**No class-A node connects layer 1 to layer 2, or layer 2 to layer 3.**

---

*Opened 2026-09-07. Classification scheme is a declared stand-in pending B-SCHEME.
Nothing in this file modifies a `.lean` file. Public HEAD `96c71da7`. NO PUSH.*
