# UNIFIED THEORY DEPENDENCY LEDGER

**GENERATED FILE — do not hand-edit.** Produced from `UNIFIED_THEORY_DEPENDENCY_LEDGER.json` by `PF_Lean4_Code/scripts/gen_dependency_ledger.py` on 2026-09-07.
Edit the JSON and re-run the generator. Directive §3 requires the human-readable ledger to be generated from the machine-readable one.

- **Central theorem status:** UNSPECIFIED
- **Branch:** `r331b-provenance` · **Public HEAD must remain** `96c71da7` · **NO PUSH**
- **Directive:** `codex/UNIFIED_THEORY_PROOF_DIRECTIVE_2026-09-07.md`
- **Program:** `codex/UNIFIED_THEORY_PROOF_PROGRAM.md` · **Charter:** `codex/ALPHA_RIGIDITY_AUDIT_CHARTER_2026-09-01.md`

---

## CLASSIFICATION — directive §3, seven classes

| key | class |
|---|---|
| **C1** | definition-or-convention |
| **C2** | theorem-derived-from-earlier-foundations |
| **C3** | independently-motivated-axiom |
| **C4** | empirical-input |
| **C5** | conditional-interface |
| **C6** | unresolved-conjecture |
| **C7** | recorded-negative-or-refuted |
| **BLOCKER** | unknown provenance |

Two orthogonal flags travel alongside the class, because they are defects rather than provenance: `circular` (premise restates or contains its conclusion) and `vacuous` (conclusion holds by construction). A node can be both a legitimate open conjecture and used circularly; one field cannot carry both facts.

### §3 field conformance

Required per node: `source file`, `fqn`, `deps`, `axioms`, `closed_term`, `rebuilt_from_source`.

- nodes: **67**
- nodes with at least one `unverified` required field: **62** — each is a blocker per §3

Per directive section 3, unknown provenance is a BLOCKER. Every node carrying 'unverified' in a required field is one, and is counted here rather than silently defaulted. Filling them needs a per-node #print axioms / #check @ sweep and a C1-completion check; that sweep is queued, not done.

---

## LAYER 1 — CONSTRUCTED UNIVERSE

| id | node | class | flags | file | axioms | closed term | rebuilt | note |
|---|---|---|---|---|---|---|---|---|
| N01 | TimelessFieldRing | **C2** |  | — | unverified | unverified | unverified | Algebraic direct limit; NormedRing/StarRing/CStarRing/NormedAlgebra C. |
| N02 | TimelessFieldCompletion | **C2** |  | `PF/SubstrateTimelessFieldCompletion.lean` | unverified | unverified | unverified | UniformSpace.Completion; mathlib-native. |
| N03 | CStar structure on completion (r54-r57) | **BLOCKER** |  | — | unverified | unverified | unverified |  |
| N04 | SubstrateConfiguration / SubstrateEquiv | **BLOCKER** |  | — | unverified | unverified | unverified | Does not exist. No Setoid/Quotient in the substrate module. |
| N05 | DerivedConstantFunctions + invariance | **BLOCKER** |  | — | unverified | unverified | unverified |  |

## LAYER 2 — ALPHA SKELETON AND CONSTANTS

| id | node | class | flags | file | axioms | closed term | rebuilt | note |
|---|---|---|---|---|---|---|---|---|
| N06 | alpha_Poincare | **C1** |  | — | unverified | unverified | unverified | r216 in-kernel: closed by rfl, records the chosen numeral, NOT about Ricci flow or the Poincare conjecture. |
| N07 | alpha_RH | **C1** |  | — | unverified | unverified | unverified |  |
| N08 | alpha_YM | **C1** |  | — | unverified | unverified | unverified |  |
| N09 | alpha_P | **C1** |  | — | unverified | unverified | unverified |  |
| N10 | alpha_NP | **C1** |  | — | unverified | unverified | unverified | 1/4 free (r124). Charter N4: forcing fed phi and 1/4 in, got phi+1/4 out. |
| N11 | alpha_Hodge | **C1** |  | — | unverified | unverified | unverified |  |
| N12 | alpha_QG | **C1** |  | — | unverified | unverified | unverified |  |
| N13 | alpha_BSD | **C1** |  | — | unverified | unverified | unverified | r124's free parameter. |
| N14 | alpha_NS | **C1** |  | — | unverified | unverified | unverified |  |
| N14b | alpha_PvNP | **C1** |  | `PF/TuringEncoding/PNPClassSeparationPrecisionBridge.lean` | unverified | unverified | unverified | Tenth anchor outside the 9-tuple; name-collision with alpha_NP flagged by r128. Charter Q1 open. |
| N15 | L1 hodge_minpoly | **C1** |  | — | unverified | unverified | unverified | Minimal polynomial of phi by construction; mathlib minpoly never invoked. |
| N16 | L2 p_norm | **C1** |  | — | unverified | unverified | unverified | Minimal polynomial x^2-2 of sqrt 2. |
| N17 | L3 np_trace | **C1** |  | — | unverified | unverified | unverified | Reduces to 1 + 2*(1/4) = 3/2. |
| N18 | L4 qg_norm | **C1** |  | — | unverified | unverified | unverified |  |
| N19 | L5 ns_scaling (alpha_NS = alpha_RH * pi) | **C1** |  | — | unverified | unverified | unverified | Was the sole narrative-only law and r124's free-parameter closer. Now provably not derivable on the K-theoretic trace route. |
| N19b | pi_not_ktheoretic_ratio (r332.A) | **C7** |  | `PF/AlphaL5PiScalingObstruction_r332.lean` | [propext, Classical.choice, Quot.sound] | no (hypothetical: MemZ13 a, MemZ13 b) | yes (built 2026-09-07 in ACTIVE tree) | For all a,b in Z[1/3], b/a != pi. Kernel-green, mathlib three, non-vacuity proved (r332.E), a!=0 shown unnecessary (r332.F). |
| N19c | alpha_ns_div_alpha_rh_eq_pi (r332.D) | **C1** |  | — | [propext, Classical.choice, Quot.sound] | yes | yes (built 2026-09-07 in ACTIVE tree) | alpha_NS/alpha_RH = pi by ring after unfolding. True of the chosen numerals, unreachable from the invariant. |
| N20 | I6 bsd_gauge | **C1** |  | — | unverified | unverified | unverified | 3pi/2 = 2*(3pi/4). GaugeInvariance exists in name only. |
| N21 | I7 ym_shift | **C1** |  | — | unverified | unverified | unverified | 2 = 1 + 1. Most-cascading law under drop (destroys 4 alphas). |
| N22 | I9 rh_prod | **C1** |  | — | unverified | unverified | unverified | (3/2)*2 = 3. |
| N23 | alpha_skeleton_unique (r128) | **C5** |  | — | unverified | unverified | unverified | Rigid GIVEN N15-N22, all of which are C1. Rigidity-given-conventions. |
| N24 | alpha_web_admits_every_positive_BSD (r124) | **C7** |  | — | [propext, Classical.choice, Quot.sound] | yes (forall t, no hypothesis bundle) | unverified |  |
| N25 | invariant_two/eight_is_redundant (r124) | **C7** |  | — | unverified | unverified | unverified |  |
| N26 | IsIntrinsic | **BLOCKER** |  | — | unverified | unverified | unverified |  |
| N27 | Perelman anchor | **C1** |  | — | unverified | unverified | unverified | C3 by pedigree, but enters as def alpha_Poincare := 1. Charter 5.7: does not independently assign the value. |
| N27b | trace-range obstruction (charter N2, r113+r123) | **C7** |  | `PF/AlphaFromSubstrateKTheory_r123.lean` | [propext, Classical.choice, Quot.sound] | yes | unverified | Substrate trace range is Z[1/3]; 7 of 9 alphas lie outside it. |

## LAYER 3 — CLAY SECTORS AND BRIDGES

| id | node | class | flags | file | axioms | closed term | rebuilt | note |
|---|---|---|---|---|---|---|---|---|
| N28 | RiemannHypothesis | **C2** |  | `PF/SpectralBijection.lean` | unverified | unverified | unverified |  |
| N29 | Clay_RiemannHypothesis_Standard | **C2** |  | — | unverified | unverified | unverified |  |
| N30 | Clay_PvsNP_Standard | **C5** |  | — | unverified | unverified | unverified |  |
| N31 | Clay_NavierStokes_Standard | **C5** |  | — | unverified | unverified | unverified |  |
| N32 | Clay_YangMillsMassGap_Standard | **C5** |  | — | unverified | unverified | unverified |  |
| N33 | Clay_BSD_Standard | **C5** |  | — | unverified | unverified | unverified |  |
| N34 | Clay_Hodge_Standard | **C5** |  | — | unverified | unverified | unverified |  |
| N35 | PF_ComplexityEncoding | **C2** |  | — | unverified | unverified | unverified | Real TMs, poly bounds, Cook-1971 certificates. |
| N36 | PF_NS3DEncodingV2 / NS3DRegularitySolutionV2 | **C1** |  | — | unverified | unverified | unverified | 5-conjunct predicate, three are mathlib-availability flags. Does not assert global-in-time smooth existence. |
| N37 | PF_YMEncodingBridge5 | **C1** |  | — | unverified | unverified | unverified | Finite-dimensional substrate model. |
| N38 | GlimmJaffe_OS_SU2_TypedAnchor | **C1** | **vacuous** | — | unverified | unverified | unverified | def : Prop := True |
| N39 | StreaterWightman_SU2_TypedAnchor | **C1** | **vacuous** | — | unverified | unverified | unverified | def : Prop := True |
| N40 | OsterwalderSchrader_SU2_TypedAnchor | **C1** | **vacuous** | — | unverified | unverified | unverified | def : Prop := True |
| N41 | OSRP_Compatible_Interacting_Ham_Open | **C6** |  | — | unverified | unverified | unverified |  |
| N42 | PF_BSDEncodingV5 | **C1** | **vacuous** | — | unverified | unverified | unverified | algebraicRankV5 = analyticRankV5 = manuscriptRankV5. Equality by rfl; 0 off a 20-curve list. |
| N43 | PF_HodgeEncoding | **C1** |  | — | unverified | unverified | unverified | Own docstring: substrate-level only, not literal geometric algebraicity by an explicit cycle. |
| N44 | PF_HodgeEncoding_FullGeneral | **C5** |  | — | unverified | unverified | unverified | Genuine cycle witnesses; unused by the headline. |
| N45 | ClayClosureBundleBulletproof | **C6** | **circular** | — | unverified | unverified | unverified |  |
| N46 | PF_T3SymIsHilbertPolyaOperator_Positive | **C6** |  | — | unverified | unverified | unverified |  |
| N47 | HilbertPolyaProgramConjecture_Positive | **C6** | **circular** | — | unverified | unverified | unverified | Content: PF_T3Sym_Positive -> RiemannHypothesis. |
| N48 | Mayer1991_Cohen2025_substrate_HP_program_citation | **C6** | **circular** | — | unverified | unverified | unverified | Definitionally equal to N47; r301 carries it a second time. |
| N49 | Hardy1914_published_theorem_substrate_citation | **C3** | **circular** | — | unverified | unverified | unverified | Genuine external theorem, but r301 lists the same Prop as conclusion E2 and requires it as hypothesis. |
| N50 | PolylogEigenvalueConjecture | **C6** |  | — | unverified | unverified | unverified | Carries the whole P vs NP sector. Charter N5: three inconsistent gap values. |
| N51 | ClayClosureBundleDualCitationAggregate | **BLOCKER** |  | — | unverified | unverified | unverified |  |
| N52 | ClayClosureBundleUniversal | **BLOCKER** | **circular** | — | unverified | unverified | unverified |  |
| N53 | Cohen 2025 numerics | **C4** |  | — | unverified | unverified | unverified | self-adjointness <1e-15 at N<=40; eigenvalue match 150 digits on five pairs; scaling 5e-6. |

## LAYER 4 — TOP-LEVEL THEOREMS

| id | node | class | flags | file | axioms | closed term | rebuilt | note |
|---|---|---|---|---|---|---|---|---|
| N54 | principia_fractalis_millennium_supreme_capstone_universal_at_HEAD | **BLOCKER** | **circular** | — | [propext, Classical.choice, Quot.sound] | NO - binder `ClayClosureBundleUniversal ->` visible in #check @ | unverified | Valid; carries no information. |
| N55 | PrincipiaFractalisSubstrateTheorem | **C1** | **vacuous** | — | unverified | unverified | unverified | Antecedent discarded. |
| N56 | SubstrateTheoremContent_r216 | **C7** |  | — | unverified | unverified | unverified |  |
| N57 | CENTRAL THEOREM | **BLOCKER** |  | — | unverified | unverified | unverified |  |
| N62 | rh_from_bulletproof_bundle_by_application (r333.A) | **C7** |  | `PF/UnifiedTheoryPremiseAudit_r333.lean` | [propext, Classical.choice, Quot.sound] | no (hypothetical: ClayClosureBundleBulletproof) | yes (built 2026-09-07 in ACTIVE tree) | Kernel proof that the bulletproof bundle yields RH by function application alone. No substrate, alpha-skeleton or transfer operator participates. |
| N63 | hardy_premise_equals_conclusion_E2 (r333.D) | **C7** |  | `PF/UnifiedTheoryPremiseAudit_r333.lean` | [propext, Classical.choice, Quot.sound] | yes | yes | rfl. r301 lists PositiveOnLineZetaZeroOrdinatesNonempty as conclusion E2 while requiring the same Prop as hypothesis. The theorem returns one of its own inputs. |

## LAYER 5 — R331B CHAIN

| id | node | class | flags | file | axioms | closed term | rebuilt | note |
|---|---|---|---|---|---|---|---|---|
| N58 | xi_T15_zero_count_identity_unconditional | **C2** |  | — | [propext, Classical.choice, Quot.sound] | yes - #check @ shows NO binders at all | pending C1 | Unconditional, no binders. NOT RH. |
| N59 | top15_re_lt_neg_1e4 | **C2** |  | — | unverified at FULL (B5) | yes | pending C1 |  |
| N60 | 18 Box<K>Bridge capstones | **C2** |  | — | unverified | unverified | unverified | Weakest box 106 at +2.211191e-05. |
| N61 | RiemannXiBox0Bridge rebuild | **BLOCKER** |  | — | unverified | unverified | unverified | a1_v3 ensure_box0_reference now builds it on both halves. |

---

## MISSING JOINS

| id | from → to | status | note |
|---|---|---|---|
| J1 | L1 → L2 | **CLOSED_NEGATIVELY** | r332 + r123: no alpha value and no needed ratio is reachable from the substrate trace range Z[1/3]. |
| J2 | L2 → L3 | **NO_EDGE** | Narrative only. |
| J3 | L3 → standard | **PARTIAL** | Faithful for RH and apparently P vs NP; unfaithful or vacuous for NS, YM, BSD, Hodge. |

---

## CREDIT COLUMN

Recording what the corpus got right. A ledger that tallies only defects misrepresents the project.

| # | credit | evidence |
|---|---|---|
| **CR1** | In-file docstrings are candid, repeatedly more so than headline theorem names and prose chapters. Nearly every Layer-3 unfaithfulness finding was self-disclosed by the file containing it. The defect is a headline/prose problem, not concealment in the formalisation. | r216 'This is a prose problem, not concealment'; BSD V5 honest-scope block; HodgeCapstoneTypedBridge.lean:72-76 |
| **CR2** | The project audits itself adversarially and publishes the negatives. | N24, N25, N56, N27b |
| **CR3** | r216 deliberately puts the flagship theorem's vacuity in the kernel so it cannot drift back out of the prose. | SubstrateTheoremContent_r216.lean header |
| **CR4** | The evidence standard is real and caught a silently-admitted sorry on 2026-09-05. | RELEASE_GATE_r331b.md B0 |
| **CR5** | The r331b chain is genuine unconditional analysis, correctly scoped as not RH. | N58-N60; gate F8 |
| **CR6** | The rigidity charter pre-registers its outcomes before running the audit, including the one unfavourable to the framework. | Charter section 8 |

---

## BLOCKERS

| id | status | description | owner |
|---|---|---|---|
| B-DIRECTIVE | **OPEN** | full directive text not yet in codex/ | Pablo |
| B-N03 | **OPEN** | CStar structure on completion unconfirmed | orchestrator |
| B-N04 | **OPEN** | no equivalence relation on substrate configurations | research |
| B-N05 | **OPEN** | no invariance statement for derived constants | research |
| B-N26 | **OPEN** | IsIntrinsic undefined | research |
| B-N51 | **OPEN** | r299 aggregate's 8 fields unaudited | orchestrator |
| B-JOIN | **OPEN** | SubstrateBearsOn / DerivationIsNonVacuous / AntecedentIsLoadBearing undefined | research |
| B-TM | **OPEN** | Machine / turingTimeComplexity faithfulness unaudited | orchestrator |
| B-CIRC | **OPEN** | premise set of top-level theorem contains its conclusion | Pablo |
| B-SCHEME | **CLOSED** | directive's seven classes received and applied | — |
| B-CHARTER | **CLOSED** | ALPHA_RIGIDITY_AUDIT_CHARTER_2026-09-01.md recovered and committed | — |
| B-L5 | **CLOSED** | L5 settled negatively by r332 | — |
| B-N61 | **IN_PROGRESS** | box 0 bridge rebuild | orchestrator |

---

## COUNTERMODEL RISKS

Full treatment: `codex/UNIFICATION_COUNTERMODEL_LEDGER.md` (directive §8).

| id | risk | status |
|---|---|---|
| R1 | The alpha web has no rigid solution at all | **STRENGTHENED** |
| R2 | L5 is underivable in principle | **RESOLVED_ON_THE_ROUTE_WE_HAVE** |
| R3 | The substrate is too weak to see any Clay problem | **LIVE** |
| R4 | The YM encoding is inconsistent, not just vacuous | **LIVE** |
| R5 | KatoRellichInput contamination | **LIVE** |
| R6 | Encoding drift between near-identical names | **LIVE** |

---

## TALLY (recomputed at generation)

| class | name | count |
|---|---|---|
| **C1** | definition-or-convention | 28 |
| **C2** | theorem-derived-from-earlier-foundations | 8 |
| **C3** | independently-motivated-axiom | 1 |
| **C4** | empirical-input | 1 |
| **C5** | conditional-interface | 7 |
| **C6** | unresolved-conjecture | 6 |
| **C7** | recorded-negative-or-refuted | 7 |
| **BLOCKER** | unknown provenance | 9 |

Flags: `circular` **6**, `vacuous` **5**.

Six of the ten C2 nodes are the substrate construction or the r331b rectangle chain, the latter correctly scoped by the corpus as NOT the unified theory. No C2 node connects layer 1 to layer 2, or layer 2 to layer 3. As of r332 the layer-1 to layer-2 join is closed negatively on the route the corpus has.

---

*Generated from the machine-readable ledger. Nothing in this file modifies a `.lean` file. Public HEAD `96c71da7`. NO PUSH.*
