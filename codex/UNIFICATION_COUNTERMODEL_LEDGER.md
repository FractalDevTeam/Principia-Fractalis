# UNIFICATION COUNTERMODEL LEDGER

**Opened:** 2026-09-07. Required by
`codex/UNIFIED_THEORY_PROOF_DIRECTIVE_2026-09-07.md` §8, which gives the
adversarial program **equal priority** with the constructive one.

§8's standing caution, applied throughout:

> **Failed search ≠ nonexistence unless formally exhaustive.**

Every entry below states whether its search was formally exhaustive, bounded, or
merely unattempted. Nothing is recorded as "no countermodel exists" on the
strength of not having found one.

---

## A. REMOVE ASSUMPTIONS SINGLY

| id | assumption removed | surviving family | status |
|---|---|---|---|
| **A1** | L5 (`α_NS = α_RH·π`) from the r128 eight | r124: the eleven-invariant system becomes a **one-parameter family** — for every `t > 0` there is an assignment with `α_BSD = t` | **KERNEL-PROVED** (`alpha_web_admits_every_positive_BSD`). Formally exhaustive over the stated system: a Gröbner elimination, `dim V(I) = 1`, `I ∩ ℚ(π)[α_BSD] = {0}` |
| **A2** | I2 (`α_RH² = 9/4`) | nothing changes — I2 follows from I3, I9, I11 | **KERNEL-PROVED** redundant (r124) |
| **A3** | I8 (`α_RH·α_NS = α_NS + α_BSD`) | nothing changes — follows from I3, I5, I9, I11 | **KERNEL-PROVED** redundant (r124) |
| **A4** | I7 (`α_YM = α_Poincaré + 1`) | most-cascading law: dropping it releases **four** α's | recorded by the 2026-08-24 provenance audit; **not independently re-derived here** |
| **A5** | the `1/4` offset in `α_NP = φ + 1/4` | every real `c` is admissible for `α_NP − α_Hodge = c` under the ten invariants that do not mention `α_NP` | **KERNEL-PROVED** (`alpha_offset_is_free`, r124) |
| **A6** | **L1** | `alpha_Hodge` released — witness `wo_L1` (`alpha_Hodge = 1`, `alpha_NP = 5/4`) | **CLOSED 2026-09-07**, r334.A. Exhaustive: one countermodel refutes redundancy |
| **A7** | **L2** | `alpha_P` released — witness `wo_L2` (`alpha_P = 1`) | **CLOSED**, r334.B |
| **A8** | **L3** | `alpha_NP` released — witness `wo_L3` (`alpha_NP = 1`) | **CLOSED**, r334.C. The eight-law form of A5 |
| **A9** | **L4** | `alpha_QG` released — witness `wo_L4` (`alpha_QG = 1`) | **CLOSED**, r334.D |
| **A10** | **I6** | `alpha_BSD` released — witness `wo_I6` (`alpha_BSD = 1`) | **CLOSED**, r334.E. r124's free parameter, inside the eight-law system |
| **A11** | **I9** | `alpha_RH` released; `alpha_NS`, `alpha_BSD`, `alpha_NP` follow through L5, I6, L3 — witness `wo_I9`. Four of nine move together | **CLOSED**, r334.F. Most cascading of the six |
| **A12** | I7 (`alpha_YM = alpha_Po + 1`) | — | **OPEN — not authorized.** The eight-law system is not fully audited until it is done |

## B. NON-ISOMORPHIC MODELS / ALTERNATE STRUCTURES PRODUCING THE SAME CONSTANTS

| id | question | status |
|---|---|---|
| **B1** | Is there a second self-consistent nine-tuple satisfying all eight r128 laws with a different anchor? | **NOT ATTEMPTED.** Would end the rigidity claim outright if found. r128 proves uniqueness *given positivity*; the sign/Galois quotient is unexplored (charter P3) |
| **B2** | What *independent* principle justifies restricting to the positive branch? | **NONE STATED.** Charter P3 records this as a prose gap. Without it, the "unique" label is doing work the mathematics does not support |
| **B3** | Alternate substrate whose invariant range is not `ℤ[1/3]` | **NOT ATTEMPTED**, and not currently well-posed — no such object exists in the corpus. This is the one escape r332 explicitly leaves open |

## C. PARAMETER-FAMILY SEARCHES

| id | finding | exhaustive? |
|---|---|---|
| **C1** | The eleven-invariant system is a one-parameter family with `α_BSD` the unique maximal independent variable | **YES** — Gröbner over ℚ(π), `codex/alpha_web_system.py`; `dim V(I) = 1`, 8-element basis, elimination ideal `{0}` |
| **C2** | The r128 eight-law system's residual parameter space | **NOT COMPUTED.** Charter P2/P3 specify the computation (S-Δ1, S-Δ2 ideals); it has not been run |

## D. RELABELLING DETECTION VIA DEFINITIONAL EQUIVALENCE

This is where the sharpest results have come from: checking whether two
differently-named objects are the *same* object.

| id | finding | proof |
|---|---|---|
| **D1** | `Mayer1991_Cohen2025_substrate_HP_program_citation` **is** `HilbertPolyaProgramConjecture_Positive` | `rfl` — r333.E. The r301 universal input therefore requires the same Prop **twice**, under two names |
| **D2** | `Hardy1914_published_theorem_substrate_citation` **is** `PositiveOnLineZetaZeroOrdinatesNonempty`, which r301 lists as delivered conclusion (E2) | `rfl` — r333.D. **The theorem returns one of its own inputs** |
| **D3** | `algebraicRankV5` **is** `analyticRankV5` — both are `manuscriptRankV5` | the corpus's own `rfl` proof. BSD "discharge" is an identity on one function |
| **D4** | `Clay_RiemannHypothesis_Standard` **is** literal RH on mathlib `riemannZeta` | `rfl` — r333.G. Confirms D5 is a real circularity, not a triviality about a private predicate |
| **D5** | `HilbertPolyaProgramConjecture_Positive` **is** `PF_T3Sym…_Positive → RiemannHypothesis` | `rfl` — r333.F. With its sibling field, RH follows by function application (r333.A) |
| **D6** | `framework_alpha.a_PvNP = 5/4` vs `α_NP = φ + 1/4 ≈ 1.868` | two different reals under near-identical names (r128 header). **Full α-namespace collision audit NOT DONE** |

## E. VACUOUS-PREMISE AND UNUSED-HYPOTHESIS DETECTION

| id | finding | proof |
|---|---|---|
| **E1** | `PrincipiaFractalisSubstrateTheorem` discards its antecedent; **any** proposition implies `PFSubstrateConsequences` | r216 §1, kernel-proved |
| **E2** | `GlimmJaffe_OS_SU2_TypedAnchor` = `Prop := True` | source. Vacuous conjunct of the YM `satisfiesClayAxioms` |
| **E3** | `StreaterWightman_SU2_TypedAnchor` = `Prop := True` | source |
| **E4** | `OsterwalderSchrader_SU2_TypedAnchor` = `Prop := True` | source |
| **E5** | r332's own `a ≠ 0` hypothesis does no work (`b/0 = 0 ≠ π`) | r332.F — self-applied. Recorded because an unused premise can be mistaken for the thing making a statement true |
| **E6** | Systematic `Prop := True` sweep across the whole corpus | **NOT DONE.** Four found opportunistically; there is no reason to think that is all of them. **Recommended as a mechanical grep** |

## F. CROSS-SECTOR CONSISTENCY

| id | finding | status |
|---|---|---|
| **F1** | Three mutually inconsistent spectral-gap values for the P≠NP sector: `0.0891` empirical / `0.1306` golden / `0.054` Lean | charter N5, **unreconciled** |
| **F2** | Full cross-sector consistency check | **NOT DONE** — requires the §5 sector matrix, which does not exist |

## G. FORMALISED RECORDED-NEGATIVES THAT CONSTRAIN THE THEORY

§8 asks that recorded negatives be *formalised*, not merely filed. Status:

| id | negative | formalised? |
|---|---|---|
| **G1** | α-web underdetermination | **YES** — r124, kernel |
| **G2** | Substrate trace range is `ℤ[1/3]`; 7 of 9 α's outside it | **YES** — r123, kernel |
| **G3** | Flagship substrate implication is vacuous | **YES** — r216, kernel |
| **G4** | π is not a ratio of trace-range quantities (L5 unreachable) | **YES** — r332, kernel, 2026-09-07 |
| **G5** | The top-level capstone's premise entails its conclusion by application | **YES** — r333, kernel, 2026-09-07 |
| **G6** | Problem 1a falsified (extremal-trace-space ≅ 9-point α-set impossible) | charter N3 — **filed, not formalised** |
| **G7** | Circular α_NP derivation (bare route excludes √2 and φ+1/4) | charter N4 — partially formalised (`bare_route_structural_finding`) |
| **G9** | Five of the eight laws force values outside the substrate trace range, and no irrational is a ratio of it either | **YES** — r334.G/H, kernel, 2026-09-07 |
| **G10** | No law of the six is redundant: the eight-law system is triangular, one constraint per value, nowhere over-determined | **YES** — r334.A–F, kernel, 2026-09-07 |
| **G8** | Refuted numeric anchors (α_EM sign error ~35×; ω_c; Δ_YM 420.43 MeV; both ch₂=0.95 derivations) | charter N6 — **filed, not formalised** |

## H. LIVE RISKS NOT YET PROBED

| id | risk | what would settle it | cost |
|---|---|---|---|
| **H1** | **The YM encoding may be inconsistent, not merely vacuous.** `satisfiesClayAxioms` demands `0 < Δ ∧ 1 ≤ Δ ∧ Δ ≠ 1` alongside twelve analytic conjuncts on a finite-dimensional model. If uninhabitable, `∃ T, …` is **false** and the YM sector is refuted on its own encoding | Exhibit an inhabitant of `Bridge5SubstrateQYM` meeting all fifteen conjuncts, or prove none exists. Precedent: the corpus already found a "structurally-uninhabitable Prop" in the earlier V3 RH route and replaced it | small, sharp |
| **H2** | **`KatoRellichInput` contamination.** Gate F4 records a module *proved false by its own file*. If any live chain cites it, that chain is unsound rather than merely weak | Reachability check from every central-theorem candidate | small |
| **H3** | **The substrate may be too weak to express any Clay problem.** Nothing in the completion construction mentions ζ, elliptic curves, Hodge classes or Navier–Stokes | Exhibit any nonvacuous theorem mentioning both `TimelessFieldCompletion` and a standard object, whose proof uses a substrate property | open-ended |
| **H4** | Systematic unused-hypothesis sweep across all capstones | Lean's unused-variable linter over the capstone set | mechanical |

---

## SUMMARY

**Seven negatives are now formalised in the kernel** (G1–G5, G9, G10), four of
them added 2026-09-07. The corpus's own adversarial instinct is good and its negative
results are real theorems, not memos.

**A6 is closed.** The remove-and-survey pass has now been run for seven of the
eight structural laws (r332 for L5, r334 for L1, L2, L3, L4, I6, I9). **Only I7
remains** (A12), and it was not in the authorization.

**The sharpest new finding is structural, not per-law.** With the anchor, the
eight laws form a *triangular* system: nine unknowns, nine constraints, exactly
one constraint pinning each unknown, **nowhere over-determined**. A rigid system
with redundancy is evidence - the surplus equations could have failed and did
not. A triangular system cannot fail, and cannot corroborate. r124 found
redundancy among the *eleven invariants*; the move to eight laws removed exactly
the redundancy that could have been evidential. Full treatment:
`codex/ALPHA_RIGIDITY_AUDIT_REPORT_2026-09-07.md` section 2.

**One exception survives the sweep, and it is real.** I9 forces `alpha_RH = 3/2`,
which is not in Z[1/3] but *is* a ratio of its elements (3 and 2 both in range).
The obstruction that closes the other five does not close I9. A uniform sweep
would have reported six closures and been wrong on one - which is why section 4
asks for the protocol per law.

**Nothing here has been shown not to exist.** A1–A5 and C1 are formally
exhaustive over their stated systems; everything else is bounded or unattempted,
and is labelled as such.

---

*Opened 2026-09-07. Public HEAD `96c71da7`. NO PUSH.*
