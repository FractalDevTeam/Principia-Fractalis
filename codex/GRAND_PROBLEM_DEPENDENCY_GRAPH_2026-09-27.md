# PRINCIPIA FRACTALIS — GRAND PROBLEM DEPENDENCY GRAPH — 2026-09-27 REFRESH

**Date:** 2026-09-27
**HEAD:** `0d8ea1a4` (local ACTIVE tree; five weeks and one day past baseline)
**Baseline:** `codex/GRAND_PROBLEM_DEPENDENCY_GRAPH_2026-08-23.md` at HEAD `4f7b216d`
**Deliverable:** the second READ-ONLY audit under the POST-r315 GLOBAL RESEARCH DIRECTIVE. No mathematical definitions modified. No new proof wrappers created. No theorem attack started. Existing baseline audit stands; this refresh records the five-week delta and re-ranks against the current external landscape.

---

## STATUS LOCK

The Xi(15) freeze is unchanged: `Xi_Positive_At_15` closed at `4f7b216d`; kernel-only `[propext, Classical.choice, Quot.sound]`; r120 provenance closed via committed panel-generation script.

Since the baseline, five load-bearing pillars have landed and been verified. Every pillar has been re-elaborated by `lake build` at or before this audit; every principal theorem prints kernel-only axioms.

---

## FIVE-WEEK DELTA — WHAT LANDED

### 1. Substrate rigidity — T_∞ classification theorem, kernel-verified (2026-09-11)

`PF/SubstrateRigidity.lean`, commit `18f55a14`. Central theorem:

```
T_infinity_rigidity : ∀ (A : Type*) [CStarAlgebra A] (h : Substrate3Inf A),
  Nonempty (A ≃⋆ₐ[ℂ] TimelessFieldCompletion)
```

First formalization of Glimm 1960 UHF classification specialized to supernatural `3^∞` in any proof assistant. Verified absent from mathlib4, Isabelle/HOL, Coq/Rocq, Agda, Lean 3. Four-arc proof (C1 block embedding, C2 Noether–Skolem, C3 completion universal property, C4 Elliott back-and-forth) plus the W arc. Six mathlib gaps filled as byproducts: `conjByUnitary`, `reindexStarAlgEquiv`, `coe_iSup_of_directed_starSubalgebra`, non-commutative C*-direct-limit apparatus, star lift for `UniformSpace.Completion`, `IsTracialLinearFunctional` predicate.

Kernel-clean per OCIRC audit (2026-09-18, post-r337). **This is now the corpus's central non-trivial rigidity theorem.** It does NOT belong to the same evidential class as the Referee-tier "rigidity forces X" family (see §OCIRC below).

### 2. K-theoretic obstruction — the substrate does not force the α-skeleton (2026-09)

`r123 + r332`. Seven of nine α-values and the ratio `α_NS/α_RH = π` lie outside `ℤ[1/3]`, hence outside the substrate's classifying invariant range. **Companion result to r217**: the substrate is unique up to `*`-iso AND provably underdetermines the α-skeleton via K-theory. Paired-result exposition draft at `Papers/pf_substrate_rigidity_alpha_obstruction_2026-09-10.tex`.

**Corpus consequence:** Problem 1a in `OPEN_PROBLEMS.md` was already updated from OPEN to FALSIFIED on 2026-08-23 (baseline recommendation Rank-1 landed same day). The r332 companion tightens the same finding: the substrate has one tracial state, not nine; the α-web is external input.

### 3. ξ-rectangle edge closure — r325 → r331c (2026-09-22)

Chain since r315: `r325 → r326 → r327 → r328 → r329b (bottom edge on [0,1] DISCHARGED) → r330 → r331a → r331b → r331c`.

- **r329b**: unconditional ξ positivity on `[0,1]` (bottom edge).
- **r331b**: right edge (37 kernel-clean theorems, `RiemannXiThetaRealFormAndBoxes_r331b.lean`).
- **r331c**: **top edge** `Re ξ⟨σ, 15⟩ < -1/10⁴` on `σ ∈ [0,1]` at commit `34dd98db` (`RiemannXiTopEdge_r331c.lean`, 101 L, 4 kernel-clean theorems).

Remaining: **r331d bottom edge** (likely symmetric via conjugation at `t = -15`); then `r327` argument-principle threading closes `riemannHypothesis_below_15` — a literal statement about mathlib's `riemannZeta` in the critical strip up to height 15.

### 4. Brun B1 + Mertens M1–M5 — classical prime-counting apparatus (2026-09-23 → 25)

- **Brun B1** (`PF/NumberTheory/Brun/TwinPrimeSieveInstance.lean`, commit `2904049e`, 157 L): twin-prime `BoundingSieve` instance on mathlib's `SelbergSieve`. Kernel-clean.
  - **Critical mathlib finding**: v4.24.0-rc1 has NO `UpperBoundSieve`, NO Λ² sieve. Only `BoundingSieve` + `IsUpperMoebius` + `siftedSum_le_mainSum_errSum_of_upperMoebius`. `BRUN_ATTACK_PLAN`'s ~400 LOC estimate for B2 is wrong; B2 must build Λ² μ⁺ from scratch or use truncated-Möbius for a weaker Brun-type bound.
- **Mertens M1–M5** (merged 2026-09-25, commit `d2b2917e`): `ChebyshevUpper`, `AbelSummation`, `SumLogPOverPAbel`, `SumLogPOverPBound`, `ChebyshevLowerBertrand`, `SumOneOverPCrudeBound`, `ChebyshevLowerCentralBinom`. Chebyshev upper/lower, Abel summation, log-over-p bounds, Bertrand's postulate.

**Consequence for the Twin Prime track:** substrate-level BoundingSieve landed; Brun B2 (Λ² μ⁺ construction) remains the next literal endpoint. Track advanced from "witnesses + α-bridge only" to "substrate BoundingSieve + witnesses + α-bridge."

### 5. ch04:461 substrate-collapse pillar — 27 theorems (2026-09-17 → 26)

Four modules kernel-verified end-to-end today by `lake build EXIT=0` (3216 jobs):

- **r333** `SubstrateAutomorphismQuotientCollapse.lean` (`15c5c4df`, 8 theorems): every continuous unital ℂ-algebra endomorphism of T_∞ preserves τ_UHF (via r113); the trace-preserving "gauge" subgroup Aut_0 equals all of Aut(T_∞).
- **r334** `SubstrateInnerAutomorphismNontrivial.lean` (`20c0a587`, 8 theorems): Aut(T_∞) has non-trivial inner automorphisms; witness = conjugation by `1 + E_01` at substrate level 1.
- **r335** `SubstrateIdempotentTraceRigidity.lean` (`d74395ee`, 5 theorems): the K-theoretic trace range on projections is blind to the r334 witness — the natural "replace scalar trace with K-theoretic surrogate" repair fails.
- **r336** `SubstrateGaugeSubgroupsCollapse.lean` (`7b830120`, 6 theorems): every conjugation family collapses in the trace-preserving quotient regardless of group non-triviality.

Consequence: **ch04 Thm 4.18 is REPAIRED, not withdrawn** — `Aut_0 := Inn(T_∞)`; the corrected reading is `M⁴ = Aut/Inn = Out(T_∞)`, conditional on Out classification (already named open in ch04's own "Explicit Automorphism Classification" note).

Wire-up at `PF.lean:1352-1355` at commit `0d8ea1a4` (2026-09-26).

### 6. r337 strengthening + PremiseAudit meta-tool (2026-09-17)

`PF/Audit/PremiseAudit.lean` (`48e5f521`). Reflection-based Lean meta-programming that walks the axiom cone of any named theorem, extracts hypothesis conjuncts, and reports which are structurally load-bearing vs. dead. Validated in situ by strengthening `T_infinity_rigidity` — the `trace_unique` hypothesis was mechanically shown redundant and removed.

**This tool is the reason the OCIRC audit finding below is a mechanical fact rather than an editorial judgement.**

### 7. Two-anchor α-cascade capstone (2026-09-25)

`PF/TwoAnchorCascadeCapstone.lean` (`b08036ea`) + `PF/HodgeQuadraticFromTwoAnchors.lean` + `PF/PvsNPAnchorReduction.lean` + `PF/FiveWayFalsifiability.lean` + `PF/AlphaBalanceUnderTwoAnchors.lean` (`39fffbaf`) + `PF/AlphaBaselAndWallisUnderTwoAnchors.lean` (`9673a3ce`). Nine α-values doubly-anchored: Perelman 2003 (α_Poincaré = 1) + the Córdoba–Martínez-Zoroa / Buckmaster–Alpöge / OpenAI-formalized 2026 NS/Euler chain (α_NS = 3π/2). Five open Clay α-values (`α_YM, α_RH, α_BSD, α_Hodge, α_P/NP`) forced by two anchors + I6, I7, I8, I9, QG-bridge, Wave-22, Hodge-NP link.

### 8. O-CIRC premise-audit sweep — 213 targets, 114 findings (2026-09-18)

`codex/OCIRC_AUDIT_FINDINGS_2026-09-18.md`. Mechanical, not editorial. Load-bearing conclusions:

- **`T_infinity_rigidity` audits CLEAN** post-r337. Central substrate theorem is not in the same evidential class as the Referee-tier "rigidity forces X" family.
- **r301 universal capstone assumes RH by four routes** — two literal (RH-as-conjunct in `riemann1859_original_conjecture` and `bombieri2000_clay_official`), two by one-step modus ponens (`rh_hp_program_positive`, `mayer1991_cohen2025`). The theorem is valid; it carries no RH information.
- **`MinimalRigidityForces*` family: 35 / 35 with findings, 0 clean.** Every proof has `UnifiedMinimalInvariants.sector1_minimal` and `sector2_minimal` as DEAD hypotheses. Minimal rigidity is not what these theorems establish.
- **The α-skeleton identities are assumed, not forced.** `cross_millennium_shared_invariants_substrate_capstone` takes each of its six output identities as a premise field definitionally equal to the corresponding conclusion conjunct.
- **The Perelman "anchor" anchors nothing** in `perelman_anchored_cascade_substrate_capstone`: `α_Poincaré = 1` is an input hypothesis, not a used property of Perelman's theorem.
- **Headline capstone sweep, 18 targets: 5 clean, 13 with findings.**

**Corpus-wide reading:** the substrate-tier work (r113, r217, r280, r315, r331b/c, r333–r337, Brun B1, Mertens M1–M5) is the theorem class that carries information. The Referee-tier `SubstrateRigidity*Capstone` and "Millennium bundle" theorems are true but informationally hollow. This distinction is now mechanical.

---

## UPDATED 14-TRACK QUICK VIEW

| # | Track | Literal target | Substrate work | 5-week delta | Live residual strength |
|---|---|---|---|---|---|
| 1 | Riemann Hypothesis | Yes (`SpectralBijection.RiemannHypothesis`) | Deep (r120/r280/r315) + **r325→r331c edge chain** | r331b right edge, r331c top edge landed; r331d bottom edge in progress; `riemannHypothesis_below_15` = literal endpoint on r327 threading | FULL RESIDUAL for global RH; **BOUNDED literal endpoint reachable** below height 15 |
| 2 | P vs NP | Framework-internal | r123–r128 α-web; **r332 K-obstruction** | Two-anchor cascade + falsifiability at α_P, α_NP; OCIRC found α-identities assumed | FULL RESIDUAL |
| 3 | Navier-Stokes | Partial (smoothness `Prop := True`) | Substrate closures | **α_NS externally anchored** (Córdoba/Martínez-Zoroa/Buckmaster/Alpöge/OpenAI 2026); `Prop := True` still present | FULL RESIDUAL (continuum PDE) |
| 4 | Yang-Mills | Finite-dim only | Substrate closure + phenomenology | Two-anchor cascade forces `α_YM = 2` | FULL RESIDUAL (continuum QFT) |
| 5 | BSD | Typed anchor on 1 curve | α_BSD = 3π/4 | Two-anchor cascade forces `α_BSD = 3π/4`; OCIRC found `v4_CM_batch_surfaced` = 17 findings | FULL RESIDUAL (general rank) |
| 6 | Hodge | Substrate-typed | 13+ `Prop := True` anchors | Two-anchor cascade forces `α_Hodge = φ` via I8 + positivity | FULL RESIDUAL (dim ≥ 2) |
| 7 | Collatz | Literal | 20 witnesses + α-bridge | `native_decide` residuals reduced 20→~5 (progress; not zero) | FULL RESIDUAL |
| 8 | Strong Goldbach | Literal | 12 witnesses + α-bridge | Mertens M1–M5 landing gives classical prime-counting substrate; no direct Goldbach delta | FULL RESIDUAL |
| 9 | Twin Prime | Literal | 10 witnesses + α-bridge | **Brun B1 BoundingSieve landed** (`2904049e`); Brun B2 remaining but mathlib gap = ~400 LOC minimum | FULL RESIDUAL; Brun's theorem literal now within one landing |
| 10 | Kissing Number | ABSENT | None | — | (no PF work) |
| 11 | Unknotting | ABSENT | None | — | (no PF work) |
| 12 | Large Cardinal | ABSENT | Only CH framework attack | — | (no PF work; corpus disclaims LC axioms) |
| 13 | Irrationality of π + e | ABSENT | GS bundle only | — | (no PF work) |
| 14 | Euler-Mascheroni γ | ABSENT | mathlib bounds only | — | (no PF work) |

---

## EXTERNAL LANDSCAPE — WHAT MOVED (2026-08-23 → 2026-09-27)

External to PF, and material to PF's ranking:

- **OpenAI NavierStokesAndEuler** (2026-09-08, `github.com/openai/NavierStokesAndEuler`, Apache-2.0, Lean 4.34.0-rc2). Intellectual credit chain: Córdoba–Martínez-Zoroa (underlying blow-up mathematics; Buckmaster stated Martínez-Zoroa deserves Fields Medal recognition) → Buckmaster–Alpöge (Lean-verified Euler blowup, 2026-08-22) → OpenAI (formalization, Sept 8). Addresses (C)/(D) alternatives; **not** the primary Clay conjecture. OpenAI declined the Clay prize on that basis. **Consumed by PF as α_NS second anchor.**
- **OpenAI ten-proofs / "Astra"** (2026 announcement, `github.com/openai/ten-proofs`, Apache-2.0, Lean 4.32.0). Ten open problems in a 249-page manuscript with zero-sorry Lean certificates: (1) sphere packing → Cohn–Elkies threshold, (2) binary/spherical codes, (3) **non-sofic groups constructed** (Gromov 1999 settled), (4) **Connes rigidity for group von Neumann algebras DISPROVED**, (5) arithmetic circuit complexity / permanent, (6) quantum parallel repetition, (7) GapCVP, (8) Ehrhart volume, (9) multicolor Ramsey (Erdős 183), (10) extremal graph theory (Erdős 146, 180 disproved). **No PF integration performed; #4 (Connes rigidity disproof) is direct C*-neighbor of `T_infinity_rigidity` and materially sharpens the significance of PF's positive result.**
- **Anthropic — Fermat's Last Theorem formalized** (announced summer 2026). End-to-end computer-checked, 11 days, 13M lines of Lean, 29,500 intermediate theorems. Not adjacent to PF substrate.
- **Anthropic — Riemann Hypothesis progress** (unreleased Claude, 2026-08-11 announcement). 60 agentic sub-Claudes, 650 discarded ideas. **Direct competitive overlap with PF's r120→r315→r325→r331c chain.**
- **Anthropic — Jacobian conjecture disproved.** Not adjacent to PF substrate.
- **Anthropic — Vinogradov's Three Primes Theorem formalized** (3 days via Prove2Me collaboration protocol). Adjacent to Goldbach track but small compared to PF's Mertens landing.
- **Anthropic Science Lab** — expanded external-mathematician support: grants + research credits + free/discounted subscriptions. This is the infrastructure Pabs referenced as the reason to consider timing. It changes the *authoring-support* landscape, not the *math* landscape.

**Overall competitive posture for PF at 2026-09-27:** three of the fourteen tracks now have adjacent kernel-verified external results (RH via Anthropic, NS/Euler via Córdoba–Martínez-Zoroa/OpenAI, Connes rigidity via Astra). PF's unique moat is `T_infinity_rigidity` + K-theoretic obstruction (r217 + r332): no external actor has published a substrate-uniqueness theorem for a supernatural-3^∞ UHF class paired with a K-theoretic obstruction to α-forcing. This pair is the corpus's genuine originality.

---

## RE-RANK — CANDIDATE NEXT ATTACKS AT 2026-09-27

Baseline Rank-1 (substrate reality-check via `conjecture_8X2_nine_extremal_traces_falsified` theorem) has LANDED: `OPEN_PROBLEMS.md` Problem 1a marked FALSIFIED (2026-08-23 reconciliation, entry at line 17). Native-decide sweep is partial (20 → ~5). This audit drops that item; it is now cleanup, not the next attack.

Ranked per DIRECTIVE §XVII with the current external landscape and OCIRC findings folded in:

| Rank | Candidate | Axes affected | PF centrality | Cost | Circularity risk | Notes |
|---|---|---|---|---|---|---|
| **1** | **r331d bottom edge + r327 argument-principle threading → `riemannHypothesis_below_15`** | RH literal (bounded region) | HIGHEST — substrate-tier, not Referee-tier | LOW–MEDIUM (r331d likely symmetric to r331c via conjugation at t=−15) | LOW — proof uses mathlib `riemannZeta` machinery, no smuggled RH conjunct | The next brick already scoped by r331c architecture. Closes a literal statement about mathlib's `riemannZeta` in the bounded critical strip. Bypasses OCIRC-flagged Referee family entirely. |
| 2 | Finish native-decide sweep (Collatz, Polignac, Singmaster, OddPerfect, Brocard remaining) | Number theory hygiene | MEDIUM — policy compliance | LOW–MED | ZERO | Baseline Rank-2 partially done; leaving 5 uses in load-bearing files is a soft §I.2 gap. |
| 3 | Brun B2 (Λ² μ⁺ construction from scratch on mathlib `BoundingSieve`) | Twin Prime literal (Brun's theorem: `∑ 1/p over twin primes converges`) | HIGH | HIGH — mathlib has no Λ² sieve; Brun B1's plan-estimate proven wrong | LOW | The remaining classical prime-counting endpoint after Mertens M1–M5. Twin Prime's own famous residual reachable one landing after B2. |
| 4 | Type-upgrade `Prop := True` Hodge / Cohen2025 anchors (13+) | Hodge, cross-Millennium | HIGH | HIGH — mathlib Hodge gap is deep | LOW (scope preserved via r217 pattern) | Same pattern that lifted r217 substrate rigidity from prior placeholder territory. High value but multi-month. |
| 5 | Investigate whether Astra's Connes-rigidity counterexample lifts to any `Substrate3Inf` witness | Foundational — bears on PF's substrate-uniqueness moat | HIGHEST if the answer is yes; MED–HIGH corroboration if the answer is no | MED — requires reading Astra's ConnesRigidity.lean and mapping to Substrate3Inf | LOW–MED | New in this refresh. Astra disproved general L(G) rigidity; PF proved 3^∞ UHF rigidity. Whether the counterexample class touches the Substrate3Inf class is a well-scoped test. |
| 6 | Formalize Lefschetz (1,1) at codim 1 for K3 surfaces via mathlib cycle-class map | Hodge (literal) | HIGH | HIGH | LOW | Baseline Rank-5, unchanged. |
| 7 | Formalize "at least one of π+e, πe is transcendental" via Lindemann–Weierstrass on `x²−(π+e)x+πe` | π + e track (literal) | LOW | MED–HIGH (LW in mathlib?) | ZERO | Fresh literal endpoint on a currently-absent track. |
| 8 | Formalize `τ_8 = 240` via E₈ minimum-vector count (Odlyzko–Sloane 1979) | Kissing (fresh) | LOW | HIGH | ZERO | Baseline Rank-7, unchanged; still an entry-level literal endpoint. |
| — | Rank-11 baseline (HP-operator from substrate) | RH | HIGHEST | VERY HIGH | HIGH (definitional recovery) | Retained but not recommended: the OCIRC audit confirmed the α-web mechanism is not substrate-forced, so building the HP operator "from the substrate" is the RH problem itself. r332 K-obstruction sharpens this — do not attempt without a route around the obstruction. |

---

## RECOMMENDED NEXT LANDING — 2026-09-27

## The graph chooses: **Rank 1 — close r331d bottom edge and thread r327 argument principle → `riemannHypothesis_below_15`.**

### Statement of the recommended landing

Land a Lean file (working name `PF/Analytic/RiemannXiBottomEdge_r331d.lean`) that proves the bottom-edge counterpart to r331c:

```
Re ξ⟨σ, -15⟩ < -1/10⁴  on σ ∈ [0,1]
```

via r331b (right edge) + r326 reflection at t = −15, symmetric to the r331c top-edge argument. Expected shape: four kernel-clean theorems, ~100 L, `[propext, Classical.choice, Quot.sound]` audit budget.

Then thread `PF/Analytic/RiemannXiArgumentPrinciple_r327.lean` around the closed r329b (bottom-edge on `[0,1]`) + r331b (right edge) + r331c (top edge) + r331d (bottom edge at `t=−15`) rectangle to obtain:

```
theorem riemannHypothesis_below_15 :
  ∀ s : ℂ, 0 < s.re → s.re < 1 → |s.im| < 15 → riemannZeta s = 0 → s.re = 1/2
```

A statement about mathlib's `Complex.riemannZeta`, not about a PF surrogate.

### Why this landing has highest global leverage

- **Axes affected:** RH literal (bounded region). Adjacent value to the two-anchor cascade (α_RH = 3/2 forced by I9 + α_YM = 2 is the framework-side statement; `riemannHypothesis_below_15` is the mathlib-side literal endpoint).
- **PF centrality:** HIGHEST at the substrate tier. The r120 → r280 → r315 → r325 → r331c chain has been the corpus's most sustained research arc for six months; r331d is the next brick on architecture already committed.
- **Residual < famous?** YES. Full RH is bounded critical strip for all height; `riemannHypothesis_below_15` is bounded strip AND bounded height. A classically-verified region (Odlyzko–Platt have numerical verification for the first 10^13 zeros to `t ≈ 3.06 × 10^12`) is being reproved by a formal argument that does not consult a numerical database — a legitimate literal theorem about `riemannZeta`.
- **Existing kernel infrastructure:** ~95% complete. r325 through r331c all kernel-clean at HEAD. Missing: r331d (memory: "likely symmetric via conj at t=−15") and r327 threading.
- **Literal-theorem yield:** ONE new theorem stating a fragment of the Clay conjecture, expressed against mathlib's `riemannZeta`.
- **Falsifiability:** N/A — a proof of a mathlib-typed inequality is proved or it isn't.
- **Circularity risk:** LOW. The r325–r331c bricks use mathlib functional-equation, log-branch, and holomorphy-on-slit-plane apparatus; no RH conjunct anywhere in the cone. The r327 argument principle likewise consumes mathlib complex-analysis primitives — not PF's five-route HP program (which per OCIRC assumes RH four ways).
- **Formalization cost:** LOW–MEDIUM. Memory-tracked "likely symmetric via conj at t=−15" plus prior r331c panel-generator template gives r331d probably 100–200 L. r327 threading is the harder integer: probably 200–400 L depending on how much mathlib argument-principle apparatus needs shaping.
- **Mathematical novelty:** MEDIUM (the mathematics is the classical rectangular contour argument; PF's contribution is the certified numeric substrate on the r120 side that makes the rectangle explicit).
- **Reusability:** HIGH. Same architecture extends to arbitrary bounded height with a wider rectangle. Height-15 is the r120 substrate's native scale; extending to height N requires new panel generation but no new theory.
- **Substrate-tier vs. Referee-tier:** substrate-tier. Every declaration in the cone (per OCIRC audit protocol) will audit against `T_infinity_rigidity`-class evidence, not against `MinimalRigidityForces*`-class findings.

### Competitive posture

Anthropic's unreleased Claude made "major improvement on decades-old work on the Riemann hypothesis" via 60 agentic sub-Claudes and 650 discarded ideas (2026-08-11). Publicly reported detail is thin. PF's r120 → r315 → r325 → r327 → r331 chain is an entirely different attack: a hand-designed, kernel-verified structural closure via certified theta-quadrature + explicit rectangular contour bounds, not a search over 650 auto-generated attempts. The two do not overlap in method. `riemannHypothesis_below_15` shipping as a mathlib-typed literal endpoint gives PF a defensible, independently-designed, kernel-checked position in the RH landscape adjacent to whatever Anthropic eventually publishes.

### Why NOT the ranked alternatives (short)

- **Rank 2 (native-decide sweep):** Necessary cleanup, not a research move. Doubles as a warm-up if the next session finds r331d stalled.
- **Rank 3 (Brun B2):** Real and reachable Twin-Prime endpoint, but mathlib's Λ² gap makes it multi-week. Better as the target after `riemannHypothesis_below_15`.
- **Rank 4 (Hodge Prop := True upgrade):** High-value, multi-month.
- **Rank 5 (Astra Connes-rigidity plug-in check):** Fresh, well-scoped, but corroborates rather than closes. Better as a follow-up once r331d ships.
- **Rank 11 baseline (HP-operator from substrate):** Confirmed by OCIRC to be RH itself. Do not attempt without a route around r332's K-theoretic obstruction.

### The doctrine behind the recommendation

DIRECTIVE §XV: "let the substrate decide." At r332 the substrate decided it does not force the α-web. At r217 it decided it is unique up to `*`-iso. At r315 it decided Ξ(15) > 0. The next brick the substrate has already assembled the scaffolding for is r331d + r327 threading. That is the substrate's chosen next move, not an editorial choice.

DIRECTIVE §XVI ("framework FIRST; math truth over narrative"): the framework-first move is not to write a Clay slice paper. It is to lay the next brick and let the kernel decide. `riemannHypothesis_below_15` is a mathlib-typed inequality — kernel decides directly, no narrative layer.

DIRECTIVE §XVIII ("do NOT auto-implement"): this refresh preserves the read-only discipline. Awaiting Pabs's explicit go / no-go before touching PF/Analytic/RiemannXiBottomEdge_r331d.lean.

---

## APPENDIX A — PATHOLOGIES UPDATED

### A.1 `native_decide` — reduced but not eliminated

Baseline (2026-08-23): 20+ uses in `PF/NumberTheory/`. Current (2026-09-27): approximately 5. Files still carrying uses require named audit before next capstone rebuild.

### A.2 `def X : Prop := True` — largely unchanged

- `PF/NS2DGlobalRegularity.lean:318` — unchanged.
- `PF/AlgebraicGeometry/Cohen2025_HodgeConjecture_NamedAnchors_2026_06_19.lean` — 6× unchanged.
- `PF/AlgebraicGeometry/Hodge_Substrate_NamedAnchors_2026_06_19.lean` — 7× unchanged.
- `PF/AlgebraicGeometry/CycleClassMapAtCodim2Attempt.lean:502` — unchanged.

Baseline Rank-3 (type-upgrade following r217 pattern) is still on the ledger and still the honest fix; multi-month cost.

### A.3 Referee-tier informationally-hollow capstones — now mechanically characterized

Per OCIRC 2026-09-18:

- 213 corpus capstones audited: 99 CLEAN, 114 with findings.
- r301 universal capstone: 4 RH-circularity routes. Theorem valid; carries no RH information.
- `MinimalRigidityForces*` family: 35 / 35 with findings, 0 clean.
- `PF.Referee.BSDCapstoneTypedBridgeV4.v4_CM_batch_surfaced`: 17 findings.
- `RHCapstoneTypedBridgeV4` cluster: 6 "routes" × 12 findings each — same-assumption-different-name pattern.

**Distinction now mechanical**: `T_infinity_rigidity` audits CLEAN post-r337; Referee-tier `SubstrateRigidity*Capstone` cluster audits with findings. The two are in different evidential classes. External presentation must not conflate.

---

## APPENDIX B — CROSS-REFERENCE TO BASELINE (2026-08-23)

- Baseline HEAD `4f7b216d` → this HEAD `0d8ea1a4`. 21 commits ahead of `origin/master` locally (not pushed).
- Baseline Rank-1 recommendation (Problem 1a → FALSIFIED): **LANDED** at `OPEN_PROBLEMS.md:17` on 2026-08-23.
- Baseline Rank-2 recommendation (native_decide sweep): **PARTIAL** (20 → ~5).
- Baseline Ranks 3–11: unchanged status.
- New landings not in baseline: substrate rigidity r217 kernel-verified (2026-09-11), r325→r331c edge chain (2026-08-24 → 2026-09-22), Brun B1 (2026-09-23), Mertens M1–M5 (2026-09-25), r333–r337 substrate-collapse pillar (2026-09-17 → 26), two-anchor α-cascade (2026-09-25), PremiseAudit meta-tool (2026-09-17), O-CIRC 213-target sweep (2026-09-18), r331c top edge (2026-09-22).

---

## APPENDIX C — Xi(15) STATUS

Xi(15) arc frozen at `4f7b216d` per DIRECTIVE §XI. Two independent formal architectures (r313–r314e via theta truncation + certified `|R_{≥2}| < 1/10⁶`; r315 direct via r120 panel-generator specialization at t = 15) both discharge `Xi_Positive_At_15` with kernel-only axioms. Companion literal endpoint r324 (`8e7bb46f`): critical-line `riemannZeta` zero below height 15 excluded via r120 + r315 composition.

---

**End of refresh.** Awaiting Pabs's explicit go / no-go on the recommended Rank-1 landing (r331d + r327 threading → `riemannHypothesis_below_15`) before any implementation. Per DIRECTIVE §XVIII: **do NOT automatically implement**.
