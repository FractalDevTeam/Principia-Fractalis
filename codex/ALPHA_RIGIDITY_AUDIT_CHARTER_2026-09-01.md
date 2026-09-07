# α-Skeleton Rigidity Audit — Scoping Charter ("DELETE THE NUMBERS")

Scoping date: 2026-09-01. Read-only; Legion-side copies only. No source file touched; no build run.
Audit executes **after r331b**. This document is the charter, not the audit.

**Ground truth source**: `D:\CLAUDE-i9\tmp\pf-audit-r325-20260825-0416\` (freshest Legion copy; 2,563 `.lean` files, ~724k LOC incl. older siblings). `D:\Principia-Fractalis-Repo\remote-backup\` is Jun-24-stale — per Grand Ledger §6.4, do not cite from it except the 06-23 clean paper. All file:line refs below are r325-snapshot paths under `PF_Lean4_Code/PF/` unless noted.

**Negative-results ledger respected throughout** (`_audits/pf-concordance-2026-08-30/PF_Concordance_GrandLedger_2026-08-30.md`). Prior results that BIND this audit — respected, not re-litigated, and under no circumstances resurrected as open questions:

| ID | Result | Artifact |
|---|---|---|
| N1 | **α-web underdetermination (r124)**: the 11-invariant system is a 1-parameter family (α_BSD free); the 1/4 NP-offset is a free parameter; I2, I8 redundant (I6 also, thm at :376). 7 of 9 α's pinned given positivity. | `AlphaWebDegreesOfFreedom_r124.lean` :179, :190, :224, :317, :344, :359, :376, :428; companion `codex/alpha_web_system.py` (Gröbner: dim V(I)=1) |
| N2 | **Trace-range obstruction (r113+r123)**: substrate projection-trace range is ℤ[1/3]; 7 of 9 α's are outside it (2-adic and 5-adic values vs. 3^∞ supernatural number). Kills any "substrate forces the α's" route. | `AlphaFromSubstrateKTheory_r123.lean` (`alpha_table_memZ13_verdict` :326); `SubstrateTraceUniqueness.lean` (r113) |
| N3 | **Problem 1a FALSIFIED (2026-08-23)**: extremal-trace-space ≅ 9-point α-set is mathematically impossible in the current substrate (composition of N2). | `tmp/.../OPEN_PROBLEMS.md` §1a + r123 reconciliation section |
| N4 | **Circular α_NP derivation**: the bare generating-function route machine-checked to *exclude* √2 and φ+1/4; "forcing" fed φ and 1/4 in and got φ+1/4 out. | `TuringEncoding/WeightedDigitalSumGeneratingFunction.lean` :131 (`bare_route_structural_finding`); `AlphaNPDerivationAttempt_r122.lean` |
| N5 | **PolylogEigenvalueConjecture open**; three mutually inconsistent gap values (0.0891 empirical / 0.1306 golden / 0.054 Lean) unreconciled. | `MillenniumSixReductions.lean` :2176–:2302; Grand Ledger §7.10 |
| N6 | Refuted numeric anchors (never load-bearing again): α_EM = R_f(1,2)·π/10 (wrong sign, ~35×); ω_c = 2.13198462 (not a value; R_f(2,s)=ζ(s)); Δ_YM = 420.43 MeV (arithmetic false; ceiling 62.3 MeV); both ch₂=0.95 first-principles derivations. | `RfIntegerAlphaDichotomy.lean`; Grand Ledger ch7/ch23/ch6/ch11 entries |

---

## §1 — Numeric anchors in load-bearing definitions

### 1.1 The α-table proper (primary anchors)

Canonical definition site: `CrossMillenniumSharedInvariants.lean` :64–:88. Mirror carrier: `AlphaSkeletonUniqueness_r128.lean` (`canonical`, :~135). Paper statement: `Papers/principia_fractalis_alpha_skeleton_2026-07-13.tex` :236–:242.

| # | Name | Value | Def site (r325) | Role |
|---|---|---|---|---|
| A1 | α_Poincaré | 1 | `CrossMillenniumSharedInvariants.lean:64` | Perelman anchor; sole admitted numerical input of r128 |
| A2 | α_P | √2 | `:67` | P-class eigenvalue parameter (conjectural interpretation) |
| A3 | α_NP | φ + 1/4 | `:70` | NP-class; the 1/4 is N4's circularity locus |
| A4 | α_RH | 3/2 | `:73` | RH axis; also the T₃^sym "carrier value" (`T3SymCanonicalAlphaCarrierAttempt.lean:136`) |
| A5 | α_NS | 3π/2 | `:76` | NS axis |
| A6 | α_YM | 2 | `:79` | YM axis |
| A7 | α_BSD | 3π/4 | `:82` | BSD axis; N1's free parameter |
| A8 | α_Hodge | φ | `:85` | Hodge axis |
| A9 | α_QG | √(2π) | `:88` | TOE completion |
| A10 | α_PvNP | 5/4 | `TuringEncoding/PNPClassSeparationPrecisionBridge.lean:457` | 10th anchor, sector-1 only; "polylog deficit" gloss; **outside** the 9-tuple of the paper and r128 — scope decision needed (§7.Q1) |

### 1.2 Auxiliary numeric anchors coupled to the skeleton

| # | Value | Site | Role | Status |
|---|---|---|---|---|
| B1 | λᵢ = π/(10·αᵢ) universal coupling | `AlphaFromSubstrateKTheory_r123.lean:424` (`lambda0`); paper :151–:156 | Ties α-table to λ-skeleton; the π/10 is a declared constant | Interpretation conjectural (N3 successor unformalized) |
| B2 | ch₂ threshold = 19/20 | `Consciousness/QuantumClassicalDecoherenceThreshold.lean:93` | Consciousness threshold | Both derivations RN (N6); literal rational, self-disclosed |
| B3 | Δ_YM := 3/2 declared gap | V4/V3/V2 chain, self-disclosed at `Referee/YMSubstrateScopeAccountability.lean:160` | YM substrate gap | Declared, not derived (Grand Ledger 5.4) |
| B4 | Spectral-gap trio 0.0891 / 0.1306 / 0.054 | `MillenniumSixReductions.lean:2176–:2302` | P≠NP gap | N5: unreconciled; RN on the 0.0891 claim |
| B5 | Cosmology: H₀ 69.8 (vs 67.4/73.0 brackets), Ω_Λ 0.7 | `Cosmology/LambdaCDMRebuttalEnergyConservation.lean:232–:242`; `Wave58/Ch08FieldEquationsConcrete.lean:260`; `Referee/FrameworkFalsifiabilityConditions.lean:74,:81` | Bracket-certified only (KV-definitional per ledger) | Suppression mechanism RN (w₀=+285.6) |
| B6 | External empirical anchors (IBM peaks at 3/2, φ+1/4; N_ν=2.984; π√2/150 splittings; E₆=78) | paper abstract :75; `IBMPeaksGaloisPair.lean` etc. | Corroboration layer | IBM "EXACT match" is `rfl` (ledger §8.11); recon-only for this audit |

**Verification note**: A1–A9 def-sites read directly this session; B-rows grep-verified at r325 plus Grand Ledger cross-check. Not every one of the ~400 `Alpha*.lean` bundle files was opened; the audit's step 1 should re-run the enumeration mechanically (grep pattern in §5.3) to catch stragglers.

### 1.3 Numeric coefficients living INSIDE the constraint set (the actual "delete" targets)

These are the numbers the audit deletes. After r128's cleanup the irreducible numeric content of the rigidity claim is:

| # | Coefficient | Where it lives | Gloss offered |
|---|---|---|---|
| C1 | `+1` shift | I7 / `ym_shift` (r128 :~118) | "gauge-duality doubling" |
| C2 | `3` product | I9 / `rh_prod` | "corpus invariant" (no independent gloss) |
| C3 | `π` scaling | L5 / `ns_scaling` (α_NS = α_RH·π) | "π-scaling law" |
| C4 | `2` trace coefficient | L3 / `np_trace` (α_Po + 2(α_NP−α_Hodge) = α_RH) | "Galois trace law on coset φ+ℚ" |
| C5 | `π` in QG norm | L4 / `qg_norm` (α_QG² = α_YM·π) | "Galois: Nm = −α_YM·π" |
| C6 | `1` anchor | A / `anchor` (α_Poincaré = 1) | Perelman 2003 (external; but see N/B in §4: ledger 5.7 — Perelman does not independently assign the α-value) |
| C7 | positivity ×9 | `IsPositive` (r128 :~100) | branch selection on quadratics |
| C8 | superseded baked values: `(3/4)·π` as hypothesis `inv_BSD` | `Referee/MinimalSubstrateRigidity.lean:87`, `Referee/CrossMillenniumCascadeParameterized.lean:122` | "framework's BSD geometric anchor" — see §6.H1 |
| C9 | superseded baked values: `1/2` in M1, `1/4` in M7/S2-3, `2π` in S2-4, `9/4` in I2, `8/3` in I12 | `Referee/MinimalSubstrateRigidity.lean:82,:92`; `Referee/MinimalSubstrateRigiditySector2.lean:96–:102`; paper I2/I12 | various glosses — see §6 |

---

## §2 — Surviving interface per anchor (what remains if the number is deleted)

| Anchor | Independently-defined surviving constraint | Independence assessment (to be tested, not assumed) |
|---|---|---|
| α_Hodge | x² = x + 1 (minimal polynomial; L1 in α_Po-relative form) | Structural IF the "golden quadratic over the Poincaré unit" story stands without knowing φ; the quadratic itself is number-free once α_Po is symbolic |
| α_P | x² = α_YM (L2: Tr 0, Nm −α_YM) | Structural relative to α_YM |
| α_QG | x² = α_YM·π (L4) | Structural **modulo C5**: the choice of π (not e, not 1) in the norm is an input |
| α_NP | α_Po + 2(α_NP − α_Hodge) = α_RH (L3) | The trace-law form is structural; but N1 proved the offset value free in the 11-web, and N4 proved the value's "derivation" circular — L3 is the *replacement* interface and is exactly what the audit must stress-test |
| α_RH | α_RH·α_YM = 3 (I9) | The 3 is bare (C2). Alternative gloss "α_Po + 1/2 critical-line shift" (M1) has the 1/2 bare. No third route currently in-corpus |
| α_YM | α_YM = α_Po + 1 (I7) | The +1 is bare (C1) |
| α_NS | α_NS = α_RH·π (L5); α_NS = 2·α_BSD (I5) | π-scaling is the load-bearing new law of r128; its independent justification is prose |
| α_BSD | α_NS = α_YM·α_BSD (I6) — BSD is *derived* in r128 from L5+I6 | Structural given L5; N1 showed that without L5 (or I12's 8/3) it is free |
| α_Poincaré | anchor = 1 | External (Perelman) per corpus; ledger 5.7 caveat stands |
| α_PvNP | α_PvNP − α_Po = 1/4 (M5) | 1/4 bare; same class as the NP offset |
| λ-coupling | λᵢ·αᵢ = π/10 (`lambda0_mul_alpha`, r123 :426) | π/10 bare; N2/N3 sever its substrate justification |

---

## §3 — The candidate constraint system (the interconnection claim, explicit)

Three nested formulations exist in-corpus; the audit must fix which is canonical **before** solving (§7.Q2):

**S-11** (r124's target): I1–I11 of `AlphaWeb` (`AlphaWebDegreesOfFreedom_r124.lean` :101–:140) = the 11 invariants of substrate-theorem conjunct C8. **SOLVED (N1)**: dim 1, α_BSD free, offset free, 3 redundant. Do not re-solve except as regression check.

**S-12** (paper's Thm `thm:invariants`, tex :248–:262): S-11 + I12 (α_QG² = (8/3)·α_BSD). Uniqueness of positive solution kernel-proved at `AlphaSkeletonUniqueness_r128.lean:233` — but I12's 8/3 is a C9 baked coefficient; the paper's own r128 header concedes the paper "needs \[8/3\] as an independent hypothesis to pin α_BSD."

**S-8+A** (r128's `StructuralLaws` + anchor, the corpus's current sharpest form):
L1 hodge_minpoly, I7 ym_shift, L2 p_norm, I9 rh_prod, L3 np_trace, L4 qg_norm, L5 ns_scaling, I6 bsd_gauge; + anchor (α_Po=1 **or** α_BSD=3π/4, interchangeable per `alpha_skeleton_unique_from_BSD` :327); + positivity. Uniqueness kernel-proved. r128's honest-scope note: "L1–L5 are inputs… the substrate does not force them."

**Extended layer**: 17 further identities (29 total), `Referee/CrossMillenniumInvariants_Extended_2026_06_19.lean:217`; locus form L1–L16 at `AlphaSkeletonAlgebraicLocusBundle.lean:32`. All derivable from the canonical point; they add no rigidity (consequences, not constraints) — treat as regression suite only.

**The audit's actual object — S-Δ ("numbers deleted")**: take S-8+A; replace every C-row coefficient with a symbol (shift s, product p, scale c, trace-coeff t, QG-norm base b, offset in M5, anchor a); retain only the *shapes* (minimal-polynomial forms, product/sum forms, coupling form) plus positivity. Solve for (α₁…α₉, s, p, c, t, b, a) — or, in the restricted variant, for the α's with coefficients ranging over the declared basis field. Two variants, run both:

- **S-Δ1 (coefficient-symbolic)**: full deletion as above. Expected outcome: high-dimensional solution manifold; the finding is its dimension and which α-ratios are invariant across it — that residue IS the interconnection content.
- **S-Δ2 (interface-only)**: keep only constraints with a surviving independent interface per §2 column 3 after adjudication (§7.Q3), with their coefficients. Uniqueness here would be the strong evidence for the thesis; underdetermination maps the real degrees of freedom and their coordinates.

---

## §4 — Constraint classification

| Constraint | As identity of the canonical values | As independent rigidity input | Notes |
|---|---|---|---|
| I1–I16 / extended 29 | **Kernel-proved** (axiom-free; `#print axioms` guards present) | n/a — facts about chosen constants | KV(trivial) grade per ledger vocabulary |
| r124 underdetermination theorems | **Kernel-proved negatives** | binding (N1) | includes redundancy of I2, I6, I8 |
| r128 uniqueness (S-12, S-8+A, from-BSD) | **Kernel-proved conditionals** | hypotheses carry all numeric content | honest-scope note in-file |
| Glosses: "gauge-duality doubling", "π-scaling law", "Galois trace law", "critical-line 1/2", "polylog deficit", "BSD geometric anchor" | — | **Prose-only** | zero formal counterparts found this pass; the audit's §2 adjudication targets |
| Substrate → α forcing (any route) | — | **Previously refuted** (N2, N3) | out of scope permanently absent new mathematics |
| α_NP / α_P from computation | — | **Previously refuted** (N4, N5) | PolylogEigenvalueConjecture remains the open carrier |
| Perelman anchor as *external* assignment | — | **Contested by own ledger** (5.7: "does not independently assign the α-value") | treat a as symbolic in S-Δ1 accordingly |
| Coefficient-rigidity §sec (1,000 random 12×9 systems, 1% perturbation) | numerics | **Recon-only** | random-system inconsistency is generic for overdetermined systems; it does not bear on whether *these* coefficients encode foreknowledge. Do not admit as evidence in the audit |

---

## §5 — Decision problem, precisely

**Fix** the ambient field: ℝ, with π transcendental over ℚ and φ, √2, √5 algebraic; exact computation in ℚ(π)[α₁…α₉, symbols] (r124's companion already works over ℚ(π)).

**P1 (regression)**: re-derive N1 and r128 results mechanically from source; confirm dim(S-11)=1, redundancy set, uniqueness of S-12/S-8+A. Any mismatch is a corpus bug, filed not fixed.

**P2 (S-Δ1)**: compute the Gröbner basis / prime decomposition of the S-Δ1 ideal. Report: dimension; independent-variable sets; the sub-variety of coefficient space over which the α-fiber is 0-dimensional; invariant ratios (candidate: α_NS/α_BSD = 2, α_P²/α_YM = 1 — the pure-shape survivors). **Unique ⇒** interconnection thesis evidenced at the shape level. **Positive-dimensional ⇒** the free coordinates are the theory's actual parameters; name them.

**P3 (S-Δ2)**: after §7.Q3 adjudication, solve the interface-only system. Same reporting. Quotient handling: without positivity, the solution set carries the sign/Galois action (x↦−x on quadratic roots; φ↦1−φ; conjugation over ℚ(√5) — cf. `IBMPeaksGaloisPair.lean`); report the quotient and whether positivity is the only branch-selector, and what *independent* principle justifies positivity (currently: none stated — prose gap).

**P4 (honesty closure)**: for every §6 flag, a one-line verdict: number deleted and recovered (derived), or number deleted and lost (declared). This table is the audit's §III deliverable.

**Tooling estimate**

| Layer | Tool | Effort |
|---|---|---|
| Exact algebra | sympy Gröbner over ℚ(π) extending `codex/alpha_web_system.py`; Singular/Macaulay2 as cross-check if dim > 1 | small; r124 precedent exists |
| Kernel formalization | Lean 4, pattern of r124/r128 (structure-with-hypotheses + forcing/freedom theorems); mathlib only, `#print axioms` guards | medium; the S-Δ1 freedom theorems are r124-shaped |
| Numerics | recon only — plotting solution manifolds, sanity-checking Gröbner output; admits no evidential weight | trivial |
| Build | `lake build PF` on the audit modules only; do not rebuild the full 2,563-file tree | bounded |

---

## §6 — §III honesty risks: numbers baked in and called derived

Flagged most severe first. Each is a place where deleting the number reveals it was an input.

| # | Flag | Site | Severity |
|---|---|---|---|
| H1 | `inv_BSD : a_BSD = (3/4)·π` sits **inside** "MinimalSatisfiesInvariants" while the capstone docstring announces α_BSD "forced"; the unified capstone (`Referee/MinimalSubstrateRigidityUnified.lean:146`) advertises "ALL NINE α-values are forced… 0-dimensional variety" on hypotheses containing the value | `Referee/MinimalSubstrateRigidity.lean:87`; `Referee/CrossMillenniumCascadeParameterized.lean:122` | **High** — this is the exact assumed-as-derived pattern; r128's header says so explicitly ("pins its values from TWO anchors, not one") |
| H2 | Paper Thm `thm:alpha-unique` proof-sketch derives α_BSD "combining (I3) and (I12)" — i.e., from the 8/3, which is the value 3π/4 restated as a coefficient | tex :267–:272 | **High** — mitigated only if the audit finds an independent interface for 8/3 |
| H3 | The "π-scaling law" L5 (α_NS = α_RH·π) is r128's replacement for I12; its justification is one prose phrase. If L5 is only motivated by the values it reproduces, H2 has moved, not resolved | `AlphaSkeletonUniqueness_r128.lean` §StructuralLaws | **High** — the audit's central adjudication |
| H4 | The 1/4 offset: r124 proved it free; L3 re-derives it from "Galois trace law" whose target (Tr = α_RH) is itself glossed prose-only; N4's circularity finding stands | r124 :317; r128 np_trace | **High** |
| H5 | M1's `1/2` ("critical-line position") imports the RH critical line into the *definition* of α_RH while ch20's own status is that RH-relevant content is conditional | `Referee/MinimalSubstrateRigidity.lean:82` | Medium |
| H6 | α_PvNP = 5/4 "polylog deficit" — bare 1/4 again, and the polylog conjecture is the open carrier (N5) | `PNPClassSeparationPrecisionBridge.lean:457` | Medium |
| H7 | Perelman anchor presented as external corroboration; ledger 5.7: the assignment α_Poincaré=1 is substrate-internal | ledger §5.7 | Medium |
| H8 | Coefficient-rigidity section (random-systems + perturbation) presented as refuting reverse-engineering; it is consistent with reverse-engineering (any exactly-satisfied overdetermined system behaves this way) | tex §sec:coefficient-rigidity | Medium — wording risk in any future submission |
| H9 | Paper cites `PF/Referee/CrossMillenniumInvariants.lean` for I1–I12 and (per r128's header) previously mis-cited the uniqueness theorem; citation hygiene between paper and corpus needs one pass | tex :263; r128 header | Low |
| H10 | λ-coupling π/10 called "universal" while its substrate derivation is severed by N2/N3 | paper :156; r123 | Medium |

---

## §7 — Open scoping questions for Pablo (answer before audit start)

- **Q1**: Is α_PvNP (5/4) in scope as a 10th unknown, or excluded as sector-1-internal? (r128's 9-tuple excludes it; the unified capstone includes it.)
- **Q2**: Canonical system = S-8+A (recommended: it is the corpus's sharpest and most honest form), with S-11/S-12 as regression baselines?
- **Q3**: Adjudication rule for §2 column 3 — what counts as an "independently defined interface"? Proposed bar: a constraint qualifies iff its statement can be written without any constant from §1.3 *and* its motivating gloss cites a formal object elsewhere in the corpus that does not itself import the α-values. Under this bar, current expectation (to be tested): L1, L2, I5/I6-shape qualify; I7, I9, L3-target, L4-π, L5-π, anchors do not yet.
- **Q4**: Does the audit run pre- or post-r331b merge of the Legion copies? (r326–r331b exist in no Legion-side copy; they are RH-finite-height work and should not affect the α-system, but confirm.)
- **Q5**: Output form — negative results appended to OPEN_PROBLEMS.md per house additive style, plus a standalone r33x-numbered Lean module pair (freedom theorems + any surviving forcing theorems)?

---

## §8 — What would count as what (pre-registered reading of outcomes)

- **S-Δ2 unique (up to Galois/sign quotient)**: the interconnection thesis has real content at the interface level; publishable as a rigidity theorem *about the interface system*, with §6 flags resolved.
- **S-Δ2 positive-dimensional**: the free coordinates are the framework's actual free parameters; the honest successor to the "no free parameters" abstract claim is "k free parameters, here they are." This outcome is also valuable and is the one N1 predicts.
- **Either way**: no outcome of this audit bears on any Clay problem (per ledger §5 all six residuals are full-strength), and no outcome revives N2/N3/N4 routes.

*Charter ends. Verification pass: all file:line citations in §1.1, §1.3, N-table, and §6 were read or grep-confirmed directly against the r325 snapshot this session; B-table rows and ledger quotations cross-checked against the Grand Ledger. Not independently re-verified: kernel status of cited theorems (no build run), and the ~400-file Alpha bundle periphery beyond the mechanical grep.*
