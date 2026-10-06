# SEMANTIC PARITY MAP — headline TOE and Millennium arcs

**Date:** 2026-10-06
**Author:** Pablo Cohen + Claude Opus 5

## How to read this

Each row is: **manuscript claim → intended object → current Lean object → exact
proved statement → assumptions → missing bridge → strongest repair.**

The governing rule, and it is a correction to how the 2026-10-06 audits were
first reported: **a vacuous, proxy-level, obsolete or wrong Lean encoding is
evidence about the formalization, not about the mathematics.** Missing Lean
coverage locates formalization work; it never downgrades a manuscript theorem.
Equally, a clean build establishes exactly its formal statement and no more.

Classification taxonomy used: *exact theorem · conditional theorem · physical
premise · conjectured bridge · operationalization · proxy · toy/scaffold ·
retrospective fit · prospective prediction · unformalized · obsolete/refuted
implementation.*

---

## 1. SUBSTRATE — `T_∞` rigidity

| | |
|---|---|
| **Manuscript claim** | Glimm 1960 UHF classification specialized to supernatural `3^∞` |
| **Intended object** | the UHF(`3^∞`) C\*-algebra, classified up to isomorphism |
| **Current Lean** | `SubstrateRigidity.lean` `T_infinity_rigidity`; `Substrate3Inf` (4 fields) |
| **Exact proved statement** | `(A : CStarAlgebra) → Substrate3Inf A → Nonempty (A ≃⋆ₐ[ℂ] TimelessFieldCompletion)` — Glimm **uniqueness for a fixed tower** |
| **Assumptions** | the four `Substrate3Inf` fields; all real mathlib objects, nothing asserted-as-conclusion |
| **Missing bridge** | subsequence invariance, and non-isomorphism across distinct supernatural numbers — both need a `K₀` functor |
| **Classification** | **exact theorem** |

**This is the strongest result in the corpus.** `T_∞` is genuinely constructed:
Kronecker embedding `M_{3^k} → M_{3^{k+1}}` → mathlib `DirectLimit` →
`UniformSpace.Completion` → a real `CStarAlgebra` instance on a *proved*
C\*-inequality. The load-bearing step is a **1098-line from-scratch
Noether–Skolem** for unital \*-homs `M_n(ℂ) → M_{kn}(ℂ)`. Vendored mathlib has no
UHF, no Glimm, no C\*-K-theory, no Murray–von Neumann. ~2700 lines, zero `sorry`,
zero axioms.

**Repair (small, text-only):** the Lean header and `PF.lean:1364` already say
"uniqueness half, fixed tower". `frontmatter/title.tex:48` and
`Papers/pf_substrate_rigidity_alpha_obstruction_2026-09-10.tex:103` still say
"classification". Propagate the correction the Lean already carries. Also update
the paper's structure description (it describes the pre-r337 five-field version;
unique traciality is now the *conclusion* `Substrate3Inf.trace_unique`).

---

## 2. α-SKELETON

| | |
|---|---|
| **Manuscript claim** | nine α-values *derived* from the substrate |
| **Intended object** | substrate invariants forcing the nine constants |
| **Current Lean** | `CrossMillenniumSharedInvariants` (nine literals + 11 identities); `AlphaSkeletonUniqueness_r128` (8 laws + anchor) |
| **Exact proved statement** | `alpha_skeleton_unique : AlphaSkeleton → IsPositive → SkeletonLaws → s = canonical` — the triangular system has a unique positive solution |
| **Assumptions** | the eight laws L1–L5, I6, I7, I9 are **postulates**; `anchor : aPoincare = 1` |
| **Missing bridge** | nothing links `MemZ13` to `K₀` of the substrate; `KZeroCarrier := ℤ × ℕ` is a raw product, not `ℤ[1/3]`, and is not in the rigidity closure |
| **Classification** | **conditional theorem** (uniqueness given the postulates) |

**One result is genuinely parameter-free and should be protected:**
`α_Hodge = φ`. Generalize the three numerals in the laws (`+1` in I7, `3` in I9,
`2` in L3) to symbols and every other value becomes a function of them — but
`α_Hodge = (1+√5)/2` is independent of all three, forced by the anchor plus L1's
*shape* (monic quadratic, trace = norm, no adjustable coefficient). That is the
single parameter-free consequence in the layer.

**Repair:** the corpus has already done the honest work — r332/r334/r335 prove
all eight laws necessary and none substrate-derivable, and
`CrossMillenniumSharedInvariants:260` already states they are "explicit
postulates, NOT consequences of the substrate". The remaining repair is
**manuscript-side**: the title page and paper front matter still describe the
α-values as derived. The `K₀` bridge is a multi-person-year mathlib prerequisite,
so the defensible near-term framing is *"a minimal postulate system with a unique
positive solution, one value (φ) forced parameter-free."*

---

## 3. RIEMANN HYPOTHESIS

| | |
|---|---|
| **Manuscript claim** | RH via a Hilbert–Pólya operator on the `T₃^sym` substrate |
| **Intended object** | a self-adjoint operator whose spectrum is the ζ-zero ordinates |
| **Current Lean (oracle layer)** | eight unrestricted Props; four `_Positive` variants |
| **Exact proved statement** | **RESOLVED BOTH WAYS, 2026-10-06.** Unrestricted forms **refuted** (`PositiveCompleteOracleRefutation`); positive forms **proved unconditionally** (`HPPositiveUnconditional`) |
| **Assumptions** | none remaining in the oracle layer |
| **Missing bridge** | — |
| **Classification** | unrestricted: **obsolete/refuted implementation**; positive: **exact theorem** |

**Shipped today, both PRISTINE, zero project axioms:**

- `no_positive_complete_oracle` — completeness over zeros of *both* signs is
  incompatible with positivity, since `ζ(1/2 − it) = conj ζ(1/2 + it)`. Eight
  Props refuted from one lemma.
- `PF_T3SymIsHilbertPolyaOperator_Positive_unconditional` — composing r281's
  conditional discharge with `XiOnLineZero`'s unconditionally-proved Hardy atom.
  **Berry–Keating, Connes, Bost–Connes and the `T₃^sym` form are now theorems**
  in the conjugate-symmetry-compatible (LMFDB upper-half-plane) convention,
  which is what those authors actually assert.
- Consequence: `HilbertPolyaProgramConjecture_Positive ↔ RiemannHypothesis`,
  unconditionally. Read constructively, **this locates the difficulty**: the
  oracle layer cannot carry it.

**Where the real open work is, named exactly.**
`NoOffLineZeroInRightHalf` (`RiemannXiZeroCountLowerBound_r331f:301`) — the one
RH-arc target that is neither circular nor refuted. Everything upstream is
landed and kernel-clean: r325 (ξ entire), r326 (`riemannXiEntire_conj`), r327
(argument principle, Apache-2.0, **Anthropic's — keep that attribution
visible**), r328 + `RiemannXiTopUnion` + r331b/c/d (four edges), r331f
(`two_distinct_critical_zeros_exists`, so `N ≥ 2` unconditionally).

**Repair, next brick:** `codex/RH_BELOW_15_ROUTE_2026-10-01.md` scopes it to
**two FTC-2 lemmas** (`hIntegral_logDeriv_eq_log_sub` and its `VIntegral`
mirror), and argues — arithmetic checked — that the `log_re` parts cancel around
the loop, leaving only constant `arg` jumps, so **no numerical `arg` value and no
winding number are needed**. Then: produce `hR1…hR5` (no
`EdgeReEnclosure`/`EdgeImEnclosure` instances exist yet), import r331c/d into
r331g for `hBot`/`hTop`, write the `count = 2 ⟹ no off-line zero` glue, and get
r331c/d/e kernel-verified (currently source-only, no oleans).

**Honest framing to keep:** RH below height 15 is classically certain since Gram.
The contribution would be a machine-checked proof *consulting no numerical
database*. Mathematical novelty: none. Formalization novelty: real — mathlib has
no argument principle, no winding number, no Rouché, no residue theorem.

---

## 4. P vs NP

| | |
|---|---|
| **Manuscript claim** | P ≠ NP via a spectral gap of `H_α` |
| **Intended object** | the standard complexity classes over a machine model |
| **Current Lean** | `TuringEncoding`; `InClassP`; `PNPClassSeparationPrecisionBridge` |
| **Exact proved statement** | theorems about PF's `ClassP`/`ClassNP`, where `InClassP` carries a trailing-input clause forcing `ClassP = {∅, univ}` |
| **Assumptions** | `PolylogEigenvalueConjecture`; on three routes, empirical antecedents |
| **Missing bridge** | **`Machine` is ⟨arbitrary predicate, arbitrary integer⟩ with no transition function** — there is no model of computation |
| **Classification** | **proxy** (the classes are not the standard ones) |

**The strongest result on this axis is a barrier, and it should be the
headline.** `AlphaRealizationNoGo` / `reduction_sharpness` proves that realizing
`(f ClassP, f ClassNP) = (√2, φ+¼)` is **equivalent to** `ClassP ≠ ClassNP` —
the framework proving its own route is exactly as hard as the problem. That is
rare, honest, and genuinely informative.

**Repair, smallest precise mismatch first:** the trailing-input clause in
`InClassP`. Drop it and rebuild `P_subset_NP` properly — that is a
*specification* repair, not a theory change, and until it lands no theorem
mentioning `ClassP` carries its intended meaning. Then give `Machine` a real
transition function, or state plainly that the axis is conditional on a
machine-model bridge not yet built.

**Two items to retire for the project's own protection:** (i)
`PF/P_NP_Axiom_Elimination.lean:316` has `theorem P_NEQ_NP : P_neq_NP_def` with
no hypothesis, **no olean, zero importers, not in the closure** — so no corpus
certificate covers it, and its proof would need `simp` to show
`π/10/√2 = π/10/(φ+¼)`, which is false. **Relocate byte-for-byte out of `PF/`
with a note; do not delete.** (ii) `EmpiricalCH2Postulate` is provably equivalent
to its own conclusion and provable with no empirical input — it adds an empirical
dependency to the corpus's standing while adding nothing to its logic.

---

## 5. YANG–MILLS MASS GAP

| | |
|---|---|
| **Manuscript claim** | positive mass gap from the fractal/substrate structure |
| **Intended object** | a quantum YM theory on `ℝ⁴` satisfying OS/Wightman, with gap > 0 |
| **Current Lean** | `YangMillsMassGap := ∃ Δ : ℝ, 0 < Δ ∧ True` (381 references); `PF_YMEncodingBridge5` with `GaugeGroup := SU2Type` |
| **Exact proved statement** | existence of a positive real, plus 15 conjunct clauses of which three are `Prop := True` published-theorem anchors |
| **Assumptions** | the witness Hamiltonian is `!![1, 1/2; 1/2, 1]`, a 2×2 real matrix; `Δ := 3/2` is its top eigenvalue |
| **Missing bridge** | **no object of type `Measure (𝒮'(ℝ⁴))` exists** |
| **Classification** | **toy/scaffold model** |

**Real asset to build from:** `YM_SchwartzReflectionConcreteWitness.lean` — a
correct continuous-linear OS time-reflection involution on genuine
`SchwartzMap (EuclideanSpace ℝ (Fin 4)) ℝ`. That is an actual piece of the OS
axioms and the one object a serious QFT formalization would reuse.

**Repair, three steps, smallest first:** (i) the Lean is currently *weaker* than
its own docstring — prove `specSet H_OS_Wightman ⊆ {1/2, 3/2}` and restore the
original quantifier in `ym_clay_literal_mass_gap`. Routine for a 2×2 symmetric
matrix. **Repair, do not downgrade.** (ii) Reclassify the 2×2 system explicitly
as a scaffold in its own docstring, so no reader mistakes it for a field theory.
(iii) The real lane: construct the measure on `𝒮'(ℝ⁴)` with a proved
characteristic functional, building up from the reflection operator. Nothing
downstream can be non-vacuous until that object exists.

---

## 6. NAVIER–STOKES

| | |
|---|---|
| **Manuscript claim** | global smoothness via fractal emergence (no blowup) |
| **Intended object** | solutions of 3D incompressible NS on `ℝ³`, smooth divergence-free data |
| **Current Lean** | `NavierStokesGlobalSmoothness : Prop := ∀ (_ : Unit), ∃ (_ : Unit), True` |
| **Exact proved statement** | nothing about NS |
| **Assumptions** | — |
| **Missing bridge** | **the Navier–Stokes equation is never written** — no time derivative, no pressure, no viscosity, no nonlinear term; `_T` is discarded so local and global existence are the same Prop |
| **Classification** | **unformalized** (the docstring says so: "This is a placeholder Prop") |

**Real asset, currently orphaned:**
`PF/NavierStokes/FujitaKato1964/ConvectiveDerivative.lean` contains a genuine
`(u·∇)v` with correct pointwise semantics and proved bilinearity — never
connected to `NS_Solution`, to any Clay statement, or to any estimate.

**External mathematics moved, and the scope must move with it.** Verified
2026-10-06: OpenAI announced finite-time blowup for 3D incompressible NS **with
smooth forcing** on 2026-09-08, with a manuscript and Lean formalization,
establishing Clay alternatives **(C)** and **(D)**; CMI called the problem
"apparently settled" on 2026-09-11. **Alternatives (A) and (B) — unforced —
remain open.**

**Repair:** (i) connect `ConvectiveDerivative` to a real `NS_Solution` predicate
that actually writes the PDE; (ii) restore the `_T` binder so local ≠ global
existence; (iii) **scope every "no blowup" reading explicitly to the unforced
case** — for forced NS it is now contradicted by a Lean-formalized result, and
for unforced it survives but only if restricted, which
`fractalEmergenceNoBlowup` currently is not.

---

## 7. BSD

| | |
|---|---|
| **Manuscript claim** | `ord_{s=1} L(E,s) = rank E(ℚ)` |
| **Intended object** | the analytic and algebraic ranks of an elliptic curve over ℚ |
| **Current Lean** | `PF_BSDEncodingV5` sets `algebraicRank := algebraicRankV5`, `analyticRank := analyticRankV5` — both are `manuscriptRankV5` |
| **Exact proved statement** | `f E = f E` by `rfl`; the file concedes "This is NOT a Clay BSD discharge" |
| **Assumptions** | a hand-written lookup table |
| **Missing bridge** | `UniversalBridge_MordellWeilRank_eq_algebraicRankV4` — never proved, and as stated false. No object in the corpus is `ord_{s=1} L(E,s)` |
| **Classification** | **proxy** |

**Real assets, and they are better than I first credited.**
`RankPipelineUniversal_r202` `rank_ge_universal` proves
`(n : Cardinal) ≤ Module.rank ℤ W.Point` from a nonzero canonical-height Gram
determinant — on mathlib's **actual** `Module.rank`, with the hypothesis package
shown inhabited for curve 389.a1. `MordellWeilRankLowerBound_r129`
`mordellWeil_rank_ge_one` is likewise real. And `a_p` values are **genuinely
computed**: `pointCount 5 = 8` by `decide` over `ZMod 5 × ZMod 5`.

**Concrete bug to fix:** the Euler product for `y² = x³ − x` (conductor 32, only
bad prime 2) **omits `p = 3`**. `a₃ = 0` (supersingular, 3 ≡ 3 mod 4), so the
missing factor is `3/4`. Documented as "all 23 good primes `p ≤ 100`" — there
are **24**. Restoring it moves the value `0.8084 → ≈0.6064`, which makes the
sandwich's third clause false. Independently, the Euler product does not converge
at `s = 1`, so no truncation bounds `L(E,1)` in either direction.

**Repair:** (i) fix `p = 3` and re-derive the bracket honestly, or withdraw the
sandwich as a bound on `L(E,1)`; (ii) the two rank arcs (r129/r202 real vs
`BSD*` lookup-table) are disconnected — the honest lane is extending r202 toward
a *real* algebraic rank, leaving the analytic side explicitly unformalized;
(iii) the four rank-zero "discharges" assume `hasCM E_36a1`, which the same file
proves **false** — retire those as vacuous.

---

## 8. HODGE

| | |
|---|---|
| **Manuscript claim** | every rational `(p,p)` Hodge class is algebraic |
| **Intended object** | smooth projective complex varieties, rational Hodge classes, algebraic cycle classes |
| **Current Lean** | `RationalHodgeClass _ := ℕ`; `isAlgebraic` ignores both binders |
| **Exact proved statement** | three tautological existentials |
| **Assumptions** | — |
| **Missing bridge** | no complex projective variety, no cohomology theory, no cycle class map |
| **Classification** | **proxy** |

**Real asset:** `MinimalChowGroup.lean` has a cycle / rational-equivalence / Chow
skeleton, with `HodgeConjectureChow` **correctly shaped and correctly left as a
hypothesis**. That is the right foundation.

**Repair:** rebuild the Clay-Hodge encoding on `MinimalChowGroup` instead of the
`ℕ` placeholder, and retire the `Prop := True` anchors named after Glimm–Jaffe /
Streater–Wightman / "Cohen 2025 Main Theorem". The structures carrying DEAD
fields (`HodgeAmbient`, `HodgeCY3Dim22Substrate`, `GeneralSmoothQuintic`) are
scaffolding whose fields should either be used or removed — 14 distinct
structures own 57 field findings in the gate sweep so far.

---

## 9. POINCARÉ

| | |
|---|---|
| **Manuscript claim** | Perelman anchors `α_Poincaré = 1` |
| **Intended object** | Perelman 2003, Ricci flow with surgery — **settled external mathematics** |
| **Current Lean** | `Perelman2003PoincareSolution : Prop := α_Poincare = 1`, proved `rfl` against `def α_Poincare : ℝ := 1` |
| **Exact proved statement** | `1 = 1` |
| **Missing bridge** | no 3-manifold, no Ricci flow — correctly so; this is a citation, not a formalization target |
| **Classification** | **physical/external premise cited as an anchor** |

**Repair:** `PoincareAnchorForced_r338` already records this honestly. Cite
Perelman externally and stop formalizing a `rfl`; the anchor does no Lean work
and should not appear to.

---

## PRIORITY LANES

1. **DONE 2026-10-06** — RH oracle layer resolved both directions
   (`PositiveCompleteOracleRefutation`, `HPPositiveUnconditional`), both PRISTINE.
2. **Semantic hygiene gate on conclusions** — the gate enforces (d2) on premises
   only; 514 of 1570 closure Prop definitions carry a conclusion-level finding,
   452 of them literal `Prop := True`. Diagnostic, not judicial: each finding
   pairs with "locate the intended theorem".
3. **Manuscript parity pass** — the Lean headers are repeatedly more honest than
   the title page and papers (substrate scope, α derivation, the six-mathlib-gaps
   count, `riemannZeta_conj` novelty). Propagate corrections the Lean already has.
4. **NS: connect `ConvectiveDerivative`** and scope the no-blowup reading to
   unforced.
5. **P vs NP: fix `InClassP`**; relocate `P_NP_Axiom_Elimination.lean`.
6. **YM: prove the spectral inclusion** so the Lean matches its docstring.
7. **RH rectangle arc** — the two FTC-2 lemmas. Weeks, real risk, highest
   formalization value.

---

Author: Pablo Cohen + Claude Opus 5. 2026-10-06.
