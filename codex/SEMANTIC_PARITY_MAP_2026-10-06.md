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

## 10. MODIFIED EINSTEIN EQUATION — the GR sector

| | |
|---|---|
| **Manuscript claim** | ch08 `thm:modified-einstein` (L217--226): `G_μν + Λ_eff(C) g_μν = 8πG (T^μν + C^μν)`. Restated ch08 L640, ch13 L21/L43, ch14 L34, ch15 L21, ch27 L71. |
| **Intended object** | a tensor field equation on a Lorentzian 4-manifold, with a consciousness stress-energy tensor `C^μν` |
| **Current Lean** | `GeneralRelativity.lean` `ModifiedEinsteinWithConsciousnessHypothesis` + `_holds` (L224) + `ModifiedGRWithConsciousnessBundle` (L214) |
| **Exact proved statement** | `∃ (Λ G_grav : ℝ), Λ = Λ ∧ G_grav = G_grav ∧ True`, witnessed `⟨0, 0, rfl, rfl, trivial⟩`. **Logically equivalent to `True`.** |
| **Assumptions** | none — the Prop is a tautology |
| **Missing bridge** | no manifold, no metric, no tensor, no Bianchi identity, no `C^μν`. ch08's own 2026-10-06 correction at L220 already establishes that the printed equation has an index mismatch (lower left, upper right) and that `Λ_eff` as a slice functional is not a covariant scalar. |
| **Classification** | **toy/scaffold — True-equivalent existential.** Self-disclosed in-file as "Placeholder Prop body"; the theorem name and docstring ("HOLDS (axiom-free)") are not. |

**A vacuity species the gate does not catch.** This Prop is not literal
`Prop := True`, so neither the semantic-hygiene conclusion check (LANE 2:
452 literal `Prop := True` of 1570) nor a `grep 'Prop := True'` sees it. The same
shape recurs twice more in the same file: `EnergyInformationEquivalenceHypothesis
:= ∃ c², 0 < c²` (witness `⟨1, by norm_num⟩`) and `DarkEnergyAsLambdaEffHypothesis
:= ∃ Λ₀ Λ_eff, 0 < Λ₀ ∧ 0 ≤ Λ_eff ∧ Λ_eff ≤ Λ₀` (satisfied by `Λ₀ = 1,
Λ_eff = 0`). **All three members of `ModifiedGRWithConsciousnessBundle` — the
bundle the file calls "the manuscript's load-bearing claims about gravity" — are
True-equivalent.** Extend the gate to flag `∃ x, x = x`, `∃ x, 0 < x` and
conjunctions whose every conjunct is discharged by `rfl`/`trivial`/`norm_num` on
a free variable.

**Where the real content is, in the same sector:** `Wave58/Ch08FieldEquationsConcrete.lean`
(462 lines, zero `Prop := True`) carries five explicit non-vacuity witnesses
`witness_1_vacuum` … `witness_5_monotonic`, plus `T_consciousness_density_pos_at_saturation`.
`Ch08Ch14ModifiedRelativity.lean` defines `kappa G := 8 * Real.pi * G` with
`kappa_pos` proved, and `alpha3_is_the_binding_bound` is honest arithmetic on
three stipulated PPN constants (`10⁻²⁰ < 10⁻⁷ < 10⁻⁴`, ratio `10¹⁶`).

**Repair:** rename `ModifiedEinsteinWithConsciousnessHypothesis_holds` to
`..._placeholder`, or discharge the bundle against the five
`Ch08FieldEquationsConcrete` witnesses, which are real. ch08 should cite those
witnesses and `ModifiedFriedmann_r187.energy_balance` (§11) rather than a
tautology. Under the ERROR/SUPERSESSION rule this is neither: it is a
formalization placeholder that the book never cited — so the repair is in the
Lean, not in the chapter.

---

## 11. CONSERVATION LAWS — and this axis is stronger than the book claims

| | |
|---|---|
| **Manuscript claim** | ch08 `thm:modified-conservation` (L110--120), `princ:generalized-conservation` (L190--196), boxed `d/dt[E_cl + E_q + I_C·c²] = 0` (L193); ch14 `thm:noether` (L103), `thm:consciousness-charge-conservation` (L205--219) |
| **Intended object** | a Noether current for the `U(1)_C` symmetry, and the covariant divergence `∇_μ(T + C)^μν = J^ν_C` |
| **Current Lean — tier (a), STRONG** | `ModifiedFriedmann_r187.lean`: `ModifiedContinuity := ∀ t, ρ' + 3(a'/a)(ρ+p) = J`, then `energy_balance` **and its converse** `modifiedContinuity_of_energy_balance` |
| **Exact proved statement (a)** | `deriv (fun s => ρ s * (a s)^3) t = (J t − 3(deriv a t / a t)·p t)·(a t)^3`, under `Differentiable ℝ a`, `Differentiable ℝ ρ`, `∀ t, a t ≠ 0` — proved with `HasDerivAt`, `.pow 3`, `field_simp`, `ring`, and an **iff** via the converse |
| **Current Lean — tier (b), PROXY** | `Ch08FieldEquationsConcrete.generalized_conservation : T_consciousness_density (19/20) ≥ 0` — the scalar slice only, and the docstring says so |
| **Current Lean — tier (c), SCHEMATIC** | `LambdaEffFromAction.absorbed_lambda_leaves_no_residue (divG divS kap : ℝ) (hkap : kap ≠ 0) (heq : divG = kap * divS) (hbianchi : divG = 0) : divS = 0` — real-number cancellation; the physics is in the hypothesis *names* |
| **Missing bridge** | no Noether theorem, no `U(1)_C` current, no covariant divergence anywhere in Lean. And ch14's `∇_μ j^μ_C = 0` is not derivable as printed — verified directly in source 2026-10-08: ch14 L188 declares `C^μν → e^{iθ(x)} C^μν` "where `θ(x)` is an **arbitrary spacetime function**", i.e. a *local* symmetry, while `grep -c` for a covariant derivative or `U(1)_C` gauge field over the whole chapter returns **0**. The displayed current uses the Levi-Civita `∇_ν`, which is not covariant under a local phase rotation, so its divergence does not vanish. Its index structure is also wrong for a phase current: the free index `μ` sits on the field and the derivative carries the contracted `ν`, where Noether gives `i(φ̄∇^μφ − φ∇^μφ̄)`. |
| **Classification** | **(a) exact theorem, FLRW-reduced · (b) proxy, self-disclosed · (c) schematic** |

**Repair, and it is favourable.** Tier (a) is a genuine non-vacuous formalization
of ch08's modified conservation law — *"energy is not conserved, `J` books the
deficit"* — as an **equivalence**, with real differential calculus. ch08 L226
currently cites only `LambdaEffFromAction`; it should cite `energy_balance` and
`modifiedContinuity_of_energy_balance`, which are strictly stronger than what it
points at. **The book under-cites its own best work here.** Separately, ch14's
charge-conservation theorem needs either a gauge field introduced or the symmetry
restated as global — an ERROR in ch14's sense, not a supersession.

---

## 12. WEINSTEIN GEOMETRIC UNITY — the RQG rescue

| | |
|---|---|
| **Manuscript claim** | ch11: `\|Ψ_RQG\|² = ch₂ = 0.95` from 14D trace-anomaly cancellation; BRST `H² = 78 = dim E₆`; holographic `13D → 4D` projection; and four resolved anomalies — muon `g−2`, Hubble tension, ANITA events, cosmological lithium (L5, L499--505) |
| **Intended object** | BRST cohomology of a 14-dimensional GU bundle, a real anomaly computation, and four experimental predictions |
| **Current Lean** | `PF/Consciousness/WeinsteinGUResonantRescue.lean` (383 lines) |
| **Exact proved statement** | `rqgWitness_amp_squared : rqgWitness.Psi_RQG_amp_squared = 0.95 := rfl` — `rfl` on a record field *defined* as `0.95`; `brst_H2_eq_78 : (78 : ℕ) = 78 := rfl`; `brst_H2_sm_decomposition : 78 = 48 + 26 + 4 := by decide`; `brst_H2_matches_E6_dim_aux` cites `Cosmology.dim_E6_eq_78`, which is **itself `(78 : ℕ) = 78`**; `holographicProjection : (Fin 13 → ℝ) → (Fin 4 → ℝ)` with `_zero`, `_add`, `_smul` genuinely proved; and four `Prop := True` discharged `trivial` |
| **Assumptions** | none for the tautologies; the `0.95` is definitional |
| **Missing bridge** | no BRST complex, no cohomology group, no E₆ root system, no 14D bundle, no anomaly integral. **The Lean does not rescue the `0.95` derivations; it stipulates the target as a record-field value.** `78 = 48 + 26 + 4` is true arithmetic with wrong physics labels: the decomposition is annotated "26 gauge boson DOF" against the Standard Model's 12 gauge bosons. |
| **Classification** | **toy/scaffold + 4 × vacuous Prop; the projection linearity is an exact theorem; the BRST identity is a numeral tautology grounded in another numeral tautology** |

**Already scoped, and by the strongest mechanism in the corpus.** ch11 L145 and
L193 each carry a `\manuscriptcorrection` that refutes its own route to `0.95`
— the 14D anomaly leg yields `≈ 6.05×10⁻⁴Φ₀`, *"off by a factor of ≈ 1570"*;
the Gaussian leg evaluates exactly to `√(5/(π+5)) ≈ 0.7837` — and **each cites an
axiom-free Lean theorem that proves the framework's own claim false**:
`anomaly_cancel_predicted_value_ne_0_95` and `prop_11_6_psi_rqg_sq_ne_0_95`, both
in `PF/Ch11AnomalyCancellationRefutationAttempt.lean` (Wave 55, commit `8e4a62a`).
Both corrections then redirect the threshold to its surviving source: *"ch₂ = 0.95
should be read as set by the Ch 6 Chern--Weil derivation, not by Ch 11's `Ψ_RQG`
Gaussian integral."* A corpus that formalizes the refutation of its own route is
doing something most published mathematics does not; this should be said plainly
rather than treated as a defect inventory.

**Repair, therefore narrow.** The derivations are scoped; the residue is the
unscoped restatements and the vacuous Props. (1) ch11 L5 (abstract) and L499--505
(summary) still assert the refuted routes and the four "resolved" anomalies in the
present indicative — propagate the L145/L193 corrections and the
`WeinsteinGURescueHonestScope` split, which already separates in Lean the
"concrete-witness side (RQG inhabited, BRST = 78, projection real)" from the
"open / typed-Prop side (Shiab + 4 experimental Props)". (2) Rename the four
anomaly Props `*_Unformalized` or delete them. (3) Cite `dim E₆ = 78` as the
external Lie-algebra fact it is rather than proving `78 = 78`. (4) Fix the "26
gauge boson DOF" annotation.

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

8. **Physics sector now mapped (added 2026-10-08)** — §§10--12 above extend this
   map from nine arcs to twelve. The three added arcs are the ones Pablo named:
   modified Einstein, conservation, Weinstein. Before 2026-10-08 no parity
   artifact covered them: `GeneralRelativity` appeared in two `codex/` files
   (neither a parity map) and `Friedmann` in one.
9. **Extend the vacuity check to True-equivalent existentials** — `∃ x, x = x`,
   `∃ x, 0 < x`, and conjunctions each of whose conjuncts falls to
   `rfl`/`trivial`/`norm_num` on a free variable. LANE 2's 452 counts literal
   `Prop := True` only; all three members of `ModifiedGRWithConsciousnessBundle`
   evade it. Until this lands, every vacuity figure in this corpus is a **lower
   bound**.
10. **Re-point ch08 L226 at `energy_balance`** — the strongest conservation
    result in the corpus is not the one the chapter cites (§11).

Author: Pablo Cohen + Claude Opus 5. 2026-10-06.
