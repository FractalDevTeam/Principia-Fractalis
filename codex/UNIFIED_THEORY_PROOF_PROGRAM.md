# UNIFIED THEORY PROOF PROGRAM

**Opened:** 2026-09-07, branch `r331b-provenance`.
**Companion:** `codex/COMPLETION_THEOREM_DRAFT.md` (the target signature),
`codex/UNIFIED_THEORY_DEPENDENCY_LEDGER.md` (node-by-node provenance).

This file is the standing answer to one question: **what would have to be true,
in the kernel, for Principia Fractalis to have proved a unified theory?** It is
written backward from that target, not forward from what exists.

Every statement below is sourced from a literal corpus declaration read on
2026-09-07. Where the corpus already audited itself, the corpus's own finding is
quoted rather than re-derived — several of those audits are more damaging to the
framework's headline claims than anything written here, and they are correct.

---

## 0. INPUT PROVENANCE — RESOLVED 2026-09-07

The first edition declared two blockers. Both are now closed.

| input | status |
|---|---|
| The directive's **seven provenance classes** and its **section 10 report order** | **CLOSED** 2026-09-07. Received from Pablo and applied. The dependency ledger is re-keyed; the A-H stand-in is withdrawn. The report order is recorded in section 7 below |
| `ALPHA_RIGIDITY_AUDIT_CHARTER_2026-09-01.md` | **CLOSED** 2026-09-07. Recovered from a Dispatch child-session outputs directory and committed to `codex/`. Its **N2** row (substrate trace range is `Z[1/3]`) is the direct ancestor of r332 |

One remains open:

| input | status |
|---|---|
| The full Unified-Theory Proof Directive text | **OPEN** (`B-DIRECTIVE`). Pablo holds it and will relay it as a file payload; committing it to `codex/` is on the orchestrator's queue |

**The seven classes, as applied:**

| key | class |
|---|---|
| **C1** | definition-or-convention |
| **C2** | theorem-derived-from-earlier-foundations |
| **C3** | independently-motivated-axiom |
| **C4** | empirical-input |
| **C5** | conditional-interface |
| **C6** | unresolved-conjecture |
| **C7** | recorded-negative-or-refuted |

Two orthogonal flags travel alongside, because they are defects rather than
provenance: `circular` (premise restates its conclusion) and `vacuous`
(conclusion holds by construction).

---

## 1. CENTRAL THEOREM STATUS

**UNSPECIFIED.**

There is no declaration in the corpus that is the unified theory's central
theorem. This is not a gap in the search; it is a structural fact, and stating
it plainly is the point of this file.

What exists at the top of the corpus is
`PF/PrincipiaFractalisMillenniumSupremeCapstoneUniversal_r301.lean:...`

```lean
theorem principia_fractalis_millennium_supreme_capstone_universal_at_HEAD
    (h : ClayClosureBundleUniversal) : ...
```

described in its own docstring as "the framework's TOTAL Millennium position at
HEAD". It is **not** a candidate central theorem, for a reason that is decisive
and is developed in §3.1: its hypothesis `h` contains, as a field, a Prop that is
definitionally the implication whose conclusion the theorem asserts. It is a
conditional whose premise restates its conclusion.

Until a central theorem is *specified* — written down as a signature, with no
hypothesis binder, over objects that are not framework-internal encodings — the
question "is the unified theory proved?" has no truth value. It is not open; it
is unasked. `codex/COMPLETION_THEOREM_DRAFT.md` is the first attempt to ask it.

### 1.1 What is genuinely proved, and is not in dispute

The framework contains real, kernel-green mathematics. Three examples, all
audited:

- **The r331b endpoint.** `xi_T15_zero_count_identity_unconditional` — the exact
  zero-count identity for the classical entire Riemann ξ on `[0,1] × [0,15]`,
  on mathlib's `riemannXiEntire`, with **no binders at all** and exactly the
  mathlib three axioms. This is genuine analysis and it is genuinely
  unconditional. It is not RH and the corpus says so.
- **The substrate tower.** `TimelessFieldCompletion :=
  UniformSpace.Completion TimelessFieldRing`. T_∞ carries `NormedRing`,
  `StarRing`, `CStarRing`, `NormedAlgebra ℂ`; the completion inherits
  `CompleteSpace`. This is a real mathlib-native construction of a real object.
- **The negative results.** `AlphaWebDegreesOfFreedom_r124` (the eleven
  invariants are underdetermined — a one-parameter family, not a point) and
  `SubstrateTheoremContent_r216` (the flagship substrate implication discards
  its antecedent) are correct, machine-checked, and were produced by this
  project about this project.

The problem is not that the corpus is empty. It is that the load-bearing joins
between these genuine pieces are the parts that do not hold.

---

## 2. DEPENDENCY GRAPH — PLACEHOLDER

The full node-by-node graph lives in
`codex/UNIFIED_THEORY_DEPENDENCY_LEDGER.md` / `.json`. This is the shape.

```
                    ┌─────────────────────────────────┐
                    │  CENTRAL THEOREM  (UNSPECIFIED) │
                    └────────────────┬────────────────┘
                                     │  ← no edge exists yet
     ┌───────────────────┬───────────┴───────────┬───────────────────┐
     │                   │                       │                   │
 ┌───▼────┐        ┌─────▼──────┐        ┌───────▼──────┐    ┌───────▼──────┐
 │ LAYER 1│        │  LAYER 2   │        │   LAYER 3    │    │   LAYER 4    │
 │substrate│       │ α-skeleton │        │ Clay bridges │    │  empirical   │
 │construct│       │            │        │              │    │              │
 └───┬────┘        └─────┬──────┘        └───────┬──────┘    └───────┬──────┘
     │                   │                       │                   │
 T_∞ pre-C*         9 α-values             6 Clay sectors      constants,
 completion         8 structural           on framework        anchors,
 UHF tower          laws                   encodings           numerics
     │                   │                       │                   │
  STATUS:             STATUS:                 STATUS:            STATUS:
  GENUINE            NOT DERIVED            MOSTLY NOT          OUT OF
  (mathlib)          (all 8 laws are        FAITHFUL            SCOPE for a
                      C1 conventions)      (see §3.3)          math theorem
     │                   │                       │
     └───────────────────┴───────────────────────┘
                         │
              ╔══════════▼═══════════╗
              ║  THE MISSING JOINS   ║
              ║  J1  substrate → α   ║   CLOSED NEGATIVELY (r332)
              ║  J2  α → sector      ║   narrative only
              ║  J3  encoding → Clay ║   faithfulness unproved or false
              ╚══════════════════════╝
```

**The three missing joins J1, J2, J3 are the whole program.** Layers 1–4 each
contain real work. No edge between them is established in the kernel.

---

## 3. OPEN OBLIGATIONS

### 3.1 The circularity obligation — the sharpest one

`r301`'s hypothesis is `ClayClosureBundleUniversal`, whose fields include
`bulletproof : ClayClosureBundleBulletproof`. That structure
(`PF/Referee/UnifiedClayClosureLinkageBulletproof.lean:56`) has three fields,
of which two are:

```lean
  rh_hp_T3sym_positive  : PF_T3SymIsHilbertPolyaOperator_Positive
  rh_hp_program_positive : HilbertPolyaProgramConjecture_Positive
```

and `HilbertPolyaProgramConjecture_Positive` has, per the corpus's own docstring
at `PF/Analytic/RH_FrameworkStandardDischarge_NamedAnchors_2026_06_19.lean:222`,
the mathematical content

    PF_T3SymIsHilbertPolyaOperator_Positive → RiemannHypothesis

The two premises therefore yield `RiemannHypothesis` by modus ponens, and
`Clay_RiemannHypothesis_Standard` is *definitionally* `RiemannHypothesis`
(`PF/Referee/StandardClayStatements.lean:36-37`), which is in turn the literal

```lean
∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1/2
```

**The premise set contains the conclusion.** The theorem is valid; it carries no
information. The corpus does not conceal this — the bundle's own docstring calls
its fields "three published-open fields" and the citation Props are explicitly
labelled "carried as a substrate-tier hypothesis". The defect is that the r301
*headline* presents the result as "the framework's TOTAL Millennium position"
without that qualification travelling with it.

**Obligation O-CIRC:** every premise of any candidate central theorem must be
checked against every conjunct of its conclusion for definitional containment,
and the check must be mechanical, not editorial. The full list for the current
top-level theorem is in `COMPLETION_THEOREM_DRAFT.md` §6.

### 3.2 The α-derivation obligation

The nine α-values are `noncomputable def`s at
`PF/CrossMillenniumSharedInvariants.lean:64-85`:

```
α_Poincaré = 1     α_Hodge = φ         α_BSD = 3π/4
α_P        = √2    α_NP    = φ + 1/4   α_NS  = 3π/2
α_YM       = 2     α_RH    = 3/2       α_QG  = √(2π)
```

`AlphaSkeletonUniqueness_r128` proves the nine-tuple is rigid given eight
structural laws {L1–L5, I6, I7, I9}. The provenance audit of those eight laws
returns, in its own summary table:

| aspect | finding |
|---|---|
| laws with provenance class **A** (intrinsic PF theorem) | **0** |
| laws with class D or E (definitional / trivial arithmetic) | **7** (all but L5) |
| laws with class **F** (target-encoded) | **8** (all) |
| laws formally using mathlib Galois API | **0** |
| load-bearing narrative-gap law | **L5** |

and its status statement, quoted exactly:

> the solution space of the r128 `StructuralLaws` is one-anchor rigid under
> positivity, conditional on accepting the eight laws as inputs; none of the
> eight laws has an intrinsic PF-substrate derivation, and L5 is the unique law
> whose narrative motivation has no formal counterpart anywhere in the corpus.

So layer (B) of the r301 headline — `α_NS = 3π/2 ∧ α_BSD = 3π/4 ∧ α_YM = 2 ∧
α_Poincaré = 1 ∧ α_NS = 2·α_BSD` — is a conjunction of `rfl`-facts about chosen
numerals plus one arithmetic identity `3π/2 = 2·(3π/4)`. `SubstrateTheoremContent_r216`
already says this in the kernel about `α_Poincaré = 1`:

> the field is closed by `rfl`. It records the numeral chosen in the definition.
> It is **not** a statement about Ricci flow, about Perelman's 2002–2003 proof,
> or about the Poincaré conjecture.

**Obligation O-ALPHA:** exhibit at least one α-value derived from the substrate
without that value, an equivalent equation, or a selected spectrum being placed
into the construction. Until then no α-value is a derived constant and the
framework has no predicted constants.

**STATUS 2026-09-07 — closed negatively on the route the corpus has.** r332
(§5) proves π is not a ratio of substrate trace-range quantities, and r123 had
already placed seven of the nine α-values outside that range. O-ALPHA is
therefore not merely undischarged but **undischargeable via the substrate's
K-theory**. It remains formally open only for a future substrate with a wider
invariant range — which does not exist.

### 3.3 The correspondence obligation — sector by sector

`Clay_*_Standard` for five of six sectors is **parameterised over an encoding**.
Whether the sector is the Clay problem depends entirely on the encoding. Read
literally on 2026-09-07:

| sector | Clay statement shape | encoding supplied | faithful? |
|---|---|---|---|
| **RH** | `∀ s, 0<re s<1 → ζ s = 0 → re s = 1/2` | none — unparameterised, on mathlib `riemannZeta` | **YES.** The statement is the real RH. |
| **P vs NP** | `¬ Surjective E.inclusion` | `ClassP`/`ClassNP` built from real Turing machines, poly-time bounds, Cook-1971 certificate definition | **YES, apparently.** Statement shape is faithful; needs a dedicated audit of `Machine`/`turingTimeComplexity`. |
| **Navier–Stokes** | `∀ u0, divFree u0 → hasGlobalSmoothSolution u0` | `hasGlobalSmoothSolution := NS3DRegularitySolutionV2`, a 5-conjunct predicate: a uniform Hadamard bound, three mathlib-availability flags, and a BKM-criterion clause | **NO.** The predicate does not assert global-in-time smooth existence. |
| **Yang–Mills** | `∃ T, satisfiesClayAxioms T ∧ massGap T > 0` | `Bridge5SubstrateQYM`; `satisfiesClayAxioms` is a 15-conjunct predicate **three of whose conjuncts are `Prop := True`** (`GlimmJaffe_OS_SU2_TypedAnchor`, `StreaterWightman_SU2_TypedAnchor`, `OsterwalderSchrader_SU2_TypedAnchor`) | **NO.** Vacuous anchors; finite-dimensional substrate model, not the continuum theory. |
| **BSD** | `∀ Ec, analyticRank Ec = algebraicRank Ec` | `algebraicRankV5 := manuscriptRankV5` and `analyticRankV5 := manuscriptRankV5` — **the same function** | **NO — vacuous by construction.** The equality is `rfl`. |
| **Hodge** | `∀ X c, isAlgebraic X c` | substrate surface type; `isAlgebraic` is "PF's 3-conjunct substrate predicate, **not literal geometric algebraicity by an explicit cycle**" (its own docstring) | **NO.** Substrate-level only. |

Two of these the corpus states outright. The BSD file's own honest-scope block:

> This is NOT a Clay BSD discharge for arbitrary `WeierstrassCurve ℚ`. For
> curves outside the 20-curve set, V5 returns `0` and equality is trivially
> `0 = 0`.

and the Hodge bridge's:

> Honest scope: substrate-level only. […] The `isAlgebraic` is PF's 3-conjunct
> substrate predicate, not literal geometric algebraicity by an explicit cycle.

A stronger Hodge encoding exists and should be preferred wherever it applies:
`PF_HodgeEncoding_FullGeneral` in
`PF/AlgebraicGeometry/Voisin2007GeneralQuinticPrecision.lean:496` uses genuine
`AlgebraicCycleOnQuinticWitness` cycle witnesses.

**Obligation O-CORR:** for each sector, either prove a correspondence theorem
(framework encoding ⟹ standard object) or restate the sector on the standard
object directly. A sector without a correspondence theorem may not appear in a
central theorem's conclusion under the Clay name.

### 3.4 The determination obligation

`SubstrateTheoremContent_r216` proves in the kernel that the flagship
`PrincipiaFractalisSubstrateTheorem : PFSubstrateAntecedents →
PFSubstrateConsequences` **discards its antecedent** (`intro _h_antecedents`),
and that the consequences are independently provable. Its §1 shows the
antecedents are interchangeable with `2 + 2 = 4`.

It also states the test for repair, which this program adopts verbatim as the
definition of a real derivation:

> A proof of at least one consequence `Cᵢ` that genuinely uses an antecedent: a
> term whose elaboration *fails* when the antecedent hypothesis is removed from
> the context.

**Obligation O-DET:** exhibit one such `Cᵢ`.

### 3.5 The empirical-premise obligation

Some conclusions in the corpus are premised on measured quantities or on
numerically-verified but unproved correspondences (e.g. the Cohen 2025 transfer
operator's eigenvalue-zero agreement "at 150-digit precision on five pairs", and
the self-adjointness residual `‖T̃_N − T̃_N†‖/‖T̃_N‖ < 10⁻¹⁵` at `N ≤ 40`).

Numerical agreement at finite `N` is evidence, not proof. Any conclusion
downstream of it is empirical-premised and must be tagged as such in the central
theorem, never mixed into a mathematical conjunct.

**Obligation O-EMP:** every conjunct of a central theorem carries an explicit
mathematical/empirical tag.

---

## 4. COUNTERMODEL RISKS

Where the program is most likely to be *refuted* rather than merely stalled.

| # | risk | why it is live | what would settle it |
|---|---|---|---|
| **R1** | **The α-web has no rigid solution at all** | **STRENGTHENED by r332.** r124 proves the eleven invariants admit a one-parameter family. r128's rigidity is bought with L5 — and L5's only non-narrative justification route is now closed | A countermodel is already half-built: r124's family. Producing a *second* self-consistent α-assignment satisfying all eight r128 laws with a different anchor would end the rigidity claim outright |
| **R2** | ~~L5 is underivable in principle~~ | **REALISED 2026-09-07.** The test statement is **true**: r332 proves `∀ a b ∈ ℤ[1/3], b/a ≠ π`. L5 can never be derived on the substrate's K-theoretic route, so the α-skeleton is ungrounded there | **SETTLED — see §5.** The risk was real and it materialised. What remains open is only a future substrate with an invariant range wider than `ℤ[1/3]`, which does not exist |
| **R3** | **The substrate is too weak to see any Clay problem** | Layer 1 is a UHF-type C*-algebra. Nothing in the completion construction mentions ζ, elliptic curves, Hodge classes, or Navier–Stokes. J1 and J2 may not merely be unproved but unprovable for lack of expressive contact | Exhibit *any* nonvacuous theorem whose statement mentions both `TimelessFieldCompletion` and a standard object, and whose proof uses a substrate property |
| **R4** | **The YM encoding is inconsistent, not just vacuous** | `satisfiesClayAxioms` requires `0 < Δ ∧ 1 ≤ Δ ∧ Δ ≠ 1` alongside twelve analytic conjuncts on a finite-dimensional model. If the conjunction is uninhabitable, `∃ T, …` is false and the YM sector is not merely unfaithful but refuted on its own encoding | Exhibit an inhabitant of `Bridge5SubstrateQYM` satisfying all fifteen conjuncts, or prove none exists. Note the precedent: the corpus already found a "structurally-uninhabitable Prop" in an earlier RH route (V3) and replaced it |
| **R5** | **`KatoRellichInput` contamination** | The gate (F4) records a module *proved false by its own file*. If any live chain cites it, that chain is unsound, not just weak | Reachability check from every central-theorem candidate |
| **R6** | **Encoding drift between near-identical names** | r128 found the corpus carries two different reals under near-identical names: `framework_alpha.a_PvNP = 5/4` vs `α_NP = φ + 1/4 ≈ 1.868` | A name-collision audit across the α-namespace |

R1 and R2 were the two that would end the program rather than delay it. **R2 has
now materialised.** R1 is correspondingly stronger: with L5's justification route
closed, nothing non-narrative remains to defend the rigidity claim.

---

## 5. THE L5 STEP — DONE 2026-09-07, VERDICT NEGATIVE

The first edition named settling L5 as the next decisive step. Pablo authorised
it; it is done. **`PF/AlphaL5PiScalingObstruction_r332.lean`**, kernel-green,
exactly the mathlib three axioms, zero `sorryAx`, non-vacuity proved.

```lean
theorem pi_not_ktheoretic_ratio
    {a b : ℝ} (ha : MemZ13 a) (hb : MemZ13 b) (h0 : a ≠ 0) : b / a ≠ Real.pi
```

`MemZ13` (r123) is membership in `ℤ[1/3]`, exactly the range of the substrate's
unique trace on `K₀(T∞)` — its complete classifying invariant, carried onto
`ℤ[1/3] ⊂ ℝ` isomorphically (Glimm/Elliott). `ℤ[1/3] ⊆ ℚ`, so any ratio of its
elements is rational; π is not.

**Verdict: PROVABLE — the negative branch.** L5 (`α_NS = α_RH · π`) has no
derivation available through the substrate's K-theory.

Three consequences, all recorded in the kernel:

1. **Join J1 is closed negatively.** r123 had shown the α-*values* are outside
   the trace range (seven of nine). r332 shows the *ratio* L5 needs is outside it
   too — so the gap cannot be closed by relating two α's to each other instead of
   deriving each one. That was the remaining escape route.
2. **The framework has no derived constants on the route it has.** L5 is what
   makes the α-skeleton rigid; without an intrinsic L5, r124's one-parameter
   family is the honest picture. The corpus should stop describing the nine
   α-values as derived.
3. **r332.D records the other half in the kernel:** `α_NS / α_RH = π` is provable
   by `ring` after unfolding the two `def`s. The identity is true *of the chosen
   numerals* and unreachable *from the invariant*. That is exactly what
   "definition-or-convention" means, stated as a theorem rather than a judgement.

Two additions beyond the recommended wording: **r332.E** proves the hypotheses
are satisfiable, so the result is not vacuous; **r332.F** records that the
`a ≠ 0` hypothesis does no work (in Lean `b/0 = 0 ≠ π`), because an unused
premise can be mistaken for the thing making a statement true.

**Scope, narrowly:** this closes L5 against the K-theoretic trace route — the
route the corpus actually has (r113, r123). It does not address a hypothetical
future substrate whose invariant range is not confined to `ℤ[1/3]`. Per charter
§8, no outcome here bears on any Clay problem and none revives N2/N3/N4.

---

## 5b. NEXT DECISIVE STEP

**Specify a central theorem — assemble `principia_fractalis_verified_position_2026_09_07`.**

This program's headline finding is that the central theorem status is
*unspecified*, which means the question cannot be asked. The way to change that
is not more auditing; it is to write one down. `COMPLETION_THEOREM_DRAFT.md` §3
already drafts it, and every conjunct is assemblable from existing green
material — now including r332:

- (V1) the substrate is a genuine constructed object;
- (V2) the r331b endpoint, unconditional;
- (V3) top-edge negativity over the full partition of `[1/2, 1]`;
- (V4) r124: the α-web admits every positive `α_BSD` — a one-parameter family;
- (V5) r216: any proposition implies `PFSubstrateConsequences`;
- **(V6, new) r332: π is not a ratio of substrate trace-range quantities.**

It would be **the corpus's first hypothesis-free top-level theorem**, and it
would state the negative results in the same breath as the positive ones. That
combination is what a referee trusts, and it replaces "UNSPECIFIED" with
something honest rather than with another capstone that hides its premises.

**Parallel, cheap, no build required:** close `B-N51` by auditing the eight
fields of `ClayClosureBundleDualCitationAggregate` (r299:116). It is the last
unaudited premise bundle feeding r301, and closing it completes the circularity
picture.

**Both require authorization.** Nothing here is started.

---

## 6. WHAT THIS PROGRAM DOES NOT SAY

- It does not say the corpus is dishonest. The corpus's in-file docstrings are
  candid — repeatedly more candid than its headline theorem names and its prose
  chapters. `r216` puts that gap in the kernel deliberately.
- It does not say the mathematics is worthless. The r331b endpoint is real
  unconditional analysis. The substrate tower is a real construction. The
  negative results are real theorems.
- It does not retract anything. Nothing here changes a single `.lean` file.
- It does not authorise a push. Public HEAD remains `96c71da7`.

---

## 7. SECTION 10 REPORT ORDER

Every orchestrator report against this program uses the directive's order,
verbatim:

1. central theorem status
2. what became proved
3. what became disproved-or-weaker
4. current blocking obligation
5. assumption-or-circularity changes
6. kernel-and-rebuild status
7. decision required from Pablo
8. next decisive action

---

*Opened 2026-09-07 on `r331b-provenance`. Central theorem status: UNSPECIFIED.
L5 settled negatively (r332). Next decisive step: specify a central theorem.*
