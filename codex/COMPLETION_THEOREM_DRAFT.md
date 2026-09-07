# THE COMPLETION THEOREM — DRAFT SIGNATURES

**Opened:** 2026-09-07. Companion to `codex/UNIFIED_THEORY_PROOF_PROGRAM.md`.

This file drafts the exact Lean signature that would constitute **mathematical
completion of the unified theory**, in two versions:

- **§2 — the strongest honest version.** What completion actually requires. Not
  currently provable; several conjuncts are not currently even *stateable*
  without new definitions. That is the point of writing it down.
- **§3 — the weaker currently-reachable version.** What could be assembled from
  today's corpus without lying. Much smaller.

**Design rules, applied throughout:**

1. **No hypothesis binders on the headline.** A theorem of the form
   `(h : Bundle) → Conclusion` is not a completion theorem. Precedent: the
   r331b endpoint `xi_T15_zero_count_identity_unconditional` shows no binders at
   all under `#check @`, and that is the standard.
2. **No bundled predicates.** Every conjunct is spelled out. A structure field
   named after a citation is a hypothesis wearing a bibliography.
3. **Standard objects only.** Sectors are stated on mathlib or standard
   mathematical objects, never on a framework encoding, unless a correspondence
   theorem is a *separate, stated conjunct*.
4. **Mathematical and empirical conclusions are never mixed.** Empirical-premised
   conclusions live in a separately-named theorem, never in the same conjunction.

---

## 1. WHAT MUST BE EXPOSED

The directive requires that a completion theorem expose, rather than bundle:

| # | must be exposed | where it appears below |
|---|---|---|
| 1 | foundational assumptions | §2.0, `Foundations` — and note there are none beyond the mathlib three |
| 2 | the constructed universe | §2.1, conjunct **(U)** |
| 3 | the equivalence relation | §2.1, conjunct **(E)** |
| 4 | every claimed sector | §2.3, conjuncts **(S1)–(S6)** |
| 5 | every claimed-derived constant | §2.2, conjuncts **(K1)–(K9)** |
| 6 | correspondence statements | §2.4, conjuncts **(C1)–(C6)** |
| 7 | mathematical vs empirical-premised | §2 is mathematical only; §4 is the empirical companion |
| 8 | premises that restate conclusions | §6, the circularity ledger |

---

## 2. THE STRONGEST HONEST VERSION

### 2.0 Foundations

No project axioms. The only permitted axiom list is mathlib's three:
`[propext, Classical.choice, Quot.sound]`. Any `sorryAx` or `ofReduceBool` in
the audit output of this theorem or of anything it depends on voids it.

This is not aspirational — the r331b chain already meets it. It is stated so
that the completion theorem cannot be met by weakening the axiom base.

### 2.1 The construction — conjuncts (U) and (E)

```lean
/-- **PRINCIPIA FRACTALIS — UNIFIED THEORY COMPLETION (strongest honest form).**

    NO HYPOTHESES. Every conjunct is on a standard object or on an explicitly
    constructed one whose construction is a conjunct of this same theorem. -/
theorem principia_fractalis_unified_theory_complete :

    -- ══ (U) THE CONSTRUCTED UNIVERSE ══════════════════════════════════
    -- The substrate exists as a constructed object, not as a hypothesis,
    -- and is a C*-algebra in mathlib's sense.
    (CStarAlgebra PF.TimelessFieldCompletion) ∧

    -- (U2) It is not the trivial algebra. A completion theorem over the
    -- zero algebra would be vacuous.
    (∃ x : PF.TimelessFieldCompletion, x ≠ 0) ∧

    -- (U3) The base-3 direct-limit structure is genuinely present, i.e. the
    -- completion is the completion OF T_∞ and not of something reindexed.
    (Nonempty (PF.TimelessFieldRing →⋆ₐ[ℂ] PF.TimelessFieldCompletion)) ∧

    -- ══ (E) THE EQUIVALENCE RELATION ══════════════════════════════════
    -- The relation under which substrate configurations are identified,
    -- stated as a Setoid on the carrier, together with the fact that the
    -- physical/mathematical content is invariant under it.
    (∃ S : Setoid PF.SubstrateConfiguration,
        -- (E1) it is the framework's own relation, not an ad-hoc one
        (∀ a b, S.r a b ↔ PF.SubstrateEquiv a b) ∧
        -- (E2) every claimed-derived constant is a well-defined function
        --      on the quotient — i.e. the constants are invariants, not
        --      artefacts of a chosen representative
        (∀ (f : PF.SubstrateConfiguration → ℝ),
            f ∈ PF.DerivedConstantFunctions →
            ∀ a b, S.r a b → f a = f b)) ∧
```

**Status of (U):** `TimelessFieldCompletion :=
UniformSpace.Completion TimelessFieldRing` exists and much of (U) is already
established — T_∞ carries `NormedRing`, `StarRing`, `CStarRing`,
`NormedAlgebra ℂ`, and the completion inherits `CompleteSpace`. `r53`'s own
docstring lists `Star`, `StarRing`, `CStarRing`, `NormedAlgebra ℂ` on the
*completion* as work items r54–r57. **(U) is the one block of this theorem that
is close.**

**Status of (E):** `PF.SubstrateConfiguration`, `PF.SubstrateEquiv` and
`PF.DerivedConstantFunctions` **do not exist**. No `Setoid` or `Quotient` appears
in `SubstrateTimelessFieldCompletion.lean`. (E) is not currently stateable. This
is a real finding: *the framework has no stated equivalence relation*, so the
question "are the derived constants invariants?" cannot presently be asked.

### 2.2 The constants — conjuncts (K1)–(K9)

This is the block that distinguishes a unified theory from a table of numbers.
It must say the α-values are **forced**, not chosen.

```lean
    -- ══ (K) THE CLAIMED-DERIVED CONSTANTS ═════════════════════════════
    -- Each α is the value of an intrinsic substrate functional. The
    -- functional must be defined WITHOUT reference to the target value.
    (∃ (Φ : PF.SubstrateInvariantFunctional),
        -- (K0) Φ is intrinsic: its definition mentions no α-value, no
        --      equation equivalent to one, and no selected spectrum.
        PF.IsIntrinsic Φ ∧
        -- (K1)-(K9) the nine values are OUTPUTS of Φ
        Φ PF.Sector.Poincare = 1 ∧
        Φ PF.Sector.RH       = 3 / 2 ∧
        Φ PF.Sector.YM       = 2 ∧
        Φ PF.Sector.P        = Real.sqrt 2 ∧
        Φ PF.Sector.NP       = goldenRatio + 1 / 4 ∧
        Φ PF.Sector.Hodge    = goldenRatio ∧
        Φ PF.Sector.QG       = Real.sqrt (2 * Real.pi) ∧
        Φ PF.Sector.BSD      = 3 * Real.pi / 4 ∧
        Φ PF.Sector.NS       = 3 * Real.pi / 2 ∧
        -- (K-RIGID) and Φ is the unique intrinsic functional with these
        --           values, so the assignment is not one of a family
        (∀ Ψ : PF.SubstrateInvariantFunctional,
            PF.IsIntrinsic Ψ → (∀ s, Ψ s = Φ s) → Ψ = Φ)) ∧
```

**Status:** the nine α-values are `noncomputable def`s at
`CrossMillenniumSharedInvariants.lean:64-85`. There is no `Φ`. The eight
structural laws that pin them are, per the corpus's own provenance audit,
**zero of class A** and **eight of class F (target-encoded)**. `α_NS = α_RH · π`
(L5) is class **G** — narrative with no formal counterpart anywhere.

`PF.IsIntrinsic` is the crux predicate and **does not exist**. Defining it
honestly is itself an open problem: it must forbid the definition from
mentioning the target value, an equivalent equation, or a selected spectrum.
Without it, (K0) can be satisfied trivially by a functional that returns a
lookup table.

**(K) is currently unreachable and is the single largest gap in the theorem.**

### 2.3 The sectors — conjuncts (S1)–(S6)

Stated on **standard objects**. No encoding parameters.

```lean
    -- ══ (S) THE CLAIMED SECTORS ═══════════════════════════════════════
    -- (S1) Riemann Hypothesis — literal, on mathlib's riemannZeta.
    (∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1 / 2) ∧

    -- (S2) P ≠ NP — on the corpus's Turing-machine classes, which are
    --      built from Machine/turingTimeComplexity and Cook-1971
    --      certificates, pending the audit in O-CORR.
    (¬ (∀ L : PF.TuringEncoding.Language,
          PF.TuringEncoding.InClassNP L → PF.TuringEncoding.InClassP L)) ∧

    -- (S3) Navier-Stokes global regularity — LITERAL. Every Schwartz
    --      divergence-free datum admits a global-in-time smooth solution
    --      of the 3D incompressible NS system. NOT a substrate predicate.
    (∀ u0 : PF.NS.SchwartzDivFreeData,
        ∃ u : ℝ≥0 → PF.NS.VelocityField,
          PF.NS.IsGlobalSmoothSolutionOfNS u u0) ∧

    -- (S4) Yang-Mills — LITERAL. A quantum YM theory on R^4 for a compact
    --      simple gauge group satisfying the Wightman/OS axioms, with a
    --      strictly positive mass gap. NOT a finite-dimensional model.
    (∃ T : PF.YM.QuantumYangMillsTheory,
        PF.YM.SatisfiesWightmanOSAxioms T ∧ 0 < PF.YM.massGap T) ∧

    -- (S5) BSD — LITERAL, for EVERY elliptic curve over Q, with the two
    --      ranks defined independently of one another.
    (∀ E : WeierstrassCurve ℚ,
        PF.BSD.analyticRank E = PF.BSD.mordellWeilRank E) ∧

    -- (S6) Hodge — LITERAL, every rational Hodge class is a Q-linear
    --      combination of algebraic cycle classes, witnessed by cycles.
    (∀ (X : PF.Hodge.SmoothProjectiveComplexVariety)
       (c : PF.Hodge.RationalHodgeClass X),
        ∃ Z : PF.Hodge.AlgebraicCycleWitness X,
          PF.Hodge.Realises c Z) ∧
```

**Status, sector by sector:**

| conjunct | current corpus form | verdict |
|---|---|---|
| (S1) | `Clay_RiemannHypothesis_Standard := RiemannHypothesis`, the literal statement | **statement already faithful**; discharge circular (§6) |
| (S2) | `Clay_PvsNP_Standard PF_ComplexityEncoding`, real TM classes | **apparently faithful**; discharge conditional on `PolylogEigenvalueConjecture` (open) |
| (S3) | `hasGlobalSmoothSolution := NS3DRegularitySolutionV2`, a 5-conjunct substrate predicate including three mathlib-availability flags | **not faithful** — `PF.NS.IsGlobalSmoothSolutionOfNS` does not exist |
| (S4) | `satisfiesClayAxioms` with three conjuncts that are literally `Prop := True` | **not faithful** — vacuous anchors |
| (S5) | both ranks `:= manuscriptRankV5`; equality by `rfl`; returns `0` off a 20-curve list | **vacuous by construction**, as the file itself states |
| (S6) | `isAlgebraic` = "PF's 3-conjunct substrate predicate, not literal geometric algebraicity by an explicit cycle" | **not faithful**; a stronger encoding with genuine cycle witnesses exists at `Voisin2007GeneralQuinticPrecision.lean:496` and should be lifted |

### 2.4 The correspondences — conjuncts (C1)–(C6)

The joins. **This is where a unified theory is or is not unified.**

```lean
    -- ══ (C) CORRESPONDENCE — the substrate ACTUALLY BEARS on the sector ══
    -- For each sector: the substrate invariant is not merely numerically
    -- equal to a sector constant, it is the SAME object, and the sector
    -- statement follows FROM substrate structure.
    (∀ s : PF.Sector,
        PF.SubstrateBearsOn s ∧
        -- the derivation genuinely uses the substrate: removing the
        -- substrate hypothesis breaks elaboration (the r216 test)
        PF.DerivationIsNonVacuous s) ∧

    -- ══ (D) DETERMINATION — the r216 test, discharged ═════════════════
    -- At least one sector consequence has a proof term that FAILS to
    -- elaborate when the substrate antecedent is removed.
    (∃ s : PF.Sector, PF.AntecedentIsLoadBearing s)
```

**Status:** `PF.SubstrateBearsOn`, `PF.DerivationIsNonVacuous`,
`PF.AntecedentIsLoadBearing` do not exist and no theorem of this shape exists.
`SubstrateTheoremContent_r216` proves the *opposite* for the flagship
implication: the antecedent is discarded (`intro _h_antecedents`) and the
consequences are independently provable, so any proposition whatsoever implies
them.

**(C) and (D) are the unified theory.** Everything else is a list.

---

## 3. THE WEAKER, CURRENTLY-REACHABLE VERSION

What could honestly be assembled today. Note what is absent: no (K), no (C),
no (D), and only one literal sector.

```lean
/-- **PRINCIPIA FRACTALIS — VERIFIED POSITION (reachable form), 2026-09-07.**

    NO HYPOTHESES. This is what the corpus can currently support with every
    conjunct on a standard object and every discharge non-circular.

    It is deliberately NOT called a completion theorem. It makes no claim
    that the substrate determines anything, and no claim that any constant
    is derived. -/
theorem principia_fractalis_verified_position_2026_09_07 :

    -- (V1) The substrate is a genuine constructed object.
    (CompleteSpace PF.TimelessFieldCompletion) ∧
    (∃ x : PF.TimelessFieldCompletion, x ≠ 0) ∧

    -- (V2) The r331b endpoint: exact zero-count identity for the classical
    --      entire Riemann xi on the T = 15 rectangle. UNCONDITIONAL.
    (RectangleIntegral' (fun s => logDeriv riemannXiEntire s) z15 w15
       = ∑ ρ ∈ (finite_zeros_rectangle
                 (riemannXiEntire_analyticOnNhd _)
                 (rectangleBorder_subset_rectangle z15 w15 z15_mem_RectangleBorder)
                 (boundary_zero_free_of_top_right_half H_TOP z15
                     z15_mem_RectangleBorder)).toFinset,
             (analyticOrderNatAt riemannXiEntire ρ : ℂ)) ∧

    -- (V3) Top-edge negativity over the full partition of [1/2, 1].
    (∀ σ : ℝ, 1/2 ≤ σ → σ ≤ 1 →
        (riemannXiEntire (⟨σ, 15⟩ : ℂ)).re < -(1/10000 : ℝ)) ∧

    -- (V4) NEGATIVE RESULT, kernel-proved: the eleven-invariant alpha web
    --      does not pin the nine values. For every t > 0 there is a
    --      satisfying assignment with alpha_BSD = t.
    (∀ t : ℝ, 0 < t → ∃ a : PF.AlphaAssignment,
        PF.SatisfiesElevenInvariants a ∧ a.aBSD = t) ∧

    -- (V5) NEGATIVE RESULT, kernel-proved: the flagship substrate
    --      implication discards its antecedent, so any proposition
    --      implies the consequences.
    (∀ P : Prop, P → PF.PFSubstrateConsequences)
```

**Every conjunct here is either already proved or provable from existing green
material.** (V2) and (V3) are the r331b chain. (V4) is
`alpha_web_admits_every_positive_BSD`. (V5) is `SubstrateTheoremContent_r216` §1.

Two of the five conjuncts are **negative results about the framework**. That is
the honest shape of the corpus today, and stating it in one theorem is more
valuable than another capstone that hides it.

---

## 4. THE EMPIRICAL COMPANION — SEPARATE, NEVER MIXED

Conclusions premised on measurement or on finite-precision numerics do not
belong in §2 or §3. They belong here, under a name that cannot be mistaken.

```lean
/-- **EMPIRICALLY-PREMISED position.** Every conclusion below rests on a
    numerical or measured premise. NOT mathematical proof. -/
theorem principia_fractalis_empirically_premised_position
    (hNum : PF.Empirical.NumericalPremises) : ...
```

Known empirical premises in the current corpus, all from the Cohen 2025
transfer-operator citation as quoted in
`RH_FrameworkStandardDischarge_NamedAnchors_2026_06_19.lean:222`:

| premise | stated precision | status |
|---|---|---|
| self-adjointness of `T̃_N` | `‖T̃_N − T̃_N†‖/‖T̃_N‖ < 10⁻¹⁵`, `N ≤ 40` | numerical at finite N |
| eigenvalue–zero correspondence | 150-digit precision, **five pairs** | numerical, five data points |
| scaling factor `5×10⁻⁶` | "derived theoretically" from truncation + normalisation + `O(1/N)` | derivation not formalised |
| first positive ordinate `t₁ ≈ 14.1347…` | thousands of decimals (Odlyzko / Gourdon / Platt) | computational, and genuinely established |

This theorem takes a hypothesis binder **on purpose**. That is what makes it
honest.

---

## 5. FIELD-BY-FIELD EXPLANATION

| conjunct | what it asserts | why it must be separate | reachable today? |
|---|---|---|---|
| **(U1)** | substrate is a C*-algebra | a unified theory needs an object, not a hypothesis | **near** — r54–r57 remain |
| **(U2)** | substrate is nontrivial | blocks the zero-algebra vacuity | **yes** |
| **(U3)** | it is the completion of T_∞ | blocks silent reindexing | **yes** |
| **(E1)** | the equivalence relation is the framework's own | prevents an ad-hoc relation chosen to make (E2) true | **no** — not stateable |
| **(E2)** | derived constants are invariants of it | a constant that changes with representative is an artefact | **no** — not stateable |
| **(K0)** | the constant-functional is intrinsic | without it, `Φ` is a lookup table | **no** — `IsIntrinsic` undefined |
| **(K1)–(K9)** | the nine α-values are outputs | currently they are `def`s; this is the whole difference | **no** |
| **(K-RIGID)** | uniqueness of `Φ` | r124 shows the eleven invariants admit a family | **no** |
| **(S1)** | literal RH | the one sector already stated faithfully | statement yes, proof no |
| **(S2)** | literal P ≠ NP | apparently faithful; needs a TM-encoding audit | statement likely, proof no |
| **(S3)** | literal NS global regularity | current predicate is a substrate stand-in | **no** |
| **(S4)** | literal YM mass gap | current anchors are `Prop := True` | **no** |
| **(S5)** | literal BSD for all curves | current equality is `rfl` on one function | **no** |
| **(S6)** | literal Hodge with cycle witnesses | current `isAlgebraic` is a substrate predicate | **no** — but the Voisin encoding is a real start |
| **(C1)–(C6)** | substrate bears on each sector | this is the unification claim itself | **no** |
| **(D)** | one antecedent is load-bearing | r216's test; the minimum evidence of derivation | **no** |

---

## 6. PREMISES THAT RESTATE DESIRED CONCLUSIONS

The directive requires this list explicitly. Every entry is read from the
current corpus, not inferred.

### 6.1 Outright circular — premise ⊇ conclusion

| # | premise, as declared | conclusion it yields | mechanism |
|---|---|---|---|
| **X1** | `ClayClosureBundleBulletproof.rh_hp_program_positive : HilbertPolyaProgramConjecture_Positive`, whose content is `PF_T3SymIsHilbertPolyaOperator_Positive → RiemannHypothesis` | `Clay_RiemannHypothesis_Standard`, which **is** `RiemannHypothesis` | with sibling field `rh_hp_T3sym_positive : PF_T3SymIsHilbertPolyaOperator_Positive`, modus ponens. Both premises sit in the same structure |
| **X2** | `Mayer1991_Cohen2025_substrate_HP_program_citation`, defined as `:= HilbertPolyaProgramConjecture_Positive` | same as X1 | the r301 hypothesis carries this a **second** time, independently of X1 |
| **X3** | `Hardy1914_published_theorem_substrate_citation`, defined as `:= PositiveOnLineZetaZeroOrdinatesNonempty` | r301 conjunct (E2) is `PositiveOnLineZetaZeroOrdinatesNonempty` | premise and conclusion are the *same Prop*. This one is not merely circular, it is an identity |

X3 deserves emphasis: r301 lists `PositiveOnLineZetaZeroOrdinatesNonempty` as
delivered conclusion (E2) while requiring it as hypothesis field `hardy1914`.
The theorem returns one of its own inputs. (Hardy 1914 is a genuine published
theorem, so the Prop is *true* — but it is assumed here, not proved here, and it
must not be reported as an output.)

### 6.2 Vacuous — conclusion holds by construction, says nothing

| # | node | mechanism |
|---|---|---|
| **X4** | `Clay_BSD_Standard PF_BSDEncodingV5` | `algebraicRankV5 = analyticRankV5 = manuscriptRankV5`; the equality is `rfl`; off a 20-curve list both return `0` |
| **X5** | `GlimmJaffe_OS_SU2_TypedAnchor`, `StreaterWightman_SU2_TypedAnchor`, `OsterwalderSchrader_SU2_TypedAnchor` | each is `def … : Prop := True`, and each is a conjunct of the YM `satisfiesClayAxioms` |
| **X6** | `PrincipiaFractalisSubstrateTheorem` | antecedent discarded; consequences independently provable; r216 §1 proves *any* proposition implies them |
| **X7** | α-skeleton layer (B) of r301 | `α_NS = 3π/2` etc. are `rfl` on chosen `def`s; the "doubling identity" is `3π/2 = 2·(3π/4)` |

### 6.3 Target-encoded — assumption chosen because the target satisfies it

All eight r128 structural laws, per the corpus's own audit: **class F, all
eight**, with **zero** of class A. Individually: L1, L2, L4 also class D
(minimal polynomial of a chosen value); L3, I6, I7, I9 also class E (trivial
arithmetic on chosen numerals); **L5 also class G** — the sole law whose
narrative motivation has no formal counterpart anywhere in the corpus, and the
exact equation that closes r124's free parameter.

### 6.4 Open conjecture carried as hypothesis (honest, but load-bearing)

| # | premise | sector it carries |
|---|---|---|
| **X8** | `PF_T3SymIsHilbertPolyaOperator_Positive` | RH |
| **X9** | `TuringEncoding.PolylogEigenvalueConjecture` | P vs NP |
| **X10** | `OSRP_Compatible_Interacting_Ham_Open` (name carries "Open") | YM |

These are not defects — carrying a named open conjecture as an explicit
hypothesis is correct practice. They become defects only when the resulting
theorem is described as a "position" or a "closure" without them travelling
with it.

---

## 7. RECOMMENDATION

Do **not** attempt §2 now. Its blocking gaps — `IsIntrinsic`,
`SubstrateEquiv`, `SubstrateBearsOn` — are definitional problems, not proof
problems, and defining them badly would produce another vacuous capstone.

Do consider §3. `principia_fractalis_verified_position_2026_09_07` is
assemblable from existing green material, would be the corpus's first
hypothesis-free top-level theorem, and would state the negative results in the
same breath as the positive ones. That combination is what a referee would trust.

**Neither is authorised by this file.** Both are drafts. Nothing here modifies a
`.lean` file, and public HEAD remains `96c71da7`.

---

*Drafted 2026-09-07. Strongest honest version: not reachable. Weaker version:
reachable, unauthorised.*
