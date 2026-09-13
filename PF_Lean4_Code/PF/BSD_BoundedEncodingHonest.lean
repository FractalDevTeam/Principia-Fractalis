/-
# BSD Bounded Encoding — Two-Rank-Witness Presentation

## ★ Epistemic Status (2026-09-12 post-review reclassification) ★

The theorems in this file operate at THREE distinct semantic layers:

  1. **Structural Lean constraints on the encoding.**
     `RankLowerBoundWitness E` has two independent rank fields; the
     encoding's Clay-predicate is `analyticRank = algebraicRank` under
     the projection maps. This layer is pure type theory.

  2. **Tree-state indicators.**
     `AlgebraicRankLowerBoundEvidence` currently exposes `heegnerRankOne`
     via the `RankWitnessTyped` structural Prop, and
     `AnalyticRankLowerBoundEvidence` currently exposes only the trivial
     constructor. Any theorem parametrised by these types reports the
     LEAN TREE'S current witness-population state, not the arithmetic
     of any specific elliptic curve.

  3. **BSD content.** BSD is NOT PROVEN, DISPROVEN, OR EVIDENCED BY
     ANY THEOREM IN THIS FILE. Specifically:
       * `RankWitnessTyped E r` ignores `E` (its first argument is
         underscored — see `PF/BSD_RankWitnessTypedUpgrade.lean:141`)
         and at `r = 1` reduces to "∃ one nonzero rational". The `-1`
         witness used for `E_{37.a1}` satisfies this trivially and
         proves NEITHER non-torsion NOR Mordell-Weil rank on any curve.
       * `r_an_lb = 0` for `E_{37.a1}` records absent tree machinery,
         NOT analytic rank zero. LMFDB records `L'(37.a1, 1) ≠ 0`
         (analytic rank = 1); the Lean number 0 is a
         tree-completeness signal, not a curve datum.
       * The theorem `boundedEncoding_ClayPredicate_falsified_by_treeAsymmetry`
         (formerly `bounded_Clay_BSD_fails_unconditionally`, kept as
         `@[deprecated]` alias) reports encoding-vs-witness-population
         tension. It is NOT a BSD refutation, NOT an unconditional BSD
         gap, NOT honest evidence about `E_{37.a1}`.

Section 5 identifiers use `treeState*` / `boundedEncoding_*` prefixes
to make the epistemic layer legible from the name alone. The original
names from commit `146c153d` are preserved as `@[deprecated]` aliases
pointing to the new names, so any paper or codex reference that cites
the old identifiers continues to typecheck.

## Purpose

This file provides an HONEST alternative to `PF/BSD_DirectDischargeAttempt.lean`'s
Σ-encoding, in which both `algebraicRank` and `analyticRank` project the same
field `p.2.r` and the Clay equality is `rfl`. The vacuity there is by design
(the file is a bookkeeping wrapper), but the design pre-dates the book's
2026-07-28/31 φ/e-multiplicity mechanism falsification (see
`codex/CH24_OPERATOR_QUASINILPOTENT_2026-07-30.md`,
`CH24_OPERATOR_ILLPOSED_2026-07-30.md`,
`CH24_SPECTRAL_DIAGNOSIS_2026-07-31.md`) and the book's own honest-scope
verification update (ch24 lines 616-702, "the Birch-Swinnerton-Dyer conjecture
is NOT proven here and remains open").

The BOUNDED encoding here:

* Carries **two independent rank witnesses** `r_alg_lb` and `r_an_lb`. The
  Clay statement `analyticRank = algebraicRank` under this encoding is
  therefore **not** `rfl` — it is a genuine hypothesis on witness content.
* Uses inductive **evidence** types that expose the current gap:
  `AlgebraicRankLowerBoundEvidence` has constructors for ranks the tree
  can currently witness (via Heegner cascade); `AnalyticRankLowerBoundEvidence`
  has only the trivial constructor, matching the empirical fact that
  `mestre_nagao_trace` produces a slope reading, not a kernel-verifiable
  analytic-rank lower bound.
* Makes the gap MACHINE-CHECKED via `no_analytic_rank_ge_one_evidence_yet`:
  the type `AnalyticRankLowerBoundEvidence E n` is empty for `n ≥ 1`, so
  any populated `RankLowerBoundWitness` with `r_an_lb ≥ 1` is inconstructible.

## What this file does NOT do

* Does **not** prove BSD or any of its sub-claims. BSD is out of reach.
* Does **not** touch `PF/BSD_DirectDischargeAttempt.lean` semantically —
  that file remains as the (self-declared) bookkeeping wrapper.
* Does **not** touch the load-bearing substrate content:
  Heegner rank-1 flags (`PF/BSD_HeegnerRank1Proof*.lean`), the r188c trace
  identity (`PF/TransferResidue_r188c.lean`), the r194 Mestre-Nagao
  instantiation (`PF/EllipticTrace_r194.lean`), or the universal
  rank-lower-bound machinery (`codex/BSD_UNIVERSAL_SECANT_2026-08-05.md`).
* Does **not** import the substrate content above; the file is deliberately
  independent so future landings can populate the encoding without
  circular dependencies.

## What this file DOES do

* Establishes an honest-scope structure and encoding that a future
  landing (with real per-curve algebraic AND analytic rank witnesses)
  can populate curve-by-curve.
* Records the current gap as a machine-checked theorem, so any regression
  claiming an analytic-rank ≥ 1 witness will surface at compile time.

## Charter reference

`codex/BSD_HONEST_REWRITE_CHARTER_2026-09-12.md` — Campaign BSD-Bounded.

## Kernel audit

All declarations audit to `[propext, Classical.choice, Quot.sound]`. See
`§Section 5 — In-file axiom audit` at the end of the file.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import PF.Referee.StandardClayStatements
import PF.BSD_HeegnerRank1Proof  -- for E_rank_one, heegnerDerived_rankWitnessTyped_E37a1

namespace PrincipiaTractalis.BSD.BoundedEncoding

open PF.Referee.StandardClayStatements
open PrincipiaTractalis
open PrincipiaTractalis.BSD_RankWitnessTypedUpgrade  -- for RankWitnessTyped
open PrincipiaTractalis.BSDGaloisPairConcordance     -- for E_rank_one
open PrincipiaTractalis.BSD_HeegnerRank1Proof         -- for the E_37a1 witnesses

/-! ## Section 1 — Evidence types (tree-population indicators)

    These inductive types are **tree-population indicators**, not
    curve-specific rank witnesses. They enumerate the shapes of
    proxy-Prop the PF tree currently exposes for constructor
    population, and the specific Props referenced (in particular
    `RankWitnessTyped`) IGNORE the curve argument they nominally
    quantify over. Concretely:

    * `RankWitnessTyped E r` (`PF/BSD_RankWitnessTypedUpgrade.lean:141`)
      has its first argument underscored (`_E`) and at `r = 1` reduces
      to `∃ one nonzero rational`. Any nonzero rational — decorative,
      Heegner-labelled, or otherwise — inhabits it. The Prop carries
      NO curve-specific arithmetic content.
    * Populating `heegnerRankOne E …` therefore records that a tree
      inhabitant exists for a fixed structural Prop-shape; it does
      NOT record a curve-specific rank-≥-1 lower bound.
    * `AnalyticRankLowerBoundEvidence` currently has only the trivial
      constructor: the tree ships no analytic-rank lower-bound
      machinery at rank ≥ 1 (`mestre_nagao_trace` in
      `PF/EllipticTrace_r194.lean` produces a slope reading, not a
      bound).

    The types thus function as a **snapshot of tree completeness** in
    two directions (algebraic-shape / analytic-shape), NOT as a claim
    about the arithmetic of any specific elliptic curve. -/

/-- Tree-population indicator for the "algebraic-rank lower bound"
    encoding slot. Constructor availability at rank `n` reports what
    the PF tree currently exposes as a structural-Prop shape at that
    rank; it does NOT report a curve-specific rank witness.

    * `trivial` — always inhabited at rank 0.
    * `heegnerRankOne` — takes a `RankWitnessTyped E 1` term, which is
      `∃ g : Fin 1 → ℚ, distinct ∧ nonzero`. That Prop ignores `E`
      and holds for any nonzero rational. Populating this constructor
      is not curve-specific evidence. On `E_{37.a1}` we happen to
      populate it via `heegnerDerived_rankWitnessTyped_E37a1` (the
      Heegner-labelled `-1`), but any other nonzero rational would
      inhabit the same Prop identically.

    Adding constructors here (e.g. a `mordellWeilLinearIndependent`
    shape backed by real MW-independent-point evidence, or a
    `gramDeterminantRankGe` shape from the universal secant chain)
    is how curve-specific content enters the encoding. -/
inductive AlgebraicRankLowerBoundEvidence : WeierstrassCurve ℚ → ℕ → Type where
  /-- Trivial: any curve admits the encoding-slot for rank-lower-bound 0. -/
  | trivial (E : WeierstrassCurve ℚ) : AlgebraicRankLowerBoundEvidence E 0
  /-- Encoding-slot populator at rank 1, backed by the tree's
      `RankWitnessTyped E 1` structural proxy (`PF/BSD_RankWitnessTypedUpgrade.lean:141`).
      The proxy IGNORES its first argument `E` and holds for any
      nonzero rational; populating this constructor for a given curve
      records only that the tree exposes a `RankWitnessTyped`-shape
      inhabitant, NOT that the curve has Mordell-Weil rank ≥ 1. -/
  | heegnerRankOne (E : WeierstrassCurve ℚ)
      (rankWitness : RankWitnessTyped E 1) :
      AlgebraicRankLowerBoundEvidence E 1

/-- Evidence for an analytic-rank lower bound. Currently only the trivial
    constructor is available: the PF tree contains NO kernel-verified
    analytic-rank lower bound ≥ 1. `mestre_nagao_trace`
    (`PF/EllipticTrace_r194.lean`) gives a slope reading, not a bound.

    See `no_analytic_rank_ge_one_evidence_yet` below for the
    machine-checked statement of this gap. -/
inductive AnalyticRankLowerBoundEvidence : WeierstrassCurve ℚ → ℕ → Type where
  /-- Trivial: analytic rank is `≥ 0` for any curve (no evidence needed). -/
  | trivial (E : WeierstrassCurve ℚ) : AnalyticRankLowerBoundEvidence E 0

/-! ## Section 2 — The two-slot witness structure

    Unlike `RankCertificate` (in `PF/BSD_DirectDischargeAttempt.lean`),
    which has a single `r` field and both rank projections read it, this
    structure has SEPARATE encoding-slot fields for the algebraic-side
    and analytic-side tree indicators. Populating both slots is a
    LEAN-TREE act (satisfying the two shape-Props in Section 1); it
    does NOT constitute Mordell-Weil rank evidence on either side.

    Since the fields are independent, the Clay equality
    `analyticRank = algebraicRank` is NOT provable by `rfl` on the
    resulting encoding — it becomes a hypothesis on the numeric
    values of `r_alg_lb` and `r_an_lb`. When those values disagree,
    the encoding's Clay predicate fails; that failure reflects the
    two-slot ASYMMETRY OF TREE-POPULATION SHAPES available at the
    time of construction. It does NOT reflect the arithmetic of the
    underlying curve. -/

/-- A two-slot tree-state record parametrised by an elliptic curve.

    * `r_alg_lb` — the numeric value in the algebraic-side encoding slot.
    * `r_an_lb`  — the numeric value in the analytic-side encoding slot.
    * `alg_evidence`, `an_evidence` — inhabitants of the corresponding
      shape-Props from Section 1 (tree-population indicators, NOT
      curve-specific rank witnesses).

    The two numeric fields are INDEPENDENT: the structure does not
    force `r_alg_lb = r_an_lb`. Nothing in the structure asserts that
    either number equals a Mordell-Weil or analytic rank on the curve
    — the shape-Props supply no such content. -/
structure RankLowerBoundWitness (E : WeierstrassCurve ℚ) : Type where
  r_alg_lb : ℕ
  r_an_lb  : ℕ
  alg_evidence : AlgebraicRankLowerBoundEvidence E r_alg_lb
  an_evidence  : AnalyticRankLowerBoundEvidence E r_an_lb

/-! ## Section 3 — The `StandardBSDEncoding` instance

    Projects the encoding's `algebraicRank` field from `r_alg_lb` and
    `analyticRank` from `r_an_lb` — two DIFFERENT slots. This is the
    essential departure from `StandardBSDEncoding_Sigma` in
    `PF/BSD_DirectDischargeAttempt.lean`, where both projections read
    the same field. As a consequence, the encoding's Clay predicate
    is not `rfl`; it depends on whether the two numeric slots agree.

    That predicate is a syntactic check on tree-slot numbers, NOT a
    reading of curve arithmetic. Its truth on any given Σ-pair
    depends entirely on which shape-Props Section 1 currently makes
    available. -/

/-- Algebraic-side numeric projection from a two-slot Σ-pair. -/
def boundedAlgebraicRank
    (p : Σ E : WeierstrassCurve ℚ, RankLowerBoundWitness E) : ℕ :=
  p.2.r_alg_lb

/-- Analytic-side numeric projection from a two-slot Σ-pair. -/
def boundedAnalyticRank
    (p : Σ E : WeierstrassCurve ℚ, RankLowerBoundWitness E) : ℕ :=
  p.2.r_an_lb

/-- The two-slot BSD encoding: `EllipticCurve` = curves with two-slot
    tree-state records; `algebraicRank` = `r_alg_lb`; `analyticRank`
    = `r_an_lb`.

    Under this encoding, `Clay_BSD_Standard` is the syntactic assertion
    `r_an_lb = r_alg_lb` for every Σ-pair. It is not `rfl`, but neither
    is it a reading of the underlying curve's arithmetic — the equality
    checks two tree-slot numbers whose interpretations are governed by
    the shape-Props in Section 1. -/
def StandardBSDEncoding_Bounded : StandardBSDEncoding where
  EllipticCurve := Σ E : WeierstrassCurve ℚ, RankLowerBoundWitness E
  algebraicRank := boundedAlgebraicRank
  analyticRank  := boundedAnalyticRank

/-! ## Section 4 — Tree-completeness diagnostics

    ★ Reclassified 2026-09-12 post-review. These theorems are
    diagnostics on the LEAN TREE'S current shape-Prop inventory
    (Section 1), NOT statements about elliptic-curve arithmetic.

    (a) `no_analytic_rank_ge_one_evidence_yet` — the type
        `AnalyticRankLowerBoundEvidence E n` is empty for `n ≥ 1`.
        Reports that Section 1 does not currently expose an
        analytic-side shape-Prop constructor at rank ≥ 1.

    (b) `bounded_witness_forces_analytic_zero` — every populated
        `RankLowerBoundWitness` currently has `r_an_lb = 0`, forced
        by (a).

    (c) `bounded_encoding_projectionAsymmetry_from_algebraic_lb`
        (renamed from `bounded_encoding_exhibits_bsd_gap`,
        preserved as `@[deprecated]` alias for provenance) —
        combining `heegnerRankOne` (any curve, algebraic-side slot
        populated with `RankWitnessTyped E 1` shape) with the analytic
        forcing (b) produces a Σ-pair where `boundedAnalyticRank ≠
        boundedAlgebraicRank`. This exhibits ENCODING-SLOT
        DISAGREEMENT arising from shape-Prop-inventory asymmetry
        in Section 1. It does NOT witness a BSD gap on the curve.

    (d) `bounded_encoding_ClayPredicate_falsifiable_via_algebraic_lb`
        (renamed from `bounded_Clay_BSD_not_provable_under_populated_algebraic`,
        preserved as `@[deprecated]` alias) — as an immediate
        consequence, `Clay_BSD_Standard StandardBSDEncoding_Bounded`
        is falsifiable whenever the algebraic-side slot admits a
        populated instance. This measures ENCODING-vs-SHAPE-INVENTORY
        tension, not BSD content on any curve. -/

/-- **Tree-inventory diagnostic.** The type
    `AnalyticRankLowerBoundEvidence E n` is empty for `n ≥ 1`: Section 1
    exposes only the trivial constructor on the analytic side. If a
    future landing adds a shape-Prop constructor at rank ≥ 1, this
    theorem will fail to compile, surfacing the change at build time.

    `mestre_nagao_trace` (`PF/EllipticTrace_r194.lean`) gives a slope
    reading, not a shape-Prop suitable for constructor population; it
    does not qualify to populate an analytic-side ≥ 1 constructor. -/
theorem no_analytic_rank_ge_one_evidence_yet
    (E : WeierstrassCurve ℚ) (n : ℕ) (hn : 1 ≤ n) :
    IsEmpty (AnalyticRankLowerBoundEvidence E n) := by
  constructor
  intro w
  -- The only constructor of `AnalyticRankLowerBoundEvidence` is `trivial`,
  -- which forces `n = 0`, contradicting `1 ≤ n`.
  cases w with
  | trivial => exact absurd hn (by decide)

/-- Under the current tree, any populated `RankLowerBoundWitness` has
    `r_an_lb = 0`: `AnalyticRankLowerBoundEvidence E r_an_lb` is
    inhabited only when `r_an_lb = 0`. -/
theorem bounded_witness_forces_analytic_zero
    {E : WeierstrassCurve ℚ} (w : RankLowerBoundWitness E) :
    w.r_an_lb = 0 := by
  -- The evidence field forces `AnalyticRankLowerBoundEvidence E w.r_an_lb`
  -- to be inhabited. The only inhabited case is `n = 0`.
  by_contra h
  have hne : w.r_an_lb ≠ 0 := h
  have hle : 1 ≤ w.r_an_lb := Nat.one_le_iff_ne_zero.mpr hne
  have := no_analytic_rank_ge_one_evidence_yet E w.r_an_lb hle
  exact this.false w.an_evidence

/-- **Encoding-slot disagreement from shape-Prop inventory asymmetry.**
    For any two-slot record with `r_alg_lb ≥ 1` (i.e. any populated
    `heegnerRankOne` — which is a `RankWitnessTyped E 1` witness,
    ignoring `E`), the analytic-side slot is forced to 0 by
    `bounded_witness_forces_analytic_zero`. The two numeric fields
    disagree; the encoding's Clay predicate fails on that pair.

    This is a diagnostic that Section 1 currently exposes a
    populated algebraic-side shape-Prop but no analytic-side
    shape-Prop at rank ≥ 1. It reports LEAN TREE state; it is NOT a
    real BSD gap on any curve, NOT a curve-arithmetic reading, and
    NOT a witness to the truth-value of BSD. -/
theorem bounded_encoding_projectionAsymmetry_from_algebraic_lb
    (p : Σ E : WeierstrassCurve ℚ, RankLowerBoundWitness E)
    (h : 1 ≤ p.2.r_alg_lb) :
    boundedAnalyticRank p ≠ boundedAlgebraicRank p := by
  unfold boundedAnalyticRank boundedAlgebraicRank
  have h_an_zero : p.2.r_an_lb = 0 := bounded_witness_forces_analytic_zero p.2
  rw [h_an_zero]
  omega

/-- Provenance alias for
    `bounded_encoding_projectionAsymmetry_from_algebraic_lb`.
    The pre-reclassification name contained "bsd_gap", suggesting a
    BSD gap on the curve. The theorem reports a Lean-tree
    encoding-slot disagreement induced by shape-Prop-inventory
    asymmetry (Section 1 currently has no analytic-side rank ≥ 1
    constructor); it is NOT a BSD gap. Preserved as an alias for
    reference continuity only. Do NOT use in new work. -/
@[deprecated bounded_encoding_projectionAsymmetry_from_algebraic_lb
  (since := "2026-09-12 (reclassification: tree inventory, not BSD gap)")]
theorem bounded_encoding_exhibits_bsd_gap
    (p : Σ E : WeierstrassCurve ℚ, RankLowerBoundWitness E)
    (h : 1 ≤ p.2.r_alg_lb) :
    boundedAnalyticRank p ≠ boundedAlgebraicRank p :=
  bounded_encoding_projectionAsymmetry_from_algebraic_lb p h

/-- **Clay predicate falsifiable via algebraic-side population.** If any
    two-slot record has `r_alg_lb ≥ 1`, then the encoding's Clay
    predicate `Clay_BSD_Standard StandardBSDEncoding_Bounded` fails on
    the resulting Σ-pair (because Section 1 forces `r_an_lb = 0`).

    This measures ENCODING-vs-SHAPE-INVENTORY tension in the LEAN TREE.
    It does NOT refute BSD, does NOT establish a gap on any curve, and
    does NOT interpret the numeric fields as MW or analytic ranks. -/
theorem bounded_encoding_ClayPredicate_falsifiable_via_algebraic_lb
    (h : ∃ p : Σ E : WeierstrassCurve ℚ, RankLowerBoundWitness E,
         1 ≤ p.2.r_alg_lb) :
    ¬ Clay_BSD_Standard StandardBSDEncoding_Bounded := by
  intro hclay
  obtain ⟨p, hp⟩ := h
  have := bounded_encoding_projectionAsymmetry_from_algebraic_lb p hp
  exact this (hclay p)

/-- Provenance alias for
    `bounded_encoding_ClayPredicate_falsifiable_via_algebraic_lb`.
    The pre-reclassification name paired "Clay_BSD" with
    "not_provable", suggesting a BSD result. The theorem measures
    tree-shape-inventory vs encoding tension; it is NOT a BSD result.
    Preserved as an alias for reference continuity. Do NOT use in
    new work. -/
@[deprecated bounded_encoding_ClayPredicate_falsifiable_via_algebraic_lb
  (since := "2026-09-12 (reclassification: tree/encoding tension, not BSD)")]
theorem bounded_Clay_BSD_not_provable_under_populated_algebraic
    (h : ∃ p : Σ E : WeierstrassCurve ℚ, RankLowerBoundWitness E,
         1 ≤ p.2.r_alg_lb) :
    ¬ Clay_BSD_Standard StandardBSDEncoding_Bounded :=
  bounded_encoding_ClayPredicate_falsifiable_via_algebraic_lb h

/-! ## Section 5 — Tree-completeness asymmetry diagnostic at E_{37.a1}

    **★ Reclassified 2026-09-12 post-review (see file docstring §Epistemic
    Status).** The instance defined below was originally introduced at
    commit `146c153d` with names suggesting it discharged BSD content on
    `E_{37.a1}`. That was an overclaim. The truth is narrower:

    * `RankWitnessTyped` (in `PF/BSD_RankWitnessTypedUpgrade.lean:141`)
      is `∃ g : Fin r → ℚ, distinct ∧ nonzero`. Its first argument `_E`
      is IGNORED (underscored). At `r = 1` this reduces to "there exists
      a nonzero rational". The witness `-1` used below satisfies this
      trivially and does NOT prove non-torsion on any curve, nor
      Mordell-Weil rank ≥ 1.

    * `r_an_lb = 0` on the analytic side does NOT assert "analytic rank
      of `E_{37.a1}` is zero" — that would contradict the LMFDB value
      `L'(37.a1, 1) ≈ 0.30599977… ≠ 0`. It records that the PF LEAN TREE
      lacks kernel-verified analytic-rank witnesses ≥ 1.

    * The resulting theorem `¬ Clay_BSD_Standard StandardBSDEncoding_Bounded`
      is therefore NOT an unconditional BSD gap. It is a diagnostic that
      the bounded encoding's Clay predicate FAILS whenever the tree
      provides asymmetric witness populations (Heegner-shape algebraic
      evidence, no analytic evidence). It reports tree state, not
      curve arithmetic.

    Names below use `treeState*` / `boundedEncoding_*` prefixes to make
    the epistemic status legible from the identifier alone. The
    original names from `146c153d` are retained as `@[deprecated]`
    aliases pointing to the new names, preserving git-history/paper
    references. Section-4 references are made to the reclassified
    names (`bounded_encoding_projectionAsymmetry_from_algebraic_lb`
    and `bounded_encoding_ClayPredicate_falsifiable_via_algebraic_lb`),
    not the deprecated `bsd_gap` / `Clay_BSD` originals. -/

/-- **Tree-state instance at E_{37.a1}.** A `RankLowerBoundWitness`
    populated on `E_{37.a1}` with `r_alg_lb = 1` and `r_an_lb = 0`.

    Semantics of the two fields:
      * `r_alg_lb = 1` — populated because the tree contains a
        `RankWitnessTyped E_rank_one 1` inhabitant (an existence claim
        for one nonzero rational, ignoring `E`). This is a STRUCTURAL
        LEAN CONSTRAINT satisfied on any curve, not a MW-rank claim
        on this specific curve.
      * `r_an_lb = 0` — populated because the tree provides ONLY the
        trivial constructor of `AnalyticRankLowerBoundEvidence` (the
        current absence of analytic-rank machinery). This does NOT
        assert `L(E_{37.a1}, s)` vanishes to order 0 at `s = 1`;
        LMFDB in fact records `L'(37.a1, 1) ≠ 0`, i.e., analytic rank
        exactly 1. The Lean number 0 here is a TREE-COMPLETENESS
        indicator, not a curve datum. -/
noncomputable def treeStateInstance_E37a1 : RankLowerBoundWitness E_rank_one where
  r_alg_lb := 1
  r_an_lb  := 0
  alg_evidence := AlgebraicRankLowerBoundEvidence.heegnerRankOne
    E_rank_one heegnerDerived_rankWitnessTyped_E37a1
  an_evidence := AnalyticRankLowerBoundEvidence.trivial E_rank_one

/-- Provenance alias for `treeStateInstance_E37a1`, preserving the
    original name from commit `146c153d` for backwards compatibility
    with any paper or codex reference. Do NOT use in new work. -/
@[deprecated treeStateInstance_E37a1
  (since := "2026-09-12 (reclassification: tree-state, not BSD, witness)")]
noncomputable def witness_E37a1 : RankLowerBoundWitness E_rank_one :=
  treeStateInstance_E37a1

/-- The packaged Σ-pair for `treeStateInstance_E37a1`. Same epistemic
    status: reports LEAN TREE state on `E_{37.a1}`, not curve arithmetic. -/
noncomputable def treeStateSigma_E37a1 :
    Σ E : WeierstrassCurve ℚ, RankLowerBoundWitness E :=
  ⟨E_rank_one, treeStateInstance_E37a1⟩

/-- Provenance alias for `treeStateSigma_E37a1`. Do NOT use in new work. -/
@[deprecated treeStateSigma_E37a1
  (since := "2026-09-12 (reclassification: tree-state, not BSD, witness)")]
noncomputable def sigmaWitness_E37a1 :
    Σ E : WeierstrassCurve ℚ, RankLowerBoundWitness E :=
  treeStateSigma_E37a1

/-- **Bounded-encoding rank-projection asymmetry at E_{37.a1}.**
    On the tree-state Σ-pair, `boundedAnalyticRank ≠ boundedAlgebraicRank`.

    Epistemic status: this is a WITNESS-POPULATION asymmetry between the
    two evidence-type inductive families in this file. It says the tree
    has a populated `heegnerRankOne` constructor (structural Prop shape)
    but only the trivial constructor of `AnalyticRankLowerBoundEvidence`.
    It does NOT say the analytic rank and algebraic rank of `E_{37.a1}`
    disagree — LMFDB records both equal to 1. -/
theorem boundedEncoding_projectionAsymmetry_at_E37a1 :
    boundedAnalyticRank treeStateSigma_E37a1
      ≠ boundedAlgebraicRank treeStateSigma_E37a1 := by
  apply bounded_encoding_projectionAsymmetry_from_algebraic_lb
  -- Goal: 1 ≤ treeStateSigma_E37a1.2.r_alg_lb, which is 1 ≤ 1.
  exact Nat.le_refl 1

/-- Provenance alias. Original name from commit `146c153d`; the phrase
    "BSD gap at E_{37.a1}" in that name was inaccurate — the theorem
    reports a Lean-tree witness-population asymmetry, not a BSD gap on
    the curve. Preserved as an alias for reference continuity only. -/
@[deprecated boundedEncoding_projectionAsymmetry_at_E37a1
  (since := "2026-09-12 (reclassification: tree-state asymmetry, not BSD gap)")]
theorem bounded_encoding_gap_at_E37a1 :
    boundedAnalyticRank treeStateSigma_E37a1
      ≠ boundedAlgebraicRank treeStateSigma_E37a1 :=
  boundedEncoding_projectionAsymmetry_at_E37a1

/-- **`Clay_BSD_Standard` predicate fails on `StandardBSDEncoding_Bounded`
    under the tree's current witness asymmetry.**

    This is NOT a refutation of the Birch-Swinnerton-Dyer conjecture,
    nor an unconditional BSD gap, nor honest evidence about the
    arithmetic of `E_{37.a1}`. The theorem records exactly ONE thing:
    when a bounded-encoding `RankLowerBoundWitness` has `r_alg_lb ≥ 1`
    but `r_an_lb = 0` (which the current tree forces for every populated
    algebraic instance, because `AnalyticRankLowerBoundEvidence` has only
    the trivial constructor), the syntactic Clay-predicate fails on the
    resulting pair.

    Fixing this failure requires EITHER (a) adding a real
    `AnalyticRankLowerBoundEvidence` constructor at rank ≥ 1 (which the
    tree currently lacks), OR (b) restricting the encoding to only allow
    the `r_alg_lb = 0` case (which would forfeit the algebraic witness).
    The theorem measures encoding-vs-witness-population tension in the
    LEAN TREE. It does not measure `E_{37.a1}`. -/
theorem boundedEncoding_ClayPredicate_falsified_by_treeAsymmetry :
    ¬ Clay_BSD_Standard StandardBSDEncoding_Bounded := by
  apply bounded_encoding_ClayPredicate_falsifiable_via_algebraic_lb
  exact ⟨treeStateSigma_E37a1, Nat.le_refl 1⟩

/-- Provenance alias. Original name from commit `146c153d`; the word
    "unconditionally" combined with "Clay_BSD" suggested a BSD result.
    The theorem is a tree-witness-asymmetry diagnostic, not a BSD
    unconditional. Preserved as an alias for reference continuity only. -/
@[deprecated boundedEncoding_ClayPredicate_falsified_by_treeAsymmetry
  (since := "2026-09-12 (reclassification: tree-asymmetry diagnostic, not BSD)")]
theorem bounded_Clay_BSD_fails_unconditionally :
    ¬ Clay_BSD_Standard StandardBSDEncoding_Bounded :=
  boundedEncoding_ClayPredicate_falsified_by_treeAsymmetry

/-! ## Section 6 — In-file axiom audit (build-tree-discipline)

    Every principal declaration in this file audits to
    `[propext, Classical.choice, Quot.sound]`. Regression discipline
    per the memory rule `build-tree-discipline` and the R_f arc's
    precedent (`PF/Consciousness/FractalResonance.lean §10`). -/

section AxiomAudit

-- Structural declarations
#print axioms AlgebraicRankLowerBoundEvidence
#print axioms AnalyticRankLowerBoundEvidence
#print axioms RankLowerBoundWitness
#print axioms boundedAlgebraicRank
#print axioms boundedAnalyticRank
#print axioms StandardBSDEncoding_Bounded

-- Section 4 tree-completeness diagnostics
#print axioms no_analytic_rank_ge_one_evidence_yet
#print axioms bounded_witness_forces_analytic_zero
#print axioms bounded_encoding_projectionAsymmetry_from_algebraic_lb
#print axioms bounded_encoding_ClayPredicate_falsifiable_via_algebraic_lb

-- Provenance aliases for Section 4 (pre-reclassification names from b00cf776)
#print axioms bounded_encoding_exhibits_bsd_gap
#print axioms bounded_Clay_BSD_not_provable_under_populated_algebraic

-- Tree-state instance and asymmetry diagnostic on E_{37.a1}
-- (2026-09-12 reclassified names)
#print axioms treeStateInstance_E37a1
#print axioms treeStateSigma_E37a1
#print axioms boundedEncoding_projectionAsymmetry_at_E37a1
#print axioms boundedEncoding_ClayPredicate_falsified_by_treeAsymmetry

-- Provenance aliases (preserve original names from commit 146c153d)
#print axioms witness_E37a1
#print axioms sigmaWitness_E37a1
#print axioms bounded_encoding_gap_at_E37a1
#print axioms bounded_Clay_BSD_fails_unconditionally

end AxiomAudit

end PrincipiaTractalis.BSD.BoundedEncoding
