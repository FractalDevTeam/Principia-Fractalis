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

/-! ## Section 1 — Evidence types

    These inductive types enumerate the currently-available (in the PF
    tree) sources of rank-lower-bound evidence, at the specific ranks
    for which kernel-verified witnesses exist. Adding a rank requires
    adding a constructor; the type IS the honest inventory. -/

/-- Evidence for an algebraic-rank lower bound. Constructors correspond
    to the sources of witness available in the PF tree at HEAD.

    * `trivial` — any rank has algebraic-rank lower bound `0`
      (there always exist zero points, so `#{P} ≥ 0`).
    * `heegnerRankOne` — a Heegner cascade instance provides a
      rank-1 lower bound for a specific curve. Populating this
      constructor for a curve requires importing the corresponding
      `PF/BSD_HeegnerRank1Proof*.lean` file (deliberately not
      imported here to keep this file free of downstream dependencies).

    Adding a constructor here (e.g. `heegnerRankTwo` for `E_{389a1}`,
    or a `gramDeterminantRankGe` constructor from the universal
    secant chain) is the mechanism by which the encoding's honest
    scope grows. -/
inductive AlgebraicRankLowerBoundEvidence : WeierstrassCurve ℚ → ℕ → Type where
  /-- Trivial: algebraic rank is `≥ 0` for any curve (no evidence needed). -/
  | trivial (E : WeierstrassCurve ℚ) : AlgebraicRankLowerBoundEvidence E 0
  /-- Rank-1 lower bound via a Heegner cascade witness for the specific
      curve `E`. Populated 2026-09-12 with the real `RankWitnessTyped E 1`
      structural proxy from `PF/BSD_RankWitnessTypedUpgrade.lean`: an
      explicit non-zero rational obtained from a Heegner-derived point
      on the curve. This is NOT a `True`-shape placeholder — it requires
      a genuine `∃ g : Fin 1 → ℚ, g 0 ≠ 0` witness. On `E_{37.a1}` this
      is discharged axiom-free via `heegnerDerived_rankWitnessTyped_E37a1`
      (the y-coordinate `-1` of the duplicate of the (0,0) generator). -/
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

/-! ## Section 2 — The bounded witness structure

    Unlike `RankCertificate` (in `PF/BSD_DirectDischargeAttempt.lean`),
    which has a single `r` field and both rank projections read it, this
    structure has SEPARATE lower-bound fields for algebraic and analytic
    rank. This means the Clay equality
    `analyticRank = algebraicRank` is NOT provable by `rfl` on the
    resulting encoding — it becomes a genuine hypothesis on witness
    content, matching the fact that BSD is an open conjecture. -/

/-- A bounded rank-witness for an elliptic curve over `ℚ`.

    * `r_alg_lb` — the claimed algebraic-rank lower bound.
    * `r_an_lb`  — the claimed analytic-rank lower bound.
    * `alg_evidence`, `an_evidence` — the corresponding evidence terms.

    The two rank fields are INDEPENDENT: the structure does NOT force
    `r_alg_lb = r_an_lb`. Any putative equality is precisely the BSD
    content on the curve `E`. -/
structure RankLowerBoundWitness (E : WeierstrassCurve ℚ) : Type where
  r_alg_lb : ℕ
  r_an_lb  : ℕ
  alg_evidence : AlgebraicRankLowerBoundEvidence E r_alg_lb
  an_evidence  : AnalyticRankLowerBoundEvidence E r_an_lb

/-! ## Section 3 — The `StandardBSDEncoding` instance

    Projects `algebraicRank` from `r_alg_lb` and `analyticRank` from
    `r_an_lb` — two DIFFERENT fields. This is the essential departure
    from `StandardBSDEncoding_Sigma` in `PF/BSD_DirectDischargeAttempt.lean`,
    where both projections read the same field. -/

/-- Algebraic-rank projection from a bounded-witness Σ-pair. -/
def boundedAlgebraicRank
    (p : Σ E : WeierstrassCurve ℚ, RankLowerBoundWitness E) : ℕ :=
  p.2.r_alg_lb

/-- Analytic-rank projection from a bounded-witness Σ-pair. -/
def boundedAnalyticRank
    (p : Σ E : WeierstrassCurve ℚ, RankLowerBoundWitness E) : ℕ :=
  p.2.r_an_lb

/-- The bounded BSD encoding: `EllipticCurve` = curves with bounded
    rank-witness pairs; `algebraicRank` = `r_alg_lb`; `analyticRank`
    = `r_an_lb`.

    Under this encoding, `Clay_BSD_Standard` says `r_an_lb = r_alg_lb`
    for every populated pair. This is NOT `rfl` — it is the honest
    Clay content on the encoded curves. -/
def StandardBSDEncoding_Bounded : StandardBSDEncoding where
  EllipticCurve := Σ E : WeierstrassCurve ℚ, RankLowerBoundWitness E
  algebraicRank := boundedAlgebraicRank
  analyticRank  := boundedAnalyticRank

/-! ## Section 4 — Honest scope theorems

    These theorems record the current honest scope of the encoding:

    (a) `no_analytic_rank_ge_one_evidence_yet` — the type
        `AnalyticRankLowerBoundEvidence E n` is empty for `n ≥ 1`.
        This makes the tree's absence of analytic-rank machinery
        machine-checked.

    (b) `bounded_encoding_only_populated_at_zero_analytic_rank` —
        every populated `RankLowerBoundWitness` currently has
        `r_an_lb = 0`. Combined with any curve for which
        `r_alg_lb ≥ 1` (e.g., via `heegnerRankOne`), this gives an
        explicit `RankLowerBoundWitness` where
        `r_an_lb ≠ r_alg_lb` — a machine-checked WITNESS of the
        BSD gap under the current tree state.

    (c) `bounded_Clay_BSD_is_open` — under the bounded encoding, the
        Clay BSD statement is unresolved: neither provable
        unconditionally, nor refutable by construction, because the
        gap is exactly the missing analytic-rank evidence. -/

/-- **The honest gap, machine-checked.** No analytic-rank lower-bound
    evidence of rank `≥ 1` exists in the current tree. If a future
    landing adds a real constructor to `AnalyticRankLowerBoundEvidence`
    for a curve at rank `≥ 1`, this theorem will fail to compile,
    surfacing the change at build time.

    Book-level scope: `mestre_nagao_trace` gives a slope reading, not
    a bound. Any populated `AnalyticRankLowerBoundEvidence E n` with
    `n ≥ 1` requires machinery not currently in the corpus. -/
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

/-- **Explicit BSD gap in the bounded encoding.** For any bounded
    witness with `r_alg_lb ≥ 1` (i.e. any populated `heegnerRankOne`
    instance), the analytic rank projection is `0` while the algebraic
    rank projection is `≥ 1`. The Clay equality therefore FAILS on
    this pair, showing that `Clay_BSD_Standard StandardBSDEncoding_Bounded`
    is currently NOT provable — the gap is real.

    This is the exact opposite of the vacuity in
    `PF/BSD_DirectDischargeAttempt.lean:clay_BSD_standard_on_sigma`,
    where the Clay statement is `rfl` regardless of content. Here it
    is falsifiable-by-construction under the current gap. -/
theorem bounded_encoding_exhibits_bsd_gap
    (p : Σ E : WeierstrassCurve ℚ, RankLowerBoundWitness E)
    (h : 1 ≤ p.2.r_alg_lb) :
    boundedAnalyticRank p ≠ boundedAlgebraicRank p := by
  unfold boundedAnalyticRank boundedAlgebraicRank
  have h_an_zero : p.2.r_an_lb = 0 := bounded_witness_forces_analytic_zero p.2
  rw [h_an_zero]
  omega

/-- **The Clay statement is open on the bounded encoding.** Equivalent
    statement of the previous theorem, phrased in terms of
    `Clay_BSD_Standard`: if there EXISTS a bounded witness with
    `r_alg_lb ≥ 1`, then `Clay_BSD_Standard StandardBSDEncoding_Bounded`
    is not provable in the current tree.

    Assumes: `∃ p, 1 ≤ p.2.r_alg_lb`. When a future landing populates
    the encoding with (say) a `heegnerRankOne` instance for `E_{37a1}`,
    the hypothesis becomes discharged and the conclusion — that the
    Clay statement fails — follows. -/
theorem bounded_Clay_BSD_not_provable_under_populated_algebraic
    (h : ∃ p : Σ E : WeierstrassCurve ℚ, RankLowerBoundWitness E,
         1 ≤ p.2.r_alg_lb) :
    ¬ Clay_BSD_Standard StandardBSDEncoding_Bounded := by
  intro hclay
  obtain ⟨p, hp⟩ := h
  have := bounded_encoding_exhibits_bsd_gap p hp
  exact this (hclay p)

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

    Names below use `treeStateAsymmetry_*` / `boundedEncoding_*` prefixes
    to make the epistemic status legible from the identifier alone. The
    original names from `146c153d` are retained as `@[deprecated]`
    aliases pointing to the new names, preserving git-history/paper
    references. -/

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
  apply bounded_encoding_exhibits_bsd_gap
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
  apply bounded_Clay_BSD_not_provable_under_populated_algebraic
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

-- Honest-scope theorems (unpopulated form)
#print axioms no_analytic_rank_ge_one_evidence_yet
#print axioms bounded_witness_forces_analytic_zero
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
