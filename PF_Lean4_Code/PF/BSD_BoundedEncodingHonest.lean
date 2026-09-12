/-
# BSD Bounded Encoding — Honest Two-Rank-Witness Presentation

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

/-! ## Section 5 — E_{37.a1} population (2026-09-12)

    Concrete population of the bounded encoding on `E_{37.a1}` (the
    famous rank-1 curve `y² + y = x³ − x`, LMFDB 37.a1), reusing the
    existing kernel-verified Heegner-cascade infrastructure in
    `PF/BSD_HeegnerRank1Proof.lean`.

    The algebraic-side evidence is `heegnerRankOne E_rank_one h`, where
    `h : RankWitnessTyped E_rank_one 1` is discharged axiom-free via
    `heegnerDerived_rankWitnessTyped_E37a1` — an explicit non-zero
    rational (the y-coordinate `−1` of the duplicate of the (0,0)
    generator, verified on the curve axiom-free by `norm_num`).

    The analytic-side evidence is `AnalyticRankLowerBoundEvidence.trivial`
    at `r_an_lb = 0` — the honest current-state answer: no kernel-verified
    analytic-rank witness ≥ 1 exists in the tree. When a future landing
    supplies real analytic-rank machinery, a new constructor can be added
    to `AnalyticRankLowerBoundEvidence` and the witness below upgraded
    to reflect the new bound; until then, the population honestly
    exhibits `r_an_lb = 0 ≠ 1 = r_alg_lb`. -/

/-- **Populated E_{37.a1} witness.** Algebraic-rank lower bound `1`,
    discharged axiom-free via the Heegner-derived non-torsion witness.
    Analytic-rank lower bound `0`, matching the honest current absence
    of kernel-verified analytic-rank machinery. -/
noncomputable def witness_E37a1 : RankLowerBoundWitness E_rank_one where
  r_alg_lb := 1
  r_an_lb  := 0
  alg_evidence := AlgebraicRankLowerBoundEvidence.heegnerRankOne
    E_rank_one heegnerDerived_rankWitnessTyped_E37a1
  an_evidence := AnalyticRankLowerBoundEvidence.trivial E_rank_one

/-- **The populated Σ-pair on `E_{37.a1}`.** Concrete inhabitant of
    `Σ E, RankLowerBoundWitness E` with `r_alg_lb = 1` and `r_an_lb = 0`,
    exhibiting the BSD gap on this specific curve as a Lean object. -/
noncomputable def sigmaWitness_E37a1 :
    Σ E : WeierstrassCurve ℚ, RankLowerBoundWitness E :=
  ⟨E_rank_one, witness_E37a1⟩

/-- **Bounded-encoding BSD gap on E_{37.a1}, UNCONDITIONAL.** For the
    populated Σ-pair `⟨E_{37.a1}, witness_E37a1⟩`, the analytic-rank
    projection is `0` and the algebraic-rank projection is `1`, so the
    Clay equality fails on this pair.

    This is the axiomatic-free discharge of the existential hypothesis
    in `bounded_Clay_BSD_not_provable_under_populated_algebraic`. -/
theorem bounded_encoding_gap_at_E37a1 :
    boundedAnalyticRank sigmaWitness_E37a1
      ≠ boundedAlgebraicRank sigmaWitness_E37a1 := by
  apply bounded_encoding_exhibits_bsd_gap
  -- Goal: 1 ≤ sigmaWitness_E37a1.2.r_alg_lb, which is 1 ≤ 1.
  exact Nat.le_refl 1

/-- **UNCONDITIONAL: `Clay_BSD_Standard` fails on the bounded encoding.**
    Discharges the existential hypothesis of
    `bounded_Clay_BSD_not_provable_under_populated_algebraic` using the
    populated `witness_E37a1`. Concludes that the Clay BSD statement on
    `StandardBSDEncoding_Bounded` is NOT true — because the encoding
    includes a curve (E_{37.a1}) whose algebraic-rank lower bound (1,
    Heegner-derived) exceeds its analytic-rank lower bound (0, the
    honest current tree state).

    This is NOT a refutation of BSD — BSD says `analytic_rank =
    algebraic_rank`, and both are 1 on E_{37.a1}. The failure here
    reflects the LEAN TREE's asymmetric state: real algebraic-rank
    witnesses (via Heegner cascade) exist, real analytic-rank witnesses
    do not. When the tree gains analytic-rank machinery, this theorem
    will become false and the bounded-encoding population will yield
    a witness of the true BSD equality on E_{37.a1} instead. -/
theorem bounded_Clay_BSD_fails_unconditionally :
    ¬ Clay_BSD_Standard StandardBSDEncoding_Bounded := by
  apply bounded_Clay_BSD_not_provable_under_populated_algebraic
  exact ⟨sigmaWitness_E37a1, Nat.le_refl 1⟩

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

-- E_{37.a1} population (2026-09-12)
#print axioms witness_E37a1
#print axioms sigmaWitness_E37a1
#print axioms bounded_encoding_gap_at_E37a1
#print axioms bounded_Clay_BSD_fails_unconditionally

end AxiomAudit

end PrincipiaTractalis.BSD.BoundedEncoding
