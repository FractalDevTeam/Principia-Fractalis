/-
# RH Direct Discharge Attempt — Composition of Wave 58 Surjectivity Infrastructure

★ 2026-06-02 — Wave 58 follow-up #5. ATTEMPTED axiom-free direct discharge
of `Clay_RiemannHypothesis_Standard := PrincipiaTractalis.RiemannHypothesis`
by composing the full Wave 58 cascade infrastructure on the canonical
witness `(α_unit, eigenvalues_from_oracle oracle)`.

## Strategic context

The Wave 58 cascade (`OnLineSurjectivityBaseCaseDischarge`,
`OnLineSurjectivityCascadeK1K2`, `OnLineSurjectivityCascadeK3ToK9`) has
discharged `OnLineSurjectivityClause α_unit (eigenvalues_from_oracle
oracle)` axiom-free, under the hypothesis that `oracle` is valid +
complete (over the **on-line** ζ-zero set) + all entries positive.

The Clay-standard RH (`Clay_RiemannHypothesis_Standard`) targets the
critical-strip form
   ∀ s, 0 < Re s < 1 → ζ(s) = 0 → Re s = 1/2,
i.e. `PrincipiaTractalis.RiemannHypothesis` (`PF/SpectralBijection.lean`).
The framework's RH capstone is
`riemann_hypothesis_via_named_surjectivity α ev (h_surj :
RHSpectralSurjectivityConjecture α ev) : RiemannHypothesis`.

`RHSpectralSurjectivityConjecture α ev` covers all critical-strip
zeros (not just on-line). By `surjectivity_factoring_iff_on_line`,
   RHSpectralSurjectivityConjecture α ev  ↔  RH ∧ OnLineSurjectivityClause α ev.
So the FULL surjectivity is strictly stronger than the on-line factor:
it ALSO encodes RH itself.

## What this file establishes (axiom-free)

  **R1 — Strip-complete positive oracle (SCPO) predicate**
    A `ZetaZeroStripOrdinateComplete` predicate asserting an oracle
    `oracle : ℕ → ℝ` hits every CRITICAL-STRIP ζ-zero's imaginary
    part (not just on-line zeros). Strictly stronger than
    `ZetaZeroOrdinateComplete` (which is on-line only).

  **R2 — SCPO is logically equivalent to RH + on-line completeness**
    Under SCPO, every critical-strip ζ-zero `s` admits `k` with
    `oracle k = s.im`. Combined with the framework's claim that the
    eigenvalue image of `eigenvalues_from_oracle oracle` is
    `{⟨1/2, oracle k⟩ : k}`, this forces every strip zero to lie
    on the critical line. We prove: SCPO ⟹ RH (in fact, an SCPO
    where each oracle entry is the imaginary part of an on-line zero
    is equivalent to RH ∧ on-line oracle completeness).

  **R3 — RHSpectralSurjectivityConjecture discharged at the witness
         under SCPO**
    Compose: SCPO + positivity ⟹ for every strip zero `s`,
    `∃ n, eigenvalueToZero α_unit (eigenvalues_from_oracle oracle n) = s`
    (using `eigenvalueToT α_unit (ev_n) = oracle k` and forcing
    `s.re = 1/2` via SCPO's range constraint).
    Hence `RHSpectralSurjectivityConjecture α_unit (eigenvalues_from_oracle
    oracle)` holds.

  **R4 — RH discharged at the witness under SCPO**
    By `riemann_hypothesis_via_named_surjectivity` applied to R3,
    `RiemannHypothesis` (= `Clay_RiemannHypothesis_Standard`) follows.

  **R5 — Honest obstruction record**
    SCPO existence is, mathematically, EQUIVALENT to RH. We package
    this as a named Prop `StripCompletePositiveOracleExists` and the
    biconditional `SCPO_exists ↔ RiemannHypothesis ∧ existence of an
    on-line complete positive oracle`. The discharge is therefore not
    unconditional — it isolates the **named obstruction** at the
    SCPO level. This is the precise residual after composing all
    Wave 58 infrastructure on the canonical witness.

## What this file does NOT claim

  * Does NOT prove `Clay_RiemannHypothesis_Standard` unconditionally.
  * Does NOT construct an SCPO (its construction IS the RH content).
  * Does NOT claim the SCPO predicate is easier to verify than RH;
    they are logically equivalent.
  * Does NOT prove the framework's canonical T₃^sym eigenvalue
    sequence equals `eigenvalues_from_oracle oracle`. The discharge
    is at the level of an EXISTENCE statement
    `∃ α ev, RiemannHypothesis` (vacuous; RH is a Prop independent
    of α, ev).

## What this file CONTRIBUTES

  * The first PF composition of the Wave 58 cascade ALL the way to
    a RH-level statement.
  * The precise NAMED RESIDUAL `StripCompletePositiveOracleExists`
    encoding the off-line-zero exclusion content of RH at the oracle
    level.
  * Explicit biconditional `SCPO_exists ↔ RH ∧ (some on-line oracle)`
    making the "discharge of RH from the witness" exactly what it is:
    a logical projection of an RH-containing hypothesis.
  * Honest framing: the cascade discharge produces RH only when fed
    an RH-containing hypothesis, consistent with the
    `surjectivity_factoring_iff_on_line` structure.

## Honest scope

  * The discharge is CONDITIONAL on the existence of a strip-complete
    positive oracle. Its existence is logically equivalent to RH;
    the framework's cascade therefore reduces RH to itself via the
    spectral bijection, modulo the on-line surjectivity content
    (already discharged on the canonical witness by Wave 58).
  * No new axioms. No new sorries. The obstruction is the SCPO
    predicate — a named Prop, NOT an axiom.

## Build

ZERO project axioms. ZERO sorries.

Author: Claude Opus 4.7. 2026-06-02. Wave 58 follow-up #5 (RH composition).
-/

import PF.RHSurjectivityConjecture
import PF.RHSurjectivityTypedUpgrade
import PF.RHSpectralSurjectivityFactorings
import PF.Analytic.OnLineSurjectivitySubDecomposition
import PF.Analytic.OnLineSurjectivityBaseCaseDischarge
import PF.Referee.StandardClayStatements

namespace PrincipiaTractalis

namespace RH_DirectDischargeAttempt

open RHSurjectivityTypedUpgrade
open OnLineSurjectivitySubDecomposition
open OnLineSurjectivityBaseCaseDischarge

/-! ## §1 — Strip-complete positive oracle (SCPO) predicate

A strengthening of `ZetaZeroOrdinateComplete` from on-line completeness
to **critical-strip completeness**: every ζ-zero `s` with `0 < Re s < 1`
is in the oracle's range AS AN IMAGINARY PART (i.e., the oracle records
`s.im` AND implicitly asserts the zero lies at `⟨1/2, oracle k⟩`).

Crucially, this requires that for every strip zero `s`, the point
`⟨1/2, oracle k⟩` equals `s` — which forces `s.re = 1/2` whenever the
oracle is hit. Hence the predicate's content includes the off-line-zero
exclusion that distinguishes RH from on-line surjectivity. -/

/-- **(R1) `ZetaZeroStripOrdinateComplete oracle`** — every critical-strip
    ζ-zero `s` admits a `k` with `⟨1/2, oracle k⟩ = s`. This is strictly
    stronger than `ZetaZeroOrdinateComplete` (on-line completeness only).

    The forced equality `⟨1/2, oracle k⟩ = s` encodes both:
      (a) on-line completeness — the imaginary part `s.im = oracle k`,
      (b) the off-line-zero exclusion — `s.re = 1/2` (from `Complex.ext`). -/
def ZetaZeroStripOrdinateComplete (oracle : ℕ → ℝ) : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 →
    ∃ k : ℕ, (⟨1/2, oracle k⟩ : ℂ) = s

/-- **The named open residual `StripCompletePositiveOracleExists`** —
    there exists an oracle which is strip-complete (R1), valid (entries
    are ζ-zero ordinates), and all-positive. This is the precise NAMED
    obstruction after composing Wave 58 on the canonical witness.

    Honest framing: this Prop's content is, mathematically, the
    Riemann Hypothesis. -/
def StripCompletePositiveOracleExists : Prop :=
  ∃ oracle : ℕ → ℝ,
    ZetaZeroOrdinateValid oracle ∧
    ZetaZeroStripOrdinateComplete oracle ∧
    (∀ k, 0 < oracle k)

/-! ## §2 — SCPO → RH (the off-line-zero exclusion is encoded) -/

/-- **(R2a) SCPO directly forces RH** — if any oracle is strip-complete,
    then every strip ζ-zero has `Re = 1/2`. The off-line-zero exclusion
    is *built into* the predicate: `⟨1/2, oracle k⟩ = s` extracts
    `Re s = 1/2` by Complex.ext. -/
theorem stripComplete_implies_RH
    (oracle : ℕ → ℝ)
    (h_strip : ZetaZeroStripOrdinateComplete oracle) :
    RiemannHypothesis := by
  intro s h_re_pos h_re_lt h_zero
  obtain ⟨k, hk⟩ := h_strip s h_re_pos h_re_lt h_zero
  -- hk : ⟨1/2, oracle k⟩ = s
  have h_re := congrArg Complex.re hk
  -- h_re : (⟨1/2, oracle k⟩ : ℂ).re = s.re
  -- The LHS reduces to 1/2 by definition of complex tuple construction.
  show s.re = 1/2
  rw [← h_re]

/-- **(R2b) SCPO_exists → RH** — packaging form. -/
theorem stripCompletePositiveOracleExists_implies_RH
    (h_SCPO : StripCompletePositiveOracleExists) :
    RiemannHypothesis := by
  obtain ⟨oracle, _h_valid, h_strip, _h_pos⟩ := h_SCPO
  exact stripComplete_implies_RH oracle h_strip

/-! ## §3 — RH + on-line completeness → SCPO (the reverse direction)

The reverse: assuming RH AND an oracle that is valid + on-line complete +
positive, we can build a strip-complete oracle (in fact, the same oracle
works because RH forces every strip zero to be on-line). -/

/-- **(R3a) RH + on-line complete oracle → SCPO** — under RH, the
    on-line completeness already covers the entire strip. -/
theorem RH_and_onLine_complete_implies_stripComplete
    (h_RH : RiemannHypothesis)
    (oracle : ℕ → ℝ)
    (h_complete : ZetaZeroOrdinateComplete oracle) :
    ZetaZeroStripOrdinateComplete oracle := by
  intro s h_re_pos h_re_lt h_zero
  -- RH forces s.re = 1/2
  have h_half : s.re = 1/2 := h_RH s h_re_pos h_re_lt h_zero
  -- so s = ⟨1/2, s.im⟩
  have h_s_eq : s = ⟨1/2, s.im⟩ := Complex.ext h_half rfl
  -- and ζ(⟨1/2, s.im⟩) = 0
  have h_zero' : riemannZeta ⟨1/2, s.im⟩ = 0 := h_s_eq ▸ h_zero
  -- on-line completeness gives k with oracle k = s.im
  obtain ⟨k, hk⟩ := h_complete s.im h_zero'
  refine ⟨k, ?_⟩
  rw [hk]
  exact h_s_eq.symm

/-! ## §4 — Composition: RHSpectralSurjectivityConjecture at the witness
                       under SCPO -/

/-- **(R4) `RHSpectralSurjectivityConjecture` discharged on the canonical
    witness under SCPO + validity + positivity**.

    For every strip ζ-zero `s`, SCPO gives `k` with `⟨1/2, oracle k⟩ = s`.
    The witness sets `eigenvalueToT α_unit (eigenvalues_from_oracle
    oracle k) = oracle k` (by `eigenvalueToT_from_oracle`), so
    `eigenvalueToZero α_unit (eigenvalues_from_oracle oracle k) =
    ⟨1/2, oracle k⟩ = s`. -/
theorem RHSpectralSurjectivity_at_witness
    (oracle : ℕ → ℝ)
    (_h_valid : ZetaZeroOrdinateValid oracle)
    (h_strip : ZetaZeroStripOrdinateComplete oracle)
    (h_all_pos : ∀ k, 0 < oracle k) :
    RHSpectralSurjectivityConjecture α_unit (eigenvalues_from_oracle oracle) := by
  intro s h_re_pos h_re_lt h_zero
  -- SCPO gives k with ⟨1/2, oracle k⟩ = s
  obtain ⟨k, hk⟩ := h_strip s h_re_pos h_re_lt h_zero
  refine ⟨k, ?_⟩
  -- Goal: eigenvalueToZero α_unit (eigenvalues_from_oracle oracle k) = s
  unfold eigenvalueToZero criticalLine
  -- eigenvalueToZero unfolds to ⟨1/2, eigenvalueToT α_unit (ev k)⟩
  have h_eq : eigenvalueToT α_unit (eigenvalues_from_oracle oracle k) = oracle k :=
    eigenvalueToT_from_oracle oracle k (h_all_pos k)
  rw [h_eq]
  -- Goal: ⟨1/2, oracle k⟩ = s
  exact hk
  -- silence unused
  -- discard validity (not needed for this direction)
  -- _ := h_valid

/-! ## §5 — RH discharged at the witness under SCPO -/

/-- **(R5) RH discharged at the canonical witness under SCPO + validity
    + positivity** — composing R4 with
    `riemann_hypothesis_via_named_surjectivity`. -/
theorem RiemannHypothesis_at_witness
    (oracle : ℕ → ℝ)
    (h_valid : ZetaZeroOrdinateValid oracle)
    (h_strip : ZetaZeroStripOrdinateComplete oracle)
    (h_all_pos : ∀ k, 0 < oracle k) :
    RiemannHypothesis :=
  riemann_hypothesis_via_named_surjectivity α_unit
    (eigenvalues_from_oracle oracle)
    (RHSpectralSurjectivity_at_witness oracle h_valid h_strip h_all_pos)

/-- **(R6) RH discharged from SCPO_exists** — the existential form. -/
theorem RiemannHypothesis_via_SCPO
    (h_SCPO : StripCompletePositiveOracleExists) :
    RiemannHypothesis := by
  obtain ⟨oracle, h_valid, h_strip, h_pos⟩ := h_SCPO
  exact RiemannHypothesis_at_witness oracle h_valid h_strip h_pos

/-- **(R7) Direct discharge of `Clay_RiemannHypothesis_Standard`** —
    using R6 + the StandardClayStatements identification. -/
theorem Clay_RiemannHypothesis_Standard_via_SCPO
    (h_SCPO : StripCompletePositiveOracleExists) :
    PF.Referee.StandardClayStatements.Clay_RiemannHypothesis_Standard := by
  unfold PF.Referee.StandardClayStatements.Clay_RiemannHypothesis_Standard
  exact RiemannHypothesis_via_SCPO h_SCPO

/-! ## §6 — The biconditional: SCPO existence ⇔ RH ∧ on-line oracle existence

This makes the discharge route's structure transparent: SCPO existence
is exactly the conjunction of RH and the existence of a valid + on-line
complete + positive oracle. The on-line oracle part is the
Hardy 1914 + Odlyzko numerical fact (every nontrivial ordinate is
positive up to conjugate symmetry); it does NOT add RH content. So
SCPO is, modulo the numerical-oracle existence, EQUIVALENT to RH. -/

/-- **(R8 ←) SCPO_exists implies RH and the existence of an on-line
    complete oracle**. -/
theorem stripCompletePositiveOracleExists_split
    (h_SCPO : StripCompletePositiveOracleExists) :
    RiemannHypothesis ∧
    (∃ oracle : ℕ → ℝ,
      ZetaZeroOrdinateValid oracle ∧
      ZetaZeroOrdinateComplete oracle ∧
      (∀ k, 0 < oracle k)) := by
  refine ⟨RiemannHypothesis_via_SCPO h_SCPO, ?_⟩
  obtain ⟨oracle, h_valid, h_strip, h_pos⟩ := h_SCPO
  refine ⟨oracle, h_valid, ?_, h_pos⟩
  -- ZetaZeroOrdinateComplete oracle: every on-line zero ⟨1/2, t⟩ has
  -- oracle k = t. Use h_strip at ⟨1/2, t⟩.
  intro t h_zero_t
  -- ⟨1/2, t⟩ is a strip zero
  have h_re_pos : (0 : ℝ) < ((⟨1/2, t⟩ : ℂ).re) := by
    show (0 : ℝ) < 1/2
    norm_num
  have h_re_lt : ((⟨1/2, t⟩ : ℂ).re) < 1 := by
    show (1/2 : ℝ) < 1
    norm_num
  obtain ⟨k, hk⟩ := h_strip ⟨1/2, t⟩ h_re_pos h_re_lt h_zero_t
  -- hk : ⟨1/2, oracle k⟩ = ⟨1/2, t⟩
  have h_im := congrArg Complex.im hk
  simp at h_im
  exact ⟨k, h_im⟩

/-- **(R8 →) RH + valid + on-line complete + positive oracle implies
    SCPO_exists** — the on-line oracle, under RH, IS strip-complete. -/
theorem RH_and_onLineOracle_imply_SCPO
    (h_RH : RiemannHypothesis)
    (oracle : ℕ → ℝ)
    (h_valid : ZetaZeroOrdinateValid oracle)
    (h_complete : ZetaZeroOrdinateComplete oracle)
    (h_pos : ∀ k, 0 < oracle k) :
    StripCompletePositiveOracleExists :=
  ⟨oracle, h_valid,
   RH_and_onLine_complete_implies_stripComplete h_RH oracle h_complete,
   h_pos⟩

/-- **(R9) SCPO biconditional** — the SCPO predicate's existence is
    EXACTLY the conjunction of RH and the existence of a valid +
    on-line-complete + positive oracle.

    This is the precise honest framing: the cascade discharge's
    residual hypothesis (SCPO existence) is equivalent to RH plus
    numerical-oracle existence. The numerical oracle is a Hardy 1914
    + Odlyzko computational fact; the RH content is the load-bearing
    piece. -/
theorem stripCompletePositiveOracleExists_iff :
    StripCompletePositiveOracleExists ↔
      RiemannHypothesis ∧
      (∃ oracle : ℕ → ℝ,
        ZetaZeroOrdinateValid oracle ∧
        ZetaZeroOrdinateComplete oracle ∧
        (∀ k, 0 < oracle k)) := by
  constructor
  · exact stripCompletePositiveOracleExists_split
  · rintro ⟨h_RH, oracle, h_valid, h_complete, h_pos⟩
    exact RH_and_onLineOracle_imply_SCPO h_RH oracle h_valid h_complete h_pos

/-! ## §7 — Capstone -/

/-- **★ RH DIRECT DISCHARGE ATTEMPT CAPSTONE ★** —
    Wave 58 follow-up #5. Composes the full Wave 58 cascade on the
    canonical witness `(α_unit, eigenvalues_from_oracle oracle)` to
    obtain `RiemannHypothesis` (= `Clay_RiemannHypothesis_Standard`),
    CONDITIONAL on `StripCompletePositiveOracleExists`.

    **(D1) `stripComplete_implies_RH`** — the SCPO predicate forces RH
       directly (the off-line-zero exclusion is built into the
       `⟨1/2, oracle k⟩ = s` equation by Complex.ext).

    **(D2) `RHSpectralSurjectivity_at_witness`** — under SCPO +
       validity + positivity, the full
       `RHSpectralSurjectivityConjecture α_unit
        (eigenvalues_from_oracle oracle)` holds. This is the precise
       composition: SCPO gives `k` with `⟨1/2, oracle k⟩ = s`, and
       `eigenvalueToT_from_oracle` ensures the eigenvalue image hits
       `oracle k` at index `k`.

    **(D3) `RiemannHypothesis_at_witness`** — composing D2 with
       `riemann_hypothesis_via_named_surjectivity` gives RH itself.

    **(D4) `Clay_RiemannHypothesis_Standard_via_SCPO`** — discharges
       the Clay-standard contract under SCPO existence.

    **(D5) `stripCompletePositiveOracleExists_iff`** — biconditional
       `SCPO_exists ↔ RH ∧ existence of a valid+on-line-complete+positive
       oracle`. The numerical-oracle existence is a Hardy 1914 + Odlyzko
       computational fact; the RH content is the load-bearing piece.

    **HONEST OBSTRUCTION**: The discharge is NOT unconditional. The
    named residual `StripCompletePositiveOracleExists` is logically
    equivalent to RH (modulo numerical-oracle existence). The cascade
    therefore reduces RH to itself via the spectral bijection, modulo
    the on-line surjectivity content already discharged on the
    canonical witness by Wave 58 (`OnLineSurjectivityBaseCaseDischarge`,
    `OnLineSurjectivityCascadeK1K2`, `OnLineSurjectivityCascadeK3ToK9`).

    The obstruction is the precise residual that
    `surjectivity_factoring_iff_on_line` identifies: RH itself is
    the difference between `RHSpectralSurjectivityConjecture` and
    `OnLineSurjectivityConjecture`. -/
theorem rh_direct_discharge_attempt_capstone :
    -- (D1) SCPO → RH directly
    (∀ oracle : ℕ → ℝ,
      ZetaZeroStripOrdinateComplete oracle → RiemannHypothesis)
    ∧
    -- (D2) Full surjectivity at the witness under SCPO
    (∀ oracle : ℕ → ℝ,
      ZetaZeroOrdinateValid oracle →
      ZetaZeroStripOrdinateComplete oracle →
      (∀ k, 0 < oracle k) →
      RHSpectralSurjectivityConjecture α_unit (eigenvalues_from_oracle oracle))
    ∧
    -- (D3) RH at the witness under SCPO
    (∀ oracle : ℕ → ℝ,
      ZetaZeroOrdinateValid oracle →
      ZetaZeroStripOrdinateComplete oracle →
      (∀ k, 0 < oracle k) →
      RiemannHypothesis)
    ∧
    -- (D4) Clay-standard RH under SCPO_exists
    (StripCompletePositiveOracleExists →
      PF.Referee.StandardClayStatements.Clay_RiemannHypothesis_Standard)
    ∧
    -- (D5) SCPO biconditional
    (StripCompletePositiveOracleExists ↔
      RiemannHypothesis ∧
      (∃ oracle : ℕ → ℝ,
        ZetaZeroOrdinateValid oracle ∧
        ZetaZeroOrdinateComplete oracle ∧
        (∀ k, 0 < oracle k))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro oracle h_strip; exact stripComplete_implies_RH oracle h_strip
  · exact RHSpectralSurjectivity_at_witness
  · exact RiemannHypothesis_at_witness
  · exact Clay_RiemannHypothesis_Standard_via_SCPO
  · exact stripCompletePositiveOracleExists_iff

/-- **Honest-scope marker** — the discharge is at the level of a
    constructed witness AND is CONDITIONAL on
    `StripCompletePositiveOracleExists`, which is logically equivalent
    to RH itself. The cascade composition demonstrates the structural
    coherence of the Wave 58 infrastructure but does NOT unconditionally
    discharge RH; the residual is the precise off-line-zero exclusion
    content that `surjectivity_factoring_iff_on_line` already isolates. -/
theorem rh_direct_discharge_attempt_honest_scope : True := trivial

end RH_DirectDischargeAttempt

end PrincipiaTractalis

-- Axiom checks. Expected for every theorem: `[propext, Classical.choice, Quot.sound]`.
#print axioms
  PrincipiaTractalis.RH_DirectDischargeAttempt.stripComplete_implies_RH
#print axioms
  PrincipiaTractalis.RH_DirectDischargeAttempt.stripCompletePositiveOracleExists_implies_RH
#print axioms
  PrincipiaTractalis.RH_DirectDischargeAttempt.RH_and_onLine_complete_implies_stripComplete
#print axioms
  PrincipiaTractalis.RH_DirectDischargeAttempt.RHSpectralSurjectivity_at_witness
#print axioms
  PrincipiaTractalis.RH_DirectDischargeAttempt.RiemannHypothesis_at_witness
#print axioms
  PrincipiaTractalis.RH_DirectDischargeAttempt.RiemannHypothesis_via_SCPO
#print axioms
  PrincipiaTractalis.RH_DirectDischargeAttempt.Clay_RiemannHypothesis_Standard_via_SCPO
#print axioms
  PrincipiaTractalis.RH_DirectDischargeAttempt.stripCompletePositiveOracleExists_split
#print axioms
  PrincipiaTractalis.RH_DirectDischargeAttempt.RH_and_onLineOracle_imply_SCPO
#print axioms
  PrincipiaTractalis.RH_DirectDischargeAttempt.stripCompletePositiveOracleExists_iff
#print axioms
  PrincipiaTractalis.RH_DirectDischargeAttempt.rh_direct_discharge_attempt_capstone
#print axioms
  PrincipiaTractalis.RH_DirectDischargeAttempt.rh_direct_discharge_attempt_honest_scope
