/-
# Conjugate Symmetry Refutes The Positive-Complete Oracle Props (2026-10-06)

Eight `Prop` definitions across five files in this corpus assert the existence of
an **all-positive** oracle that enumerates **every** ζ-zero ordinate. They are
not open problems. They are **false**, and both ingredients needed to refute them
have been kernel-clean in this tree since June.

## The argument, in three lines

1. `RiemannZetaZeroBelow15_r324` proves **unconditionally** that there is an
   on-line zero with `1 < t < 15`.
2. `XiRealWitness.riemannZeta_conj` gives `ζ(conj s) = conj(ζ s)`, so
   `ζ(1/2 − i t) = 0` as well.
3. A positive oracle cannot enumerate a zero of negative ordinate.

That is the whole proof. No new analysis — two existing theorems pointed at each
other. (`XiOnLineZero`'s `positiveOnLineZetaZeroOrdinatesNonempty` would also
suffice and is the strictly weaker input; r324 is used here because its `∃ t,
1 < t ∧ t < 15 ∧ …` form needs no set-membership unfolding.)

## Why it was not already done

Two files diagnosed this correctly in prose in June 2026 —
`OnLineSurjectivitySubDecomposition` ("structurally uninhabitable") and
`HilbertPolyaIdentificationBulletproof` ("ζ has conjugate symmetry … a positive
oracle cannot hit the negative-`t` member of each pair"). The response was to
**add** repaired `_Positive` variants while leaving the eight false originals
standing, unmarked, with their published-conjecture docstrings intact.

`V3SubstrateForcedDischargeBulletproof` states the reason: *"Lean can't refute
it because mathlib lacks usable ζ-conjugate-symmetry."* **That stopped being
true of this tree when `riemannZeta_conj` was proved here.** The refutation has
been available and unexecuted; this module executes it.

## What this changes

**Retires as vacuous, not conditional** — eight Props, and with them every
implication fronted by one, including `full_SCPO_implies_Clay_RH`.
`refuted_prop_implies_anything` makes the point sharply: from a false antecedent
everything follows, so such a theorem carries no information about RH.

**Nothing true becomes false.** No theorem in the corpus *proves* any of the
eight; every occurrence is a hypothesis or one side of a biconditional between
two false Props. So this is the removal of a vacuity, not the withdrawal of a
result — but it should be stated in the kernel rather than discovered by a
referee. One docstring is actively misleading and is flagged below.

**Does not touch** the honest parts of the RH arc: the certified-quadrature sign
changes, `riemannXiEntire` and its zero-correspondence, the rectangle argument
principle, the functional-equation halving, or `NoOffLineZeroInRightHalf` —
which remains the corpus's one genuinely non-circular open target.

**And the repair already exists.** `ZetaZeroOrdinateCompletePositive` restricts
completeness to `t > 0`; its own docstring calls it "the
conjugate-symmetry-compatible form". §4 confirms the refuting witness lies
outside that predicate's domain, so the four `_Positive` variants are untouched
here. The fix was written in June; only the theorem saying the unrestricted form
is false was missing.

## The actively false docstring, for separate repair

`RH_ClayLiteralClosureAttempt`, on `OnLineOrdinateOracleExists`, claims it is
*"known unconditionally in published mathematics"* via "Hardy 1914 + Odlyzko
enumeration". Hardy and Odlyzko enumerate **upper-half-plane** ordinates; the
Prop as written demands a positive oracle hit **every** on-line zero, negative
ones included. That sentence is false and is the one a referee would quote. It
is prose, so it is not corrected by this module — flagged for a text pass.

## Scope

**Formalized**: conjugate closure of on-line zeros; a strip zero of strictly
negative ordinate; strip-completeness implies on-line completeness; the core
incompatibility of unrestricted completeness with positivity; the eight
refutations; the no-information consequence; the domain separation protecting the
positive variants; and the unconditional truth of the partial Berry–Keating form.

**Not claimed**: anything about RH. Refuting a false hypothesis neither proves
nor disproves the Riemann Hypothesis, and this module makes no progress on it.
The ordinate is not computed, only bracketed by the imported r324.

Author: Pablo Cohen + Claude Opus 5. 2026-10-06.
-/
import PF.Analytic.RH_DirectDischargeAttempt
import PF.Analytic.RiemannZetaZeroBelow15_r324
import PF.Analytic.XiRealWitness
import PF.Analytic.OnLineSurjectivitySubDecomposition
import PF.Analytic.HilbertPolyaIdentificationPrecise
import PF.Analytic.RHProofAttemptMayerT3SymExplicit
import PF.Analytic.RH_ClayLiteralClosureAttempt
import PF.Analytic.Mayer1991TransferOperatorFormalization
import Mathlib.Tactic

namespace PrincipiaTractalis.PositiveCompleteOracleRefutation

open PrincipiaTractalis.RH_DirectDischargeAttempt
open PrincipiaTractalis.OnLineSurjectivitySubDecomposition
open PrincipiaTractalis.RiemannZetaZeroBelow15
open PrincipiaTractalis.XiRealWitness

/-! ## §1 — Conjugate closure of on-line zeros -/

/-- **The conjugate of an on-line ζ-zero is an on-line ζ-zero.**

    From this corpus's own `riemannZeta_conj`, since
    `conj ⟨1/2, t⟩ = ⟨1/2, -t⟩`. -/
theorem zeta_zero_conj_on_line (t : ℝ) (h : riemannZeta (⟨1 / 2, t⟩ : ℂ) = 0) :
    riemannZeta (⟨1 / 2, -t⟩ : ℂ) = 0 := by
  have hc : ((starRingEnd ℂ) (⟨1 / 2, t⟩ : ℂ)) = (⟨1 / 2, -t⟩ : ℂ) := by
    apply Complex.ext <;> simp
  rw [← hc, riemannZeta_conj, h, map_zero]

/-- **★ There is a critical-strip ζ-zero with strictly negative ordinate. ★**

    The load-bearing fact: r324's unconditional on-line zero at `1 < t < 15`,
    reflected. No all-positive oracle can accommodate it. -/
theorem exists_strip_zero_negative_ordinate :
    ∃ s : ℂ, 0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0 ∧ s.im < 0 := by
  obtain ⟨t, ht1, _ht15, hz⟩ :=
    exists_critical_line_riemannZeta_zero_between_one_and_fifteen
  refine ⟨(⟨1 / 2, -t⟩ : ℂ), ?_, ?_, zeta_zero_conj_on_line t hz, ?_⟩
  · norm_num
  · norm_num
  · simp only []
    linarith

/-! ## §2 — The core incompatibility -/

/-- **Strip-completeness implies on-line completeness**, since an on-line zero
    is a strip zero. This lets one lemma cover both families of target Prop. -/
theorem complete_of_stripComplete {oracle : ℕ → ℝ}
    (h : ZetaZeroStripOrdinateComplete oracle) :
    ZetaZeroOrdinateComplete oracle := by
  intro t ht
  obtain ⟨k, hk⟩ := h (⟨1 / 2, t⟩ : ℂ) (by norm_num) (by norm_num) ht
  refine ⟨k, ?_⟩
  have h' := congrArg Complex.im hk
  simpa using h'

/-- **★★★ THE CORE REFUTATION ★★★**

    No oracle is simultaneously complete on on-line ζ-zeros and everywhere
    positive. Stated with exactly the two clauses that matter: validity is
    **not** needed, which is what makes this maximally reusable. -/
theorem no_positive_complete_oracle {oracle : ℕ → ℝ}
    (hcomplete : ZetaZeroOrdinateComplete oracle) (hpos : ∀ k, 0 < oracle k) :
    False := by
  obtain ⟨t, ht1, _ht15, hz⟩ :=
    exists_critical_line_riemannZeta_zero_between_one_and_fifteen
  obtain ⟨k, hk⟩ := hcomplete (-t) (zeta_zero_conj_on_line t hz)
  have hp := hpos k
  rw [hk] at hp
  linarith

/-- The strip-shaped corollary of the core lemma. -/
theorem no_positive_stripComplete_oracle {oracle : ℕ → ℝ}
    (hcomplete : ZetaZeroStripOrdinateComplete oracle)
    (hpos : ∀ k, 0 < oracle k) : False :=
  no_positive_complete_oracle (complete_of_stripComplete hcomplete) hpos

/-! ## §3 — The eight refutations -/

/-- **★ (1/8) `StripCompletePositiveOracleExists` is FALSE.** The named "open
    residual" of the RH direct-discharge route is not open. -/
theorem not_stripCompletePositiveOracleExists :
    ¬ StripCompletePositiveOracleExists := by
  rintro ⟨oracle, _hvalid, hcomplete, hpos⟩
  exact no_positive_stripComplete_oracle hcomplete hpos

/-- **★ (2/8)** `Mayer_T3Sym_CanonicalSpectrum_HitsAllZetaZeros` is FALSE. -/
theorem not_mayer_T3Sym_CanonicalSpectrum_HitsAllZetaZeros :
    ¬ PrincipiaTractalis.RHProofAttemptMayerT3SymExplicit.Mayer_T3Sym_CanonicalSpectrum_HitsAllZetaZeros := by
  rintro ⟨oracle, _hvalid, hcomplete, hpos⟩
  exact no_positive_stripComplete_oracle hcomplete hpos

/-- **★ (3/8)** `OnLineOrdinateOracleExists` is FALSE — the one whose docstring
    claims it is "known unconditionally in published mathematics". -/
theorem not_onLineOrdinateOracleExists :
    ¬ PrincipiaTractalis.RH_ClayLiteralClosureAttempt.OnLineOrdinateOracleExists := by
  rintro ⟨oracle, _hvalid, hcomplete, hpos⟩
  exact no_positive_complete_oracle hcomplete hpos

/-- **★ (4/8)** `BerryKeatingHamiltonianHypothesis` is FALSE. -/
theorem not_berryKeatingHamiltonianHypothesis :
    ¬ PrincipiaTractalis.HilbertPolyaIdentificationPrecise.BerryKeatingHamiltonianHypothesis := by
  rintro ⟨oracle, _hvalid, hcomplete, hpos⟩
  exact no_positive_complete_oracle hcomplete hpos

/-- **★ (5/8)** `ConnesTraceFormulaHypothesis` is FALSE. -/
theorem not_connesTraceFormulaHypothesis :
    ¬ PrincipiaTractalis.HilbertPolyaIdentificationPrecise.ConnesTraceFormulaHypothesis := by
  rintro ⟨oracle, _hvalid, hcomplete, hpos⟩
  exact no_positive_complete_oracle hcomplete hpos

/-- **★ (6/8)** `BostConnesKMSPhaseTransition` is FALSE. -/
theorem not_bostConnesKMSPhaseTransition :
    ¬ PrincipiaTractalis.HilbertPolyaIdentificationPrecise.BostConnesKMSPhaseTransition := by
  rintro ⟨oracle, _hvalid, hcomplete, hpos⟩
  exact no_positive_complete_oracle hcomplete hpos

/-- **★ (7/8)** `PF_T3SymIsHilbertPolyaOperator` is FALSE. This is the Prop
    several RH-axis headline theorems are fronted by. -/
theorem not_PF_T3SymIsHilbertPolyaOperator :
    ¬ PrincipiaTractalis.HilbertPolyaIdentificationPrecise.PF_T3SymIsHilbertPolyaOperator := by
  rintro ⟨oracle, _hvalid, hcomplete, hpos⟩
  exact no_positive_complete_oracle hcomplete hpos

/-- **★ (8/8)** `Mayer1991_SymmetricQuotientHasZetaSpectrum` is FALSE. -/
theorem not_mayer1991_SymmetricQuotientHasZetaSpectrum :
    ¬ PrincipiaTractalis.Mayer1991TransferOperatorFormalization.Mayer1991_SymmetricQuotientHasZetaSpectrum := by
  rintro ⟨oracle, _hvalid, hcomplete, hpos⟩
  exact no_positive_complete_oracle hcomplete hpos

/-- **★ Therefore every implication fronted by one of these carries no
    information.** A theorem of shape `SCPO → RH` is not a reduction of RH; it
    is a statement about an empty hypothesis class. -/
theorem refuted_prop_implies_anything (P : Prop)
    (h : StripCompletePositiveOracleExists) : P :=
  absurd h not_stripCompletePositiveOracleExists

/-! ## §4 — The positive variants survive, and one conditional becomes a theorem -/

/-- **The refuting witness lies outside the positive form's domain.**

    `ZetaZeroOrdinateCompletePositive` quantifies only over `t > 0`, and the
    witness has `t < 0`. So the corpus's own repaired variants are untouched by
    this argument. -/
theorem refutation_witness_is_outside_the_positive_form :
    ∃ t : ℝ, riemannZeta (⟨1 / 2, t⟩ : ℂ) = 0 ∧ t < 0 ∧ ¬ (0 < t) := by
  obtain ⟨t, ht1, _ht15, hz⟩ :=
    exists_critical_line_riemannZeta_zero_between_one_and_fifteen
  exact ⟨-t, zeta_zero_conj_on_line t hz, by linarith, by linarith⟩

/-- **★ A free upgrade: the partial Berry–Keating form is UNCONDITIONALLY TRUE. ★**

    `BerryKeatingHamiltonianHypothesis_partial N` has **no completeness clause**,
    so the constant oracle at r324's zero satisfies it outright. The corpus
    currently derives it only from the (false) SCPO, which made that derivation
    vacuous; this replaces a vacuous conditional with a theorem. -/
theorem berryKeating_partial_unconditional (N : ℕ) :
    PrincipiaTractalis.HilbertPolyaIdentificationPrecise.BerryKeatingHamiltonianHypothesis_partial N := by
  obtain ⟨t, ht1, _ht15, hz⟩ :=
    exists_critical_line_riemannZeta_zero_between_one_and_fifteen
  refine ⟨fun _ => t, ?_, ?_⟩
  · intro k _hk
    linarith
  · intro _k
    exact hz

/-! ## §5 — Capstone -/

/-- **★ Positive-complete oracle refutation — capstone ★**

    A strip zero of negative ordinate exists; completeness and positivity are
    jointly unsatisfiable; all eight Props built from that conjunction are false;
    implications fronted by them carry no information; the positive-restricted
    variants are untouched; and the partial Berry–Keating form is unconditionally
    true. -/
theorem PositiveCompleteOracleRefutation_capstone :
    (∃ s : ℂ, 0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0 ∧ s.im < 0) ∧
    (∀ oracle : ℕ → ℝ, ZetaZeroOrdinateComplete oracle →
      (∀ k, 0 < oracle k) → False) ∧
    (¬ StripCompletePositiveOracleExists) ∧
    (¬ PrincipiaTractalis.HilbertPolyaIdentificationPrecise.PF_T3SymIsHilbertPolyaOperator) ∧
    (∃ t : ℝ, riemannZeta (⟨1 / 2, t⟩ : ℂ) = 0 ∧ t < 0 ∧ ¬ (0 < t)) ∧
    (∀ N : ℕ,
      PrincipiaTractalis.HilbertPolyaIdentificationPrecise.BerryKeatingHamiltonianHypothesis_partial N) :=
  ⟨exists_strip_zero_negative_ordinate,
   fun _ hc hp => no_positive_complete_oracle hc hp,
   not_stripCompletePositiveOracleExists,
   not_PF_T3SymIsHilbertPolyaOperator,
   refutation_witness_is_outside_the_positive_form,
   berryKeating_partial_unconditional⟩

end PrincipiaTractalis.PositiveCompleteOracleRefutation

/-! ## Axiom audit — LIVE, not commented out -/

#print axioms PrincipiaTractalis.PositiveCompleteOracleRefutation.zeta_zero_conj_on_line
#print axioms PrincipiaTractalis.PositiveCompleteOracleRefutation.exists_strip_zero_negative_ordinate
#print axioms PrincipiaTractalis.PositiveCompleteOracleRefutation.complete_of_stripComplete
#print axioms PrincipiaTractalis.PositiveCompleteOracleRefutation.no_positive_complete_oracle
#print axioms PrincipiaTractalis.PositiveCompleteOracleRefutation.no_positive_stripComplete_oracle
#print axioms PrincipiaTractalis.PositiveCompleteOracleRefutation.not_stripCompletePositiveOracleExists
#print axioms PrincipiaTractalis.PositiveCompleteOracleRefutation.not_mayer_T3Sym_CanonicalSpectrum_HitsAllZetaZeros
#print axioms PrincipiaTractalis.PositiveCompleteOracleRefutation.not_onLineOrdinateOracleExists
#print axioms PrincipiaTractalis.PositiveCompleteOracleRefutation.not_berryKeatingHamiltonianHypothesis
#print axioms PrincipiaTractalis.PositiveCompleteOracleRefutation.not_connesTraceFormulaHypothesis
#print axioms PrincipiaTractalis.PositiveCompleteOracleRefutation.not_bostConnesKMSPhaseTransition
#print axioms PrincipiaTractalis.PositiveCompleteOracleRefutation.not_PF_T3SymIsHilbertPolyaOperator
#print axioms PrincipiaTractalis.PositiveCompleteOracleRefutation.not_mayer1991_SymmetricQuotientHasZetaSpectrum
#print axioms PrincipiaTractalis.PositiveCompleteOracleRefutation.refuted_prop_implies_anything
#print axioms PrincipiaTractalis.PositiveCompleteOracleRefutation.refutation_witness_is_outside_the_positive_form
#print axioms PrincipiaTractalis.PositiveCompleteOracleRefutation.berryKeating_partial_unconditional
#print axioms PrincipiaTractalis.PositiveCompleteOracleRefutation.PositiveCompleteOracleRefutation_capstone
