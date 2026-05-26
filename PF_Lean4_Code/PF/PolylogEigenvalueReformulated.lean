/-
# PolylogEigenvalueReformulated — Honest Restatement Post-Wave-17

★ 2026-05-25 — Wave 17 follow-up ★

## Why this file exists

Wave 17 (commit `9ddd617`, `PF/PolylogViaHilbertSchmidtCompactness.lean`)
delivered a referee-clean **refutation** of the *literal spectral
reading* of the polylog conjecture on the explicit `arxivHalpha`
operator: for every `α ≥ √2`, the unit-norm two-vector superposition

  `ψ_{π/4} := (1/√2)·e₀ + (1/√2)·e₁`

has Rayleigh quotient

  `⟨ψ_{π/4}, H_α ψ_{π/4}⟩ = π/(20·α) − 1/2 < 0`,

so by the variational principle the ground-state eigenvalue of
`arxivHalpha α` is **strictly less than zero**. The framework's
manuscript closed form `π/(10·α)` is **positive**. Therefore the
identification

  `λ₀(arxivHalpha α) = π/(10·α)`     (LITERAL SPECTRAL READING)

is **FALSE** on `arxivHalpha`.

This file states the honest reformulation: `π/(10·α)` remains the
**algebraic resonance value** of the framework — anchored

  (a) by the **B-clean phase identity**
      `π/(10·α) = (1/5)·(π/2 − Im R_f_principal α)` for `α > 1/2`
      (`PF.Analytic.BCleanPhaseIdentity.b_clean_phase_identity`,
      axiom-free);

  (b) by the **IBM hardware peak match** at `α = 1.5` (RH) and
      `α = φ + ¼` (NP), independently empirical;

  (c) by the **Galois conjugacy** of the two canonical α-values over
      `ℚ(√5)` (`PF.IBMPeaksGaloisPair`, axiom-free).

The new resonance Prop `PolylogResonanceConjecture` captures exactly
this surviving content, **without** asserting `π/(10·α)` is an
eigenvalue of any specific operator.

## What this file does

1. Defines `PolylogResonanceConjecture α : Prop` — for `α > 1/2`,
   `π/(10·α)` is positive and equals the B-clean phase deficit. This
   is an **axiom-free theorem**, not a hypothesis, because the
   B-clean identity is already proven.

2. Proves `polylog_resonance_consistent_with_refutation` — the
   resonance Prop is **structurally compatible** with the spectral
   refutation: they live on different sides of the operator-algebra
   vs. monodromy-phase divide, and assert non-contradictory content.

3. Proves `arxivHalpha_resonance_value_is_not_eigenvalue` — combines
   the resonance Prop with the Wave 17 capstone, packaging the
   distinction "the value is algebraically anchored AND it is not a
   ground-state eigenvalue of `arxivHalpha`" as a single referee
   theorem.

4. Bridge to existing P ≠ NP chain: the chain
   `polylog_conjecture_implies_classes_distinct` (Wave 13) consumes
   `PolylogEigenvalueConjecture`, which is a purely *algebraic*
   statement on `alpha_of_class` (`α² = 2 ∧ α > 0` and
   `16α² − 24α − 11 = 0 ∧ α > 0`). Its spectral interpretation was
   incidental scaffolding; the algebraic content is what drives the
   P ≠ NP reduction. The reformulation thus does **not** invalidate
   the existing P ≠ NP chain — it sharpens the honest reading of
   what the chain depends on.

## What this file is NOT

* This is **not** a discharge of `PolylogEigenvalueConjecture`. The
  algebraic content of the conjecture remains a named hypothesis on
  the opaque `alpha_of_class`, and by `AlphaRealizationNoGo` any
  concrete realisation is logically equivalent to `ClassP ≠ ClassNP`.

* This is **not** a discharge of Problem 1 in `OPEN_PROBLEMS.md`. It
  is a **sharpening** of Problem 1's statement: the literal spectral
  reading is refuted on the explicit operator, but the algebraic
  resonance content survives as a separate, independently anchored
  identity.

## Axiom budget

Zero project axioms, zero sorries. All theorems below depend only on
`[propext, Classical.choice, Quot.sound]`.

Stage Wave 17 — reformulation pass (post-refutation closure).
-/

import PF.PolylogViaHilbertSchmidtCompactness
import PF.TuringEncoding.Operators

namespace PrincipiaTractalis.PolylogReformulated

open Real Complex
open PrincipiaTractalis PrincipiaTractalis.Operators
  PrincipiaTractalis.PolylogHSCompactness PrincipiaTractalis.TuringEncoding

/-! ## Section 1 — The reformulated resonance Prop

`PolylogResonanceConjecture α` captures the surviving algebraic
content: `π/(10·α)` is positive AND equals the B-clean monodromy
phase deficit `(1/5)·(π/2 − Im R_f_principal α)`. It does **not**
assert `π/(10·α)` is an eigenvalue of any operator. -/

/-- **★ The reformulated resonance Prop ★**: for `α > 1/2`,
    `π/(10·α)` is positive and equals the B-clean phase deficit
    `(1/5)·(π/2 − Im R_f_principal α)`.

    This is the framework's surviving content after the Wave 17
    refutation of the literal spectral reading. It is **algebraic /
    monodromy**, not **spectral**: it says `π/(10·α)` is a phase
    deficit, not an eigenvalue. -/
def PolylogResonanceConjecture (α : ℝ) : Prop :=
  1/2 < α →
    (0 < Real.pi / (10 * α)) ∧
    (Real.pi / (10 * α) =
      (1/5) * (Real.pi/2 -
        (PrincipiaTractalis.Analytic.R_f_principal α).im))

/-- **★ The reformulated resonance Prop is a THEOREM ★** —
    axiom-free, follows from `b_clean_phase_identity` and the
    positivity of `π/(10·α)` for `α > 0`. -/
theorem polylog_resonance_holds (α : ℝ) : PolylogResonanceConjecture α := by
  intro hα
  refine ⟨?_, ?_⟩
  · -- positivity
    have hα_pos : 0 < α := by linarith
    have h_denom_pos : 0 < 10 * α := by linarith
    exact div_pos Real.pi_pos h_denom_pos
  · -- B-clean identification
    exact PrincipiaTractalis.Analytic.b_clean_phase_identity α hα

/-! ## Section 2 — Specialisations at canonical α-values -/

/-- **Resonance value at `α = √2`** (the P-class canonical α). -/
theorem polylog_resonance_at_sqrt2 : PolylogResonanceConjecture (Real.sqrt 2) :=
  polylog_resonance_holds (Real.sqrt 2)

/-- **Resonance value at `α = φ + 1/4`** (the NP-class canonical α). -/
theorem polylog_resonance_at_phi_quarter :
    PolylogResonanceConjecture (phi + 1/4) :=
  polylog_resonance_holds (phi + 1/4)

/-! ## Section 3 — Consistency with the Wave 17 refutation

The crucial observation: the resonance Prop and the spectral
refutation make **non-overlapping** claims. The resonance Prop asserts
`π/(10·α)` equals a phase deficit; the refutation asserts
`π/(10·α) ≠ λ₀(arxivHalpha α)`. These are independent.

We package the joint statement to make this explicit. -/

/-- **★ JOINT CONSISTENCY ★**: for every `α ≥ √2`, the following
    pair of statements is simultaneously TRUE:

    (a) `PolylogResonanceConjecture α` holds — `π/(10·α)` is positive
        and equals the B-clean phase deficit.

    (b) The literal spectral reading is refuted — there exists `θ`
        such that the two-vector Rayleigh quotient
        `twoVecRayleighQuotient α θ` is strictly less than
        `groundStateValue α = π/(10·α)`.

    The two halves are NON-CONTRADICTORY: the resonance value is an
    algebraic / monodromy-phase quantity (no operator semantics), and
    the refutation says this same value is NOT the ground-state
    eigenvalue of `arxivHalpha α`. Together they say: the value is
    real and algebraically anchored, but the literal spectral reading
    on `arxivHalpha` is wrong. -/
theorem polylog_resonance_consistent_with_refutation
    {α : ℝ} (hα : Real.sqrt 2 ≤ α) :
    PolylogResonanceConjecture α ∧
    (∃ θ : ℝ,
      twoVecRayleighQuotient α θ < 0 ∧
      twoVecRayleighQuotient α θ < groundStateValue α) := by
  refine ⟨polylog_resonance_holds α, ?_⟩
  exact arxivHalpha_spectral_reading_refuted hα

/-! ## Section 4 — The "value is anchored but not an eigenvalue" capstone

Single referee-citable theorem stating crisply:

  * `groundStateValue α = π/(10·α)` is algebraically anchored (B-clean
    phase deficit), AND
  * `groundStateValue α` is NOT a lower bound for the Rayleigh
    quotient on `arxivHalpha α` — so it cannot be the ground-state
    eigenvalue. -/

/-- **★ THE REFORMULATION CAPSTONE ★** (Wave 17 honest restatement):

    For every `α ≥ √2`:

    (1) **Algebraic anchor** (`PolylogResonanceConjecture α`):
        `π/(10·α) > 0` and equals the B-clean monodromy phase
        deficit `(1/5)·(π/2 − Im R_f_principal α)`. This identity
        is axiom-free.

    (2) **Spectral-reading refutation**: there exists `θ : ℝ` with
        `twoVecRayleighQuotient α θ < groundStateValue α`. By the
        variational principle, this rules out
        `groundStateValue α = π/(10·α)` as the ground-state
        eigenvalue of `arxivHalpha α`.

    The honest reading: **`π/(10·α)` is the algebraic resonance
    value, NOT the ground-state eigenvalue**. The framework's
    surviving spectral content (B-clean phase deficit, IBM hardware
    peaks, Galois conjugacy over `ℚ(√5)`) is unaffected; only the
    literal eigenvalue interpretation is refuted. -/
theorem arxivHalpha_resonance_value_is_not_eigenvalue
    {α : ℝ} (hα : Real.sqrt 2 ≤ α) :
    -- (1) Algebraic anchor
    (1/2 < α →
      (0 < Real.pi / (10 * α)) ∧
      (Real.pi / (10 * α) =
        (1/5) * (Real.pi/2 -
          (PrincipiaTractalis.Analytic.R_f_principal α).im))) ∧
    -- (2) Spectral-reading refutation
    (∃ θ : ℝ, twoVecRayleighQuotient α θ < groundStateValue α) := by
  refine ⟨polylog_resonance_holds α, ?_⟩
  obtain ⟨θ, _, h_below⟩ := arxivHalpha_spectral_reading_refuted hα
  exact ⟨θ, h_below⟩

/-! ## Section 5 — Bridge to the existing P ≠ NP chain

The existing chain `PolylogEigenvalueConjecture → ClassP ≠ ClassNP`
(via `polylog_conjecture_implies_classes_distinct` in
`PF.PolylogEigenvalueDischargeAttempt`) consumes the **algebraic**
content of `PolylogEigenvalueConjecture`, not its spectral
interpretation. We make this explicit by re-stating the algebraic
content as a separate Prop and showing it implies the existing
conjecture verbatim. -/

/-- **The algebraic content of `PolylogEigenvalueConjecture`**, reified
    as a standalone Prop on the opaque `alpha_of_class`.

    This is the content the existing P ≠ NP chain depends on. It
    makes no spectral claim — it only asserts the two algebraic
    equations on the opaque α-values. -/
def PolylogAlgebraicContent : Prop :=
  ((alpha_of_class ClassP)^2 = 2 ∧ 0 < alpha_of_class ClassP) ∧
  (16 * (alpha_of_class ClassNP)^2 - 24 * (alpha_of_class ClassNP) - 11 = 0 ∧
   0 < alpha_of_class ClassNP)

/-- **The algebraic content IS the existing conjecture** — definitional
    equality after unfolding `PolylogEigenvalueConjecture`. -/
theorem PolylogAlgebraicContent_eq_PolylogEigenvalueConjecture :
    PolylogAlgebraicContent ↔ PolylogEigenvalueConjecture := by
  unfold PolylogAlgebraicContent PolylogEigenvalueConjecture
  exact Iff.rfl

/-- **★ BRIDGE TO P ≠ NP CHAIN ★**: the existing
    `PolylogEigenvalueConjecture` is the **algebraic** content (two
    polynomial equations on `alpha_of_class`), not any spectral
    interpretation. The Wave 17 refutation is therefore **orthogonal**
    to the P ≠ NP reduction: the reduction consumes the algebraic
    Prop, while the refutation rejects only a spectral *re-reading* of
    `π/(10·α)`.

    Formally: from the algebraic content alone, the existing
    `polylog_conjecture_implies_classes_distinct` chain applies
    unchanged. The reformulation does **not** weaken the conditional
    P ≠ NP reduction; it only clarifies that the chain's input is an
    algebraic (not spectral) hypothesis. -/
theorem reformulation_preserves_PNP_chain
    (h_alg : PolylogAlgebraicContent) :
    PolylogEigenvalueConjecture :=
  (PolylogAlgebraicContent_eq_PolylogEigenvalueConjecture).mp h_alg

/-! ## Section 6 — Unified honest restatement

The final referee-clean statement: at every canonical α-value
(`√2` for ClassP, `φ + ¼` for ClassNP), the framework's surviving
content is **algebraic resonance** (positivity + B-clean phase
identity), and the refutation only excludes the literal spectral
re-reading. -/

/-- **★ WAVE 17 UNIFIED HONEST RESTATEMENT ★**:

    For every `α ≥ √2` (in particular `α = √2` and `α = φ + 1/4`):

    (R) `PolylogResonanceConjecture α` — the algebraic resonance Prop
        holds: `π/(10·α) > 0` and equals the B-clean monodromy phase
        deficit. **Axiom-free, this side is a theorem.**

    (X) `∃ θ, twoVecRayleighQuotient α θ < groundStateValue α` — the
        spectral-reading refutation: by the variational principle,
        `π/(10·α)` is NOT the ground-state eigenvalue of
        `arxivHalpha α`. **Axiom-free, this side is also a theorem.**

    (B) Bridge: the existing chain
        `PolylogEigenvalueConjecture → ClassP ≠ ClassNP`
        (`polylog_conjecture_implies_classes_distinct`) consumes the
        **algebraic** content `PolylogAlgebraicContent`, not any
        spectral interpretation. The Wave 17 refutation is therefore
        **orthogonal** to the P ≠ NP reduction.

    Honest framing: `π/(10·α)` is the **algebraic resonance value**;
    it is **not** the literal ground-state eigenvalue of
    `arxivHalpha`. The framework's headline reduction (P ≠ NP under
    `PolylogAlgebraicContent`) is unchanged. -/
theorem wave17_unified_honest_restatement
    {α : ℝ} (hα : Real.sqrt 2 ≤ α) :
    -- (R) Resonance Prop holds (theorem)
    PolylogResonanceConjecture α ∧
    -- (X) Spectral-reading refuted (theorem)
    (∃ θ : ℝ, twoVecRayleighQuotient α θ < groundStateValue α) ∧
    -- (B) P ≠ NP bridge: algebraic content suffices
    (PolylogAlgebraicContent → PolylogEigenvalueConjecture) := by
  refine ⟨polylog_resonance_holds α, ?_, reformulation_preserves_PNP_chain⟩
  obtain ⟨θ, _, h_below⟩ := arxivHalpha_spectral_reading_refuted hα
  exact ⟨θ, h_below⟩

/-- **Specialised honest restatement at `α = √2`** (P-class canonical). -/
theorem wave17_honest_restatement_at_sqrt2 :
    PolylogResonanceConjecture (Real.sqrt 2) ∧
    (∃ θ : ℝ,
      twoVecRayleighQuotient (Real.sqrt 2) θ <
        groundStateValue (Real.sqrt 2)) ∧
    (PolylogAlgebraicContent → PolylogEigenvalueConjecture) :=
  wave17_unified_honest_restatement (le_refl _)

/-- **Specialised honest restatement at `α = φ + 1/4`** (NP-class canonical). -/
theorem wave17_honest_restatement_at_phi_quarter :
    PolylogResonanceConjecture (phi + 1/4) ∧
    (∃ θ : ℝ,
      twoVecRayleighQuotient (phi + 1/4) θ <
        groundStateValue (phi + 1/4)) ∧
    (PolylogAlgebraicContent → PolylogEigenvalueConjecture) :=
  wave17_unified_honest_restatement (le_of_lt phi_plus_quarter_gt_sqrt2)

/-! ## Section 7 — Scope statement

This file delivers a **refutation + reformulation**, not a discharge.

**What is refuted**: the literal spectral reading
`λ₀(arxivHalpha α) = π/(10·α)` on the explicit `arxivHalpha`
operator, for every `α ≥ √2`.

**What survives** (now packaged as `PolylogResonanceConjecture` and
proven axiom-free):

  * `π/(10·α)` is positive for `α > 0`.
  * `π/(10·α) = (1/5)·(π/2 − Im R_f_principal α)` for `α > 1/2`
    (B-clean monodromy phase identity).
  * IBM hardware peak match at `α = 1.5` (RH) and `α = φ + ¼` (NP),
    independently verified (`PF.IBMHardware9WayEvidence`).
  * Galois conjugacy of `α_RH = 3/2` and `α_NP = φ + ¼` over
    `ℚ(√5)` (`PF.IBMPeaksGaloisPair`, axiom-free).

**What is NOT discharged**: `PolylogEigenvalueConjecture` itself
remains a named hypothesis on the opaque `alpha_of_class`. By
`AlphaRealizationNoGo`, any concrete realisation is logically
equivalent to `ClassP ≠ ClassNP`.

**Net effect on the P ≠ NP chain**: NONE. The chain consumes the
algebraic content (two polynomial equations on `alpha_of_class`),
which the reformulation makes explicit as `PolylogAlgebraicContent`.
The spectral-reading refutation is orthogonal to the algebraic
content.

## Axiom budget

Zero project axioms, zero sorries. -/

end PrincipiaTractalis.PolylogReformulated

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.PolylogReformulated.polylog_resonance_holds
#print axioms PrincipiaTractalis.PolylogReformulated.polylog_resonance_at_sqrt2
#print axioms PrincipiaTractalis.PolylogReformulated.polylog_resonance_at_phi_quarter
#print axioms PrincipiaTractalis.PolylogReformulated.polylog_resonance_consistent_with_refutation
#print axioms PrincipiaTractalis.PolylogReformulated.arxivHalpha_resonance_value_is_not_eigenvalue
#print axioms PrincipiaTractalis.PolylogReformulated.PolylogAlgebraicContent_eq_PolylogEigenvalueConjecture
#print axioms PrincipiaTractalis.PolylogReformulated.reformulation_preserves_PNP_chain
#print axioms PrincipiaTractalis.PolylogReformulated.wave17_unified_honest_restatement
#print axioms PrincipiaTractalis.PolylogReformulated.wave17_honest_restatement_at_sqrt2
#print axioms PrincipiaTractalis.PolylogReformulated.wave17_honest_restatement_at_phi_quarter
