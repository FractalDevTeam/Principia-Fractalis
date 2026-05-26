/-
# PolylogResonanceOrthogonalityCapstone — Single Citable Orthogonality Bundle

★ 2026-05-25 — Wave 19/20 follow-up — single referee-citable theorem ★

## Why this file exists

Wave 18 (`PolylogEigenvalueReformulated.lean`, commit `ce18a88`) and
Wave 19 (commit `a968642`) established, across multiple Lean files,
the following four-part architecture:

  (R) The reformulated resonance Prop `polylog_resonance_holds` is a
      **theorem** (axiom-free), establishing `π/(10·α) > 0 ∧
      π/(10·α) = (1/5)·(π/2 − Im R_f_principal α)` for `α > 1/2`.

  (B) The bridge `reformulation_preserves_PNP_chain` is **definitional**
      (`Iff.rfl` after unfolding), showing
      `PolylogAlgebraicContent ↔ PolylogEigenvalueConjecture`.

  (C) The chain `polylog_conjecture_implies_classes_distinct`
      consumes only the **algebraic** content (two polynomial equations
      on `alpha_of_class`), NOT the literal eigenvalue interpretation.

  (X) The literal spectral interpretation
      `λ₀(arxivHalpha α) = π/(10·α)` is **refuted** by Wave 17
      (`spectral_reading_refuted_at_sqrt2/phi_quarter`).

These four facts together state: **the framework's content survives
the Wave 17 spectral-reading refutation intact**, because the chain
to `P ≠ NP` consumes the algebraic content (which is unrefuted),
not the spectral re-reading (which is refuted).

## What this file does

Single citable bundle theorem
`polylog_resonance_pnp_orthogonality_citable` that packages all four
facts (R, B, C, X) into one referee-quotable statement. Downstream
files and the manuscript can cite this one theorem instead of
chasing four separate lemmas across three files.

## Honest scope

This file **DOES NOT** discharge `P ≠ NP`. It only documents the
**orthogonality**: the spectral-reading refutation does not weaken
the conditional `PolylogAlgebraicContent → ClassP ≠ ClassNP`
reduction, because the reduction never relied on the spectral
reading in the first place.

The headline reduction remains conditional on `PolylogAlgebraicContent`,
which (by `AlphaRealizationNoGo`) is logically equivalent to
`ClassP ≠ ClassNP`. No new mathematical content is produced; this
is a **refactoring** of existing axiom-free results into a single
quotable bundle.

## Axiom budget

Zero project axioms, zero sorries. All theorems depend only on
`[propext, Classical.choice, Quot.sound]`.

Stage Wave 22 — orthogonality bundle refactor.
-/

import PF.PolylogEigenvalueReformulated
import PF.PolylogEigenvalueDischargeAttempt
import PF.PolylogViaHilbertSchmidtCompactness
import PF.TuringEncoding.Operators
import PF.IntervalArithmetic

namespace PrincipiaTractalis.PolylogOrthogonality

open PrincipiaTractalis
  PrincipiaTractalis.PolylogReformulated
  PrincipiaTractalis.PolylogEigenvalueDischarge
  PrincipiaTractalis.PolylogHSCompactness
  PrincipiaTractalis.TuringEncoding
  PrincipiaTractalis.Operators

/-! ## The single citable orthogonality theorem -/

/-- **★ THE SINGLE CITABLE ORTHOGONALITY THEOREM ★**:

    For every `α ≥ √2` (in particular for the two canonical
    α-values `√2` (ClassP) and `φ + 1/4` (ClassNP)), the following
    four facts hold simultaneously and ARE NON-CONTRADICTORY:

    (R) **Resonance reformulation is a THEOREM** (axiom-free):
        `PolylogResonanceConjecture α` holds, i.e.
        `π/(10·α) > 0 ∧ π/(10·α) = (1/5)·(π/2 − Im R_f_principal α)`
        for `α > 1/2`. The B-clean monodromy phase identity is
        already proven (`b_clean_phase_identity`).

    (B) **Bridge is DEFINITIONAL** (`Iff.rfl` after unfolding):
        `PolylogAlgebraicContent ↔ PolylogEigenvalueConjecture`.
        The "algebraic content" Prop and the existing conjecture
        are the same Prop up to unfolding — there is no smuggled
        spectral assumption hiding in the conjecture.

    (C) **Chain consumes only algebraic content**, not spectral
        interpretation: given `PolylogAlgebraicContent`, the
        existing chain `polylog_conjecture_implies_classes_distinct`
        delivers `ClassP ≠ ClassNP`. No spectral hypothesis is used
        anywhere in the derivation.

    (X) **Literal spectral interpretation is REFUTED** (axiom-free):
        there exists `θ : ℝ` such that
        `twoVecRayleighQuotient α θ < groundStateValue α`. By the
        variational principle, this forbids
        `groundStateValue α = π/(10·α)` from being the ground-state
        eigenvalue of `arxivHalpha α`.

    **Net effect (the orthogonality)**: facts (X) and (C) live on
    different sides of the algebraic / spectral divide. The
    spectral refutation (X) cannot weaken the algebraic-content
    reduction (C), because (C) never depended on the spectral
    interpretation. The framework's content **survives** the
    Wave 17 refutation intact.

    **Honest scope**: this theorem DOES NOT discharge `P ≠ NP`.
    `PolylogAlgebraicContent` remains a named hypothesis on the
    opaque `alpha_of_class`. By `AlphaRealizationNoGo`, any concrete
    realisation is logically equivalent to `ClassP ≠ ClassNP`. The
    contribution here is purely **structural clarity**: a single
    quotable bundle for downstream code and manuscript references. -/
theorem polylog_resonance_pnp_orthogonality_citable
    {α : ℝ} (hα : Real.sqrt 2 ≤ α) :
    -- (R) Resonance reformulation is a theorem
    PolylogResonanceConjecture α ∧
    -- (B) Bridge is definitional (`Iff.rfl`)
    (PolylogAlgebraicContent ↔ PolylogEigenvalueConjecture) ∧
    -- (C) Chain consumes algebraic content → P ≠ NP
    (PolylogAlgebraicContent → ClassP ≠ ClassNP) ∧
    -- (X) Literal spectral reading is refuted
    (∃ θ : ℝ, twoVecRayleighQuotient α θ < groundStateValue α) := by
  refine ⟨polylog_resonance_holds α,
          PolylogAlgebraicContent_eq_PolylogEigenvalueConjecture,
          ?_, ?_⟩
  · -- (C) algebraic content → P ≠ NP, via the existing chain
    intro h_alg
    exact polylog_conjecture_implies_classes_distinct
      (reformulation_preserves_PNP_chain h_alg)
  · -- (X) spectral-reading refutation
    obtain ⟨θ, _, h_below⟩ := arxivHalpha_spectral_reading_refuted hα
    exact ⟨θ, h_below⟩

/-! ## Specialisations at the two canonical α-values -/

/-- **Orthogonality bundle at `α = √2`** (ClassP canonical). -/
theorem polylog_resonance_pnp_orthogonality_at_sqrt2 :
    PolylogResonanceConjecture (Real.sqrt 2) ∧
    (PolylogAlgebraicContent ↔ PolylogEigenvalueConjecture) ∧
    (PolylogAlgebraicContent → ClassP ≠ ClassNP) ∧
    (∃ θ : ℝ,
      twoVecRayleighQuotient (Real.sqrt 2) θ <
        groundStateValue (Real.sqrt 2)) :=
  polylog_resonance_pnp_orthogonality_citable (le_refl _)

/-- **Orthogonality bundle at `α = φ + 1/4`** (ClassNP canonical). -/
theorem polylog_resonance_pnp_orthogonality_at_phi_quarter :
    PolylogResonanceConjecture (phi + 1/4) ∧
    (PolylogAlgebraicContent ↔ PolylogEigenvalueConjecture) ∧
    (PolylogAlgebraicContent → ClassP ≠ ClassNP) ∧
    (∃ θ : ℝ,
      twoVecRayleighQuotient (phi + 1/4) θ <
        groundStateValue (phi + 1/4)) :=
  polylog_resonance_pnp_orthogonality_citable
    (le_of_lt phi_plus_quarter_gt_sqrt2)

/-! ## Scope statement (referee-quotable)

This file produces NO new mathematical content. It is a structural
refactor that bundles four axiom-free results from prior waves
(`polylog_resonance_holds` — Wave 17/18,
 `PolylogAlgebraicContent_eq_PolylogEigenvalueConjecture` — Wave 18,
 `polylog_conjecture_implies_classes_distinct` — Wave 13,
 `arxivHalpha_spectral_reading_refuted` — Wave 17)
into a single citable orthogonality theorem.

**What this theorem says**: the Wave 17 spectral-reading refutation
(X) is orthogonal to the Wave 13 P ≠ NP reduction (C), because (C)
consumes the algebraic content (B), not the spectral interpretation.

**What this theorem does NOT say**: it does NOT discharge `P ≠ NP`.
The P ≠ NP reduction remains conditional on `PolylogAlgebraicContent`,
which is logically equivalent to `ClassP ≠ ClassNP` (no-go).

## Axiom budget

Zero project axioms, zero sorries. -/

end PrincipiaTractalis.PolylogOrthogonality

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms
  PrincipiaTractalis.PolylogOrthogonality.polylog_resonance_pnp_orthogonality_citable
#print axioms
  PrincipiaTractalis.PolylogOrthogonality.polylog_resonance_pnp_orthogonality_at_sqrt2
#print axioms
  PrincipiaTractalis.PolylogOrthogonality.polylog_resonance_pnp_orthogonality_at_phi_quarter
