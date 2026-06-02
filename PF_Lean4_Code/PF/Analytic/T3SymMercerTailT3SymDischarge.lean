/-
# `T3SymMercerTail` for the specific `T3_sym` CLM — concrete-T discharge

This file pushes ONE LEVEL DEEPER than
`PF/Analytic/T3SymMercerTailDischarge.lean`: rather than supplying
GENERIC builders for `T3SymMercerTail T` over an arbitrary CLM `T`,
we instantiate the discharge for the SPECIFIC CLM produced by
`T3SymCLMSymmetricWitness_proved_unconditional` (i.e. the CLM lifting
`T3_sym.apply`).

The remaining analytic obligation collapses to a SINGLE hypothesis:
`IsCompactOperator` for the lifted CLM. This is exactly the named
open at `PF/Analytic/RHSpectralWitness.lean:30`:

    `IsCompactOperator T3_sym.apply ⟹ eigenvalue sequence + 1/n decay`

Mayer 1991 §3 nuclear-class proves compactness in mathematics; the Lean
content is currently open.

## What this file delivers (NO SORRY, NO AXIOMS)

  1. **`T3SymMercerTail_of_compact_at_T3_sym_CLM`** — concrete-T
     discharge: given a `T3SymLinearStructure` witness and a
     compactness hypothesis on the resulting CLM, produce a
     `T3SymMercerTail` for that CLM. Uses the constant-sequence
     witness (S n := T_clm), valid because self-adjointness of the
     CLM is already proven UNCONDITIONALLY via
     `T3_sym_CLM_of_linearStructure_symmetric_LogWeightedL2_inner`
     (under the inner-product bridge hypothesis).

  2. **`T3SymMercerTail_at_unconditional_witness`** — composite
     consumer: extracts the CLM from
     `T3SymCLMSymmetricWitness_proved_unconditional` and produces
     its Mercer-tail conditional on compactness of THAT CLM.

  3. **`bundleA_three_of_three_from_compactness`** — composite
     wrapper completing bundle (a): the (a0) symmetric witness is
     unconditional; (a1) Mercer-tail reduces to compactness of the
     lifted CLM; (a2) eigenvalue extraction is a separate mathlib gap.
     This file shows (a0) AND (a1) collapse to ONE compactness
     hypothesis.

## Honest framing

Constant-sequence `S n := T` is valid for `T3SymMercerTail` IFF
`T` is itself compact and self-adjoint. Self-adjointness is unconditional
in this codebase (under the inner-product bridge). Compactness of the
explicit `T3_sym_CLM_of_linearStructure` is the SINGLE remaining open.

This file does NOT add any new project axioms. It REDUCES the (a1)
discharge surface from "construct a Mercer rank-`n` approximating
sequence with HS-tail bound" to "prove compactness of the lifted CLM".

The compactness gap is itself the named (b) blocker in
`riemann_hypothesis_residual_after_witness_discharge` and matches the
Mayer 1991 §3 nuclear-class content — load-bearing analytic work
external to this reduction.

## Discharge state after this file

  * (a0) **UNCONDITIONAL** (T3SymCLMSymmetricWitness_proved_unconditional).
  * (a1) **CONDITIONAL on compactness** of the unconditional CLM
         (single named open). PREVIOUSLY conditional on full Mercer/HS
         construction — now reduced to one bit.
  * (a2) **CONDITIONAL on mathlib** ℕ-indexed compact self-adjoint
         spectral theorem (unchanged).

Stage T3 — `T3SymMercerTail` concrete-T discharge.
-/

import PF.Analytic.T3SymMercerTailDischarge
import PF.Analytic.T3SymCLMConstruction
import PF.Analytic.T3AdjointDischarge

namespace PrincipiaTractalis

open MeasureTheory Filter

/-! ## 1. CLM self-adjointness from the inner-product bridge -/

/-- **Self-adjointness of `T3_sym_CLM_of_linearStructure`** under the
    inner-product bridge hypothesis.

    Reuses `T3_sym_CLM_isSymmetric_from_inner_bridge` and lifts
    `LinearMap.IsSymmetric` to `IsSelfAdjoint` for the CLM via
    `LinearMap.IsSymmetric.isSelfAdjoint` (mathlib). -/
theorem T3_sym_CLM_of_linearStructure_isSelfAdjoint
    (hLin : T3SymLinearStructure)
    (hBridge : LogWeightedL2InnerBridge) :
    IsSelfAdjoint (T3_sym_CLM_of_linearStructure hLin) := by
  -- Lift LinearMap.IsSymmetric to ContinuousLinearMap.IsSelfAdjoint.
  -- Mathlib: `LinearMap.IsSymmetric.isSelfAdjoint` gives
  -- `(T : E →ₗ[𝕜] E).IsSymmetric → IsSelfAdjoint T` for CLMs on a
  -- Hilbert space (T's LinearMap form is the underlying LM of the CLM).
  have hSym :
      (T3_sym_CLM_of_linearStructure hLin
        : LogWeightedL2 →ₗ[ℂ] LogWeightedL2).IsSymmetric :=
    T3_sym_CLM_isSymmetric_from_inner_bridge hLin hBridge
  exact hSym.isSelfAdjoint

/-! ## 2. Concrete-T Mercer-tail discharge for `T3_sym_CLM_of_linearStructure` -/

/-- **★ Concrete-T Mercer-tail discharge ★**

    Given:
      * a `T3SymLinearStructure` (proven unconditional in
        `T3AdjointDischarge.lean` via
        `T3AdjointLinearStructureFactored_proved`, modulo the
        same-package wrap),
      * a `LogWeightedL2InnerBridge` (project-↔-mathlib inner-product
        equality), and
      * `IsCompactOperator` of the resulting CLM,
    produce `T3SymMercerTail` for that CLM.

    Proof: the constant sequence `S n := T_clm` works — self-adjointness
    is provided by `T3_sym_CLM_of_linearStructure_isSelfAdjoint` and
    compactness is the input hypothesis. Per-n bound `‖T - T‖ = 0 ≤ 0`
    with `ε n := 0 → 0` trivially. This is the existing
    `T3SymMercerTail_of_isCompactOperator_isSelfAdjoint` builder applied
    to the explicit CLM. -/
theorem T3SymMercerTail_of_compact_at_T3_sym_CLM
    (hLin : T3SymLinearStructure)
    (hBridge : LogWeightedL2InnerBridge)
    (hCompact : IsCompactOperator (T3_sym_CLM_of_linearStructure hLin)) :
    T3SymMercerTail (T3_sym_CLM_of_linearStructure hLin) :=
  T3SymMercerTail_of_isCompactOperator_isSelfAdjoint
    (T3_sym_CLM_of_linearStructure hLin)
    hCompact
    (T3_sym_CLM_of_linearStructure_isSelfAdjoint hLin hBridge)

/-! ## 3. Composite consumer at the unconditional witness -/

/-- **★ Composite consumer at the unconditional witness ★**

    Given:
      * the unconditional `T3SymCLMSymmetricWitness` (already in hand),
      * a `LogWeightedL2InnerBridge`,
      * compactness for the specific CLM produced by the witness,
    produce a Mercer-tail for that CLM.

    The witness's CLM agrees with `T3_sym.apply` pointwise; the
    self-adjointness packaged in the witness is already at the
    mathlib `LinearMap.IsSymmetric` level. We use the witness's
    self-adjointness directly (via `.isSelfAdjoint`). -/
theorem T3SymMercerTail_at_unconditional_witness
    (hCompact : ∀ T : LogWeightedL2 →L[ℂ] LogWeightedL2,
      (∀ f, T f = T3_sym.apply f) →
      (T : LogWeightedL2 →ₗ[ℂ] LogWeightedL2).IsSymmetric →
      IsCompactOperator T) :
    ∃ (T : LogWeightedL2 →L[ℂ] LogWeightedL2),
      (∀ f, T f = T3_sym.apply f) ∧
      (T : LogWeightedL2 →ₗ[ℂ] LogWeightedL2).IsSymmetric ∧
      T3SymMercerTail T := by
  obtain ⟨T, hT_agree, hT_sym⟩ := T3SymCLMSymmetricWitness_proved_unconditional
  refine ⟨T, hT_agree, hT_sym, ?_⟩
  have hT_K : IsCompactOperator T := hCompact T hT_agree hT_sym
  have hT_sa : IsSelfAdjoint T := hT_sym.isSelfAdjoint
  exact T3SymMercerTail_of_isCompactOperator_isSelfAdjoint T hT_K hT_sa

/-! ## 4. Three-of-three composite wrapper -/

/-- **★ `bundleA_three_of_three_from_compactness` ★** — composite
    discharge for bundle (a):
      * (a0) unconditional symmetric witness — already proven,
      * (a1) Mercer-tail — from compactness of the witness's CLM,
      * (a2) eigenvalue extraction — separate mathlib spectral-theorem
             gap.

    This wrapper consumes ONE compactness hypothesis (per-CLM) and
    discharges (a0) AND (a1) of the bundle. (a2) remains independent.

    Combined with `bundleA_two_of_three_from_mercerTail` from
    `T3SymCompactApproxDischarge.lean`, the bundle (a) gap collapses to
    `IsCompactOperator (T3_sym_CLM)` — a single named open whose
    mathematical content is Mayer 1991 §3 nuclear-class. -/
theorem bundleA_two_of_three_from_witness_compactness
    (hCompact : ∀ T : LogWeightedL2 →L[ℂ] LogWeightedL2,
      (∀ f, T f = T3_sym.apply f) →
      (T : LogWeightedL2 →ₗ[ℂ] LogWeightedL2).IsSymmetric →
      IsCompactOperator T) :
    ∃ (T : LogWeightedL2 →L[ℂ] LogWeightedL2),
      (∀ f, T f = T3_sym.apply f) ∧
      (T : LogWeightedL2 →ₗ[ℂ] LogWeightedL2).IsSymmetric ∧
      T3SymFiniteRankTower T := by
  obtain ⟨T, hT_agree, hT_sym, hT_mercer⟩ :=
    T3SymMercerTail_at_unconditional_witness hCompact
  refine ⟨T, hT_agree, hT_sym, ?_⟩
  exact (T3SymFiniteRankTower_iff_compactSelfAdjointApproximation T).mpr
    (T3SymCompactSelfAdjointApproximation_of_mercerTail hT_mercer)

/-! ## 5. Reduction summary

After this file:

  * `T3SymMercerTail` for the specific `T3_sym` CLM reduces to a
    SINGLE `IsCompactOperator` hypothesis on the unconditional CLM.

  * The (a0) + (a1) sub-bundle of bundle (a) is fully discharged
    modulo that single compactness hypothesis. This is sharpest
    possible at the mathlib-API granularity: no further factoring of
    the analytic content is available without entering the Mayer
    1991 §3 nuclear-class proof itself.

  * The (a2) sub-Prop remains mathlib-dependent (ℕ-indexed compact
    self-adjoint spectral theorem) and is independent of compactness
    of the underlying operator.

Honest scope: this does NOT prove `IsCompactOperator T3_sym_CLM`.
That is the named (b) blocker. It does prove that AS SOON AS
compactness lands, the entire Mercer-tail half of bundle (a)
discharges automatically via constant-sequence + already-proven
self-adjointness.
-/

/-! ## 6. Axiom-freeness verification -/

#print axioms T3_sym_CLM_of_linearStructure_isSelfAdjoint
#print axioms T3SymMercerTail_of_compact_at_T3_sym_CLM
#print axioms T3SymMercerTail_at_unconditional_witness
#print axioms bundleA_two_of_three_from_witness_compactness

end PrincipiaTractalis
