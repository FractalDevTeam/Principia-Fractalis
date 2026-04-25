/-
# Log-weighted Lebesgue Integral Infrastructure

Parallel infrastructure for the log-weighted inner product
  ⟨f, g⟩ = ∫₀¹ conj(f(x)) · g(x) · dx/x
that the transfer operator T₃ uses for self-adjointness.

This file defines the measure `logWeightedMeasure := (1/x) · volume on ℝ`
via `MeasureTheory.Measure.withDensity`. A future refactor should replace
the structure-based `LogWeightedL2` in `PF/TransferOperator.lean` with
`MeasureTheory.Lp ℂ 2 logWeightedMeasure`, which automatically provides
the inner product; once that lands, `LogWeightedL2.inner` and
`T3_self_adjoint_conj` become theorems (by the change-of-variables
proof in Chapter 20).

Started 2026-04-24 as action item #1 of RESEARCH_ROADMAP.md.

Reference: Principia Fractalis, Chapter 20
-/

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Data.ENNReal.Basic

namespace PrincipiaTractalis

open MeasureTheory

/-- The log-weighted measure on the real line: dμ = (1/x) · dx, with
    dμ({x ≤ 0}) = 0 by the piecewise definition (the physical domain
    is (0, 1], but we extend by 0 on the complement for convenience).

    On (0, 1], this is a sigma-finite but infinite measure:
      ∫_{(0,1]} dx/x = ∞ (logarithmic divergence at 0).
    Yet L² with respect to it is well-defined. -/
noncomputable def logWeightedMeasure : Measure ℝ :=
  volume.withDensity (fun x => if x ≤ 0 then 0 else (ENNReal.ofReal (1 / x)))

/-- The density function used in the measure definition, isolated for
    reuse in proofs. -/
noncomputable def logWeightDensity (x : ℝ) : ENNReal :=
  if x ≤ 0 then 0 else ENNReal.ofReal (1 / x)

lemma logWeightedMeasure_def :
    logWeightedMeasure = volume.withDensity logWeightDensity := by
  rfl

/-- The log-weighted density is everywhere finite (ne top). -/
lemma logWeightDensity_ne_top (x : ℝ) : logWeightDensity x ≠ ⊤ := by
  unfold logWeightDensity
  split_ifs
  · exact ENNReal.zero_ne_top
  · exact ENNReal.ofReal_ne_top

/-- `logWeightedMeasure` is sigma-finite. -/
instance : SigmaFinite logWeightedMeasure := by
  unfold logWeightedMeasure
  exact MeasureTheory.SigmaFinite.withDensity_of_ne_top' (fun x => logWeightDensity_ne_top x)

/-- The concrete L²(logWeightedMeasure) Hilbert space. This is the type that
    should replace the current structure-based `LogWeightedL2` in
    `PF/TransferOperator.lean`. It automatically inherits an
    `InnerProductSpace ℂ` instance from mathlib's `MeasureTheory.L2` theory
    — when the refactor is complete, `LogWeightedL2.inner` and
    `T3_self_adjoint_conj` become provable theorems, not axioms.

    The `SigmaFinite` instance above is required for this type to
    satisfy the `NormedAddCommGroup` / `InnerProductSpace` instances
    consistently. -/
noncomputable abbrev LogWeightedL2_concrete : Type :=
  MeasureTheory.Lp ℂ 2 logWeightedMeasure

end PrincipiaTractalis
