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
import PF.TransferOperator

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

/-! ## Phase A Foundations: Measurability of Transfer-Operator Constituents

Measurability lemmas for the maps that compose `transferOperatorAction`
(in `PF/TransferOperator.lean`). These are prerequisites for the
eventual Phase A elimination of `LogWeightedL2.inner` — the load-bearing
`MemLp` proof for the rewritten `transferOperatorAction` output requires
that each constituent map (inverse branches, weight functions, expanding
maps) is Borel measurable so the integral against `logWeightedMeasure`
is well-defined.

Added 2026-04-29 as durable infrastructure ahead of the structural
abbrev swap (`LogWeightedL2 := LogWeightedL2_concrete`).
RESEARCH_ROADMAP.md §2.1.
-/

/-- The inverse branch $y_k(x) = (x + k)/b$ is continuous on $\mathbb{R}$
    when $b \ne 0$. -/
theorem inverseBranch_continuous (b : ℕ) (k : Fin b) (hb : (b : ℝ) ≠ 0) :
    Continuous (fun x : ℝ => inverseBranch b k x) := by
  unfold inverseBranch
  exact (continuous_id.add continuous_const).div_const _

/-- The inverse branch $y_k(x) = (x + k)/b$ is Borel measurable on
    $\mathbb{R}$ when $b \ge 1$ (which is the only regime the transfer
    operator framework uses; in particular $b = 3$). -/
theorem inverseBranch_measurable (b : ℕ) (k : Fin b) (hb : b ≥ 1) :
    Measurable (fun x : ℝ => inverseBranch b k x) := by
  have hb_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hb)
  exact (inverseBranch_continuous b k (ne_of_gt hb_pos)).measurable

-- Note: `expandingMap_measurable` and `weightFunction_measurable`
-- deferred. The expanding map requires `Int.measurable_floor`-style
-- measurability of the floor function (mathlib API in flux); the weight
-- function requires `Measurable.dite` or an equivalent disposition for
-- the if-then-else over a propositional condition. Both are tractable
-- in a follow-on session; the `inverseBranch` lemmas above suffice as
-- foundational infrastructure for the immediate Phase A path
-- (the `MemLp` proof for `transferOperatorAction`'s output is dominated
-- by the inverse-branch composition, which is the load-bearing
-- measurability claim).

end PrincipiaTractalis
