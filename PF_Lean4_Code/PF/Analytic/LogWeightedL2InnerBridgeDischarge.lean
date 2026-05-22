/-
# `LogWeightedL2InnerBridge` Discharge — Project `inner` = mathlib `⟪·,·⟫_ℂ`

This file discharges `LogWeightedL2InnerBridge` from
`PF/Analytic/T3SymCLMConstruction.lean:170` directly via mathlib's
`MeasureTheory.L2.inner_def` and `RCLike.inner_apply'`.

## Why a bridge is needed

The project defines:
* `LogWeightedL2 := Lp ℂ 2 (logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1))`
  (`PF/TransferOperator.lean:93-94`)
* `LogWeightedL2.inner f g := ∫ x in (Ioo 0 1), conj(f.toFunℝ x) * g.toFunℝ x
                                 ∂logWeightedMeasure`
  (`PF/TransferOperator.lean:244-247`)

Mathlib provides an `InnerProductSpace ℂ LogWeightedL2` via the
`Lp ℂ 2 μ`-instance (`PF/TransferOperator.lean:101-102`), whose `inner`
is `∫ a, ⟪f a, g a⟫_ℂ ∂μ` (`MeasureTheory.L2.inner_def`).

The two sides agree because:
1. `∫ x in (Ioo 0 1), · ∂logWeightedMeasure` is by definition
   `∫ x, · ∂(logWeightedMeasure.restrict (Ioo 0 1))` —
   the project's outer integration measure IS `μ.restrict (Ioo 0 1)`
   in `setIntegral` notation.
2. `f.toFunℝ x = (f : ℝ → ℂ) x` definitionally:
   `toFunℝ f = (f.toFun : ℝ → ℂ) = ((f : Lp ℂ 2 _).val : ℝ → ℂ)`
   matches `Lp.instCoeFun`'s unfolding.
3. `⟪f a, g a⟫_ℂ = conj (f a) * g a` via `RCLike.inner_apply'`.

## Build state

ZERO project axioms. ZERO `sorry`. Builds against the same mathlib
snapshot as `PF.Analytic.T3SymCLMConstruction`.
-/

import PF.Analytic.T3SymCLMConstruction

namespace PrincipiaTractalis

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate

/-- **★ `LogWeightedL2InnerBridge` discharged ★** — the project's
    `LogWeightedL2.inner f g` coincides with mathlib's
    `⟪f, g⟫_ℂ` (the `Lp ℂ 2 μ`-induced inner product).

    Proof: `setIntegral` notation unfolds to `integral` against the
    restricted measure, `RCLike.inner_apply'` turns
    `⟪f a, g a⟫_ℂ = conj (f a) * g a`, and the Lp coercion makes
    `f.toFunℝ x = (f : ℝ → ℂ) x` definitionally. -/
theorem logWeightedL2InnerBridge_proved : LogWeightedL2InnerBridge := by
  intro f g
  -- Unfold the project-level inner product.
  unfold LogWeightedL2.inner
  -- LHS: ∫ x in (Ioo 0 1), conj (f.toFunℝ x) * g.toFunℝ x ∂logWeightedMeasure
  --    = ∫ x, [indicator/restrict] (conj (f.toFunℝ x) * g.toFunℝ x)
  --        ∂(logWeightedMeasure.restrict (Ioo 0 1))
  -- by the definition of setIntegral notation.
  -- RHS: ⟪f, g⟫_ℂ = ∫ a, ⟪f a, g a⟫_ℂ ∂(logWeightedMeasure.restrict (Ioo 0 1))
  -- by L2.inner_def.
  rw [L2.inner_def (𝕜 := ℂ)]
  -- Now both sides are integrals over the same measure.
  -- The remaining gap: integrand equality
  --   conj (f.toFunℝ x) * g.toFunℝ x  =  ⟪f x, g x⟫_ℂ
  -- This holds pointwise via RCLike.inner_apply'.
  congr 1
  funext a
  -- ⟪f a, g a⟫_ℂ = conj (f a) * g a
  rw [RCLike.inner_apply' (𝕜 := ℂ)]
  -- Now both sides have the same shape; the `(f : ℝ → ℂ) a` form
  -- equals `f.toFunℝ a` since both reduce to `((f : Lp ℂ 2 _).val : ℝ → ℂ) a`.
  rfl

/-! ## Downstream consumer: `T3SymCLMSymmetricWitness` from just `T3SymLinearStructure`

With `LogWeightedL2InnerBridge` proven, `T3SymCLMSymmetricWitness` is
discharged given ONLY a `T3SymLinearStructure` witness — the
inner-bridge hypothesis is no longer needed externally.
-/

/-- **★ `T3SymCLMSymmetricWitness` from `T3SymLinearStructure` alone ★** —
    composes `T3SymCLMSymmetricWitness_proved_via_linearStructure` with
    the now-proven `logWeightedL2InnerBridge_proved`.

    After this theorem, bundle (a)'s `T3SymCLMSymmetricWitness` gap
    reduces to a SINGLE remaining Prop: `T3SymLinearStructure`
    (the three Lp-level identities additivity / complex-homogeneity /
    norm-bound for `T3_sym.apply`). -/
theorem T3SymCLMSymmetricWitness_proved_from_linearStructure_only
    (hLin : T3SymLinearStructure) :
    T3SymCLMSymmetricWitness :=
  T3SymCLMSymmetricWitness_proved_via_linearStructure
    hLin logWeightedL2InnerBridge_proved

/-! ## Axiom-freeness verification -/

#print axioms logWeightedL2InnerBridge_proved
#print axioms T3SymCLMSymmetricWitness_proved_from_linearStructure_only

end PrincipiaTractalis
