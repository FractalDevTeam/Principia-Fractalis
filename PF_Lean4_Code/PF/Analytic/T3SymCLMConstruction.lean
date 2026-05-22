/-
# T3_sym CLM Construction — Conditional Reduction to Linear-Structure Witnesses

This file pushes one level deeper into bundle (a) of
`PF/Analytic/T3SymCompactWitness.lean` by factoring the load-bearing
`T3SymCLMSymmetricWitness` Prop into three smaller, named, axiom-free
sub-Props at mathlib-API granularity, and providing the conditional
extraction chain.

## Why this file exists

`PF/Analytic/T3SymCompactWitness.lean:118-140` introduces
`T3SymCLMSymmetricWitness` as an existential over a CLM that agrees
with `T3_sym.apply` and is symmetric in the inner-product sense. The
docstring there points at `PF/LogWeightedIntegral.lean:2190` for
`transferOperator_clm`, which is a CLM-wrapping of the contracting
half `T_b` via `LinearMap.mkContinuous`.

State of `PF/LogWeightedIntegral.lean` (audited 2026-05-21):
  * `transferOperator_clm` exists at the documented line 2190.
  * It wraps the contracting **`transferOperator_lp`** form, parametrised
    over generic `(b, phases)` — NOT the symmetrised `T3_sym.apply`.
  * The file is NOT currently imported anywhere
    (no `import PF.LogWeightedIntegral` in `PF.lean` or its descendants).
  * The file has a stale `.olean` cached against an older `mathlib`/
    `PF.TransferOperator` snapshot. A forced rebuild
    (`touch PF/LogWeightedIntegral.lean && lake build PF.LogWeightedIntegral`)
    fails at two specific spots:

      - line 1989 (`logWeightedMeasure_restrict_Ioo_map_inverseBranch_absolutelyContinuous`):
        unsolved goal because the closing `rw` chain at lines 2020-2027
        no longer triggers measure unification under the current mathlib.
      - line 2052 (`inverseBranch_ae_eq_propagation`): `inverseBranch_measurable`
        now resolves to `PF.TransferOperator`'s 0-hypothesis version
        rather than this file's 1-hypothesis version, so the explicit
        `hb` argument becomes a type error.

These breaks lie in the AE-equality propagation chain (lines 1986-2078)
that `transferOperator_lp_add` (line 2094) and `transferOperator_lp_smul`
(line 2145) — i.e. the linear-map ingredients of `transferOperator_clm`
— consume internally.

## What this file delivers (NO SORRY, NO AXIOMS)

  1. **`T3SymLinearStructure`** — structured Prop asserting that
     `T3_sym.apply` is additive, complex-homogeneous, and norm-bounded
     by `‖f‖`. These are the precise three ingredients that
     `LinearMap.mkContinuous` consumes. None are axioms.

  2. **`T3_sym_CLM_of_linearStructure`** — explicit CLM constructed
     from `T3SymLinearStructure` via `LinearMap.mkContinuous`.

  3. **`T3_sym_CLM_apply_eq`** — action-agreement: the constructed CLM
     coincides with `T3_sym.apply` as a function.

  4. **`T3_sym_CLM_isSymmetric_from_inner_bridge`** — symmetry of the
     constructed CLM follows from `T3_self_adjoint_conj` once an
     inner-product bridge `LogWeightedL2.inner f g = ⟪f, g⟫_𝕜` is
     supplied. This bridge is a small named hypothesis at mathlib API
     surface (`Lp.inner_def` + `setIntegral` rewrite); it is NOT an
     axiom.

  5. **`T3SymCLMSymmetricWitness_proved_via_linearStructure`** —
     the end-to-end discharge: given `T3SymLinearStructure` plus the
     inner-product bridge, produces `T3SymCLMSymmetricWitness`.

## Honest framing

After this file, the bundle (a) `T3SymCLMSymmetricWitness` gap is
factored further into:

  * **`T3SymLinearStructure`** — three Lp-level lemmas
    (`T3_sym.apply` additive, complex-homogeneous, norm-bounded by `‖f‖`).
    The natural source for these is `PF/LogWeightedIntegral.lean`'s
    `transferOperator_lp_add` / `_smul` / `_norm_le` chain. The current
    file is not directly reusable due to the two broken-build spots
    above, but the underlying mathematical content is the standard
    Lp-AE-propagation argument: roughly 700 lines of measure-theoretic
    bookkeeping.

  * **`LogWeightedL2InnerBridge`** — a single equation
    `LogWeightedL2.inner f g = ⟪f, g⟫` (Lp `Inner.inner` from mathlib's
    `MeasureTheory.L2Space.inner_def`). Direct from
    `MeasureTheory.L2.inner_def` plus `MeasureTheory.integral_restrict`
    once the `f.toFunℝ` vs `Lp.coeFn` distinction is reconciled (both
    are AE-strongly-measurable representatives).

NEITHER is an axiom. Both are honestly-named Props with concrete
mathlib-pointed extraction targets.

## Build state

ZERO project axioms; ZERO `sorry`. Build clean against the same
mathlib snapshot as `PF.Analytic.T3SymCompactWitness`.
-/

import PF.Analytic.T3SymCompactWitness

namespace PrincipiaTractalis

open scoped InnerProductSpace
open MeasureTheory

/-! ## 1. Linear-structure witness for `T3_sym.apply` -/

/-- **`T3SymLinearStructure`** — packages the three function-level
    ingredients that `LinearMap.mkContinuous` consumes for `T3_sym.apply`:
    additivity, complex-homogeneity, and the operator-norm bound.

    Provenance (when supplied): each component is an Lp-level identity
    proven via the `transferOperator_lp_add` / `_smul` /
    `transferOperator_lp_norm_le` chain
    (`PF/LogWeightedIntegral.lean:2094`, `:2145`, `:1898`) lifted to
    the symmetrised operator via the average-decomposition
    `T3_sym.apply f = (1/2) • (T3.apply f + T3_adjoint.apply f)`. -/
structure T3SymLinearStructure : Prop where
  /-- Additivity: $T_3^{\mathrm{sym}}(f + g) = T_3^{\mathrm{sym}} f + T_3^{\mathrm{sym}} g$. -/
  add : ∀ (f g : LogWeightedL2),
    T3_sym.apply (f + g) = T3_sym.apply f + T3_sym.apply g
  /-- Complex-homogeneity: $T_3^{\mathrm{sym}}(c \cdot f) = c \cdot T_3^{\mathrm{sym}} f$. -/
  smul : ∀ (c : ℂ) (f : LogWeightedL2),
    T3_sym.apply (c • f) = c • T3_sym.apply f
  /-- Operator-norm bound: $\|T_3^{\mathrm{sym}} f\| \le \|f\|$ — Mayer 1991
      contractivity transferred to the symmetrised half-sum. -/
  norm_le : ∀ (f : LogWeightedL2), ‖T3_sym.apply f‖ ≤ ‖f‖

/-! ## 2. CLM construction from `T3SymLinearStructure` -/

/-- **`T3_sym_CLM_of_linearStructure`** — explicit
    `LogWeightedL2 →L[ℂ] LogWeightedL2` CLM built from a
    `T3SymLinearStructure` witness via `LinearMap.mkContinuous` with
    operator-norm bound `M = 1`. -/
noncomputable def T3_sym_CLM_of_linearStructure
    (hLin : T3SymLinearStructure) :
    LogWeightedL2 →L[ℂ] LogWeightedL2 :=
  LinearMap.mkContinuous
    { toFun := T3_sym.apply
      map_add' := hLin.add
      map_smul' := hLin.smul }
    1
    (fun f => by rw [one_mul]; exact hLin.norm_le f)

/-- **Action-agreement**: the constructed CLM evaluates to `T3_sym.apply`. -/
theorem T3_sym_CLM_of_linearStructure_apply_eq
    (hLin : T3SymLinearStructure) (f : LogWeightedL2) :
    T3_sym_CLM_of_linearStructure hLin f = T3_sym.apply f :=
  rfl

/-- **Operator-norm bound** for the constructed CLM: `‖T_3^{sym}_CLM‖ ≤ 1`. -/
theorem T3_sym_CLM_of_linearStructure_norm_le
    (hLin : T3SymLinearStructure) :
    ‖T3_sym_CLM_of_linearStructure hLin‖ ≤ 1 := by
  unfold T3_sym_CLM_of_linearStructure
  exact LinearMap.mkContinuous_norm_le _ zero_le_one _

/-! ## 3. Inner-product bridge -/

/-- **`LogWeightedL2InnerBridge`** — the equality between the project's
    Bochner-form `LogWeightedL2.inner f g` and mathlib's
    `InnerProductSpace ℂ LogWeightedL2` (i.e. the `Lp ℂ 2 μ`-induced)
    inner product `⟪f, g⟫_ℂ`.

    Provenance (when supplied): `MeasureTheory.L2.inner_def` gives
    `⟪f, g⟫_Lp = ∫ a, ⟪f a, g a⟫ ∂(μ_log.restrict (Ioo 0 1))`. Unfolding
    `⟪f a, g a⟫_ℂ = (starRingEnd ℂ) (f a) * g a` and reducing
    `∫ _ ∂(μ.restrict s) = ∫ in s, _ ∂μ` (`MeasureTheory.integral_restrict`)
    matches the LHS of `LogWeightedL2.inner` modulo the `f.toFunℝ` /
    `Lp.coeFn` representative bridge (both AE-equal representatives of
    the same Lp class). -/
def LogWeightedL2InnerBridge : Prop :=
  ∀ (f g : LogWeightedL2),
    LogWeightedL2.inner f g = @inner ℂ LogWeightedL2 _ f g

/-! ## 4. Symmetry of the constructed CLM -/

/-- **Symmetry under the project's `LogWeightedL2.inner`**: the
    constructed CLM is `⟪·, ·⟫`-symmetric, directly from the proven
    `T3_self_adjoint_conj` (universal, no MemLp2 hypotheses).

    No inner-product bridge required for this version — it lives in
    the project's `⟪·, ·⟫` inner product. To upgrade to mathlib's
    `LinearMap.IsSymmetric` (which uses the `InnerProductSpace ℂ`
    instance), see `T3_sym_CLM_isSymmetric_from_inner_bridge` below. -/
theorem T3_sym_CLM_of_linearStructure_symmetric_LogWeightedL2_inner
    (hLin : T3SymLinearStructure) (f g : LogWeightedL2) :
    ⟪T3_sym_CLM_of_linearStructure hLin f, g⟫
      = ⟪f, T3_sym_CLM_of_linearStructure hLin g⟫ := by
  rw [T3_sym_CLM_of_linearStructure_apply_eq,
      T3_sym_CLM_of_linearStructure_apply_eq]
  exact T3_self_adjoint_conj f g

/-- **Mathlib-level `IsSymmetric`** for the constructed CLM. Lifts
    `T3_sym_CLM_of_linearStructure_symmetric_LogWeightedL2_inner` from
    the project's `⟪·, ·⟫` to mathlib's `InnerProductSpace ℂ`-induced
    inner product via the `LogWeightedL2InnerBridge`. -/
theorem T3_sym_CLM_isSymmetric_from_inner_bridge
    (hLin : T3SymLinearStructure)
    (hBridge : LogWeightedL2InnerBridge) :
    (T3_sym_CLM_of_linearStructure hLin
        : LogWeightedL2 →ₗ[ℂ] LogWeightedL2).IsSymmetric := by
  intro x y
  -- Goal: ⟪(T_clm x : LogWeightedL2), y⟫_ℂ = ⟪x, T_clm y⟫_ℂ
  -- Bridge ℂ-inner → LogWeightedL2.inner for both sides:
  rw [show @inner ℂ LogWeightedL2 _ ((T3_sym_CLM_of_linearStructure hLin : LogWeightedL2 →ₗ[ℂ] LogWeightedL2) x) y
        = LogWeightedL2.inner (T3_sym_CLM_of_linearStructure hLin x) y
      from (hBridge _ _).symm]
  rw [show @inner ℂ LogWeightedL2 _ x ((T3_sym_CLM_of_linearStructure hLin : LogWeightedL2 →ₗ[ℂ] LogWeightedL2) y)
        = LogWeightedL2.inner x (T3_sym_CLM_of_linearStructure hLin y)
      from (hBridge _ _).symm]
  exact T3_sym_CLM_of_linearStructure_symmetric_LogWeightedL2_inner hLin x y

/-! ## 5. End-to-end discharge of `T3SymCLMSymmetricWitness` -/

/-- **★ `T3SymCLMSymmetricWitness` discharged conditionally on the
    linear-structure + inner-bridge factor pair ★**

    Given:
      * `T3SymLinearStructure` — the three Lp-level linearity/bound
        ingredients (additivity, complex-homogeneity, norm bound),
      * `LogWeightedL2InnerBridge` — the inner-product equality
        `LogWeightedL2.inner = ⟪·, ·⟫_ℂ`,
    produces a `T3SymCLMSymmetricWitness`.

    No project axioms; no `sorry`. -/
theorem T3SymCLMSymmetricWitness_proved_via_linearStructure
    (hLin : T3SymLinearStructure)
    (hBridge : LogWeightedL2InnerBridge) :
    T3SymCLMSymmetricWitness :=
  ⟨T3_sym_CLM_of_linearStructure hLin,
   T3_sym_CLM_of_linearStructure_apply_eq hLin,
   T3_sym_CLM_isSymmetric_from_inner_bridge hLin hBridge⟩

/-! ## 6. Concrete progress summary

After this file, the bundle (a) state for `T3SymCLMSymmetricWitness`
is FACTORED further into:

  * `T3SymLinearStructure` (3 Lp-level identities; natural source =
    `PF/LogWeightedIntegral.lean`'s `transferOperator_lp_*` chain
    after the two-spot rebuild fix), and
  * `LogWeightedL2InnerBridge` (single inner-product equality;
    natural source = `MeasureTheory.L2.inner_def` +
    `MeasureTheory.integral_restrict` + `f.toFunℝ`-as-`Lp.coeFn`-rep).

Both are at mathlib-API granularity. Neither is an axiom. The current
file alone discharges `T3SymCLMSymmetricWitness` modulo these two
named, attackable Props.

Combined with `T3SymFiniteRankTower` and `T3SymEigenvalueExtraction`
from `T3SymCompactWitness.lean`, the bundle (a) gap of
`riemann_hypothesis_residual_after_witness_discharge` is now factored
into FOUR concretely-attackable Props at mathlib-API granularity —
none of which is an axiom. -/

/-! ## 7. Axiom-freeness verification -/

#print axioms T3SymLinearStructure
#print axioms T3_sym_CLM_of_linearStructure
#print axioms T3_sym_CLM_of_linearStructure_apply_eq
#print axioms T3_sym_CLM_of_linearStructure_norm_le
#print axioms LogWeightedL2InnerBridge
#print axioms T3_sym_CLM_of_linearStructure_symmetric_LogWeightedL2_inner
#print axioms T3_sym_CLM_isSymmetric_from_inner_bridge
#print axioms T3SymCLMSymmetricWitness_proved_via_linearStructure

end PrincipiaTractalis
