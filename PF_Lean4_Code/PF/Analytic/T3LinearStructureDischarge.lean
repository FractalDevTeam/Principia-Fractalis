/-
# `T3LinearStructure` — Direct Linear-Structure Discharge

This file pushes the CONTRACTING half of the half-sum factorisation
(`PF/Analytic/T3SymLinearStructureDischarge.lean`) one level deeper, by
proving the `add` and `smul` components of `T3LinearStructure`
DIRECTLY from the operator definition (`PF/TransferOperator.lean:1245`)
using:

  * `T3_toFunℝ_Ioo_unconditional` (`PF/TransferOperator.lean:1800`) —
    Lp-representative ↔ pointwise formula bridge (uncond., since
    MemLp closure is in source via `T3_apply_func_MemLp`).

  * `LogWeightedL2.toFunℝ_add` / `LogWeightedL2.toFunℝ_smul`
    (`PF/TransferOperator.lean:342, 333`) — `Lp ℂ 2 μ` linear-op AE
    bridges via `Lp.coeFn_add` / `Lp.coeFn_smul`.

  * `inverseBranch_qmp_restrict`
    (`PF/TransferOperator.lean:1029`) — QuasiMeasurePreserving for
    the contracting branches `y_k(x) = (x+k)/3`, giving
    `Measure.QuasiMeasurePreserving.ae_eq` to propagate AE-equality
    of input `f.toFunℝ` through the branch composition `f.toFunℝ ∘ y_k`.

## What this file delivers (NO SORRY, NO AXIOMS)

  1. **`T3LinearStructure_add_proved`** — additivity of `T3.apply`.
  2. **`T3LinearStructure_smul_proved`** — ℂ-homogeneity of `T3.apply`.
  3. **`T3NormBound`** — refined sub-Prop for the operator-norm bound
     `‖T_3 f‖ ≤ ‖f‖` (Mayer 1991 contractivity), the ONE remaining
     analytic content for `T3LinearStructure` after this file.
  4. **`T3AdjointNormBound`** — analogue for `T3_adjoint`.
  5. **`T3AdjointLinearStructureFactored`** — refined sub-Prop bundling
     the THREE adjoint ingredients (the adjoint additivity/homogeneity
     needs an expanding-map QMP which is a separate piece of analytic
     content; factored here as a Prop pending an explicit construction).
  6. **`T3LinearStructure_proved_from_norm_bound`** — packages (1) + (2)
     with a `T3NormBound` witness into `T3LinearStructure`.
  7. **`T3AdjointLinearStructure_proved_from_factored`** — bridges
     the factored adjoint Prop to `T3AdjointLinearStructure`.

## Honest framing

After this file, the bundle (a) gap for `T3SymLinearStructure`
reduces to:
  * For the contracting half: SINGLE one-line norm-bound Prop
    `T3NormBound` (additivity + homogeneity now PROVED).
  * For the expanding half: still the 3-piece
    `T3AdjointLinearStructureFactored` (no new structural reduction
    in this file — the expanding-direction QMP is a separate analytic
    obligation that requires `Real.volume_preimage_mul_*` chaining
    with translation/dilation Jacobian).

This delivers a STRICT refinement on the contracting half. The
expanding half remains as before pending an expanding-map QMP file.

## Build state

ZERO project axioms. ZERO `sorry`. Builds against the same mathlib
snapshot as `PF.Analytic.T3SymLinearStructureDischarge`.
-/

import PF.Analytic.T3SymLinearStructureDischarge

namespace PrincipiaTractalis

open scoped InnerProductSpace
open MeasureTheory

/-! ## 1. Additivity for `T3.apply` -/

/-- **★ Additivity of `T3.apply` ★**

    `T3.apply (f + g) = T3.apply f + T3.apply g`.

    Proof chain:
      1. Both sides are elements of `Lp ℂ 2 μ` (i.e. `LogWeightedL2`).
      2. Show their underlying `↑↑(·)` AE-coincide via:
         a. `T3_toFunℝ_Ioo_unconditional` on each side.
         b. Pointwise distribution of `f.toFunℝ + g.toFunℝ` through the
            sum-over-branches in `transferOperatorAction_func`.
         c. `LogWeightedL2.toFunℝ_add` on the RHS sum.
         d. `inverseBranch_qmp_restrict.ae_eq` to propagate the
            `(f + g).toFunℝ =ᵐ f.toFunℝ + g.toFunℝ` identity through
            `y_k = inverseBranch 3 k`.
      3. Finalise via `Lp.ext` on AE-equality of representatives. -/
theorem T3LinearStructure_add_proved (f g : LogWeightedL2) :
    T3.apply (f + g) = T3.apply f + T3.apply g := by
  apply MeasureTheory.Lp.ext
  have h_lhs : (T3.apply (f + g)).toFunℝ
        =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)]
        transferOperatorAction_func 3 phaseFactorBase3 (f + g) :=
    T3_toFunℝ_Ioo_unconditional (f + g)
  have h_rhs_add : (T3.apply f + T3.apply g).toFunℝ
        =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)]
        (T3.apply f).toFunℝ + (T3.apply g).toFunℝ :=
    LogWeightedL2.toFunℝ_add (T3.apply f) (T3.apply g)
  have h_apply_f : (T3.apply f).toFunℝ
        =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)]
        transferOperatorAction_func 3 phaseFactorBase3 f :=
    T3_toFunℝ_Ioo_unconditional f
  have h_apply_g : (T3.apply g).toFunℝ
        =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)]
        transferOperatorAction_func 3 phaseFactorBase3 g :=
    T3_toFunℝ_Ioo_unconditional g
  have h_fg_add : (f + g).toFunℝ
        =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)]
        f.toFunℝ + g.toFunℝ :=
    LogWeightedL2.toFunℝ_add f g
  -- Per-branch AE: ((f+g).toFunℝ ∘ y_k) =ᵐ ((f.toFunℝ + g.toFunℝ) ∘ y_k)
  have h_branch_ae : ∀ k : Fin 3, ∀ᵐ x ∂(logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)),
      (f + g).toFunℝ (inverseBranch 3 k x)
        = f.toFunℝ (inverseBranch 3 k x) + g.toFunℝ (inverseBranch 3 k x) := by
    intro k
    have h_qmp := inverseBranch_qmp_restrict k
    have h_comp : ((f + g).toFunℝ) ∘ (inverseBranch 3 k)
                  =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)]
                  (f.toFunℝ + g.toFunℝ) ∘ (inverseBranch 3 k) :=
      h_qmp.ae_eq h_fg_add
    filter_upwards [h_comp] with x hx
    exact hx
  -- Combine all 3 branches simultaneously
  have h_all_branches : ∀ᵐ x ∂(logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)),
      ∀ k : Fin 3, (f + g).toFunℝ (inverseBranch 3 k x)
        = f.toFunℝ (inverseBranch 3 k x) + g.toFunℝ (inverseBranch 3 k x) :=
    Filter.eventually_all.mpr h_branch_ae
  -- Pointwise distribute through the sum
  have h_pointwise_distribute : ∀ᵐ x ∂(logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)),
      transferOperatorAction_func 3 phaseFactorBase3 (f + g) x
        = transferOperatorAction_func 3 phaseFactorBase3 f x
          + transferOperatorAction_func 3 phaseFactorBase3 g x := by
    filter_upwards [h_all_branches] with x hx_all
    unfold transferOperatorAction_func
    rw [show ∑ k : Fin 3,
            phaseFactorBase3 k * (weightFunction 3 k x : ℂ) *
              (f + g).toFunℝ (inverseBranch 3 k x)
          = ∑ k : Fin 3,
            (phaseFactorBase3 k * (weightFunction 3 k x : ℂ) *
              f.toFunℝ (inverseBranch 3 k x) +
              phaseFactorBase3 k * (weightFunction 3 k x : ℂ) *
              g.toFunℝ (inverseBranch 3 k x))
        from by
          apply Finset.sum_congr rfl
          intros k _
          rw [hx_all k]
          ring]
    rw [Finset.sum_add_distrib]
    ring
  -- Combine: ↑↑(T3.apply (f+g)) =ᵐ ↑↑(T3.apply f + T3.apply g)
  have h_lhs_to_sum : (T3.apply (f + g)).toFunℝ
        =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)]
        (fun x => transferOperatorAction_func 3 phaseFactorBase3 f x
                  + transferOperatorAction_func 3 phaseFactorBase3 g x) := by
    filter_upwards [h_lhs, h_pointwise_distribute] with x h1 h2
    rw [h1, h2]
  have h_rhs_to_sum : (T3.apply f + T3.apply g).toFunℝ
        =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)]
        (fun x => transferOperatorAction_func 3 phaseFactorBase3 f x
                  + transferOperatorAction_func 3 phaseFactorBase3 g x) := by
    filter_upwards [h_rhs_add, h_apply_f, h_apply_g] with x h_sum h_f h_g
    -- h_sum : (T3.apply f + T3.apply g).toFunℝ x = (T3.apply f).toFunℝ x + (T3.apply g).toFunℝ x
    -- (Pi.add_apply form, since toFunℝ_add gives AE-equality to the pi-sum)
    rw [h_sum]
    show (T3.apply f).toFunℝ x + (T3.apply g).toFunℝ x = _
    rw [h_f, h_g]
  exact h_lhs_to_sum.trans h_rhs_to_sum.symm

/-! ## 2. Complex homogeneity for `T3.apply` -/

/-- **★ Complex-homogeneity of `T3.apply` ★**

    `T3.apply (c • f) = c • T3.apply f` for any `c : ℂ`. -/
theorem T3LinearStructure_smul_proved (c : ℂ) (f : LogWeightedL2) :
    T3.apply (c • f) = c • T3.apply f := by
  apply MeasureTheory.Lp.ext
  have h_lhs : (T3.apply (c • f)).toFunℝ
        =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)]
        transferOperatorAction_func 3 phaseFactorBase3 (c • f) :=
    T3_toFunℝ_Ioo_unconditional (c • f)
  have h_rhs_smul : (c • T3.apply f).toFunℝ
        =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)]
        c • (T3.apply f).toFunℝ :=
    LogWeightedL2.toFunℝ_smul c (T3.apply f)
  have h_apply_f : (T3.apply f).toFunℝ
        =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)]
        transferOperatorAction_func 3 phaseFactorBase3 f :=
    T3_toFunℝ_Ioo_unconditional f
  have h_cf_smul : (c • f).toFunℝ
        =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)]
        c • f.toFunℝ :=
    LogWeightedL2.toFunℝ_smul c f
  have h_branch_ae : ∀ k : Fin 3, ∀ᵐ x ∂(logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)),
      (c • f).toFunℝ (inverseBranch 3 k x) = c • f.toFunℝ (inverseBranch 3 k x) := by
    intro k
    have h_qmp := inverseBranch_qmp_restrict k
    have h_comp : ((c • f).toFunℝ) ∘ (inverseBranch 3 k)
                  =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)]
                  (c • f.toFunℝ) ∘ (inverseBranch 3 k) :=
      h_qmp.ae_eq h_cf_smul
    filter_upwards [h_comp] with x hx
    exact hx
  have h_all_branches : ∀ᵐ x ∂(logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)),
      ∀ k : Fin 3, (c • f).toFunℝ (inverseBranch 3 k x)
        = c • f.toFunℝ (inverseBranch 3 k x) :=
    Filter.eventually_all.mpr h_branch_ae
  have h_pointwise_distribute : ∀ᵐ x ∂(logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)),
      transferOperatorAction_func 3 phaseFactorBase3 (c • f) x
        = c * transferOperatorAction_func 3 phaseFactorBase3 f x := by
    filter_upwards [h_all_branches] with x hx_all
    unfold transferOperatorAction_func
    rw [show ∑ k : Fin 3,
            phaseFactorBase3 k * (weightFunction 3 k x : ℂ) *
              (c • f).toFunℝ (inverseBranch 3 k x)
          = ∑ k : Fin 3,
            c * (phaseFactorBase3 k * (weightFunction 3 k x : ℂ) *
              f.toFunℝ (inverseBranch 3 k x))
        from by
          apply Finset.sum_congr rfl
          intros k _
          rw [hx_all k]
          rw [smul_eq_mul]; ring]
    rw [← Finset.mul_sum]
    ring
  have h_lhs_to_smul : (T3.apply (c • f)).toFunℝ
        =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)]
        (fun x => c * transferOperatorAction_func 3 phaseFactorBase3 f x) := by
    filter_upwards [h_lhs, h_pointwise_distribute] with x h1 h2
    rw [h1, h2]
  have h_rhs_to_smul : (c • T3.apply f).toFunℝ
        =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)]
        (fun x => c * transferOperatorAction_func 3 phaseFactorBase3 f x) := by
    filter_upwards [h_rhs_smul, h_apply_f] with x h_smul h_f
    rw [h_smul]
    show c • (T3.apply f).toFunℝ x = _
    rw [h_f, smul_eq_mul]
  exact h_lhs_to_smul.trans h_rhs_to_smul.symm

/-! ## 3. Norm-bound sub-Props (Mayer 1991 — refined sub-Props) -/

/-- **`T3NormBound`** — refined sub-Prop bundling the Mayer 1991
    contractivity bound `‖T_3 f‖ ≤ ‖f‖` on `L²([0,1], dx/x)` for the
    contracting transfer operator `T3.apply`.

    Provenance (when supplied): Mayer 1991 (BAMS) §2 — per-branch
    Cauchy-Schwarz on the explicit pointwise formula combined with
    the already-proved per-branch L² identity
    `branch_logWeightedMeasure_norm_sq_eq_real`
    (`PF/TransferOperator.lean:1617`). This is the SINGLE remaining
    analytic content for `T3LinearStructure` after the additivity
    and homogeneity discharge above. -/
structure T3NormBound : Prop where
  norm_le : ∀ (f : LogWeightedL2), ‖T3.apply f‖ ≤ ‖f‖

/-- **`T3AdjointNormBound`** — analogue for `T3_adjoint.apply`.

    Provenance (when supplied): formal-adjoint contractivity from
    `T3NormBound` via Mayer 1991's `‖T_3^*‖ = ‖T_3‖ ≤ 1` for the
    adjoint of a contraction on a Hilbert space. -/
structure T3AdjointNormBound : Prop where
  norm_le : ∀ (f : LogWeightedL2), ‖T3_adjoint.apply f‖ ≤ ‖f‖

/-! ## 4. `T3LinearStructure` from `T3NormBound` -/

/-- **★★ `T3LinearStructure` from `T3NormBound` ★★**

    Packages the proven additivity + homogeneity (this file) with
    a `T3NormBound` witness into the full `T3LinearStructure` Prop.

    After this theorem, the contracting-half `T3LinearStructure` gap
    reduces to the SINGLE one-line norm-bound Prop `T3NormBound`. -/
theorem T3LinearStructure_proved_from_norm_bound
    (hNorm : T3NormBound) : T3LinearStructure :=
  ⟨T3LinearStructure_add_proved,
   T3LinearStructure_smul_proved,
   hNorm.norm_le⟩

/-! ## 5. `T3AdjointLinearStructureFactored` — sub-Prop pending expanding QMP

The expanding-direction `add` and `smul` for `T3_adjoint.apply` require
AE-equality propagation through `x ↦ 3 * x - k` on the partition
`I_k = (k/3, (k+1)/3)`, which is the analogue of `inverseBranch_qmp_restrict`
for the expanding map. This QMP requires:

  * `Real.volume_preimage_mul_*` (volume scaling by 3),
  * translation invariance (`measurePreserving_sub_right`),
  * branch-localisation (the if-cascade restriction).

Rather than building this expanding-direction QMP here (which is a
separate file's worth of measure-theoretic plumbing), we factor the
remaining adjoint linearity content as a sub-Prop, plus its norm bound. -/

/-- **`T3AdjointLinearStructureFactored`** — factored package of the
    three adjoint ingredients pending the expanding-map QMP. -/
structure T3AdjointLinearStructureFactored : Prop where
  /-- Adjoint additivity. -/
  add : ∀ (f g : LogWeightedL2),
    T3_adjoint.apply (f + g) = T3_adjoint.apply f + T3_adjoint.apply g
  /-- Adjoint ℂ-homogeneity. -/
  smul : ∀ (c : ℂ) (f : LogWeightedL2),
    T3_adjoint.apply (c • f) = c • T3_adjoint.apply f
  /-- Adjoint contractivity. -/
  norm_le : ∀ (f : LogWeightedL2), ‖T3_adjoint.apply f‖ ≤ ‖f‖

/-- **★★ `T3AdjointLinearStructure` from the factored Prop ★★** -/
theorem T3AdjointLinearStructure_proved_from_factored
    (hFac : T3AdjointLinearStructureFactored) : T3AdjointLinearStructure :=
  ⟨hFac.add, hFac.smul, hFac.norm_le⟩

/-! ## 6. End-to-end discharge: `T3SymCLMSymmetricWitness` from sub-Props -/

/-- **★★★ `T3SymCLMSymmetricWitness` from the refined sub-Props ★★★**

    Combines:
      * The proved-here additivity + homogeneity for `T3.apply`.
      * A `T3NormBound` witness (Mayer 1991 contractivity for `T_3`).
      * A `T3AdjointLinearStructureFactored` witness (adjoint linearity
        + contractivity).
    via the existing `T3SymCLMSymmetricWitness_proved_from_halves`
    machinery (`PF/Analytic/T3SymLinearStructureDischarge.lean:206`). -/
theorem T3SymCLMSymmetricWitness_proved_from_refined
    (hNorm : T3NormBound)
    (hFac : T3AdjointLinearStructureFactored) :
    T3SymCLMSymmetricWitness :=
  T3SymCLMSymmetricWitness_proved_from_halves
    (T3LinearStructure_proved_from_norm_bound hNorm)
    (T3AdjointLinearStructure_proved_from_factored hFac)

/-! ## 7. Axiom-freeness verification -/

#print axioms T3LinearStructure_add_proved
#print axioms T3LinearStructure_smul_proved
#print axioms T3NormBound
#print axioms T3AdjointNormBound
#print axioms T3LinearStructure_proved_from_norm_bound
#print axioms T3AdjointLinearStructureFactored
#print axioms T3AdjointLinearStructure_proved_from_factored
#print axioms T3SymCLMSymmetricWitness_proved_from_refined

end PrincipiaTractalis
