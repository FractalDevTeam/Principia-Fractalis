/-
# `T3AdjointLinearStructureFactored` — Unconditional Discharge

This file PROVES `T3AdjointLinearStructureFactored` (defined in
`PF/Analytic/T3LinearStructureDischarge.lean`) — the THREE adjoint
ingredients (additivity, ℂ-homogeneity, contractivity for `T3_adjoint.apply`).

It is the PARALLEL chain to `T3NormSquaredBoundDischarge.lean` (which
discharged the contracting half `T3LinearStructure`). Together, the
TWO discharges yield `T3SymCLMSymmetricWitness` UNCONDITIONALLY.

## What this file delivers (NO SORRY, NO AXIOMS)

  1. **`T3_adjoint_action_func_add_ae`** — per-branch AE distribution
     of `(f+g).toFunℝ (3x-k) =ᵐ[μ_log↾(0,1)] f.toFunℝ (3x-k) + g.toFunℝ (3x-k)`
     via `expandingBranch_qmp_to_unit` restricted to each `I_k`, summed
     over the if-cascade.

  2. **`T3AdjointLinearStructure_add_proved`** — adjoint additivity:
     `T3_adjoint.apply (f + g) = T3_adjoint.apply f + T3_adjoint.apply g`.

  3. **`T3AdjointLinearStructure_smul_proved`** — adjoint ℂ-homogeneity:
     `T3_adjoint.apply (c • f) = c • T3_adjoint.apply f`.

  4. **`T3AdjointNormSquaredBound_proved`** — L²-squared CONTRACTIVITY
     (actually EQUALITY here, since `T3_adjoint` is an ISOMETRY on the
     dual decomposition): `∫_(0,1) |T3* f|² ∂μ_log = ∫_(0,1) |f|² ∂μ_log`.
     Sharper than the contracting case (no `Cauchy–Schwarz` slack —
     the if-cascade picks ONE branch per `x`, so pointwise
     `|T3* f(x)|² = |adjointWeight_k(x)|² · |f(3x-k)|²` on `I_k`, and
     per-branch CoV gives `(1/3)·∫_(0,1)|f|² dμ_log` per branch ⇒ summed
     over `Fin 3` ⇒ `∫_(0,1)|f|² dμ_log`.).

  5. **`T3AdjointNormBound_proved`** — `‖T3* f‖ ≤ ‖f‖`.

  6. **`T3AdjointLinearStructureFactored_proved`** — packaging.

  7. **`T3SymCLMSymmetricWitness_proved_unconditional`** — FULL discharge
     of `T3SymCLMSymmetricWitness`, eliminating BOTH halves' hypotheses.

## Build state

ZERO project axioms. ZERO `sorry`.
-/

import PF.Analytic.T3NormSquaredBoundDischarge

namespace PrincipiaTractalis

open MeasureTheory
open scoped InnerProductSpace

/-! ## 1. Per-branch AE propagation through the expanding map

The expanding-branch QMP `expandingBranch_qmp_to_unit k :
  Measure.QuasiMeasurePreserving (fun x => 3*x - k) (μ_log↾I_k) (μ_log↾(0,1))`
gives us AE propagation from `μ_log↾(0,1)` of `f.toFunℝ`-statements to
`μ_log↾I_k` of `f.toFunℝ ∘ (3*·-k)`-statements.

We then lift each `μ_log↾I_k` AE statement to `μ_log↾(0,1)` via the
fact that `I_k ⊆ (0,1)` ⇒ `(μ_log↾(0,1))↾I_k = μ_log↾I_k`. -/

/-- **Subset identity for restrictions**: `(μ_log↾(0,1))↾I_k = μ_log↾I_k`
    since `I_k ⊆ (0,1)` for every `k : Fin 3`. -/
private lemma logWeighted_restrict_Ik_eq (k : Fin 3) :
    (logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)).restrict
      (Set.Ioo ((k.val : ℝ)/3) (((k.val : ℝ) + 1)/3))
    = logWeightedMeasure.restrict
        (Set.Ioo ((k.val : ℝ)/3) (((k.val : ℝ) + 1)/3)) := by
  rw [MeasureTheory.Measure.restrict_restrict measurableSet_Ioo]
  congr 1
  ext y
  simp only [Set.mem_inter_iff, Set.mem_Ioo]
  have hk_nonneg : (0:ℝ) ≤ (k.val : ℝ) / 3 := by positivity
  have hk_ub : ((k.val : ℝ) + 1) / 3 ≤ 1 := by
    have : (k.val : ℝ) ≤ 2 := by
      have : k.val ≤ 2 := by have := k.isLt; omega
      exact_mod_cast this
    linarith
  refine ⟨fun ⟨h1, _⟩ => h1, fun ⟨h1, h2⟩ => ⟨⟨h1, h2⟩, ?_⟩⟩
  exact ⟨lt_of_le_of_lt hk_nonneg h1, lt_of_lt_of_le h2 hk_ub⟩

/-! ## 2. Adjoint additivity -/

/-- **★ Additivity of `T3_adjoint.apply` ★**

    `T3_adjoint.apply (f + g) = T3_adjoint.apply f + T3_adjoint.apply g`.

    Proof: AE equality of representatives via the if-cascade
    `T3_adjoint_action_func`, distributing `(f+g)` through each branch
    using `expandingBranch_qmp_to_unit k` to propagate the AE-equality
    `(f+g).toFunℝ =ᵐ f.toFunℝ + g.toFunℝ` (from `LogWeightedL2.toFunℝ_add`)
    through `x ↦ 3x - k` on `I_k`, then lifted to `(0,1)`. -/
theorem T3AdjointLinearStructure_add_proved (f g : LogWeightedL2) :
    T3_adjoint.apply (f + g) = T3_adjoint.apply f + T3_adjoint.apply g := by
  apply MeasureTheory.Lp.ext
  -- Bridges between Lp-rep and explicit if-cascade for adjoint.
  have h_lhs : (T3_adjoint.apply (f + g)).toFunℝ
        =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)]
        T3_adjoint_action_func (f + g) :=
    T3_adjoint_toFunℝ_Ioo_unconditional (f + g)
  have h_rhs_add : (T3_adjoint.apply f + T3_adjoint.apply g).toFunℝ
        =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)]
        (T3_adjoint.apply f).toFunℝ + (T3_adjoint.apply g).toFunℝ :=
    LogWeightedL2.toFunℝ_add (T3_adjoint.apply f) (T3_adjoint.apply g)
  have h_apply_f : (T3_adjoint.apply f).toFunℝ
        =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)]
        T3_adjoint_action_func f :=
    T3_adjoint_toFunℝ_Ioo_unconditional f
  have h_apply_g : (T3_adjoint.apply g).toFunℝ
        =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)]
        T3_adjoint_action_func g :=
    T3_adjoint_toFunℝ_Ioo_unconditional g
  have h_fg_add : (f + g).toFunℝ
        =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)]
        f.toFunℝ + g.toFunℝ :=
    LogWeightedL2.toFunℝ_add f g
  -- Per-branch AE propagation through `x ↦ 3*x - k` on (0,1).
  -- Strategy: lift `h_fg_add` (statement on μ_log↾(0,1)) to each μ_log↾I_k
  -- via `(μ_log↾(0,1))↾I_k = μ_log↾I_k`. Then apply QMP.ae_eq with
  -- `expandingBranch_qmp_to_unit k`. Then lift the resulting μ_log↾I_k
  -- AE-equality back to μ_log↾(0,1) by indicator-localisation.
  have h_branch_ae : ∀ k : Fin 3, ∀ᵐ x ∂(logWeightedMeasure.restrict
      (Set.Ioo ((k.val : ℝ)/3) (((k.val : ℝ) + 1)/3))),
      (f + g).toFunℝ (3 * x - (k.val : ℝ))
        = f.toFunℝ (3 * x - (k.val : ℝ)) + g.toFunℝ (3 * x - (k.val : ℝ)) := by
    intro k
    have h_qmp := expandingBranch_qmp_to_unit k
    have h_comp : ((f + g).toFunℝ) ∘ (fun x : ℝ => 3 * x - (k.val : ℝ))
                  =ᵐ[logWeightedMeasure.restrict
                      (Set.Ioo ((k.val : ℝ)/3) (((k.val : ℝ) + 1)/3))]
                  (f.toFunℝ + g.toFunℝ) ∘ (fun x : ℝ => 3 * x - (k.val : ℝ)) :=
      h_qmp.ae_eq h_fg_add
    filter_upwards [h_comp] with x hx
    exact hx
  -- Pointwise distribution of the if-cascade.
  -- For each x ∈ (0,1), exactly one branch `I_k` is active (modulo {1/3, 2/3}).
  -- We show the branch-equality holds AE on μ_log↾(0,1) by combining the three
  -- per-branch AE-eqs via indicator-localisation.
  -- KEY: use `(ae_restrict_iff' measurableSet_Ioo).mp` to lift each branch.
  have h_branch_ae_lift : ∀ k : Fin 3, ∀ᵐ x ∂(logWeightedMeasure.restrict
      (Set.Ioo (0:ℝ) 1)),
      x ∈ Set.Ioo ((k.val : ℝ)/3) (((k.val : ℝ) + 1)/3) →
      (f + g).toFunℝ (3 * x - (k.val : ℝ))
        = f.toFunℝ (3 * x - (k.val : ℝ)) + g.toFunℝ (3 * x - (k.val : ℝ)) := by
    intro k
    -- We have h_branch_ae k : AE on μ_log↾I_k.
    -- Use μ_log↾I_k = (μ_log↾(0,1))↾I_k.
    have h_eq := logWeighted_restrict_Ik_eq k
    have h_on_Ik : ∀ᵐ x ∂((logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)).restrict
        (Set.Ioo ((k.val : ℝ)/3) (((k.val : ℝ) + 1)/3))),
        (f + g).toFunℝ (3 * x - (k.val : ℝ))
          = f.toFunℝ (3 * x - (k.val : ℝ)) + g.toFunℝ (3 * x - (k.val : ℝ)) := by
      rw [h_eq]; exact h_branch_ae k
    exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mp h_on_Ik
  -- Combine all 3 branches simultaneously.
  have h_all_branches : ∀ᵐ x ∂(logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)),
      ∀ k : Fin 3,
      x ∈ Set.Ioo ((k.val : ℝ)/3) (((k.val : ℝ) + 1)/3) →
      (f + g).toFunℝ (3 * x - (k.val : ℝ))
        = f.toFunℝ (3 * x - (k.val : ℝ)) + g.toFunℝ (3 * x - (k.val : ℝ)) :=
    Filter.eventually_all.mpr h_branch_ae_lift
  -- Now show pointwise distribution on the if-cascade.
  -- Need: T3_adjoint_action_func (f+g) x = T3_adjoint_action_func f x + T3_adjoint_action_func g x
  -- modulo {1/3, 2/3}.
  -- {1/3, 2/3} AE
  have h_bdry_vol_zero : (MeasureTheory.volume : MeasureTheory.Measure ℝ)
      ({(1/3 : ℝ), 2/3}) = 0 := by
    have h_subset : ({(1/3 : ℝ), 2/3} : Set ℝ) ⊆ {(1/3 : ℝ)} ∪ {(2/3 : ℝ)} := by
      intro y hy; simp at hy ⊢; tauto
    refine MeasureTheory.measure_mono_null h_subset ?_
    apply le_antisymm _ (zero_le _)
    calc (MeasureTheory.volume : MeasureTheory.Measure ℝ)
            (({(1/3 : ℝ)} : Set ℝ) ∪ {(2/3 : ℝ)})
        ≤ MeasureTheory.volume ({(1/3 : ℝ)} : Set ℝ) +
            MeasureTheory.volume ({(2/3 : ℝ)} : Set ℝ) :=
          MeasureTheory.measure_union_le _ _
      _ = 0 + 0 := by rw [Real.volume_singleton, Real.volume_singleton]
      _ = 0 := by ring
  have h_bdry_meas_zero : (logWeightedMeasure : MeasureTheory.Measure ℝ)
      ({(1/3 : ℝ), 2/3}) = 0 := by
    apply logWeightedMeasure_null_of_volume_pos_null
    · exact ((Set.finite_singleton (2/3 : ℝ)).insert _).measurableSet
    · refine MeasureTheory.measure_mono_null Set.inter_subset_left ?_
      exact h_bdry_vol_zero
  have h_bdry_ae : ∀ᵐ x ∂(logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)),
      x ≠ 1/3 ∧ x ≠ 2/3 := by
    have h_global : ∀ᵐ x ∂(logWeightedMeasure : MeasureTheory.Measure ℝ),
        x ≠ 1/3 ∧ x ≠ 2/3 := by
      rw [MeasureTheory.ae_iff]
      have h_eq : {x : ℝ | ¬(x ≠ 1/3 ∧ x ≠ 2/3)} = {(1/3 : ℝ), 2/3} := by
        ext y
        simp only [Set.mem_setOf_eq, ne_eq, not_and, not_not, Set.mem_insert_iff,
          Set.mem_singleton_iff]
        tauto
      rw [h_eq]
      exact h_bdry_meas_zero
    exact MeasureTheory.ae_restrict_of_ae h_global
  -- Pointwise distribution of T3_adjoint_action_func (modulo {1/3, 2/3}).
  have h_pointwise_distribute : ∀ᵐ x ∂(logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)),
      T3_adjoint_action_func (f + g) x
        = T3_adjoint_action_func f x + T3_adjoint_action_func g x := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    have h_all := (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mp h_all_branches
    have h_bdry := (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mp h_bdry_ae
    filter_upwards [h_all, h_bdry] with x hx_all_imp hx_bdry_imp hx_Ioo
    have hx_all := hx_all_imp hx_Ioo
    have hx_bdry := hx_bdry_imp hx_Ioo
    obtain ⟨hx_ne_1_3, hx_ne_2_3⟩ := hx_bdry
    unfold T3_adjoint_action_func
    -- Pre-compute branch ranges.
    have h_b0_lo : ((0 : Fin 3).val : ℝ)/3 = 0 := by norm_num
    have h_b0_hi : (((0 : Fin 3).val : ℝ) + 1)/3 = 1/3 := by norm_num
    have h_b1_lo : ((1 : Fin 3).val : ℝ)/3 = 1/3 := by norm_num
    have h_b1_hi : (((1 : Fin 3).val : ℝ) + 1)/3 = 2/3 := by norm_num
    have h_b2_lo : ((2 : Fin 3).val : ℝ)/3 = 2/3 := by norm_num
    have h_b2_hi : (((2 : Fin 3).val : ℝ) + 1)/3 = 1 := by norm_num
    have h_v0 : ((0 : Fin 3).val : ℝ) = 0 := by norm_num
    have h_v1 : ((1 : Fin 3).val : ℝ) = 1 := by norm_num
    have h_v2 : ((2 : Fin 3).val : ℝ) = 2 := by norm_num
    -- split_ifs on all three if-cascades simultaneously.
    split_ifs with h_op_a h_op_b
    · -- x ≤ 1/3 ⇒ in I_0
      have hx1 : x < 1/3 ∨ x = 1/3 := lt_or_eq_of_le h_op_a
      have hx1' : x < 1/3 := hx1.resolve_right hx_ne_1_3
      have h_in_I0 : x ∈ Set.Ioo (((0 : Fin 3).val : ℝ)/3) ((((0 : Fin 3).val : ℝ) + 1)/3) := by
        rw [h_b0_lo, h_b0_hi]; exact ⟨hx_Ioo.1, hx1'⟩
      have h_distrib := hx_all 0 h_in_I0
      rw [h_v0] at h_distrib
      simp only [sub_zero] at h_distrib
      rw [h_distrib]; ring
    · -- 1/3 < x ≤ 2/3 ⇒ in I_1
      have hx1 : x > 1/3 := lt_of_not_ge h_op_a
      have hx2 : x < 2/3 ∨ x = 2/3 := lt_or_eq_of_le h_op_b
      have hx2' : x < 2/3 := hx2.resolve_right hx_ne_2_3
      have h_in_I1 : x ∈ Set.Ioo (((1 : Fin 3).val : ℝ)/3) ((((1 : Fin 3).val : ℝ) + 1)/3) := by
        rw [h_b1_lo, h_b1_hi]; exact ⟨hx1, hx2'⟩
      have h_distrib := hx_all 1 h_in_I1
      rw [h_v1] at h_distrib
      rw [h_distrib]; ring
    · -- 2/3 < x ⇒ in I_2
      have hx1 : x > 1/3 := lt_of_not_ge h_op_a
      have hx2 : x > 2/3 := lt_of_not_ge h_op_b
      have h_in_I2 : x ∈ Set.Ioo (((2 : Fin 3).val : ℝ)/3) ((((2 : Fin 3).val : ℝ) + 1)/3) := by
        rw [h_b2_lo, h_b2_hi]; exact ⟨hx2, hx_Ioo.2⟩
      have h_distrib := hx_all 2 h_in_I2
      rw [h_v2] at h_distrib
      rw [h_distrib]; ring
  -- Combine LHS = (T3_adjoint (f+g)).toFunℝ =ᵐ T3_adjoint_action_func (f+g)
  --              =ᵐ T3_adjoint_action_func f + T3_adjoint_action_func g
  --              =ᵐ (T3_adjoint f).toFunℝ + (T3_adjoint g).toFunℝ
  --              =ᵐ (T3_adjoint f + T3_adjoint g).toFunℝ.
  have h_lhs_to_sum : (T3_adjoint.apply (f + g)).toFunℝ
        =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)]
        (fun x => T3_adjoint_action_func f x + T3_adjoint_action_func g x) := by
    filter_upwards [h_lhs, h_pointwise_distribute] with x h1 h2
    rw [h1, h2]
  have h_rhs_to_sum : (T3_adjoint.apply f + T3_adjoint.apply g).toFunℝ
        =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)]
        (fun x => T3_adjoint_action_func f x + T3_adjoint_action_func g x) := by
    filter_upwards [h_rhs_add, h_apply_f, h_apply_g] with x h_sum h_f h_g
    rw [h_sum]
    show (T3_adjoint.apply f).toFunℝ x + (T3_adjoint.apply g).toFunℝ x = _
    rw [h_f, h_g]
  exact h_lhs_to_sum.trans h_rhs_to_sum.symm

/-! ## 3. Adjoint ℂ-homogeneity -/

/-- **★ ℂ-homogeneity of `T3_adjoint.apply` ★**

    `T3_adjoint.apply (c • f) = c • T3_adjoint.apply f`. -/
theorem T3AdjointLinearStructure_smul_proved (c : ℂ) (f : LogWeightedL2) :
    T3_adjoint.apply (c • f) = c • T3_adjoint.apply f := by
  apply MeasureTheory.Lp.ext
  have h_lhs : (T3_adjoint.apply (c • f)).toFunℝ
        =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)]
        T3_adjoint_action_func (c • f) :=
    T3_adjoint_toFunℝ_Ioo_unconditional (c • f)
  have h_rhs_smul : (c • T3_adjoint.apply f).toFunℝ
        =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)]
        c • (T3_adjoint.apply f).toFunℝ :=
    LogWeightedL2.toFunℝ_smul c (T3_adjoint.apply f)
  have h_apply_f : (T3_adjoint.apply f).toFunℝ
        =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)]
        T3_adjoint_action_func f :=
    T3_adjoint_toFunℝ_Ioo_unconditional f
  have h_cf_smul : (c • f).toFunℝ
        =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)]
        c • f.toFunℝ :=
    LogWeightedL2.toFunℝ_smul c f
  have h_branch_ae : ∀ k : Fin 3, ∀ᵐ x ∂(logWeightedMeasure.restrict
      (Set.Ioo ((k.val : ℝ)/3) (((k.val : ℝ) + 1)/3))),
      (c • f).toFunℝ (3 * x - (k.val : ℝ))
        = c • f.toFunℝ (3 * x - (k.val : ℝ)) := by
    intro k
    have h_qmp := expandingBranch_qmp_to_unit k
    have h_comp : ((c • f).toFunℝ) ∘ (fun x : ℝ => 3 * x - (k.val : ℝ))
                  =ᵐ[logWeightedMeasure.restrict
                      (Set.Ioo ((k.val : ℝ)/3) (((k.val : ℝ) + 1)/3))]
                  (c • f.toFunℝ) ∘ (fun x : ℝ => 3 * x - (k.val : ℝ)) :=
      h_qmp.ae_eq h_cf_smul
    filter_upwards [h_comp] with x hx
    exact hx
  have h_branch_ae_lift : ∀ k : Fin 3, ∀ᵐ x ∂(logWeightedMeasure.restrict
      (Set.Ioo (0:ℝ) 1)),
      x ∈ Set.Ioo ((k.val : ℝ)/3) (((k.val : ℝ) + 1)/3) →
      (c • f).toFunℝ (3 * x - (k.val : ℝ))
        = c • f.toFunℝ (3 * x - (k.val : ℝ)) := by
    intro k
    have h_eq := logWeighted_restrict_Ik_eq k
    have h_on_Ik : ∀ᵐ x ∂((logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)).restrict
        (Set.Ioo ((k.val : ℝ)/3) (((k.val : ℝ) + 1)/3))),
        (c • f).toFunℝ (3 * x - (k.val : ℝ))
          = c • f.toFunℝ (3 * x - (k.val : ℝ)) := by
      rw [h_eq]; exact h_branch_ae k
    exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mp h_on_Ik
  have h_all_branches : ∀ᵐ x ∂(logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)),
      ∀ k : Fin 3,
      x ∈ Set.Ioo ((k.val : ℝ)/3) (((k.val : ℝ) + 1)/3) →
      (c • f).toFunℝ (3 * x - (k.val : ℝ))
        = c • f.toFunℝ (3 * x - (k.val : ℝ)) :=
    Filter.eventually_all.mpr h_branch_ae_lift
  -- {1/3, 2/3} AE-set.
  have h_bdry_vol_zero : (MeasureTheory.volume : MeasureTheory.Measure ℝ)
      ({(1/3 : ℝ), 2/3}) = 0 := by
    have h_subset : ({(1/3 : ℝ), 2/3} : Set ℝ) ⊆ {(1/3 : ℝ)} ∪ {(2/3 : ℝ)} := by
      intro y hy; simp at hy ⊢; tauto
    refine MeasureTheory.measure_mono_null h_subset ?_
    apply le_antisymm _ (zero_le _)
    calc (MeasureTheory.volume : MeasureTheory.Measure ℝ)
            (({(1/3 : ℝ)} : Set ℝ) ∪ {(2/3 : ℝ)})
        ≤ MeasureTheory.volume ({(1/3 : ℝ)} : Set ℝ) +
            MeasureTheory.volume ({(2/3 : ℝ)} : Set ℝ) :=
          MeasureTheory.measure_union_le _ _
      _ = 0 + 0 := by rw [Real.volume_singleton, Real.volume_singleton]
      _ = 0 := by ring
  have h_bdry_meas_zero : (logWeightedMeasure : MeasureTheory.Measure ℝ)
      ({(1/3 : ℝ), 2/3}) = 0 := by
    apply logWeightedMeasure_null_of_volume_pos_null
    · exact ((Set.finite_singleton (2/3 : ℝ)).insert _).measurableSet
    · refine MeasureTheory.measure_mono_null Set.inter_subset_left ?_
      exact h_bdry_vol_zero
  have h_bdry_ae : ∀ᵐ x ∂(logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)),
      x ≠ 1/3 ∧ x ≠ 2/3 := by
    have h_global : ∀ᵐ x ∂(logWeightedMeasure : MeasureTheory.Measure ℝ),
        x ≠ 1/3 ∧ x ≠ 2/3 := by
      rw [MeasureTheory.ae_iff]
      have h_eq : {x : ℝ | ¬(x ≠ 1/3 ∧ x ≠ 2/3)} = {(1/3 : ℝ), 2/3} := by
        ext y
        simp only [Set.mem_setOf_eq, ne_eq, not_and, not_not, Set.mem_insert_iff,
          Set.mem_singleton_iff]
        tauto
      rw [h_eq]
      exact h_bdry_meas_zero
    exact MeasureTheory.ae_restrict_of_ae h_global
  -- Pointwise distribution on the if-cascade.
  have h_pointwise_distribute : ∀ᵐ x ∂(logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)),
      T3_adjoint_action_func (c • f) x
        = c * T3_adjoint_action_func f x := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    have h_all := (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mp h_all_branches
    have h_bdry := (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mp h_bdry_ae
    filter_upwards [h_all, h_bdry] with x hx_all_imp hx_bdry_imp hx_Ioo
    have hx_all := hx_all_imp hx_Ioo
    have hx_bdry := hx_bdry_imp hx_Ioo
    obtain ⟨hx_ne_1_3, hx_ne_2_3⟩ := hx_bdry
    unfold T3_adjoint_action_func
    have h_b0_lo : ((0 : Fin 3).val : ℝ)/3 = 0 := by norm_num
    have h_b0_hi : (((0 : Fin 3).val : ℝ) + 1)/3 = 1/3 := by norm_num
    have h_b1_lo : ((1 : Fin 3).val : ℝ)/3 = 1/3 := by norm_num
    have h_b1_hi : (((1 : Fin 3).val : ℝ) + 1)/3 = 2/3 := by norm_num
    have h_b2_lo : ((2 : Fin 3).val : ℝ)/3 = 2/3 := by norm_num
    have h_b2_hi : (((2 : Fin 3).val : ℝ) + 1)/3 = 1 := by norm_num
    have h_v0 : ((0 : Fin 3).val : ℝ) = 0 := by norm_num
    have h_v1 : ((1 : Fin 3).val : ℝ) = 1 := by norm_num
    have h_v2 : ((2 : Fin 3).val : ℝ) = 2 := by norm_num
    -- split_ifs on the matching conditions in LHS and RHS simultaneously.
    split_ifs with h_op_a h_op_b
    · -- x ≤ 1/3 on both
      have hx1 : x < 1/3 ∨ x = 1/3 := lt_or_eq_of_le h_op_a
      have hx1' : x < 1/3 := hx1.resolve_right hx_ne_1_3
      have h_in_I0 : x ∈ Set.Ioo (((0 : Fin 3).val : ℝ)/3) ((((0 : Fin 3).val : ℝ) + 1)/3) := by
        rw [h_b0_lo, h_b0_hi]; exact ⟨hx_Ioo.1, hx1'⟩
      have h_distrib := hx_all 0 h_in_I0
      rw [h_v0] at h_distrib
      simp only [sub_zero] at h_distrib
      rw [h_distrib, smul_eq_mul]; ring
    · -- x > 1/3, x ≤ 2/3
      have hx1 : x > 1/3 := lt_of_not_ge h_op_a
      have hx2 : x < 2/3 ∨ x = 2/3 := lt_or_eq_of_le h_op_b
      have hx2' : x < 2/3 := hx2.resolve_right hx_ne_2_3
      have h_in_I1 : x ∈ Set.Ioo (((1 : Fin 3).val : ℝ)/3) ((((1 : Fin 3).val : ℝ) + 1)/3) := by
        rw [h_b1_lo, h_b1_hi]; exact ⟨hx1, hx2'⟩
      have h_distrib := hx_all 1 h_in_I1
      rw [h_v1] at h_distrib
      rw [h_distrib, smul_eq_mul]; ring
    · -- x > 1/3, x > 2/3
      have hx1 : x > 1/3 := lt_of_not_ge h_op_a
      have hx2 : x > 2/3 := lt_of_not_ge h_op_b
      have h_in_I2 : x ∈ Set.Ioo (((2 : Fin 3).val : ℝ)/3) ((((2 : Fin 3).val : ℝ) + 1)/3) := by
        rw [h_b2_lo, h_b2_hi]; exact ⟨hx2, hx_Ioo.2⟩
      have h_distrib := hx_all 2 h_in_I2
      rw [h_v2] at h_distrib
      rw [h_distrib, smul_eq_mul]; ring
  have h_lhs_to_smul : (T3_adjoint.apply (c • f)).toFunℝ
        =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)]
        (fun x => c * T3_adjoint_action_func f x) := by
    filter_upwards [h_lhs, h_pointwise_distribute] with x h1 h2
    rw [h1, h2]
  have h_rhs_to_smul : (c • T3_adjoint.apply f).toFunℝ
        =ᵐ[logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)]
        (fun x => c * T3_adjoint_action_func f x) := by
    filter_upwards [h_rhs_smul, h_apply_f] with x h_smul h_f
    rw [h_smul]
    show c • (T3_adjoint.apply f).toFunℝ x = _
    rw [h_f, smul_eq_mul]
  exact h_lhs_to_smul.trans h_rhs_to_smul.symm

/-! ## 4. Adjoint L²-squared bound (isometry) -/

/-- **Pointwise normSq of `T3_adjoint_action_func f x`** on each branch.
    Since the if-cascade picks ONE branch per `x`:

      `|T3* f(x)|² = |adjointWeight_k(x)|² · |f(3x - k)|²` on `I_k`.

    Combined with the indicator-decomposition, this gives the L²-squared
    identity via per-branch CoV (already established as
    `branch_logWeightedMeasure_norm_sq_eq_adjoint_real`). -/
private lemma T3_adjoint_normSq_pointwise_eq (f : LogWeightedL2) :
    ∀ᵐ x ∂(logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)),
      Complex.normSq (T3_adjoint_action_func f x)
        = ∑ k : Fin 3,
            (Set.Ioo ((k.val : ℝ)/3) (((k.val : ℝ) + 1)/3)).indicator
              (fun y => Complex.normSq ((adjointWeight k y : ℂ) *
                f.toFunℝ (3 * y - (k.val : ℝ)))) x := by
  -- {1/3, 2/3} AE.
  have h_bdry_vol_zero : (MeasureTheory.volume : MeasureTheory.Measure ℝ)
      ({(1/3 : ℝ), 2/3}) = 0 := by
    have h_subset : ({(1/3 : ℝ), 2/3} : Set ℝ) ⊆ {(1/3 : ℝ)} ∪ {(2/3 : ℝ)} := by
      intro y hy; simp at hy ⊢; tauto
    refine MeasureTheory.measure_mono_null h_subset ?_
    apply le_antisymm _ (zero_le _)
    calc (MeasureTheory.volume : MeasureTheory.Measure ℝ)
            (({(1/3 : ℝ)} : Set ℝ) ∪ {(2/3 : ℝ)})
        ≤ MeasureTheory.volume ({(1/3 : ℝ)} : Set ℝ) +
            MeasureTheory.volume ({(2/3 : ℝ)} : Set ℝ) :=
          MeasureTheory.measure_union_le _ _
      _ = 0 + 0 := by rw [Real.volume_singleton, Real.volume_singleton]
      _ = 0 := by ring
  have h_bdry_meas_zero : (logWeightedMeasure : MeasureTheory.Measure ℝ)
      ({(1/3 : ℝ), 2/3}) = 0 := by
    apply logWeightedMeasure_null_of_volume_pos_null
    · exact ((Set.finite_singleton (2/3 : ℝ)).insert _).measurableSet
    · refine MeasureTheory.measure_mono_null Set.inter_subset_left ?_
      exact h_bdry_vol_zero
  have h_bdry_ae : ∀ᵐ x ∂(logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)),
      x ≠ 1/3 ∧ x ≠ 2/3 := by
    have h_global : ∀ᵐ x ∂(logWeightedMeasure : MeasureTheory.Measure ℝ),
        x ≠ 1/3 ∧ x ≠ 2/3 := by
      rw [MeasureTheory.ae_iff]
      have h_eq : {x : ℝ | ¬(x ≠ 1/3 ∧ x ≠ 2/3)} = {(1/3 : ℝ), 2/3} := by
        ext y
        simp only [Set.mem_setOf_eq, ne_eq, not_and, not_not, Set.mem_insert_iff,
          Set.mem_singleton_iff]
        tauto
      rw [h_eq]
      exact h_bdry_meas_zero
    exact MeasureTheory.ae_restrict_of_ae h_global
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
  have h_bdry := (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mp h_bdry_ae
  filter_upwards [h_bdry] with x hx_bdry_imp hx_Ioo
  have hx_bdry := hx_bdry_imp hx_Ioo
  obtain ⟨hx_ne_1_3, hx_ne_2_3⟩ := hx_bdry
  unfold T3_adjoint_action_func
  simp only [Fin.sum_univ_three]
  -- Pre-compute branch range bounds.
  have h_b0_lo : ((0 : Fin 3).val : ℝ)/3 = 0 := by norm_num
  have h_b0_hi : (((0 : Fin 3).val : ℝ) + 1)/3 = 1/3 := by norm_num
  have h_b1_lo : ((1 : Fin 3).val : ℝ)/3 = 1/3 := by norm_num
  have h_b1_hi : (((1 : Fin 3).val : ℝ) + 1)/3 = 2/3 := by norm_num
  have h_b2_lo : ((2 : Fin 3).val : ℝ)/3 = 2/3 := by norm_num
  have h_b2_hi : (((2 : Fin 3).val : ℝ) + 1)/3 = 1 := by norm_num
  have h_v0 : ((0 : Fin 3).val : ℝ) = 0 := by norm_num
  have h_v1 : ((1 : Fin 3).val : ℝ) = 1 := by norm_num
  have h_v2 : ((2 : Fin 3).val : ℝ) = 2 := by norm_num
  -- |phaseFactorBase3Conj k|² = 1.
  have h_phase_sq : ∀ k : Fin 3,
      Complex.normSq (phaseFactorBase3Conj k) = 1 := by
    intro k
    rw [Complex.normSq_eq_norm_sq, phaseFactorBase3Conj_norm]
    norm_num
  rcases lt_trichotomy x (1/3 : ℝ) with hx1 | hx1 | hx1
  · -- x ∈ I_0
    rw [if_pos hx1.le]
    have h_in_I0 : x ∈ Set.Ioo (((0 : Fin 3).val : ℝ)/3) ((((0 : Fin 3).val : ℝ) + 1)/3) := by
      rw [h_b0_lo, h_b0_hi]; exact ⟨hx_Ioo.1, hx1⟩
    have h_notin_I1 : x ∉ Set.Ioo (((1 : Fin 3).val : ℝ)/3) ((((1 : Fin 3).val : ℝ) + 1)/3) := by
      rw [h_b1_lo, h_b1_hi]; simp only [Set.mem_Ioo, not_and, not_lt]; intro h; linarith
    have h_notin_I2 : x ∉ Set.Ioo (((2 : Fin 3).val : ℝ)/3) ((((2 : Fin 3).val : ℝ) + 1)/3) := by
      rw [h_b2_lo, h_b2_hi]; simp only [Set.mem_Ioo, not_and, not_lt]; intro h; linarith
    rw [Set.indicator_of_mem h_in_I0, Set.indicator_of_notMem h_notin_I1,
        Set.indicator_of_notMem h_notin_I2]
    rw [h_v0]
    simp only [sub_zero]
    rw [mul_assoc, Complex.normSq_mul, h_phase_sq, one_mul]
    ring
  · exact absurd hx1 hx_ne_1_3
  · have h_op_1 : ¬(x ≤ 1/3) := not_le.mpr hx1
    rcases lt_trichotomy x (2/3 : ℝ) with hx2 | hx2 | hx2
    · rw [if_neg h_op_1, if_pos hx2.le]
      have h_notin_I0 : x ∉ Set.Ioo (((0 : Fin 3).val : ℝ)/3) ((((0 : Fin 3).val : ℝ) + 1)/3) := by
        rw [h_b0_lo, h_b0_hi]; simp only [Set.mem_Ioo, not_and, not_lt]; intro _; linarith
      have h_in_I1 : x ∈ Set.Ioo (((1 : Fin 3).val : ℝ)/3) ((((1 : Fin 3).val : ℝ) + 1)/3) := by
        rw [h_b1_lo, h_b1_hi]; exact ⟨hx1, hx2⟩
      have h_notin_I2 : x ∉ Set.Ioo (((2 : Fin 3).val : ℝ)/3) ((((2 : Fin 3).val : ℝ) + 1)/3) := by
        rw [h_b2_lo, h_b2_hi]; simp only [Set.mem_Ioo, not_and, not_lt]; intro h; linarith
      rw [Set.indicator_of_notMem h_notin_I0, Set.indicator_of_mem h_in_I1,
          Set.indicator_of_notMem h_notin_I2]
      rw [h_v1]
      rw [mul_assoc, Complex.normSq_mul, h_phase_sq, one_mul]
      ring
    · exact absurd hx2 hx_ne_2_3
    · rw [if_neg h_op_1, if_neg (not_le.mpr hx2)]
      have h_notin_I0 : x ∉ Set.Ioo (((0 : Fin 3).val : ℝ)/3) ((((0 : Fin 3).val : ℝ) + 1)/3) := by
        rw [h_b0_lo, h_b0_hi]; simp only [Set.mem_Ioo, not_and, not_lt]; intro _; linarith
      have h_notin_I1 : x ∉ Set.Ioo (((1 : Fin 3).val : ℝ)/3) ((((1 : Fin 3).val : ℝ) + 1)/3) := by
        rw [h_b1_lo, h_b1_hi]; simp only [Set.mem_Ioo, not_and, not_lt]; intro _; linarith
      have h_in_I2 : x ∈ Set.Ioo (((2 : Fin 3).val : ℝ)/3) ((((2 : Fin 3).val : ℝ) + 1)/3) := by
        rw [h_b2_lo, h_b2_hi]; exact ⟨hx2, hx_Ioo.2⟩
      rw [Set.indicator_of_notMem h_notin_I0, Set.indicator_of_notMem h_notin_I1,
          Set.indicator_of_mem h_in_I2]
      rw [h_v2]
      rw [mul_assoc, Complex.normSq_mul, h_phase_sq, one_mul]
      ring

/-- **★★★ L²-squared isometry-type bound for `T3_adjoint`** ★★★

      `∫_(0,1) |T3* f(x)|² ∂μ_log = ∫_(0,1) |f(x)|² ∂μ_log`.

    Even sharper than the contracting case (which had Cauchy-Schwarz
    slack producing `≤` instead of `=`). For the adjoint, the if-cascade
    activates exactly one branch per `x`, so pointwise we have an
    equality, no Cauchy-Schwarz needed. After summing over branches
    (each contributing `(1/3)·∫|f|²`), the total equals `∫|f|²`. -/
theorem T3AdjointNormSquared_eq (f : LogWeightedL2) :
    (∫ x in Set.Ioo (0:ℝ) 1,
        Complex.normSq (T3_adjoint_action_func f x)
        ∂logWeightedMeasure)
    = (∫ x in Set.Ioo (0:ℝ) 1,
        Complex.normSq (f.toFunℝ x)
        ∂logWeightedMeasure) := by
  -- Step 1: rewrite LHS via pointwise indicator-sum equality.
  have h_eq_ae := T3_adjoint_normSq_pointwise_eq f
  have h_step1 : (∫ x in Set.Ioo (0:ℝ) 1,
        Complex.normSq (T3_adjoint_action_func f x)
        ∂logWeightedMeasure)
      = ∫ x in Set.Ioo (0:ℝ) 1,
        (∑ k : Fin 3,
          (Set.Ioo ((k.val : ℝ)/3) (((k.val : ℝ) + 1)/3)).indicator
            (fun y => Complex.normSq ((adjointWeight k y : ℂ) *
              f.toFunℝ (3 * y - (k.val : ℝ)))) x)
        ∂logWeightedMeasure := by
    exact MeasureTheory.integral_congr_ae h_eq_ae
  -- Step 2: integrate the sum: ∫∑ = ∑∫.
  -- Each summand is the indicator of I_k of a positive ℝ-valued integrable function.
  have h_int_summand : ∀ k : Fin 3, MeasureTheory.Integrable
      (fun x => (Set.Ioo ((k.val : ℝ)/3) (((k.val : ℝ) + 1)/3)).indicator
        (fun y => Complex.normSq ((adjointWeight k y : ℂ) *
          f.toFunℝ (3 * y - (k.val : ℝ)))) x)
      (logWeightedMeasure.restrict (Set.Ioo (0:ℝ) 1)) := by
    intro k
    -- Restrict integrability to I_k, lift via indicator.
    have h_branch_normSq_int : MeasureTheory.IntegrableOn
        (fun x => Complex.normSq ((adjointWeight k x : ℂ) *
          f.toFunℝ (3 * x - (k.val : ℝ))))
        (Set.Ioo ((k.val : ℝ)/3) (((k.val : ℝ) + 1)/3)) logWeightedMeasure := by
      have hf := LogWeightedL2.MemLp2_universal f
      have hMemLp := branch_function_MemLp2_adjoint k f hf
      have h_int_normSq := (MeasureTheory.memLp_two_iff_integrable_sq_norm
          hMemLp.1).mp hMemLp
      have h_eq : (fun x : ℝ => ‖(adjointWeight k x : ℂ) *
                  f.toFunℝ (3 * x - (k.val : ℝ))‖ ^ 2)
                = (fun x : ℝ => Complex.normSq
                    ((adjointWeight k x : ℂ) * f.toFunℝ (3 * x - (k.val : ℝ)))) := by
        funext x
        exact (Complex.normSq_eq_norm_sq _).symm
      rw [h_eq] at h_int_normSq
      unfold MeasureTheory.IntegrableOn
      exact h_int_normSq
    -- IntegrableOn on I_k ⇒ Integrable of indicator on μ_log↾(0,1).
    -- Use `Integrable.indicator` plus restriction lifting.
    rw [MeasureTheory.integrable_indicator_iff measurableSet_Ioo]
    -- Goal: IntegrableOn (...) I_k (μ_log↾(0,1)).
    -- Use (μ_log↾(0,1))↾I_k = μ_log↾I_k.
    unfold MeasureTheory.IntegrableOn
    rw [logWeighted_restrict_Ik_eq k]
    exact h_branch_normSq_int
  have h_step2 : ∫ x in Set.Ioo (0:ℝ) 1,
        (∑ k : Fin 3,
          (Set.Ioo ((k.val : ℝ)/3) (((k.val : ℝ) + 1)/3)).indicator
            (fun y => Complex.normSq ((adjointWeight k y : ℂ) *
              f.toFunℝ (3 * y - (k.val : ℝ)))) x)
        ∂logWeightedMeasure
      = ∑ k : Fin 3, ∫ x in Set.Ioo (0:ℝ) 1,
          (Set.Ioo ((k.val : ℝ)/3) (((k.val : ℝ) + 1)/3)).indicator
            (fun y => Complex.normSq ((adjointWeight k y : ℂ) *
              f.toFunℝ (3 * y - (k.val : ℝ)))) x
          ∂logWeightedMeasure := by
    rw [MeasureTheory.integral_finset_sum Finset.univ
        (fun k _ => h_int_summand k)]
  -- Step 3: rewrite each indicator integral as the integral over I_k.
  have h_step3 : ∀ k : Fin 3,
      ∫ x in Set.Ioo (0:ℝ) 1,
          (Set.Ioo ((k.val : ℝ)/3) (((k.val : ℝ) + 1)/3)).indicator
            (fun y => Complex.normSq ((adjointWeight k y : ℂ) *
              f.toFunℝ (3 * y - (k.val : ℝ)))) x
          ∂logWeightedMeasure
      = ∫ x in Set.Ioo ((k.val : ℝ)/3) (((k.val : ℝ) + 1)/3),
          Complex.normSq ((adjointWeight k x : ℂ) *
            f.toFunℝ (3 * x - (k.val : ℝ)))
          ∂logWeightedMeasure := by
    intro k
    rw [MeasureTheory.integral_indicator measurableSet_Ioo]
    rw [logWeighted_restrict_Ik_eq k]
  -- Step 4: per-branch CoV gives each branch = (1/3) · ∫|f|².
  have h_step4 : ∑ k : Fin 3,
      ∫ x in Set.Ioo ((k.val : ℝ)/3) (((k.val : ℝ) + 1)/3),
          Complex.normSq ((adjointWeight k x : ℂ) *
            f.toFunℝ (3 * x - (k.val : ℝ)))
          ∂logWeightedMeasure
      = ∑ _ : Fin 3, (1 / 3 : ℝ) *
          ∫ u in Set.Ioo (0:ℝ) 1, Complex.normSq (f.toFunℝ u) ∂logWeightedMeasure := by
    apply Finset.sum_congr rfl
    intros k _
    exact branch_logWeightedMeasure_norm_sq_eq_adjoint_real k f
  -- Step 5: sum of 3 copies of (1/3) · ∫ = ∫.
  have h_step5 : ∑ _ : Fin 3, (1 / 3 : ℝ) *
      ∫ u in Set.Ioo (0:ℝ) 1, Complex.normSq (f.toFunℝ u) ∂logWeightedMeasure
      = ∫ u in Set.Ioo (0:ℝ) 1, Complex.normSq (f.toFunℝ u) ∂logWeightedMeasure := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    ring
  -- Assemble.
  calc (∫ x in Set.Ioo (0:ℝ) 1,
        Complex.normSq (T3_adjoint_action_func f x) ∂logWeightedMeasure)
      = ∫ x in Set.Ioo (0:ℝ) 1,
        (∑ k : Fin 3,
          (Set.Ioo ((k.val : ℝ)/3) (((k.val : ℝ) + 1)/3)).indicator
            (fun y => Complex.normSq ((adjointWeight k y : ℂ) *
              f.toFunℝ (3 * y - (k.val : ℝ)))) x)
        ∂logWeightedMeasure := h_step1
    _ = ∑ k : Fin 3, ∫ x in Set.Ioo (0:ℝ) 1,
          (Set.Ioo ((k.val : ℝ)/3) (((k.val : ℝ) + 1)/3)).indicator
            (fun y => Complex.normSq ((adjointWeight k y : ℂ) *
              f.toFunℝ (3 * y - (k.val : ℝ)))) x
          ∂logWeightedMeasure := h_step2
    _ = ∑ k : Fin 3, ∫ x in Set.Ioo ((k.val : ℝ)/3) (((k.val : ℝ) + 1)/3),
          Complex.normSq ((adjointWeight k x : ℂ) *
            f.toFunℝ (3 * x - (k.val : ℝ)))
          ∂logWeightedMeasure := Finset.sum_congr rfl (fun k _ => h_step3 k)
    _ = ∑ _ : Fin 3, (1 / 3 : ℝ) *
          ∫ u in Set.Ioo (0:ℝ) 1, Complex.normSq (f.toFunℝ u) ∂logWeightedMeasure := h_step4
    _ = ∫ u in Set.Ioo (0:ℝ) 1, Complex.normSq (f.toFunℝ u) ∂logWeightedMeasure := h_step5

/-! ## 5. Adjoint `Lp`-norm bound -/

/-- **Bridge**: `‖T3_adjoint.apply f‖² = ∫ normSq(T3_adjoint_action_func f)`.
    Mirror of `T3_apply_lp_norm_sq_eq_integral_pointwise`. -/
private lemma T3_adjoint_apply_lp_norm_sq_eq_integral_pointwise (f : LogWeightedL2) :
    ‖T3_adjoint.apply f‖ ^ 2 =
    ∫ x in Set.Ioo (0:ℝ) 1,
        Complex.normSq (T3_adjoint_action_func f x)
        ∂logWeightedMeasure := by
  rw [logWeightedL2_lp_norm_sq_eq_integral_normSq (T3_adjoint.apply f)]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [T3_adjoint_toFunℝ_Ioo_unconditional f] with x hx
  rw [hx]

/-- **★★★ `T3AdjointNormBound_proved`** ★★★

    Mayer 1991 adjoint contractivity (in fact, isometry) on `L²([0,1], dx/x)`.
    Composes `T3AdjointNormSquared_eq` with the Lp-bridge. -/
theorem T3AdjointNormBound_proved : T3AdjointNormBound := by
  refine ⟨fun f => ?_⟩
  have h_nn_lhs : (0 : ℝ) ≤ ‖T3_adjoint.apply f‖ := norm_nonneg _
  have h_nn_rhs : (0 : ℝ) ≤ ‖f‖ := norm_nonneg _
  have h_sq_lp : ‖T3_adjoint.apply f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [T3_adjoint_apply_lp_norm_sq_eq_integral_pointwise f,
        logWeightedL2_lp_norm_sq_eq_integral_normSq f]
    -- Equality, so ≤ holds.
    exact le_of_eq (T3AdjointNormSquared_eq f)
  have h1 : Real.sqrt (‖T3_adjoint.apply f‖ ^ 2) ≤ Real.sqrt (‖f‖ ^ 2) :=
    Real.sqrt_le_sqrt h_sq_lp
  rwa [Real.sqrt_sq h_nn_lhs, Real.sqrt_sq h_nn_rhs] at h1

/-! ## 6. The factored package -/

/-- **★★★ `T3AdjointLinearStructureFactored` proven UNCONDITIONALLY** ★★★

    Packages the three adjoint ingredients (additivity, homogeneity,
    contractivity) all proven above. -/
theorem T3AdjointLinearStructureFactored_proved : T3AdjointLinearStructureFactored where
  add := T3AdjointLinearStructure_add_proved
  smul := T3AdjointLinearStructure_smul_proved
  norm_le := T3AdjointNormBound_proved.norm_le

/-! ## 7. Full discharge of `T3SymCLMSymmetricWitness` -/

/-- **★★★★ `T3SymCLMSymmetricWitness` PROVEN UNCONDITIONALLY** ★★★★

    Composes:
      * `T3NormSquaredBound_proved` (contracting half, `T3NormSquaredBoundDischarge.lean`),
      * `T3AdjointLinearStructureFactored_proved` (expanding half, THIS file).
    Both halves' analytic content is now discharged with ZERO project
    axioms and ZERO `sorry`. -/
theorem T3SymCLMSymmetricWitness_proved_unconditional :
    T3SymCLMSymmetricWitness :=
  T3SymCLMSymmetricWitness_from_t3adjoint_only
    T3AdjointLinearStructureFactored_proved

/-! ## 8. Axiom-freeness verification -/

#print axioms T3AdjointLinearStructure_add_proved
#print axioms T3AdjointLinearStructure_smul_proved
#print axioms T3AdjointNormSquared_eq
#print axioms T3AdjointNormBound_proved
#print axioms T3AdjointLinearStructureFactored_proved
#print axioms T3SymCLMSymmetricWitness_proved_unconditional

end PrincipiaTractalis
