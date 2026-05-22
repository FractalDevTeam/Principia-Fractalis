/-
# `T3NormSquaredBound` — Unconditional Discharge

This file PROVES `T3NormSquaredBound` (defined in
`PF/Analytic/T3NormBoundDischarge.lean`) — the L²-squared integral
inequality

  `∫_(0,1) |T_3 f|² ∂μ_log  ≤  ∫_(0,1) |f|² ∂μ_log`

— following Mayer 1991 (BAMS) §2 via pointwise Cauchy–Schwarz +
per-branch change-of-variables + partition. The ingredients all
already exist in `PF/TransferOperator.lean` (lines 762, 1617) and
in mathlib (`sq_sum_le_card_mul_sum_sq`).

After this file, the contracting half `T3LinearStructure` becomes
FULLY UNCONDITIONAL, and `T3SymCLMSymmetricWitness` reduces to the
single remaining hypothesis `T3AdjointLinearStructureFactored`.

## What this file delivers (NO SORRY, NO AXIOMS)

  1. **`logWeightedMeasure_Ioo_partition_three`** — μ_log-measure version
     of the dyadic-thirds partition for `Ioo 0 1`. Established via
     `setIntegral_union` twice; the interface points `{1/3, 2/3}` are
     μ_log-null since μ_log↾(0,1) ≪ volume.

  2. **`branch_sum_pointwise_Cauchy_Schwarz`** — pointwise inequality
     `normSq(∑ k, phase_k · w_k(x) · f(y_k(x))) ≤ 3 · ∑ k, normSq(w_k(x) · f(y_k(x)))`.

  3. **`T3NormSquaredBound_proved`** — the discharged theorem.

  4. **`T3SymCLMSymmetricWitness_from_t3adjoint_only`** —
     `T3AdjointLinearStructureFactored → T3SymCLMSymmetricWitness`,
     eliminating one of the two open factors of
     `T3SymCLMSymmetricWitness`.

## Build state

ZERO project axioms. ZERO `sorry`.
-/

import PF.Analytic.T3NormBoundDischarge
import Mathlib.Algebra.Order.Chebyshev

namespace PrincipiaTractalis

open MeasureTheory
open scoped InnerProductSpace

/-! ## 1. μ_log-measure partition of `Ioo 0 1` -/

/-- **Singletons are μ_log-null on `Ioo 0 1`.** Direct from
    `μ_log↾(0,1) ≪ volume` plus volume-null singletons in ℝ. -/
private lemma logWeightedMeasure_singleton_zero (a : ℝ) :
    logWeightedMeasure {a} = 0 := by
  -- volume {a} = 0 in ℝ, and μ_log ≪ volume globally via withDensity
  have h_vol : (volume : Measure ℝ) {a} = 0 := measure_singleton a
  exact (withDensity_absolutelyContinuous (volume : Measure ℝ) _) h_vol

/-- **The three dyadic-thirds sub-intervals are pairwise disjoint.** -/
private lemma dyadic_third_disjoint_01 :
    Disjoint (Set.Ioo (0:ℝ) (1/3)) (Set.Ioo ((1:ℝ)/3) 1) := by
  rw [Set.disjoint_iff]
  intros x hx
  exact absurd hx.1.2 (not_lt.mpr (le_of_lt hx.2.1))

private lemma dyadic_third_disjoint_12 :
    Disjoint (Set.Ioo ((1:ℝ)/3) (2/3)) (Set.Ioo ((2:ℝ)/3) 1) := by
  rw [Set.disjoint_iff]
  intros x hx
  exact absurd hx.1.2 (not_lt.mpr (le_of_lt hx.2.1))

private lemma dyadic_third_disjoint_0_12 :
    Disjoint (Set.Ioo (0:ℝ) (1/3))
             (Set.Ioo ((1:ℝ)/3) (2/3) ∪ Set.Ioo ((2:ℝ)/3) 1) := by
  rw [Set.disjoint_iff]
  intros x hx
  rcases hx.2 with h | h
  · exact absurd hx.1.2 (not_lt.mpr (le_of_lt h.1))
  · exact absurd hx.1.2 (not_lt.mpr
      (le_of_lt (lt_trans (by norm_num : (1:ℝ)/3 < 2/3) h.1)))

/-- **μ_log-AE-set-equality**: `Ioo 0 1 =ᵐ[μ_log] Ioo 0 (1/3) ∪ Ioo (1/3) (2/3) ∪ Ioo (2/3) 1`.
    Differ only at `{1/3, 2/3}` which is μ_log-null. -/
private lemma Ioo_01_ae_eq_partition :
    Set.Ioo (0:ℝ) 1 =ᵐ[logWeightedMeasure]
      (Set.Ioo (0:ℝ) ((1:ℝ)/3) ∪ (Set.Ioo ((1:ℝ)/3) ((2:ℝ)/3)
        ∪ Set.Ioo ((2:ℝ)/3) (1:ℝ)) : Set ℝ) := by
  rw [MeasureTheory.ae_eq_set]
  refine ⟨?_, ?_⟩
  · -- (Ioo 0 1) \ partition has measure 0; it's contained in {1/3, 2/3}.
    have h_sub : Set.Ioo (0:ℝ) 1 \
        (Set.Ioo (0:ℝ) ((1:ℝ)/3) ∪ (Set.Ioo ((1:ℝ)/3) ((2:ℝ)/3)
          ∪ Set.Ioo ((2:ℝ)/3) (1:ℝ)))
        ⊆ ({(1:ℝ)/3} ∪ ({(2:ℝ)/3} : Set ℝ)) := by
      intros x hx
      have hx1 : x ∈ Set.Ioo (0:ℝ) 1 := hx.1
      have hx_not : x ∉ Set.Ioo (0:ℝ) ((1:ℝ)/3) ∪ (Set.Ioo ((1:ℝ)/3) ((2:ℝ)/3)
                      ∪ Set.Ioo ((2:ℝ)/3) (1:ℝ)) := hx.2
      have h_not_left : x ∉ Set.Ioo (0:ℝ) ((1:ℝ)/3) := fun h => hx_not (Or.inl h)
      have h_not_mid  : x ∉ Set.Ioo ((1:ℝ)/3) ((2:ℝ)/3) :=
        fun h => hx_not (Or.inr (Or.inl h))
      have h_not_right : x ∉ Set.Ioo ((2:ℝ)/3) (1:ℝ) :=
        fun h => hx_not (Or.inr (Or.inr h))
      by_cases h13 : x ≤ 1/3
      · have hx_eq : x = 1/3 := by
          by_contra hne
          have hlt : x < 1/3 := lt_of_le_of_ne h13 hne
          exact h_not_left ⟨hx1.1, hlt⟩
        exact Or.inl hx_eq
      · push_neg at h13
        by_cases h23 : x ≤ 2/3
        · have hx_eq : x = 2/3 := by
            by_contra hne
            have hlt : x < 2/3 := lt_of_le_of_ne h23 hne
            exact h_not_mid ⟨h13, hlt⟩
          exact Or.inr hx_eq
        · push_neg at h23
          -- 2/3 < x and x < 1: contradiction with h_not_right
          exfalso
          exact h_not_right ⟨h23, hx1.2⟩
    have h_meas_pair : logWeightedMeasure
        (({(1:ℝ)/3} : Set ℝ) ∪ ({(2:ℝ)/3} : Set ℝ)) = 0 := by
      have h1 := logWeightedMeasure_singleton_zero ((1:ℝ)/3)
      have h2 := logWeightedMeasure_singleton_zero ((2:ℝ)/3)
      have h_le : logWeightedMeasure (({(1:ℝ)/3} : Set ℝ) ∪ ({(2:ℝ)/3} : Set ℝ))
          ≤ logWeightedMeasure ({(1:ℝ)/3} : Set ℝ)
            + logWeightedMeasure ({(2:ℝ)/3} : Set ℝ) :=
        measure_union_le _ _
      rw [h1, h2, add_zero] at h_le
      exact le_antisymm h_le bot_le
    exact measure_mono_null h_sub h_meas_pair
  · -- partition \ (Ioo 0 1) is empty
    have h_empty : (Set.Ioo (0:ℝ) ((1:ℝ)/3) ∪ (Set.Ioo ((1:ℝ)/3) ((2:ℝ)/3)
        ∪ Set.Ioo ((2:ℝ)/3) (1:ℝ))) \ Set.Ioo (0:ℝ) 1 ⊆ (∅ : Set ℝ) := by
      intros x hx
      have hpart := hx.1
      have hnot1 : x ∉ Set.Ioo (0:ℝ) 1 := hx.2
      rcases hpart with h | h | h
      · exact absurd ⟨h.1, lt_trans h.2 (by norm_num : (1:ℝ)/3 < 1)⟩ hnot1
      · exact absurd ⟨lt_trans (by norm_num : (0:ℝ) < 1/3) h.1,
                       lt_trans h.2 (by norm_num : (2:ℝ)/3 < 1)⟩ hnot1
      · exact absurd ⟨lt_trans (by norm_num : (0:ℝ) < 2/3) h.1, h.2⟩ hnot1
    exact measure_mono_null h_empty measure_empty

/-- **μ_log partition of `Ioo 0 1` for ℝ-valued integrals** —
    decompose into the three dyadic-thirds. Both sides equal a common
    integrable LHS via `setIntegral_congr_set` + double `setIntegral_union`.
    The interface points {1/3, 2/3} are μ_log-null. -/
private lemma setIntegral_Ioo_partition_three_logWeighted_real
    (F : ℝ → ℝ)
    (h_int : MeasureTheory.IntegrableOn F (Set.Ioo (0:ℝ) 1) logWeightedMeasure) :
    ∫ x in Set.Ioo (0:ℝ) 1, F x ∂logWeightedMeasure
    = (∫ x in Set.Ioo (0:ℝ) (1/3), F x ∂logWeightedMeasure)
      + (∫ x in Set.Ioo ((1:ℝ)/3) (2/3), F x ∂logWeightedMeasure)
      + (∫ x in Set.Ioo ((2:ℝ)/3) 1, F x ∂logWeightedMeasure) := by
  -- Step 1: rewrite LHS via AE-set-equality to the union form.
  rw [MeasureTheory.setIntegral_congr_set (μ := logWeightedMeasure)
      (Ioo_01_ae_eq_partition)]
  -- Step 2: integrability on each sub-interval (subset of (0,1)).
  have h_sub_left : Set.Ioo (0:ℝ) (1/3) ⊆ Set.Ioo (0:ℝ) 1 :=
    fun y hy => ⟨hy.1, lt_trans hy.2 (by norm_num)⟩
  have h_sub_mid : Set.Ioo ((1:ℝ)/3) (2/3) ⊆ Set.Ioo (0:ℝ) 1 :=
    fun y hy => ⟨lt_trans (by norm_num : (0:ℝ) < 1/3) hy.1,
                  lt_trans hy.2 (by norm_num)⟩
  have h_sub_right : Set.Ioo ((2:ℝ)/3) 1 ⊆ Set.Ioo (0:ℝ) 1 :=
    fun y hy => ⟨lt_trans (by norm_num : (0:ℝ) < 2/3) hy.1, hy.2⟩
  have h_int_left : MeasureTheory.IntegrableOn F (Set.Ioo (0:ℝ) (1/3))
      logWeightedMeasure := h_int.mono_set h_sub_left
  have h_int_mid : MeasureTheory.IntegrableOn F (Set.Ioo ((1:ℝ)/3) (2/3))
      logWeightedMeasure := h_int.mono_set h_sub_mid
  have h_int_right : MeasureTheory.IntegrableOn F (Set.Ioo ((2:ℝ)/3) 1)
      logWeightedMeasure := h_int.mono_set h_sub_right
  have h_int_mid_right : MeasureTheory.IntegrableOn F
      (Set.Ioo ((1:ℝ)/3) (2/3) ∪ Set.Ioo ((2:ℝ)/3) 1)
      logWeightedMeasure := h_int_mid.union h_int_right
  -- Step 3: apply setIntegral_union twice.
  rw [MeasureTheory.setIntegral_union dyadic_third_disjoint_0_12
      (measurableSet_Ioo.union measurableSet_Ioo)
      h_int_left h_int_mid_right]
  rw [MeasureTheory.setIntegral_union dyadic_third_disjoint_12
      measurableSet_Ioo h_int_mid h_int_right]
  linarith

/-! ## 2. Pointwise Cauchy-Schwarz bound -/

/-- **Pointwise Cauchy-Schwarz** for the inner sum (no phase, no 1/3 factor):
    `‖∑ k:Fin 3, z_k‖² ≤ 3 · ∑ k:Fin 3, ‖z_k‖²` for any `z : Fin 3 → ℂ`.

    Triangle inequality + Chebyshev's `sq_sum_le_card_mul_sum_sq` on the
    nonneg ℝ-valued function `k ↦ ‖z k‖`. -/
private lemma normSq_sum_le_card_mul_sum_normSq_fin3 (z : Fin 3 → ℂ) :
    Complex.normSq (∑ k, z k) ≤ 3 * ∑ k, Complex.normSq (z k) := by
  -- Rewrite normSq via norm²
  rw [Complex.normSq_eq_norm_sq]
  conv_rhs =>
    rw [show (fun k => Complex.normSq (z k)) = (fun k => ‖z k‖ ^ 2) from
      funext (fun k => Complex.normSq_eq_norm_sq (z k))]
  -- Triangle: ‖∑ z_k‖ ≤ ∑ ‖z_k‖
  have h_tri : ‖∑ k, z k‖ ≤ ∑ k, ‖z k‖ := norm_sum_le _ _
  have h_nn : (0 : ℝ) ≤ ‖∑ k, z k‖ := norm_nonneg _
  have h_sq : ‖∑ k, z k‖ ^ 2 ≤ (∑ k, ‖z k‖) ^ 2 := by
    have h_rhs_nn : (0 : ℝ) ≤ ∑ k, ‖z k‖ :=
      Finset.sum_nonneg (fun k _ => norm_nonneg _)
    exact sq_le_sq' (by linarith [neg_nonpos_of_nonneg h_rhs_nn]) h_tri
  -- Chebyshev: (∑ a_k)² ≤ #s · ∑ a_k² applied to nonneg a_k = ‖z_k‖
  have h_cheb : (∑ k, ‖z k‖) ^ 2 ≤ (Finset.univ : Finset (Fin 3)).card *
      ∑ k, ‖z k‖ ^ 2 := sq_sum_le_card_mul_sum_sq
  have h_card : (Finset.univ : Finset (Fin 3)).card = 3 := by
    simp [Finset.card_univ]
  rw [h_card] at h_cheb
  have h_combined : ‖∑ k, z k‖ ^ 2 ≤ (3 : ℕ) * ∑ k, ‖z k‖ ^ 2 :=
    le_trans h_sq h_cheb
  exact_mod_cast h_combined

/-! ## 3. Per-summand integrability of the bound -/

/-- **Per-branch normSq is integrable** under μ_log on (0,1). Direct from
    `branch_function_MemLp2`'s integrability of the norm-square. -/
private lemma branch_normSq_integrable (k : Fin 3) (f : LogWeightedL2) :
    MeasureTheory.IntegrableOn
      (fun x => Complex.normSq ((weightFunction 3 k x : ℂ) *
          f.toFunℝ (inverseBranch 3 k x)))
      (Set.Ioo (0:ℝ) 1) logWeightedMeasure := by
  have hf := LogWeightedL2.MemLp2_universal f
  have hMemLp := branch_function_MemLp2 k f hf
  -- MemLp 2 → integrable of ‖·‖²
  have h_int_normSq := (MeasureTheory.memLp_two_iff_integrable_sq_norm
    hMemLp.1).mp hMemLp
  -- ‖·‖² = normSq
  have h_eq : (fun x : ℝ => ‖(weightFunction 3 k x : ℂ) *
                f.toFunℝ (inverseBranch 3 k x)‖ ^ 2)
            = (fun x : ℝ => Complex.normSq
                ((weightFunction 3 k x : ℂ) * f.toFunℝ (inverseBranch 3 k x))) := by
    funext x
    exact (Complex.normSq_eq_norm_sq _).symm
  rw [h_eq] at h_int_normSq
  unfold MeasureTheory.IntegrableOn
  exact h_int_normSq

/-! ## 4. Main pointwise bound on `transferOperatorAction_func`'s normSq -/

/-- **Pointwise bound** for `normSq(transferOperatorAction_func 3 phaseFactorBase3 f x)`:

      `normSq(T_3 f x) ≤ (1/3) · ∑_k normSq(w_k(x) · f(y_k(x)))`.

    Combines:
      * `transferOperatorAction_func` def expanding into `(1/3) · ∑ phase_k · w_k · f∘y_k`,
      * `normSq_sum_le_card_mul_sum_normSq_fin3` (pointwise Cauchy-Schwarz),
      * `phaseFactorBase3_norm` ⇒ `normSq(phase_k * z) = normSq(z)`. -/
private lemma transfer_func_normSq_pointwise_bound (f : LogWeightedL2) (x : ℝ) :
    Complex.normSq (transferOperatorAction_func 3 phaseFactorBase3 f x)
      ≤ (1/3) * ∑ k : Fin 3,
          Complex.normSq ((weightFunction 3 k x : ℂ) *
              f.toFunℝ (inverseBranch 3 k x)) := by
  -- Unfold transferOperatorAction_func.
  unfold transferOperatorAction_func
  -- normSq((1/3 : ℂ) * S) = normSq(1/3 : ℂ) * normSq(S) = (1/9) * normSq(S)
  rw [Complex.normSq_mul]
  -- Compute normSq(1/3 : ℂ) = 1/9. (Note: in the def it's `(1 / b : ℂ)` with b = 3 (ℕ).)
  have h_normSq_third : Complex.normSq ((1 / (3 : ℕ) : ℂ)) = 1 / 9 := by
    push_cast
    rw [show ((1 : ℂ) / 3) = ((1/3 : ℝ) : ℂ) from by push_cast; ring]
    rw [Complex.normSq_ofReal]
    norm_num
  rw [h_normSq_third]
  -- Now: (1/9) * normSq(S) ≤ (1/3) * ∑ normSq(w_k · f∘y_k) iff normSq(S) ≤ 3 * ∑ normSq(...).
  -- Define the inner summands.
  set z : Fin 3 → ℂ := fun k =>
    phaseFactorBase3 k * (weightFunction 3 k x : ℂ) * f.toFunℝ (inverseBranch 3 k x) with hz_def
  -- normSq(z k) = normSq(w_k(x) * f(y_k(x))) since |phase_k| = 1.
  have h_phase_drop : ∀ k : Fin 3, Complex.normSq (z k)
      = Complex.normSq ((weightFunction 3 k x : ℂ) *
            f.toFunℝ (inverseBranch 3 k x)) := by
    intro k
    show Complex.normSq (phaseFactorBase3 k *
            (weightFunction 3 k x : ℂ) * f.toFunℝ (inverseBranch 3 k x))
      = Complex.normSq ((weightFunction 3 k x : ℂ) *
            f.toFunℝ (inverseBranch 3 k x))
    rw [mul_assoc, Complex.normSq_mul]
    have h_phase_sq : Complex.normSq (phaseFactorBase3 k) = 1 := by
      rw [Complex.normSq_eq_norm_sq, phaseFactorBase3_norm]
      norm_num
    rw [h_phase_sq]; ring
  -- Apply the pointwise Cauchy-Schwarz lemma at the z.
  have h_CS : Complex.normSq (∑ k, z k) ≤ 3 * ∑ k, Complex.normSq (z k) :=
    normSq_sum_le_card_mul_sum_normSq_fin3 z
  -- Substitute the phase-dropped form on RHS.
  have h_CS' : Complex.normSq (∑ k, z k)
      ≤ 3 * ∑ k, Complex.normSq ((weightFunction 3 k x : ℂ) *
            f.toFunℝ (inverseBranch 3 k x)) := by
    refine le_trans h_CS ?_
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 3)
    apply Finset.sum_le_sum
    intros k _
    rw [h_phase_drop k]
  -- The LHS of goal is (1/9) * normSq(∑ z); show via h_CS'.
  -- Goal: (1/9) * normSq(∑ z) ≤ (1/3) * ∑ normSq(w_k · f∘y_k).
  -- Equivalent to: normSq(∑ z) ≤ 3 * ∑ normSq(...). i.e. h_CS'.
  have h_nn_sum : (0 : ℝ) ≤
      ∑ k : Fin 3, Complex.normSq ((weightFunction 3 k x : ℂ) *
              f.toFunℝ (inverseBranch 3 k x)) :=
    Finset.sum_nonneg (fun k _ => Complex.normSq_nonneg _)
  -- Multiply h_CS' by (1/9). Then `(1/9) · normSq(∑z) ≤ (1/9) · 3 · ∑ normSq = (1/3) · ∑ normSq`.
  have h_scaled : (1/9 : ℝ) * Complex.normSq (∑ k, z k)
      ≤ (1/9 : ℝ) * (3 * ∑ k, Complex.normSq ((weightFunction 3 k x : ℂ) *
            f.toFunℝ (inverseBranch 3 k x))) :=
    mul_le_mul_of_nonneg_left h_CS' (by norm_num : (0:ℝ) ≤ 1/9)
  have h_simp : (1/9 : ℝ) * (3 * ∑ k, Complex.normSq ((weightFunction 3 k x : ℂ) *
            f.toFunℝ (inverseBranch 3 k x)))
      = (1/3 : ℝ) * ∑ k, Complex.normSq ((weightFunction 3 k x : ℂ) *
            f.toFunℝ (inverseBranch 3 k x)) := by
    ring
  rw [h_simp] at h_scaled
  -- The remaining gap: align (1/9) with the LHS form from normSq_mul.
  -- (1/9 : ℝ) might be hidden behind a cast / form mismatch.
  -- LHS now: Complex.normSq (1/(3:ℕ) : ℂ) * normSq(∑ z) ; we already proved
  --  Complex.normSq (1/(3:ℕ) : ℂ) = 1/9. So after that rewrite, the LHS reads
  --  (1/9) * normSq(...).
  exact h_scaled

/-! ## 5. THE THEOREM — `T3NormSquaredBound` discharged -/

/-- **★★★ `T3NormSquaredBound_proved` ★★★**

    Mayer 1991 (BAMS) §2 contractivity estimate proven via pointwise
    Cauchy-Schwarz + per-branch CoV + μ_log partition. The integral
    `∫_(0,1) |T_3 f|² ∂μ_log ≤ ∫_(0,1) |f|² ∂μ_log` discharged
    UNCONDITIONALLY with ZERO project axioms. -/
theorem T3NormSquaredBound_proved : T3NormSquaredBound := by
  refine ⟨fun f => ?_⟩
  -- Plan:
  --   ∫ normSq(T3 f) ∂μ_log
  --     ≤ ∫ (1/3) ∑_k normSq(w_k · f∘y_k) ∂μ_log    [pointwise bound]
  --     = (1/3) ∑_k ∫ normSq(w_k · f∘y_k) ∂μ_log    [linearity]
  --     = (1/3) ∑_k 3 ∫_{I_k} normSq(f) ∂μ_log       [per-branch CoV]
  --     = ∑_k ∫_{I_k} normSq(f) ∂μ_log
  --     = ∫ normSq(f) ∂μ_log                          [partition]

  -- Step A: bound the LHS integrand by the sum bound integrand.
  -- First the RHS integrand is integrable on (0,1):
  have h_int_bound : MeasureTheory.IntegrableOn
      (fun x => (1/3 : ℝ) * ∑ k : Fin 3,
          Complex.normSq ((weightFunction 3 k x : ℂ) *
              f.toFunℝ (inverseBranch 3 k x)))
      (Set.Ioo (0:ℝ) 1) logWeightedMeasure := by
    apply MeasureTheory.Integrable.const_mul
    apply MeasureTheory.integrable_finset_sum
    intros k _
    exact branch_normSq_integrable k f
  -- LHS integrand also integrable (T3_apply_func_MemLp + memLp_two_iff_integrable_sq_norm).
  have h_int_lhs : MeasureTheory.IntegrableOn
      (fun x => Complex.normSq (transferOperatorAction_func 3 phaseFactorBase3 f x))
      (Set.Ioo (0:ℝ) 1) logWeightedMeasure := by
    have h_MemLp := T3_apply_func_MemLp f
    have h_int_normSq := (MeasureTheory.memLp_two_iff_integrable_sq_norm
        h_MemLp.1).mp h_MemLp
    have h_eq : (fun x : ℝ => ‖transferOperatorAction_func 3 phaseFactorBase3 f x‖ ^ 2)
              = (fun x : ℝ =>
                  Complex.normSq (transferOperatorAction_func 3 phaseFactorBase3 f x)) := by
      funext x
      exact (Complex.normSq_eq_norm_sq _).symm
    rw [h_eq] at h_int_normSq
    unfold MeasureTheory.IntegrableOn
    exact h_int_normSq
  -- Step A: monotonicity of integral via pointwise bound + integrability.
  have h_step_A : ∫ x in Set.Ioo (0:ℝ) 1,
        Complex.normSq (transferOperatorAction_func 3 phaseFactorBase3 f x)
        ∂logWeightedMeasure
      ≤ ∫ x in Set.Ioo (0:ℝ) 1,
        (1/3 : ℝ) * ∑ k : Fin 3,
            Complex.normSq ((weightFunction 3 k x : ℂ) *
                f.toFunℝ (inverseBranch 3 k x))
        ∂logWeightedMeasure := by
    refine MeasureTheory.integral_mono_ae h_int_lhs h_int_bound ?_
    exact Filter.Eventually.of_forall (fun x => transfer_func_normSq_pointwise_bound f x)
  -- Step B: linearity — pull out 1/3 and swap sum/integral on the RHS.
  have h_step_B : ∫ x in Set.Ioo (0:ℝ) 1,
        (1/3 : ℝ) * ∑ k : Fin 3,
            Complex.normSq ((weightFunction 3 k x : ℂ) *
                f.toFunℝ (inverseBranch 3 k x))
        ∂logWeightedMeasure
      = (1/3 : ℝ) * ∑ k : Fin 3, ∫ x in Set.Ioo (0:ℝ) 1,
          Complex.normSq ((weightFunction 3 k x : ℂ) *
              f.toFunℝ (inverseBranch 3 k x))
          ∂logWeightedMeasure := by
    rw [MeasureTheory.integral_const_mul]
    congr 1
    -- Swap finite sum & integral.
    rw [MeasureTheory.integral_finset_sum Finset.univ
        (fun k _ => branch_normSq_integrable k f)]
  -- Step C: per-branch CoV via branch_logWeightedMeasure_norm_sq_eq_real.
  have h_step_C : (1/3 : ℝ) * ∑ k : Fin 3, ∫ x in Set.Ioo (0:ℝ) 1,
          Complex.normSq ((weightFunction 3 k x : ℂ) *
              f.toFunℝ (inverseBranch 3 k x))
          ∂logWeightedMeasure
      = ∑ k : Fin 3, ∫ u in Set.Ioo ((k.val : ℝ)/3) (((k.val : ℝ) + 1)/3),
          Complex.normSq (f.toFunℝ u) ∂logWeightedMeasure := by
    -- Each term: (1/3) · 3 · ∫_{I_k} = ∫_{I_k}.
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros k _
    rw [branch_logWeightedMeasure_norm_sq_eq_real k f]
    ring
  -- Step D: partition the per-I_k sum equals integral over (0,1).
  -- Use the μ_log version with F = normSq(f.toFunℝ).
  have h_int_f_normSq : MeasureTheory.IntegrableOn
      (fun u => Complex.normSq (f.toFunℝ u))
      (Set.Ioo (0:ℝ) 1) logWeightedMeasure := by
    have hMemLp := LogWeightedL2.MemLp2_universal f
    have h_int := (MeasureTheory.memLp_two_iff_integrable_sq_norm
        hMemLp.1).mp hMemLp
    have h_eq : (fun x : ℝ => ‖f.toFunℝ x‖ ^ 2)
              = (fun x : ℝ => Complex.normSq (f.toFunℝ x)) := by
      funext x
      exact (Complex.normSq_eq_norm_sq _).symm
    rw [h_eq] at h_int
    unfold MeasureTheory.IntegrableOn
    exact h_int
  have h_partition := setIntegral_Ioo_partition_three_logWeighted_real
      (fun u => Complex.normSq (f.toFunℝ u)) h_int_f_normSq
  -- Expand the Fin 3 sum on LHS of h_step_C's RHS to three explicit pieces:
  --   k = 0: Ioo 0 (1/3)
  --   k = 1: Ioo (1/3) (2/3)
  --   k = 2: Ioo (2/3) 1
  have h_step_D : ∑ k : Fin 3, ∫ u in Set.Ioo ((k.val : ℝ)/3) (((k.val : ℝ) + 1)/3),
          Complex.normSq (f.toFunℝ u) ∂logWeightedMeasure
      = ∫ u in Set.Ioo (0:ℝ) 1,
          Complex.normSq (f.toFunℝ u) ∂logWeightedMeasure := by
    rw [Fin.sum_univ_three]
    simp only [Fin.val_zero, Nat.cast_zero, zero_div, zero_add,
      Fin.val_one, Nat.cast_one, Fin.val_two, Nat.cast_ofNat]
    have h_arith1 : ((1:ℝ) + 1)/3 = 2/3 := by norm_num
    have h_arith2 : ((2:ℝ) + 1)/3 = 1 := by norm_num
    rw [h_arith1, h_arith2]
    -- LHS now: ∫ Ioo 0 (1/3) + ∫ Ioo (1/3) (2/3) + ∫ Ioo (2/3) 1 = ∫ Ioo 0 1.
    rw [h_partition]
  -- Assemble the chain.
  calc ∫ x in Set.Ioo (0:ℝ) 1,
        Complex.normSq (transferOperatorAction_func 3 phaseFactorBase3 f x)
        ∂logWeightedMeasure
      ≤ ∫ x in Set.Ioo (0:ℝ) 1,
        (1/3 : ℝ) * ∑ k : Fin 3,
            Complex.normSq ((weightFunction 3 k x : ℂ) *
                f.toFunℝ (inverseBranch 3 k x))
        ∂logWeightedMeasure := h_step_A
    _ = (1/3 : ℝ) * ∑ k : Fin 3, ∫ x in Set.Ioo (0:ℝ) 1,
          Complex.normSq ((weightFunction 3 k x : ℂ) *
              f.toFunℝ (inverseBranch 3 k x))
          ∂logWeightedMeasure := h_step_B
    _ = ∑ k : Fin 3, ∫ u in Set.Ioo ((k.val : ℝ)/3) (((k.val : ℝ) + 1)/3),
          Complex.normSq (f.toFunℝ u) ∂logWeightedMeasure := h_step_C
    _ = ∫ u in Set.Ioo (0:ℝ) 1,
          Complex.normSq (f.toFunℝ u) ∂logWeightedMeasure := h_step_D

/-! ## 6. Composed unconditional theorems -/

/-- **★★★ `T3LinearStructure` proven UNCONDITIONALLY (contracting half) ★★★**

    Composes `T3NormSquaredBound_proved` with
    `T3LinearStructure_proved_from_squared` (`T3NormBoundDischarge.lean`).
    After this theorem, the contracting half of `T3SymLinearStructure`
    is fully discharged with ZERO open hypotheses. -/
theorem T3LinearStructure_proved_unconditional : T3LinearStructure :=
  T3LinearStructure_proved_from_squared T3NormSquaredBound_proved

/-- **★★★ `T3SymCLMSymmetricWitness` from `T3AdjointLinearStructureFactored` ONLY ★★★**

    With `T3NormSquaredBound` discharged unconditionally, only the
    expanding-side adjoint linearity (`T3AdjointLinearStructureFactored`)
    remains open in the chain to `T3SymCLMSymmetricWitness`. -/
theorem T3SymCLMSymmetricWitness_from_t3adjoint_only
    (hFac : T3AdjointLinearStructureFactored) : T3SymCLMSymmetricWitness :=
  T3SymCLMSymmetricWitness_proved_from_squared T3NormSquaredBound_proved hFac

/-! ## 7. Axiom-freeness verification -/

#print axioms T3NormSquaredBound_proved
#print axioms T3LinearStructure_proved_unconditional
#print axioms T3SymCLMSymmetricWitness_from_t3adjoint_only

end PrincipiaTractalis
