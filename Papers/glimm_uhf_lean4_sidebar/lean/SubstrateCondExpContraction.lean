/-
# r110: The substrate conditional-expectation `‖·‖₂` CONTRACTION — discharging
  `CondExpL2Contraction` and isolating the completion-tier residual.

★ 2026-07-23 r110 — the KADISON–SCHWARZ 2-norm contraction for `E_k`, PROVED
elementarily, discharging the r109 residual `CondExpL2Contraction`. ★

## What r110 establishes (all UNCONDITIONAL, kernel-only)

r109 (`PF/SubstrateConditionalExpectation.lean`) built the substrate
conditional expectation `E_k : T∞ → M_{3^k}` unconditionally and NAMED two
residuals gating the completion-tier faithfulness summit:

  (2) `CondExpL2Contraction` — the `‖·‖₂` (trace 2-seminorm) contraction, which
      r109 flagged as "the single hard analytic core; absent from mathlib".
  (3) `CondExpCompletionExtension` — the uniform-continuity extension of `E_k`
      to the completion.

r110 DISCHARGES residual (2) `CondExpL2Contraction` **unconditionally**, by
targeting the SCALAR 2-norm contraction directly rather than the operator
Kadison–Schwarz inequality. The single-step engine is elementary:

    τ_n((E B)⋆(E B)) ≤ τ_{n+1}(B⋆B),

where `(E B) i j = (1/3) Σ_t B(i,t)(j,t)`. Its proof is:

  * a finite Cauchy–Schwarz `|Σ_{t:Fin 3} a_t|² ≤ 3 Σ_t |a_t|²`
    (`sq_sum_le_card_mul_sum_sq`), giving the pointwise bound
    `|(E B) i j|² ≤ (1/3) Σ_t |B(i,t)(j,t)|²`;
  * the observation that the resulting sum is the diagonal-tail (`s = t`)
    sub-sum of `τ_{n+1}(B⋆B) = (1/3^{n+1}) Σ_{i,s,j,t} |B(j,t)(i,s)|²`, all
    terms `≥ 0`, so `Finset.single_le_sum` closes it.

No PSD operator theory, no complete positivity. Iterating through
`partialTraceDown` and descending to `condExp` gives the ring-level
contraction, which is DEFINITIONALLY `CondExpL2Contraction`.

## The remaining residual for the SUMMIT

Completion faithfulness (`UHF_trace (x⋆x) = 0 → x = 0` on
`TimelessFieldCompletion`) via `E_k` requires residual (3), the
UNIFORM-CONTINUITY EXTENSION `Ê_k` to the completion. That extension needs
the **OPERATOR-norm** contraction `‖E_k‖ ≤ 1` (partial trace is unital
completely positive ⇒ norm 1), whose single-step form
`‖partialTraceStep n B‖ ≤ ‖B‖` in the L2-operator norm is the one lemma NOT
reachable elementarily (matrix partial-trace complete positivity is absent
from mathlib). It is isolated below as `PartialTraceStepOpNormContraction`.

Thus r110 converts r109's residual (2) from "hard analytic core" to THEOREM,
leaving the SUMMIT gated on exactly one operator-norm lemma (or the full
completion-extension of which it is the load-bearing input), and via r108's
`traceDetects_iff_faithful` this is exactly completion faithfulness/simplicity.

Kernel-only [propext, Classical.choice, Quot.sound]. Zero project axioms.
Zero sorries.

Stage 2026-07-23 r110 — the conditional-expectation 2-norm contraction,
discharging `CondExpL2Contraction`.
-/

import PF.SubstrateConditionalExpectation
import PF.SubstrateTraceDetectionAttempt
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace SubstrateCondExpContraction

open scoped ComplexOrder
open scoped Matrix.Norms.L2Operator
open SubstrateBase3Embed SubstrateDirectLimit
open SubstrateUHFBoundedTrace SubstrateUHFPreTraceDirectLimit
open SubstrateUHFTraceIsStarPreserving
open SubstrateConditionalExpectation

/-! ## §1 — The finite Cauchy–Schwarz kernel on `Fin 3` -/

/-- **Finite Cauchy–Schwarz on `Fin 3` for `normSq`**:
    `|Σ_{t} a_t|² ≤ 3 · Σ_t |a_t|²`. Elementary: `‖Σ a‖ ≤ Σ ‖a‖`
    (`norm_sum_le`) squared, then `sq_sum_le_card_mul_sum_sq`. -/
theorem normSq_sum_fin3_le (a : Fin 3 → ℂ) :
    Complex.normSq (∑ t, a t) ≤ 3 * ∑ t, Complex.normSq (a t) := by
  have h1 : ‖∑ t, a t‖ ≤ ∑ t, ‖a t‖ := norm_sum_le _ _
  have h2 : (∑ t, ‖a t‖) ^ 2 ≤ (Finset.univ.card : ℝ) * ∑ t, ‖a t‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [Complex.normSq_eq_norm_sq]
  calc ‖∑ t, a t‖ ^ 2
        ≤ (∑ t, ‖a t‖) ^ 2 := by gcongr
    _ ≤ (Finset.univ.card : ℝ) * ∑ t, ‖a t‖ ^ 2 := h2
    _ = 3 * ∑ t, Complex.normSq (a t) := by
          rw [Finset.card_univ, Fintype.card_fin]
          simp_rw [← Complex.normSq_eq_norm_sq]
          norm_num

/-! ## §2 — The `.re` of the normalized trace of `star M * M` as a real sum -/

/-- **The real content of the trace 2-seminorm**:
    `Re τ_N(M⋆ M) = (Σ_{i,j} |M j i|²) / N`. -/
theorem re_normalized_trace_star_mul_self {N : ℕ} [NeZero N]
    (M : Matrix (Fin N) (Fin N) ℂ) :
    (normalized_matrix_trace (star M * M)).re
      = (∑ i, ∑ j, Complex.normSq (M j i)) / (N : ℝ) := by
  have htr : Matrix.trace (star M * M)
      = ((∑ i, ∑ j, Complex.normSq (M j i) : ℝ) : ℂ) := by
    push_cast
    show (∑ i, (star M * M) i i) = ∑ i, ∑ j, (Complex.normSq (M j i) : ℂ)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Matrix.star_apply, Complex.normSq_eq_conj_mul_self, Complex.star_def]
  show (Matrix.trace (star M * M) / (N : ℂ)).re
      = (∑ i, ∑ j, Complex.normSq (M j i)) / (N : ℝ)
  rw [htr, show ((N : ℕ) : ℂ) = (((N : ℝ)) : ℂ) from by push_cast; ring,
      ← Complex.ofReal_div, Complex.ofReal_re]

/-! ## §3 — The single-step 2-norm contraction (THE elementary crux) -/

/-- **★ r110.a: single-step `‖·‖₂` contraction ★**
    `Re τ_n((E B)⋆(E B)) ≤ Re τ_{n+1}(B⋆B)` for the single-step partial
    trace `E = partialTraceStep n`. Pure finite sums + nonnegativity. -/
theorem partialTraceStep_normSq_trace_le (n : ℕ)
    (B : Matrix (Fin (3^(n+1))) (Fin (3^(n+1))) ℂ) :
    (normalized_matrix_trace
        (star (partialTraceStep n B) * partialTraceStep n B)).re ≤
      (normalized_matrix_trace (star B * B)).re := by
  rw [re_normalized_trace_star_mul_self, re_normalized_trace_star_mul_self]
  -- Abbreviations for the two numerators.
  set SL := ∑ i, ∑ j, Complex.normSq (partialTraceStep n B j i) with hSL
  set SR := ∑ p, ∑ q, Complex.normSq (B q p) with hSR
  -- The diagonal-tail numerator.
  set D := ∑ i, ∑ j, ∑ t,
      Complex.normSq (B (levelStepEquiv n (j, t)) (levelStepEquiv n (i, t))) with hD
  -- Pointwise Cauchy–Schwarz bound.
  have pt : ∀ i j, 3 * Complex.normSq (partialTraceStep n B j i)
      ≤ ∑ t, Complex.normSq (B (levelStepEquiv n (j, t)) (levelStepEquiv n (i, t))) := by
    intro i j
    rw [partialTraceStep_apply, Complex.normSq_mul]
    have hns3 : Complex.normSq (3⁻¹ : ℂ) = (9 : ℝ)⁻¹ := by
      rw [Complex.normSq_inv]; norm_num [Complex.normSq_ofNat]
    rw [hns3]
    have hcs := normSq_sum_fin3_le
      (fun t : Fin 3 => B (levelStepEquiv n (j, t)) (levelStepEquiv n (i, t)))
    simp only at hcs
    nlinarith [hcs]
  -- Claim 1: 3 * SL ≤ D.
  have claim1 : 3 * SL ≤ D := by
    rw [hSL, hD, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => pt i j)
  -- Claim 2: D ≤ SR (diagonal ⊆ full, nonnegative complement).
  have claim2 : D ≤ SR := by
    have hexp : SR = ∑ i, ∑ j, ∑ t, ∑ s,
        Complex.normSq (B (levelStepEquiv n (j, t)) (levelStepEquiv n (i, s))) := by
      rw [hSR, ← (levelStepEquiv n).sum_comp
        (fun p => ∑ q, Complex.normSq (B q p))]
      have hin : ∀ x : Fin (3^n) × Fin 3,
          (∑ q, Complex.normSq (B q (levelStepEquiv n x)))
            = ∑ y : Fin (3^n) × Fin 3,
                Complex.normSq (B (levelStepEquiv n y) (levelStepEquiv n x)) :=
        fun x => ((levelStepEquiv n).sum_comp
          (fun q => Complex.normSq (B q (levelStepEquiv n x)))).symm
      simp_rw [hin, Fintype.sum_prod_type]
      -- reorder ∑ i ∑ s ∑ j ∑ t  →  ∑ i ∑ j ∑ t ∑ s
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.sum_comm]
    rw [hexp, hD]
    refine Finset.sum_le_sum (fun i _ => ?_)
    refine Finset.sum_le_sum (fun j _ => ?_)
    refine Finset.sum_le_sum (fun t _ => ?_)
    exact Finset.single_le_sum
      (f := fun s => Complex.normSq
        (B (levelStepEquiv n (j, t)) (levelStepEquiv n (i, s))))
      (fun s _ => Complex.normSq_nonneg _) (Finset.mem_univ t)
  -- Combine: 3 * SL ≤ SR, then divide.
  have hkey : 3 * SL ≤ SR := le_trans claim1 claim2
  have h3n : (0 : ℝ) < ((3^n : ℕ) : ℝ) := by positivity
  have h3n1 : (0 : ℝ) < ((3^(n+1) : ℕ) : ℝ) := by positivity
  rw [div_le_div_iff₀ h3n h3n1]
  have hpow : ((3^(n+1) : ℕ) : ℝ) = 3 * ((3^n : ℕ) : ℝ) := by
    push_cast [pow_succ]; ring
  rw [hpow]
  calc SL * (3 * ((3^n : ℕ) : ℝ))
        = (3 * SL) * ((3^n : ℕ) : ℝ) := by ring
    _ ≤ SR * ((3^n : ℕ) : ℝ) := mul_le_mul_of_nonneg_right hkey h3n.le

/-! ## §4 — Iterating to `partialTraceDown` and to `condExp` -/

/-- **r110.b: iterated `‖·‖₂` contraction** for `partialTraceDown k j`. -/
theorem partialTraceDown_normSq_trace_le (k : ℕ) :
    ∀ (j : ℕ) (h : k ≤ j) (B : Matrix (Fin (3^j)) (Fin (3^j)) ℂ),
    (normalized_matrix_trace
        (star (partialTraceDown k j h B) * partialTraceDown k j h B)).re ≤
      (normalized_matrix_trace (star B * B)).re := by
  intro j h
  induction j, h using Nat.le_induction with
  | base =>
    intro B
    rw [partialTraceDown_self]
    exact le_of_eq rfl
  | succ n hn ih =>
    intro B
    rw [partialTraceDown_succ_apply k n hn (Nat.le_succ_of_le hn)]
    exact le_trans (ih (partialTraceStep n B))
      (partialTraceStep_normSq_trace_le n B)

/-- **★★★ r110.c: THE CONDITIONAL-EXPECTATION 2-NORM CONTRACTION ★★★**
    `Re τ_k((E_k x)⋆(E_k x)) ≤ Re τ(x⋆ x)` for every `x : TimelessFieldRing`.
    For `k ≤ m` it is the iterated partial-trace contraction; for `m ≤ k`
    it is EQUALITY (the substrate embedding is a trace-preserving
    *-homomorphism). -/
theorem condExp_l2_contraction (k : ℕ) (x : TimelessFieldRing) :
    (normalized_matrix_trace (star (condExp k x) * condExp k x)).re ≤
      (substrate_pre_trace (star x * x)).re := by
  obtain ⟨m, A, rfl⟩ := DirectLimit.exists_eq_mk
    (fun i j (h : i ≤ j) => substrateRingHomIter i j h) x
  rw [condExp_of_level, substrate_quotient_star_same_level m A,
      substrate_quotient_mul_same_level m (star A) A, substrate_pre_trace_of_level]
  by_cases hkm : k ≤ m
  · rw [levelToLevelK_of_le k m hkm]
    exact partialTraceDown_normSq_trace_le k m hkm A
  · have hmk : m ≤ k := le_of_not_le hkm
    rw [levelToLevelK_of_ge k m hmk]
    have heq : normalized_matrix_trace
          (star (substrateRingHomIter m k hmk A) * substrateRingHomIter m k hmk A)
        = normalized_matrix_trace (star A * A) := by
      rw [← substrateRingHomIter_star m k hmk A,
          ← map_mul (substrateRingHomIter m k hmk) (star A) A,
          substrateRingHomIter_normalized_trace]
    rw [heq]

/-! ## §5 — Discharging the r109 residual `CondExpL2Contraction` -/

/-- **★★★ r110.d: `CondExpL2Contraction` IS A THEOREM ★★★**

    The r109-named residual (2) is discharged unconditionally: it is exactly
    `condExp_l2_contraction` universally quantified over `k` and `x`. -/
theorem condExpL2Contraction_holds : CondExpL2Contraction :=
  condExp_l2_contraction

/-! ## §6 — The isolated completion-tier residual (the operator-norm wall) -/

/-- **The one remaining hard lemma for the completion extension.**

    In the `L2`-operator norm, the single-step partial trace is a
    contraction: `‖partialTraceStep n B‖ ≤ ‖B‖`. Classically true (the
    partial trace is unital completely positive, hence norm 1), but the
    matrix partial-trace complete-positivity input is absent from mathlib.

    This is the load-bearing analytic input for r109's residual (3)
    `CondExpCompletionExtension` (uniform-continuity extension of `E_k` to
    `TimelessFieldCompletion` with `ι_k(Ê_k x) → x`), and hence — via r108's
    `traceDetects_iff_faithful` — for the completion-tier faithfulness SUMMIT.
    It is stated here as the single named residual, NOT proved. -/
def PartialTraceStepOpNormContraction : Prop :=
  ∀ (n : ℕ) (B : Matrix (Fin (3^(n+1))) (Fin (3^(n+1))) ℂ),
    ‖partialTraceStep n B‖ ≤ ‖B‖

/-! ## §7 — r110 capstone -/

/-- **★★★ r110 SUBSTRATE CONDITIONAL-EXPECTATION 2-NORM CONTRACTION
    CAPSTONE ★★★**

    **LANDED (unconditional, kernel-only):**

      (a) `normSq_sum_fin3_le` — the finite Cauchy–Schwarz kernel.
      (b) `re_normalized_trace_star_mul_self` — `Re τ_N(M⋆ M) = Σ|·|²/N`.
      (c) `partialTraceStep_normSq_trace_le` — the single-step 2-norm
          contraction (the elementary crux).
      (d) `partialTraceDown_normSq_trace_le` — its iterate over the gap.
      (e) `condExp_l2_contraction` — the direct-limit-level contraction
          `Re τ_k((E_k x)⋆(E_k x)) ≤ Re τ(x⋆ x)`.
      (f) `condExpL2Contraction_holds` — **discharges r109 residual (2)
          `CondExpL2Contraction`** (definitionally).

    **ISOLATED RESIDUAL (the SUMMIT wall):**

      `PartialTraceStepOpNormContraction` — the `L2`-operator-norm
      contraction `‖E_k‖ ≤ 1`, the single input needed to lift `E_k` to the
      completion (r109 residual (3) `CondExpCompletionExtension`) and thereby
      close completion faithfulness (equivalently, by r108, Glimm simplicity
      of `T∞`).

    Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
    axioms. Zero sorries. -/
theorem r110_substrate_condexp_contraction_capstone :
    -- (c) single-step contraction
    (∀ (n : ℕ) (B : Matrix (Fin (3^(n+1))) (Fin (3^(n+1))) ℂ),
      (normalized_matrix_trace
          (star (partialTraceStep n B) * partialTraceStep n B)).re ≤
        (normalized_matrix_trace (star B * B)).re) ∧
    -- (e) direct-limit-level contraction
    (∀ (k : ℕ) (x : TimelessFieldRing),
      (normalized_matrix_trace (star (condExp k x) * condExp k x)).re ≤
        (substrate_pre_trace (star x * x)).re) ∧
    -- (f) r109 residual (2) discharged
    CondExpL2Contraction :=
  ⟨partialTraceStep_normSq_trace_le,
   condExp_l2_contraction,
   condExpL2Contraction_holds⟩

/-! ## §8 — Axiom audit -/

#print axioms normSq_sum_fin3_le
#print axioms re_normalized_trace_star_mul_self
#print axioms partialTraceStep_normSq_trace_le
#print axioms partialTraceDown_normSq_trace_le
#print axioms condExp_l2_contraction
#print axioms condExpL2Contraction_holds
#print axioms r110_substrate_condexp_contraction_capstone

end SubstrateCondExpContraction
end PrincipiaTractalis
