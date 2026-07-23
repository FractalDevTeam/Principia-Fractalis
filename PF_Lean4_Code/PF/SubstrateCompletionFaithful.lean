/-
# r112: CLOSING THE SUMMIT — completion-tier faithfulness of the substrate UHF
  trace as an UNCONDITIONAL theorem, via the conditional-expectation extension.

★ 2026-07-23 r112 — THE SUMMIT. The final uniform-space packaging that lifts the
substrate conditional expectation `E_k : T∞ → M_{3^k}` (r109) to the completion,
using r110's 2-norm contraction and r111's operator-norm contraction, and thereby
discharges completion-tier faithfulness of `UHF_trace` unconditionally. ★

## What r112 establishes (all UNCONDITIONAL, kernel-only)

r109 built `E_k` (algebraic keystone); r110 proved its `‖·‖₂` contraction; r111
proved its `L²`-operator-norm contraction `‖E_k x‖ ≤ ‖x‖`. r108 showed that
completion faithfulness ⇔ trace-detection ⇔ Glimm simplicity. r112 assembles the
completion-side extension and closes the loop:

  * `condExpFin k : T∞̂ → M_{3^k}` — `E_k` extended to the completion by uniform
    continuity (it is `LipschitzWith 1`), with `condExpFin k ↑a = E_k a`.
  * `condExpCompletion k : T∞̂ → T∞̂ := ↑ ∘ ι_k ∘ condExpFin k` — the completion
    conditional expectation, `LipschitzWith 1`, uniformly continuous, with
    `condExpCompletion k ↑a = ↑(ι_k (E_k a))` (discharges r109's
    `CondExpCompletionExtension` — property (ii)).
  * `condExpCompletion_tendsto` — `condExpCompletion k x → x` as `k → ∞`, by the
    ε/2 density lift over the 1-Lipschitz equicontinuous family (property (iii)).
  * `condExpCompletion_l2_contraction` — the `‖·‖₂` contraction lifted to the
    completion by continuity + `isClosed_le` induction on the dense image
    (using r110's `condExp_l2_contraction`).
  * `UHF_trace_faithful` — **★ THE SUMMIT ★**: `UHF_trace (x⋆ x) = 0 → x = 0`
    for every `x : TimelessFieldCompletion`, UNCONDITIONAL.

## Residuals discharged

  * `CondExpCompletionExtension`                               (r109)
  * `SubstrateUHFCompletionPositiveFaithfulnessSubstrateConjecture` (r100)
  * `SubstrateCompletionTraceDetectsIdeals`                    (r106/r108)
  * completion algebraic simplicity `∀ I, I = ⊥ ∨ I = ⊤`      (r106/r108)

r103's `UHF_trace_faithful_of_simple` and r106's simplicity development are now
UNCONDITIONAL (their completion faithfulness hypothesis is a theorem here).

Kernel-only [propext, Classical.choice, Quot.sound]. Zero project axioms. Zero
sorries.

Stage 2026-07-23 r112 — the completion conditional expectation and unconditional
completion-tier UHF trace faithfulness.
-/

import PF.SubstrateConditionalExpectation
import PF.SubstrateCondExpContraction
import PF.SubstrateCondExpOpNorm
import PF.SubstrateUHFTraceIsFaithful
import PF.SubstrateTraceDetectionAttempt
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace SubstrateCompletionFaithful

open scoped Matrix.Norms.L2Operator
open scoped ComplexOrder
open SubstrateBase3Embed SubstrateDirectLimit
open SubstrateTimelessFieldNorm SubstrateTimelessFieldCompletion
open SubstrateUHFBoundedTrace SubstrateUHFPreTraceDirectLimit
open SubstrateUHFTraceIsStarPreserving SubstrateUHFTraceIsPositive
open SubstrateUHFTraceIsFaithful
open SubstrateConditionalExpectation SubstrateCondExpContraction
open SubstrateCondExpOpNorm SubstrateTraceDetectionAttempt
open SubstrateCompletionSimplicity

/-! ## §1 — `E_k` is `LipschitzWith 1` as a map `T∞ → M_{3^k}` -/

/-- `E_k` sends negations to negations. -/
theorem condExp_neg (k : ℕ) (y : TimelessFieldRing) :
    condExp k (-y) = - condExp k y := by
  rw [← neg_one_smul ℂ y, condExp_smul, neg_one_smul]

/-- `E_k` is additive on differences. -/
theorem condExp_sub (k : ℕ) (x y : TimelessFieldRing) :
    condExp k (x - y) = condExp k x - condExp k y := by
  rw [sub_eq_add_neg, condExp_add, condExp_neg, ← sub_eq_add_neg]

/-- **`E_k : T∞ → M_{3^k}` is `LipschitzWith 1`** — from additivity + r111's
    operator-norm contraction `‖E_k x‖ ≤ ‖x‖`. -/
theorem condExp_lipschitz (k : ℕ) : LipschitzWith 1 (condExp k) := by
  refine LipschitzWith.of_dist_le_mul (fun a b => ?_)
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← condExp_sub]
  exact condExp_opNorm_le k (a - b)

theorem condExp_uniformContinuous (k : ℕ) : UniformContinuous (condExp k) :=
  (condExp_lipschitz k).uniformContinuous

/-! ## §2 — The cocone identity and the level embedding isometry -/

/-- **Cocone identity**: `ι_k (ι_{m→k} A) = ι_m A` in `T∞` (same equivalence
    class across levels, `k ≥ m`). -/
theorem substrateLevelToTimelessField_iter (m k : ℕ) (h : m ≤ k)
    (A : Matrix (Fin (3^m)) (Fin (3^m)) ℂ) :
    substrateLevelToTimelessField k (substrateRingHomIter m k h A)
      = substrateLevelToTimelessField m A := by
  apply Quotient.sound
  refine ⟨k, le_rfl, h, ?_⟩
  show substrateRingHomIter k k le_rfl (substrateRingHomIter m k h A)
        = substrateRingHomIter m k h A
  rw [substrateRingHomIter_self]
  rfl

/-- **The canonical level embedding `ι_k : M_{3^k} → T∞` is an isometry.** -/
theorem substrateLevelToTimelessField_isometry (k : ℕ) :
    Isometry (substrateLevelToTimelessField k) := by
  refine Isometry.of_dist_eq (fun X Y => ?_)
  rw [dist_eq_norm, dist_eq_norm]
  have hneg : -(substrateLevelToTimelessField k Y) = substrateLevelToTimelessField k (-Y) :=
    DirectLimit.neg_def
      (G := fun k : ℕ => Matrix (Fin (3^k)) (Fin (3^k)) ℂ)
      (f := fun i j (h : i ≤ j) => substrateRingHomIter i j h) k Y
  have hadd : substrateLevelToTimelessField k X + substrateLevelToTimelessField k (-Y)
      = substrateLevelToTimelessField k (X + -Y) :=
    substrate_quotient_add_same_level k X (-Y)
  calc ‖substrateLevelToTimelessField k X - substrateLevelToTimelessField k Y‖
      = ‖substrateLevelToTimelessField k X + -(substrateLevelToTimelessField k Y)‖ := by
        rw [sub_eq_add_neg]
    _ = ‖substrateLevelToTimelessField k X + substrateLevelToTimelessField k (-Y)‖ := by
        rw [hneg]
    _ = ‖substrateLevelToTimelessField k (X + -Y)‖ := by rw [hadd]
    _ = ‖X + -Y‖ := substrateLevelToTimelessField_opNorm_eq k (X + -Y)
    _ = ‖X - Y‖ := by rw [← sub_eq_add_neg]

/-! ## §3 — `condExpFin`: `E_k` extended to the completion (matrix-valued) -/

/-- **`E_k` extended to the completion**, matrix-valued:
    `condExpFin k : T∞̂ → M_{3^k}`. -/
noncomputable def condExpFin (k : ℕ) :
    TimelessFieldCompletion → Matrix (Fin (3^k)) (Fin (3^k)) ℂ :=
  UniformSpace.Completion.extension (condExp k)

theorem condExpFin_coe (k : ℕ) (a : TimelessFieldRing) :
    condExpFin k (a : TimelessFieldCompletion) = condExp k a :=
  UniformSpace.Completion.extension_coe (condExp_uniformContinuous k) a

theorem condExpFin_uniformContinuous (k : ℕ) : UniformContinuous (condExpFin k) :=
  UniformSpace.Completion.uniformContinuous_extension

theorem condExpFin_continuous (k : ℕ) : Continuous (condExpFin k) :=
  (condExpFin_uniformContinuous k).continuous

theorem condExpFin_lipschitz (k : ℕ) : LipschitzWith 1 (condExpFin k) :=
  (condExp_lipschitz k).completion_extension

/-! ## §4 — `condExpCompletion`: the completion conditional expectation -/

/-- **★ The completion conditional expectation ★**
    `condExpCompletion k : T∞̂ → T∞̂`, `= ↑ ∘ ι_k ∘ condExpFin k`. -/
noncomputable def condExpCompletion (k : ℕ) :
    TimelessFieldCompletion → TimelessFieldCompletion :=
  fun x => ((substrateLevelToTimelessField k (condExpFin k x) : TimelessFieldRing) :
             TimelessFieldCompletion)

/-- **Dense-image value** (discharges the coherence conjunct of
    `CondExpCompletionExtension`): `condExpCompletion k ↑a = ↑(ι_k (E_k a))`. -/
theorem condExpCompletion_coe (k : ℕ) (a : TimelessFieldRing) :
    condExpCompletion k (a : TimelessFieldCompletion) =
      ((substrateLevelToTimelessField k (condExp k a) : TimelessFieldRing) :
        TimelessFieldCompletion) := by
  unfold condExpCompletion
  rw [condExpFin_coe]

theorem condExpCompletion_continuous (k : ℕ) :
    Continuous (condExpCompletion k) := by
  unfold condExpCompletion
  have hcoe := UniformSpace.Completion.continuous_coe TimelessFieldRing
  exact hcoe.comp
    ((substrateLevelToTimelessField_isometry k).continuous.comp (condExpFin_continuous k))

theorem condExpCompletion_uniformContinuous (k : ℕ) :
    UniformContinuous (condExpCompletion k) := by
  unfold condExpCompletion
  have hcoe := UniformSpace.Completion.uniformContinuous_coe TimelessFieldRing
  exact hcoe.comp
    ((substrateLevelToTimelessField_isometry k).uniformContinuous.comp
      (condExpFin_uniformContinuous k))

/-- **`condExpCompletion k` is `LipschitzWith 1`** (nonexpanding). -/
theorem condExpCompletion_lipschitz (k : ℕ) : LipschitzWith 1 (condExpCompletion k) := by
  refine LipschitzWith.of_dist_le_mul (fun y z => ?_)
  rw [NNReal.coe_one, one_mul]
  calc dist (condExpCompletion k y) (condExpCompletion k z)
      = dist (substrateLevelToTimelessField k (condExpFin k y))
             (substrateLevelToTimelessField k (condExpFin k z)) :=
        UniformSpace.Completion.coe_isometry.dist_eq _ _
    _ = dist (condExpFin k y) (condExpFin k z) :=
        (substrateLevelToTimelessField_isometry k).dist_eq _ _
    _ ≤ dist y z := by
        have h := (condExpFin_lipschitz k).dist_le_mul y z
        rwa [NNReal.coe_one, one_mul] at h

/-- **`condExpCompletion k` fixes the coerced image of a level-`≤ k` element.** -/
theorem condExpCompletion_fixes_coe_lower (k m : ℕ) (h : m ≤ k)
    (A : Matrix (Fin (3^m)) (Fin (3^m)) ℂ) :
    condExpCompletion k
        ((substrateLevelToTimelessField m A : TimelessFieldRing) : TimelessFieldCompletion) =
      ((substrateLevelToTimelessField m A : TimelessFieldRing) : TimelessFieldCompletion) := by
  rw [condExpCompletion_coe]
  congr 1
  rw [condExp_lower_level k m h A, substrateLevelToTimelessField_iter m k h A]

/-! ## §5 — `condExpCompletion k x → x` (the density lift) -/

/-- **★ `condExpCompletion k x → x` ★** — the reconstruction property
    (discharges the `Tendsto` conjunct of `CondExpCompletionExtension`).
    ε/2 density lift over the uniformly 1-Lipschitz family. -/
theorem condExpCompletion_tendsto (x : TimelessFieldCompletion) :
    Filter.Tendsto (fun k => condExpCompletion k x) Filter.atTop (nhds x) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨a, ha⟩ :=
    UniformSpace.Completion.denseRange_coe.exists_dist_lt x (half_pos hε)
  obtain ⟨m, A, ha_eq⟩ :=
    DirectLimit.exists_eq_mk (fun i j (h : i ≤ j) => substrateRingHomIter i j h) a
  refine ⟨m, fun k hk => ?_⟩
  have hfix : condExpCompletion k (a : TimelessFieldCompletion) = (a : TimelessFieldCompletion) := by
    rw [ha_eq]; exact condExpCompletion_fixes_coe_lower k m hk A
  have hlip : dist (condExpCompletion k x) (condExpCompletion k (a : TimelessFieldCompletion))
      ≤ dist x (a : TimelessFieldCompletion) := by
    have h := (condExpCompletion_lipschitz k).dist_le_mul x (a : TimelessFieldCompletion)
    rwa [NNReal.coe_one, one_mul] at h
  calc dist (condExpCompletion k x) x
      ≤ dist (condExpCompletion k x) (condExpCompletion k (a : TimelessFieldCompletion))
          + dist (condExpCompletion k (a : TimelessFieldCompletion)) x := dist_triangle _ _ _
    _ ≤ dist x (a : TimelessFieldCompletion) + dist (a : TimelessFieldCompletion) x := by
        apply add_le_add hlip
        rw [hfix]
    _ = dist x (a : TimelessFieldCompletion) + dist x (a : TimelessFieldCompletion) := by
        rw [dist_comm (a : TimelessFieldCompletion) x]
    _ < ε := by rw [← two_mul]; linarith [ha]

/-! ## §6 — The trace bridge and the `‖·‖₂` contraction on the completion -/

/-- **The UHF-trace / matrix-trace bridge on the range of `condExpCompletion`**:
    `τ_UHF ((E_k x)⋆(E_k x)) = τ_{3^k} ((condExpFin k x)⋆ (condExpFin k x))`,
    for EVERY `x` (definitional: `condExpCompletion` factors through `ι_k`). -/
theorem UHF_trace_condExpCompletion (k : ℕ) (x : TimelessFieldCompletion) :
    UHF_trace (star (condExpCompletion k x) * condExpCompletion k x)
      = normalized_matrix_trace (star (condExpFin k x) * condExpFin k x) := by
  unfold condExpCompletion
  rw [star_coe_TimelessFieldCompletion, ← UniformSpace.Completion.coe_mul, UHF_trace_coe]
  show substrate_pre_trace
        (star (⟦⟨k, condExpFin k x⟩⟧ : TimelessFieldRing) * ⟦⟨k, condExpFin k x⟩⟧) = _
  rw [substrate_quotient_star_same_level k (condExpFin k x),
      substrate_quotient_mul_same_level k (star (condExpFin k x)) (condExpFin k x),
      substrate_pre_trace_of_level]

/-- **RHS bridge**: `τ_UHF (⋆a·a) = pre_trace(⋆a·a)` on the dense image. -/
theorem UHF_trace_star_self_coe (a : TimelessFieldRing) :
    UHF_trace (star (a : TimelessFieldCompletion) * (a : TimelessFieldCompletion))
      = substrate_pre_trace (star a * a) := by
  rw [star_coe_TimelessFieldCompletion, ← UniformSpace.Completion.coe_mul, UHF_trace_coe]

/-- **★ The completion `‖·‖₂` contraction ★**
    `Re τ_UHF ((E_k x)⋆(E_k x)) ≤ Re τ_UHF (x⋆ x)`, lifted from r110's
    ring-level `condExp_l2_contraction` by continuity + `isClosed_le`. -/
theorem condExpCompletion_l2_contraction (k : ℕ) (x : TimelessFieldCompletion) :
    (UHF_trace (star (condExpCompletion k x) * condExpCompletion k x)).re ≤
      (UHF_trace (star x * x)).re := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    refine isClosed_le ?_ ?_
    · exact Complex.continuous_re.comp
        (UHF_trace_uniformContinuous.continuous.comp
          ((continuous_star_TimelessFieldCompletion.comp
            (condExpCompletion_continuous k)).mul (condExpCompletion_continuous k)))
    · exact Complex.continuous_re.comp
        (UHF_trace_uniformContinuous.continuous.comp
          (continuous_star_TimelessFieldCompletion.mul continuous_id))
  | ih a =>
    have hL : UHF_trace (star (condExpCompletion k (a : TimelessFieldCompletion))
          * condExpCompletion k (a : TimelessFieldCompletion))
        = normalized_matrix_trace (star (condExp k a) * condExp k a) := by
      rw [UHF_trace_condExpCompletion k (a : TimelessFieldCompletion), condExpFin_coe]
    rw [hL, UHF_trace_star_self_coe a]
    exact condExp_l2_contraction k a

/-! ## §7 — Matrix faithfulness from a nonpositive real trace -/

/-- **Matrix faithfulness in `.re`-form**: if `Re τ_{3^k}(M⋆ M) ≤ 0` then `M = 0`.
    Uses r98 positivity (`0 ≤ τ(M⋆M)` in the complex order) + r100 matrix
    faithfulness. -/
theorem matrix_faithful_of_re_nonpos {n : ℕ} [NeZero n]
    (M : Matrix (Fin n) (Fin n) ℂ)
    (hre : (normalized_matrix_trace (star M * M)).re ≤ 0) : M = 0 := by
  have hpos : (0 : ℂ) ≤ normalized_matrix_trace (star M * M) :=
    normalized_matrix_trace_star_mul_self_nonneg M
  rw [Complex.le_def] at hpos
  obtain ⟨hre_nn, him⟩ := hpos
  rw [Complex.zero_re] at hre_nn
  rw [Complex.zero_im] at him
  have hval : normalized_matrix_trace (star M * M) = 0 := by
    apply Complex.ext
    · rw [Complex.zero_re]; exact le_antisymm hre hre_nn
    · rw [Complex.zero_im]; exact him.symm
  exact (normalized_matrix_trace_star_mul_self_eq_zero_iff M).mp hval

/-! ## §8 — Faithfulness on the completion -/

/-- If `τ_UHF (x⋆ x) = 0` then `condExpFin k x = 0` (matrix level), for all `k`. -/
theorem condExpFin_eq_zero_of_faithful (k : ℕ) (x : TimelessFieldCompletion)
    (hx : UHF_trace (star x * x) = 0) : condExpFin k x = 0 := by
  have hre : (normalized_matrix_trace (star (condExpFin k x) * condExpFin k x)).re ≤ 0 := by
    have hcontr := condExpCompletion_l2_contraction k x
    rw [UHF_trace_condExpCompletion k x, hx] at hcontr
    simpa using hcontr
  exact matrix_faithful_of_re_nonpos (condExpFin k x) hre

/-- If `τ_UHF (x⋆ x) = 0` then `condExpCompletion k x = 0`, for all `k`. -/
theorem condExpCompletion_eq_zero_of_faithful (k : ℕ) (x : TimelessFieldCompletion)
    (hx : UHF_trace (star x * x) = 0) : condExpCompletion k x = 0 := by
  unfold condExpCompletion
  rw [condExpFin_eq_zero_of_faithful k x hx]
  have h0 : substrateLevelToTimelessField k (0 : Matrix (Fin (3^k)) (Fin (3^k)) ℂ)
      = (0 : TimelessFieldRing) := substrate_quotient_zero_same_level k
  rw [h0]
  exact UniformSpace.Completion.coe_zero

/-- **★★★ r112 — THE SUMMIT: `UHF_trace` IS FAITHFUL ON THE COMPLETION ★★★**
    `UHF_trace (x⋆ x) = 0 → x = 0` for every `x : TimelessFieldCompletion`,
    UNCONDITIONAL. Since `condExpCompletion k x = 0` for all `k` and
    `condExpCompletion k x → x`, uniqueness of limits forces `x = 0`. -/
theorem UHF_trace_faithful (x : TimelessFieldCompletion)
    (hx : UHF_trace (star x * x) = 0) : x = 0 := by
  have hall : ∀ k, condExpCompletion k x = 0 :=
    fun k => condExpCompletion_eq_zero_of_faithful k x hx
  have htend : Filter.Tendsto (fun k => condExpCompletion k x) Filter.atTop (nhds x) :=
    condExpCompletion_tendsto x
  have htend0 : Filter.Tendsto (fun k => condExpCompletion k x) Filter.atTop (nhds 0) := by
    simp only [hall]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique htend htend0

/-! ## §9 — Discharging the named residuals -/

/-- **★ r109 residual `CondExpCompletionExtension` DISCHARGED ★** -/
theorem condExpCompletionExtension_holds : CondExpCompletionExtension :=
  ⟨condExpCompletion,
   condExpCompletion_uniformContinuous,
   condExpCompletion_coe,
   condExpCompletion_tendsto⟩

/-- **★ r100 residual
    `SubstrateUHFCompletionPositiveFaithfulnessSubstrateConjecture` DISCHARGED ★** -/
theorem substrate_UHF_completion_positive_faithfulness :
    SubstrateUHFCompletionPositiveFaithfulnessSubstrateConjecture := by
  intro x hx
  rw [UHF_trace_faithful x hx, star_zero, mul_zero]

/-- **★ r112 — the unconditional completion faithfulness theorem ★** -/
theorem substrate_UHF_trace_faithful_unconditional :
    ∀ x : TimelessFieldCompletion, UHF_trace (star x * x) = 0 → x = 0 :=
  UHF_trace_faithful

/-- **★ r106/r108 residual `SubstrateCompletionTraceDetectsIdeals` DISCHARGED ★** -/
theorem substrate_completion_traceDetectsIdeals :
    SubstrateCompletionTraceDetectsIdeals :=
  traceDetects_iff_faithful.mpr UHF_trace_faithful

/-- **★ Completion algebraic simplicity, UNCONDITIONAL ★** — every two-sided
    ideal of `T∞̂` is `⊥` or `⊤` (Glimm simplicity of the substrate UHF algebra). -/
theorem substrate_completion_simple_unconditional :
    ∀ I : TwoSidedIdeal TimelessFieldCompletion, I = ⊥ ∨ I = ⊤ :=
  traceDetects_iff_simple.mp substrate_completion_traceDetectsIdeals

/-! ## §10 — r112 capstone -/

/-- **★★★ r112 SUBSTRATE COMPLETION-FAITHFULNESS CAPSTONE — THE SUMMIT ★★★**

    **LANDED (unconditional, kernel-only):**

      (1) `condExpFin` / `condExpCompletion` — `E_k` extended to the completion,
          `LipschitzWith 1`, uniformly continuous, with
          `condExpCompletion k ↑a = ↑(ι_k (E_k a))`.
      (2) `condExpCompletion_tendsto` — `E_k x → x` (reconstruction).
      (3) `condExpCompletion_l2_contraction` — the `‖·‖₂` contraction on the
          completion.
      (4) `UHF_trace_faithful` — **THE SUMMIT**: completion-tier faithfulness
          of the substrate UHF trace, UNCONDITIONAL.

    **RESIDUALS DISCHARGED:**

      * `CondExpCompletionExtension`                               (r109)
      * `SubstrateUHFCompletionPositiveFaithfulnessSubstrateConjecture` (r100)
      * `SubstrateCompletionTraceDetectsIdeals`                    (r106/r108)
      * completion simplicity `∀ I, I = ⊥ ∨ I = ⊤`                (r106/r108)

    r103/r106 completion faithfulness is now UNCONDITIONAL.

    Kernel-only [propext, Classical.choice, Quot.sound]. Zero project axioms.
    Zero sorries. -/
theorem r112_substrate_completion_faithful_capstone :
    CondExpCompletionExtension ∧
    (∀ x : TimelessFieldCompletion,
      Filter.Tendsto (fun k => condExpCompletion k x) Filter.atTop (nhds x)) ∧
    (∀ (k : ℕ) (x : TimelessFieldCompletion),
      (UHF_trace (star (condExpCompletion k x) * condExpCompletion k x)).re ≤
        (UHF_trace (star x * x)).re) ∧
    (∀ x : TimelessFieldCompletion, UHF_trace (star x * x) = 0 → x = 0) ∧
    SubstrateUHFCompletionPositiveFaithfulnessSubstrateConjecture ∧
    SubstrateCompletionTraceDetectsIdeals ∧
    (∀ I : TwoSidedIdeal TimelessFieldCompletion, I = ⊥ ∨ I = ⊤) :=
  ⟨condExpCompletionExtension_holds,
   condExpCompletion_tendsto,
   condExpCompletion_l2_contraction,
   UHF_trace_faithful,
   substrate_UHF_completion_positive_faithfulness,
   substrate_completion_traceDetectsIdeals,
   substrate_completion_simple_unconditional⟩

/-! ## §11 — Axiom audit -/

#print axioms condExp_lipschitz
#print axioms substrateLevelToTimelessField_iter
#print axioms substrateLevelToTimelessField_isometry
#print axioms condExpFin
#print axioms condExpCompletion
#print axioms condExpCompletion_coe
#print axioms condExpCompletion_tendsto
#print axioms condExpCompletion_l2_contraction
#print axioms UHF_trace_faithful
#print axioms condExpCompletionExtension_holds
#print axioms substrate_UHF_completion_positive_faithfulness
#print axioms substrate_UHF_trace_faithful_unconditional
#print axioms substrate_completion_traceDetectsIdeals
#print axioms substrate_completion_simple_unconditional
#print axioms r112_substrate_completion_faithful_capstone

end SubstrateCompletionFaithful
end PrincipiaTractalis
