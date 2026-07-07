/-
# r87: The substrate pre-trace on `TimelessFieldRing` via direct-limit lift

★ 2026-07-07 r87 — closing the last analytic residual of the substrate
UHF trace on `TimelessFieldCompletion` ★

## The framework-first content

r86 supplied the completion-extension scaffolding conditional on a
uniformly continuous linear + unital pre-trace on `TimelessFieldRing`.
r87 constructs that pre-trace explicitly:

    substrate_pre_trace : TimelessFieldRing → ℂ

via `DirectLimit.lift` applied to the family of level-k normalized
matrix traces `τ_k = normalized_matrix_trace` (r84) subject to the
substrate compatibility condition:

    τ_j (substrateRingHomIter i j h A) = τ_i A

which itself reduces (by induction on the level gap) to the single-step
trace-preservation identity

    normalized_matrix_trace (substrateEmbedMatrix k A) =
      normalized_matrix_trace A

proved via the block-diagonal structure `substrateEmbedMatrix k A =
Matrix.reindex (levelStepEquiv k) (levelStepEquiv k) (A ⊗ₖ I_3)` +
`trace_kronecker` + `trace_reindex_self` + arithmetic on `3^(k+1)`.

Combined with the r86 substrate reduction, r87 UNCONDITIONALLY
supplies the substrate UHF trace on `TimelessFieldCompletion`.

## Semantic scope

r87 delivers:
  * Kernel-verified single-step trace preservation.
  * Kernel-verified iterated trace preservation via `Nat.le_induction`.
  * Explicit `substrate_pre_trace` via `DirectLimit.lift`.
  * Kernel-verified additivity + unital via `DirectLimit.induction₂`
    + r84 matrix-level linearity + `substrate_quotient_add_same_level`.
  * Kernel-verified 1-Lipschitz distance bound via r86 level-k
    Lipschitz + r43 level embedding isometry + `DirectLimit.neg_def`
    + `substrate_quotient_add_same_level`.
  * Kernel-verified uniform continuity via `LipschitzWith.uniformContinuous`.
  * Discharge of `SubstratePreTraceExistsConjecture` (r86 residual).
  * Discharge of `SubstrateUHFTraceExistsConjecture` (chain through r86
    `substrate_UHF_trace_from_pre_trace`).
  * r87 capstone bundling all identities.

Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
axioms. Zero sorries.

Stage 2026-07-07 r87 — substrate pre-trace on TimelessFieldRing +
unconditional UHF trace on TimelessFieldCompletion.
-/

import PF.SubstrateUHFCompletionTrace
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace SubstrateUHFPreTraceDirectLimit

open scoped Matrix.Norms.L2Operator
open scoped ComplexOrder
open scoped Kronecker
open SubstrateUHFBoundedTrace SubstrateUHFTraceLipschitz
open SubstrateUHFCompletionTrace
open SubstrateBase3Embed SubstrateBase3RingHom SubstrateDirectLimit
open SubstrateTimelessFieldCompletion SubstrateTimelessFieldNorm

/-! ## §1 — Auxiliary: trace preserved under `Matrix.reindex e e` -/

/-- **Trace of a same-equiv reindexing agrees with the original trace**.

    For `M : Matrix ι ι ℂ` and any `e : ι ≃ κ`,
    `Matrix.trace (Matrix.reindex e e M) = Matrix.trace M`. -/
lemma trace_reindex_self {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (M : Matrix ι ι ℂ) :
    Matrix.trace (Matrix.reindex e e M) = Matrix.trace M := by
  show ∑ i, (M.submatrix e.symm e.symm) i i = ∑ j, M j j
  exact Fintype.sum_bijective e.symm e.symm.bijective
    (fun i => (M.submatrix e.symm e.symm) i i)
    (fun j => M j j)
    (fun _ => rfl)

/-! ## §2 — Single-step trace preservation of the substrate embedding

`substrateEmbedMatrix k A = Matrix.reindex (levelStepEquiv k)
(levelStepEquiv k) (A ⊗ₖ I_3)`. Its trace equals `3 · trace A`, and
its normalized trace equals `normalized_matrix_trace A`. -/

/-- **r87.a: trace of `substrateEmbedMatrix k A`** equals `3 · trace A`. -/
theorem substrateEmbedMatrix_trace (k : ℕ)
    (A : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    Matrix.trace (substrateEmbedMatrix k A) = 3 * Matrix.trace A := by
  unfold substrateEmbedMatrix
  rw [trace_reindex_self, Matrix.trace_kronecker, Matrix.trace_one,
      Fintype.card_fin]
  ring

/-- **r87.b: substrate embedding preserves the normalized trace**. -/
theorem substrateEmbedMatrix_normalized_trace (k : ℕ)
    (A : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    normalized_matrix_trace (substrateEmbedMatrix k A) =
      normalized_matrix_trace A := by
  unfold normalized_matrix_trace
  rw [substrateEmbedMatrix_trace]
  have h_pow : ((3^(k+1) : ℕ) : ℂ) = 3 * ((3^k : ℕ) : ℂ) := by
    push_cast; rw [pow_succ]; ring
  rw [h_pow]
  have h3 : (3 : ℂ) ≠ 0 := by norm_num
  have h3k : ((3^k : ℕ) : ℂ) ≠ 0 := by
    have h3n : (3^k : ℕ) ≠ 0 := by positivity
    exact_mod_cast h3n
  field_simp

/-- **r87.c: substrate RingHom bundle preserves the normalized trace**.

    Immediate from r87.b via the r29 `substrateRingHom_apply` identity. -/
theorem substrateRingHom_normalized_trace (k : ℕ)
    (A : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    normalized_matrix_trace (substrateRingHom k A) =
      normalized_matrix_trace A := by
  rw [substrateRingHom_apply]
  exact substrateEmbedMatrix_normalized_trace k A

/-! ## §3 — Iterated trace preservation via `Nat.le_induction` -/

/-- **r87.d: iterated substrate embedding preserves the normalized trace**.

    By induction on the level gap `i ≤ j` using `substrateRingHomIter_self`
    (base) and `substrateRingHomIter_succ` (step). -/
theorem substrateRingHomIter_normalized_trace (i : ℕ) :
    ∀ (j : ℕ) (h : i ≤ j) (A : Matrix (Fin (3^i)) (Fin (3^i)) ℂ),
    normalized_matrix_trace (substrateRingHomIter i j h A) =
      normalized_matrix_trace A := by
  intro j h
  induction j, h using Nat.le_induction with
  | base =>
    intro A
    rw [substrateRingHomIter_self]
    rfl
  | succ n hn ih =>
    intro A
    rw [substrateRingHomIter_succ i n hn (hn.trans (Nat.le_succ n))]
    rw [RingHom.comp_apply]
    rw [substrateRingHom_normalized_trace n (substrateRingHomIter i n hn A)]
    exact ih A

/-! ## §4 — The substrate pre-trace via `DirectLimit.lift` -/

/-- **★★★ r87 SUBSTRATE PRE-TRACE ★★★** on `TimelessFieldRing`.

    Constructed via `DirectLimit.lift` from the family of level-k
    normalized matrix traces, using r87.d as the compatibility witness. -/
noncomputable def substrate_pre_trace : TimelessFieldRing → ℂ :=
  DirectLimit.lift
    (fun i j (h : i ≤ j) => substrateRingHomIter i j h)
    (fun _ A => normalized_matrix_trace A)
    (fun i j h A => (substrateRingHomIter_normalized_trace i j h A).symm)

/-- **r87.e: `substrate_pre_trace` at a level representative**:
    `substrate_pre_trace ⟦(k, A)⟧ = normalized_matrix_trace A`. -/
@[simp] theorem substrate_pre_trace_of_level (k : ℕ)
    (A : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    substrate_pre_trace (⟦⟨k, A⟩⟧ : TimelessFieldRing) =
      normalized_matrix_trace A :=
  rfl

/-! ## §5 — Additivity + unital of `substrate_pre_trace` -/

/-- **r87.f: `substrate_pre_trace` is additive**. Proved via
    `DirectLimit.exists_eq_mk₂` reducing to common-level representatives +
    `substrate_quotient_add_same_level` + r84's matrix-level additivity. -/
theorem substrate_pre_trace_add (x y : TimelessFieldRing) :
    substrate_pre_trace (x + y) =
      substrate_pre_trace x + substrate_pre_trace y := by
  obtain ⟨i, A, B, hx, hy⟩ :=
    DirectLimit.exists_eq_mk₂
      (fun i j (h : i ≤ j) => substrateRingHomIter i j h) x y
  subst hx; subst hy
  rw [substrate_quotient_add_same_level i A B]
  show normalized_matrix_trace (A + B) =
       normalized_matrix_trace A + normalized_matrix_trace B
  exact normalized_matrix_trace_add A B

/-- **r87.g: `substrate_pre_trace` sends 1 to 1**. -/
theorem substrate_pre_trace_one :
    substrate_pre_trace (1 : TimelessFieldRing) = 1 := by
  have h_one_def : (1 : TimelessFieldRing) =
      (⟦⟨0, (1 : Matrix (Fin (3^0)) (Fin (3^0)) ℂ)⟩⟧ : TimelessFieldRing) :=
    DirectLimit.one_def
      (G := fun k : ℕ => Matrix (Fin (3^k)) (Fin (3^k)) ℂ)
      (f := fun i j (h : i ≤ j) => substrateRingHomIter i j h) 0
  rw [h_one_def]
  show normalized_matrix_trace (1 : Matrix (Fin (3^0)) (Fin (3^0)) ℂ) = 1
  exact normalized_matrix_trace_one

/-! ## §6 — 1-Lipschitz + uniform continuity of `substrate_pre_trace` -/

/-- **r87.h: `substrate_pre_trace` distance bound**.
    For common-level representatives x = ⟦(i, A)⟧, y = ⟦(i, B)⟧:

        dist (substrate_pre_trace x) (substrate_pre_trace y) ≤ dist x y

    Reduces (via `DirectLimit.induction₂`) to:

        dist (τ_i A) (τ_i B) ≤ dist ⟦(i, A)⟧ ⟦(i, B)⟧

    where LHS ≤ dist A B via r86 level-k Lipschitz and RHS = dist A B
    via r43 level-embedding isometry + `substrate_quotient_add_same_level`
    + `DirectLimit.neg_def`. -/
theorem substrate_pre_trace_dist_bound (x y : TimelessFieldRing) :
    dist (substrate_pre_trace x) (substrate_pre_trace y) ≤ dist x y := by
  -- Reduce to common-level representatives via r43 substrateLevelToTimelessField.
  obtain ⟨i, A, B, hx, hy⟩ :=
    DirectLimit.exists_eq_mk₂
      (fun i j (h : i ≤ j) => substrateRingHomIter i j h) x y
  -- Rewrite x = substrateLevelToTimelessField i A, y = substrateLevelToTimelessField i B
  have hx' : x = substrateLevelToTimelessField i A := hx
  have hy' : y = substrateLevelToTimelessField i B := hy
  rw [hx', hy']
  -- pre-trace on the level embedding = normalized_matrix_trace A/B
  have h_ptA : substrate_pre_trace (substrateLevelToTimelessField i A) =
                 normalized_matrix_trace A := rfl
  have h_ptB : substrate_pre_trace (substrateLevelToTimelessField i B) =
                 normalized_matrix_trace B := rfl
  rw [h_ptA, h_ptB]
  -- Substrate LHS: dist τA τB ≤ dist A B (r86 level-k Lipschitz)
  have h_LHS :
      dist (normalized_matrix_trace A) (normalized_matrix_trace B) ≤ dist A B :=
    substrate_level_trace_dist_bound A B
  -- Substrate RHS: dist (embed A) (embed B) = dist A B via r43 isometry.
  have h_RHS :
      dist (substrateLevelToTimelessField i A)
           (substrateLevelToTimelessField i B) = dist A B := by
    rw [dist_eq_norm, dist_eq_norm]
    -- Reduce the norm of a subtraction of level-embedded elements.
    have h_neg_def :
        -(substrateLevelToTimelessField i B) =
          substrateLevelToTimelessField i (-B) :=
      DirectLimit.neg_def
        (G := fun k : ℕ => Matrix (Fin (3^k)) (Fin (3^k)) ℂ)
        (f := fun i j (h : i ≤ j) => substrateRingHomIter i j h) i B
    have h_add_def :
        substrateLevelToTimelessField i A +
          substrateLevelToTimelessField i (-B) =
            substrateLevelToTimelessField i (A + -B) :=
      substrate_quotient_add_same_level i A (-B)
    calc ‖substrateLevelToTimelessField i A - substrateLevelToTimelessField i B‖
        = ‖substrateLevelToTimelessField i A + (-substrateLevelToTimelessField i B)‖ := by
          rw [sub_eq_add_neg]
      _ = ‖substrateLevelToTimelessField i A + substrateLevelToTimelessField i (-B)‖ := by
          rw [h_neg_def]
      _ = ‖substrateLevelToTimelessField i (A + -B)‖ := by rw [h_add_def]
      _ = ‖A + -B‖ := substrateLevelToTimelessField_opNorm_eq i (A + -B)
      _ = ‖A - B‖ := by rw [← sub_eq_add_neg]
  rw [h_RHS]
  exact h_LHS

/-- **r87.i: `substrate_pre_trace` is `LipschitzWith 1`**. -/
theorem substrate_pre_trace_lipschitz :
    LipschitzWith 1 substrate_pre_trace :=
  LipschitzWith.mk_one substrate_pre_trace_dist_bound

/-- **r87.j: `substrate_pre_trace` is uniformly continuous**. -/
theorem substrate_pre_trace_uniformContinuous :
    UniformContinuous substrate_pre_trace :=
  substrate_pre_trace_lipschitz.uniformContinuous

/-! ## §7 — Discharge of the r86 substrate residuals -/

/-- **★★★ r87: `SubstratePreTraceExistsConjecture` DISCHARGED ★★★**.

    r87 supplies `substrate_pre_trace` as the existential witness. -/
theorem substrate_pre_trace_exists : SubstratePreTraceExistsConjecture :=
  ⟨substrate_pre_trace,
   substrate_pre_trace_uniformContinuous,
   substrate_pre_trace_add,
   substrate_pre_trace_one⟩

/-- **★★★ r87: `SubstrateUHFTraceExistsConjecture` DISCHARGED ★★★**.

    Chain: r87 pre-trace existence ⇒ r86 substrate reduction ⇒
    UHF trace on `TimelessFieldCompletion` exists. -/
theorem substrate_UHF_trace_exists : SubstrateUHFTraceExistsConjecture :=
  substrate_UHF_trace_from_pre_trace substrate_pre_trace_exists

/-! ## §8 — Explicit UHF trace on TimelessFieldCompletion -/

/-- **The substrate UHF trace on `TimelessFieldCompletion`**, explicitly.

    Defined as the completion extension of the r87 substrate pre-trace. -/
noncomputable def UHF_trace : TimelessFieldCompletion → ℂ :=
  UHF_trace_extension_from_pre_trace substrate_pre_trace

/-- **r87.k: `UHF_trace` is uniformly continuous**. -/
theorem UHF_trace_uniformContinuous : UniformContinuous UHF_trace :=
  UHF_trace_extension_uniformContinuous substrate_pre_trace

/-- **r87.l: `UHF_trace` agrees with the substrate pre-trace on the
    dense embedded image**. -/
theorem UHF_trace_coe (a : TimelessFieldRing) :
    UHF_trace (a : TimelessFieldCompletion) = substrate_pre_trace a :=
  UHF_trace_extension_agrees_on_dense
    substrate_pre_trace substrate_pre_trace_uniformContinuous a

/-! ## §9 — r87 substrate pre-trace + UHF trace capstone -/

/-- **★★★ r87 SUBSTRATE PRE-TRACE + UHF TRACE CAPSTONE ★★★**

    Bundles the r87 substrate content:

      (Z1) `substrateEmbedMatrix_trace` — the block-diagonal formula
           `trace (substrateEmbedMatrix k A) = 3 · trace A`.
      (Z2) `substrateEmbedMatrix_normalized_trace` — single-step
           normalized-trace preservation.
      (Z3) `substrateRingHomIter_normalized_trace` — iterated normalized-
           trace preservation via `Nat.le_induction`.
      (Z4) `substrate_pre_trace : TimelessFieldRing → ℂ` — the pre-trace
           via `DirectLimit.lift`.
      (Z5) `substrate_pre_trace_add` + `substrate_pre_trace_one` —
           additivity + unital.
      (Z6) `substrate_pre_trace_dist_bound` — 1-Lipschitz distance bound
           via r86 level-k Lipschitz + r43 level-embedding isometry.
      (Z7) `substrate_pre_trace_uniformContinuous` — the UC property.
      (Z8) `substrate_pre_trace_exists : SubstratePreTraceExistsConjecture`
           — the r86 substrate residual DISCHARGED.
      (Z9) `substrate_UHF_trace_exists : SubstrateUHFTraceExistsConjecture`
           — the essential UHF trace target DISCHARGED (via r86 reduction).
      (Z10) `UHF_trace : TimelessFieldCompletion → ℂ` — the substrate
            UHF trace, explicitly.
      (Z11) `UHF_trace_uniformContinuous` — the UHF trace is UC.
      (Z12) `UHF_trace_coe` — dense-image agreement of the UHF trace.

    Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
    axioms. Zero sorries.

    Substrate significance: r87 closes the entire analytic side of
    the substrate UHF trace construction. The substrate normalized
    matrix trace on each finite level (r84) lifts unconditionally
    to a uniformly continuous linear + unital ℂ-valued function on
    `TimelessFieldCompletion` (the r53-r59 UHF C*-algebra completion).
    This is the essential UHF trace of the substrate ToE spectral
    bridge. Subsequent substrate work will connect this trace to
    the r82 canonical trace value τ(δ_i) = 1/9 via the density of
    the substrate 9-projection realization inside `TimelessFieldRing`. -/
theorem r87_substrate_pre_trace_and_UHF_trace_capstone :
    (∀ (k : ℕ) (A : Matrix (Fin (3^k)) (Fin (3^k)) ℂ),
      Matrix.trace (substrateEmbedMatrix k A) = 3 * Matrix.trace A) ∧
    (∀ (k : ℕ) (A : Matrix (Fin (3^k)) (Fin (3^k)) ℂ),
      normalized_matrix_trace (substrateEmbedMatrix k A) =
        normalized_matrix_trace A) ∧
    (∀ (i j : ℕ) (h : i ≤ j) (A : Matrix (Fin (3^i)) (Fin (3^i)) ℂ),
      normalized_matrix_trace (substrateRingHomIter i j h A) =
        normalized_matrix_trace A) ∧
    (∀ x y : TimelessFieldRing,
      substrate_pre_trace (x + y) =
        substrate_pre_trace x + substrate_pre_trace y) ∧
    substrate_pre_trace (1 : TimelessFieldRing) = 1 ∧
    LipschitzWith 1 substrate_pre_trace ∧
    UniformContinuous substrate_pre_trace ∧
    SubstratePreTraceExistsConjecture ∧
    SubstrateUHFTraceExistsConjecture ∧
    UniformContinuous UHF_trace ∧
    (∀ a : TimelessFieldRing,
      UHF_trace (a : TimelessFieldCompletion) = substrate_pre_trace a) :=
  ⟨substrateEmbedMatrix_trace,
   substrateEmbedMatrix_normalized_trace,
   fun i j h A => substrateRingHomIter_normalized_trace i j h A,
   substrate_pre_trace_add,
   substrate_pre_trace_one,
   substrate_pre_trace_lipschitz,
   substrate_pre_trace_uniformContinuous,
   substrate_pre_trace_exists,
   substrate_UHF_trace_exists,
   UHF_trace_uniformContinuous,
   UHF_trace_coe⟩

end SubstrateUHFPreTraceDirectLimit
end PrincipiaTractalis
