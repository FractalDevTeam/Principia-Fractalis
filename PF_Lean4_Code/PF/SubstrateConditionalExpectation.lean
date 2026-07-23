/-
# r109: The substrate trace-preserving conditional expectation E_k : T∞ → M_{3^k}

★ 2026-07-22 r109 — THE KEYSTONE construction: the partial-trace conditional
expectation onto the level-k corner of the substrate UHF algebra. ★

Per r108's TFAE (PF/SubstrateTraceDetectionAttempt.lean), the entire
completion-tier faithfulness summit collapses to the construction of the
trace-preserving conditional expectation `E_k : T∞ → M_{3^k}`, which is a
`‖·‖₂`-contraction with `E_k x → x`. r109 builds the tractable core of that
object — the partial trace over the tail — at the matrix level and descends
it to the algebraic direct limit `TimelessFieldRing`.

Stage 2026-07-22 r109 — substrate conditional expectation (partial trace).
-/

import PF.SubstrateUHFTraceIsFaithful
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace SubstrateConditionalExpectation

open scoped Kronecker
open scoped ComplexOrder
open SubstrateBase3Embed SubstrateBase3RingHom SubstrateDirectLimit
open SubstrateUHFBoundedTrace SubstrateUHFPreTraceDirectLimit
open SubstrateTimelessFieldCompletion SubstrateTimelessFieldNorm
open SubstrateUHFTraceIsStarPreserving

/-! ## §1 — The single-step partial trace `M_{3^{n+1}} → M_{3^n}` -/

/-- **Single-step partial trace** — traces out the trailing `Fin 3` tensor
    factor. Under the reindexing `levelStepEquiv n : Fin(3^n) × Fin 3 ≃
    Fin(3^{n+1})`, this is `(id ⊗ τ₃)` where `τ₃` is the normalized trace on
    the 3×3 block: `(E B) i j = (1/3) Σ_t B (i,t) (j,t)`. -/
noncomputable def partialTraceStep (n : ℕ)
    (B : Matrix (Fin (3^(n+1))) (Fin (3^(n+1))) ℂ) :
    Matrix (Fin (3^n)) (Fin (3^n)) ℂ :=
  Matrix.of fun i j =>
    (3⁻¹ : ℂ) * ∑ t : Fin 3, B (levelStepEquiv n (i, t)) (levelStepEquiv n (j, t))

@[simp] theorem partialTraceStep_apply (n : ℕ)
    (B : Matrix (Fin (3^(n+1))) (Fin (3^(n+1))) ℂ) (i j : Fin (3^n)) :
    partialTraceStep n B i j =
      (3⁻¹ : ℂ) * ∑ t : Fin 3,
        B (levelStepEquiv n (i, t)) (levelStepEquiv n (j, t)) := rfl

/-- **The partial trace inverts the substrate embedding** (single step):
    `E (ι_n A) = A`. This is the "identity on the level-n corner" property. -/
theorem partialTraceStep_substrateEmbedMatrix (n : ℕ)
    (A : Matrix (Fin (3^n)) (Fin (3^n)) ℂ) :
    partialTraceStep n (substrateEmbedMatrix n A) = A := by
  ext i j
  have hval : ∀ t : Fin 3,
      (substrateEmbedMatrix n A)
        (levelStepEquiv n (i, t)) (levelStepEquiv n (j, t)) = A i j := by
    intro t
    unfold substrateEmbedMatrix
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      Matrix.kronecker_apply, Matrix.one_apply_eq, mul_one]
  rw [partialTraceStep_apply, Finset.sum_congr rfl (fun t _ => hval t)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← mul_assoc, show (3⁻¹ : ℂ) * ((3 : ℕ) : ℂ) = 1 by push_cast; norm_num, one_mul]

/-! ## §2 — Trace preservation of the single-step partial trace -/

/-- Reindexing bijection sum identity: `Σ_{(i,t)} B (lse (i,t)) (lse (i,t))
    = Σ_p B p p = trace B`. -/
theorem partialTraceStep_trace (n : ℕ)
    (B : Matrix (Fin (3^(n+1))) (Fin (3^(n+1))) ℂ) :
    Matrix.trace (partialTraceStep n B) = (3⁻¹ : ℂ) * Matrix.trace B := by
  simp only [Matrix.trace, Matrix.diag_apply, partialTraceStep_apply]
  rw [← Finset.mul_sum]
  congr 1
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_bijective (levelStepEquiv n) (levelStepEquiv n).bijective
    (fun p => B (levelStepEquiv n p) (levelStepEquiv n p))
    (fun q => B q q) (fun _ => rfl)

/-- **Single-step normalized-trace preservation.** -/
theorem partialTraceStep_normalized_trace (n : ℕ)
    (B : Matrix (Fin (3^(n+1))) (Fin (3^(n+1))) ℂ) :
    normalized_matrix_trace (partialTraceStep n B) =
      normalized_matrix_trace B := by
  unfold normalized_matrix_trace
  rw [partialTraceStep_trace]
  have h_pow : ((3^(n+1) : ℕ) : ℂ) = 3 * ((3^n : ℕ) : ℂ) := by
    push_cast; rw [pow_succ]; ring
  rw [h_pow]
  have h3 : (3 : ℂ) ≠ 0 := by norm_num
  have h3k : ((3^n : ℕ) : ℂ) ≠ 0 := by
    have : (3^n : ℕ) ≠ 0 := by positivity
    exact_mod_cast this
  field_simp

/-! ## §2b — Construction 1a: the single-step partial trace is ℂ-linear,
    unital, and *-preserving. -/

/-- **Additive.** -/
theorem partialTraceStep_add (n : ℕ)
    (B C : Matrix (Fin (3^(n+1))) (Fin (3^(n+1))) ℂ) :
    partialTraceStep n (B + C) =
      partialTraceStep n B + partialTraceStep n C := by
  ext i j
  simp only [partialTraceStep_apply, Matrix.add_apply, Finset.sum_add_distrib, mul_add]

/-- **ℂ-homogeneous.** -/
theorem partialTraceStep_smul (n : ℕ) (c : ℂ)
    (B : Matrix (Fin (3^(n+1))) (Fin (3^(n+1))) ℂ) :
    partialTraceStep n (c • B) = c • partialTraceStep n B := by
  ext i j
  simp only [partialTraceStep_apply, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

/-- **Unital.** -/
theorem partialTraceStep_one (n : ℕ) :
    partialTraceStep n (1 : Matrix (Fin (3^(n+1))) (Fin (3^(n+1))) ℂ) =
      (1 : Matrix (Fin (3^n)) (Fin (3^n)) ℂ) := by
  ext i j
  rw [partialTraceStep_apply]
  by_cases hij : i = j
  · subst hij
    rw [Finset.sum_congr rfl (fun t _ => Matrix.one_apply_eq (levelStepEquiv n (i, t))),
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
        show (3⁻¹ : ℂ) * ((3 : ℕ) : ℂ) = 1 by push_cast; norm_num, Matrix.one_apply_eq]
  · have hne : ∀ t : Fin 3, (1 : Matrix (Fin (3^(n+1))) (Fin (3^(n+1))) ℂ)
        (levelStepEquiv n (i, t)) (levelStepEquiv n (j, t)) = 0 := by
      intro t
      apply Matrix.one_apply_ne
      intro h
      exact hij (congrArg Prod.fst ((levelStepEquiv n).injective h))
    rw [Finset.sum_congr rfl (fun t _ => hne t), Finset.sum_const_zero, mul_zero,
        Matrix.one_apply_ne hij]

/-- **\*-preserving** (`star` = conjugate transpose). -/
theorem partialTraceStep_star (n : ℕ)
    (B : Matrix (Fin (3^(n+1))) (Fin (3^(n+1))) ℂ) :
    partialTraceStep n (star B) = star (partialTraceStep n B) := by
  ext i j
  rw [partialTraceStep_apply, Matrix.star_apply, partialTraceStep_apply]
  simp only [Matrix.star_apply]
  have h3 : star (3⁻¹ : ℂ) = 3⁻¹ := by rw [star_inv₀]; norm_num
  rw [star_mul', h3, star_sum]

/-! ## §3 — The iterated partial trace `partialTraceDown k j : M_{3^j} → M_{3^k}` -/

/-- **Iterated partial trace** — traces out the tail from level `j` down to
    level `k` (for `k ≤ j`), by composing the single-step partial traces. -/
noncomputable def partialTraceDown (k j : ℕ) (h : k ≤ j) :
    Matrix (Fin (3^j)) (Fin (3^j)) ℂ → Matrix (Fin (3^k)) (Fin (3^k)) ℂ :=
  Nat.leRecOn h
    (fun {m}
      (g : Matrix (Fin (3^m)) (Fin (3^m)) ℂ → Matrix (Fin (3^k)) (Fin (3^k)) ℂ) =>
      (fun B => g (partialTraceStep m B)))
    (id)

theorem partialTraceDown_self (k : ℕ) :
    partialTraceDown k k le_rfl = id := by
  unfold partialTraceDown
  exact Nat.leRecOn_self _

theorem partialTraceDown_succ (k n : ℕ) (h1 : k ≤ n) (h2 : k ≤ n + 1) :
    partialTraceDown k (n + 1) h2 =
      fun B => partialTraceDown k n h1 (partialTraceStep n B) := by
  unfold partialTraceDown
  exact Nat.leRecOn_succ h1 _

theorem partialTraceDown_succ_apply (k n : ℕ) (h1 : k ≤ n) (h2 : k ≤ n + 1)
    (B : Matrix (Fin (3^(n+1))) (Fin (3^(n+1))) ℂ) :
    partialTraceDown k (n + 1) h2 B =
      partialTraceDown k n h1 (partialTraceStep n B) :=
  congrFun (partialTraceDown_succ k n h1 h2) B

/-- **Iterated normalized-trace preservation.** -/
theorem partialTraceDown_normalized_trace (k : ℕ) :
    ∀ (j : ℕ) (h : k ≤ j) (B : Matrix (Fin (3^j)) (Fin (3^j)) ℂ),
    normalized_matrix_trace (partialTraceDown k j h B) =
      normalized_matrix_trace B := by
  intro j h
  induction j, h using Nat.le_induction with
  | base => intro B; rw [partialTraceDown_self]; rfl
  | succ n hn ih =>
    intro B
    rw [partialTraceDown_succ_apply k n hn (Nat.le_succ_of_le hn),
        ih (partialTraceStep n B), partialTraceStep_normalized_trace]

/-- **The iterated partial trace inverts the iterated substrate embedding**
    over a gap: for `k ≤ i ≤ j`, `E_k^j (ι_{i→j} A) = E_k^i A`. -/
theorem partialTraceDown_substrateRingHomIter (k i : ℕ) (hki : k ≤ i) :
    ∀ (j : ℕ) (hij : i ≤ j) (A : Matrix (Fin (3^i)) (Fin (3^i)) ℂ),
    partialTraceDown k j (hki.trans hij) (substrateRingHomIter i j hij A) =
      partialTraceDown k i hki A := by
  intro j hij
  induction j, hij using Nat.le_induction with
  | base =>
    intro A
    rw [substrateRingHomIter_self]; rfl
  | succ n hn ih =>
    intro A
    have hkn : k ≤ n := hki.trans hn
    rw [partialTraceDown_succ_apply k n hkn (hki.trans (Nat.le_succ_of_le hn)),
        substrateRingHomIter_succ i n hn (hn.trans (Nat.le_succ n)),
        RingHom.comp_apply, substrateRingHom_apply,
        partialTraceStep_substrateEmbedMatrix]
    exact ih A

/-- **Special case**: the iterated partial trace inverts the embedding of a
    level-`k` element: `E_k^j (ι_{k→j} C) = C`. -/
theorem partialTraceDown_substrateRingHomIter_self (k j : ℕ) (hkj : k ≤ j)
    (C : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    partialTraceDown k j hkj (substrateRingHomIter k j hkj C) = C := by
  have hmain := partialTraceDown_substrateRingHomIter k k le_rfl j hkj C
  rw [partialTraceDown_self] at hmain
  exact hmain

/-! ## §3b — Construction 1a lifted to the iterated partial trace. -/

theorem partialTraceDown_add (k : ℕ) :
    ∀ (j : ℕ) (h : k ≤ j) (B C : Matrix (Fin (3^j)) (Fin (3^j)) ℂ),
    partialTraceDown k j h (B + C) =
      partialTraceDown k j h B + partialTraceDown k j h C := by
  intro j h
  induction j, h using Nat.le_induction with
  | base => intro B C; rw [partialTraceDown_self]; rfl
  | succ n hn ih =>
    intro B C
    simp only [partialTraceDown_succ_apply k n hn (Nat.le_succ_of_le hn),
      partialTraceStep_add, ih]

theorem partialTraceDown_smul (k : ℕ) :
    ∀ (j : ℕ) (h : k ≤ j) (c : ℂ) (B : Matrix (Fin (3^j)) (Fin (3^j)) ℂ),
    partialTraceDown k j h (c • B) = c • partialTraceDown k j h B := by
  intro j h
  induction j, h using Nat.le_induction with
  | base => intro c B; rw [partialTraceDown_self]; rfl
  | succ n hn ih =>
    intro c B
    simp only [partialTraceDown_succ_apply k n hn (Nat.le_succ_of_le hn),
      partialTraceStep_smul, ih]

theorem partialTraceDown_one (k : ℕ) :
    ∀ (j : ℕ) (h : k ≤ j),
    partialTraceDown k j h (1 : Matrix (Fin (3^j)) (Fin (3^j)) ℂ) = 1 := by
  intro j h
  induction j, h using Nat.le_induction with
  | base => rw [partialTraceDown_self]; rfl
  | succ n hn ih =>
    rw [partialTraceDown_succ_apply k n hn (Nat.le_succ_of_le hn),
        partialTraceStep_one, ih]

theorem partialTraceDown_star (k : ℕ) :
    ∀ (j : ℕ) (h : k ≤ j) (B : Matrix (Fin (3^j)) (Fin (3^j)) ℂ),
    partialTraceDown k j h (star B) = star (partialTraceDown k j h B) := by
  intro j h
  induction j, h using Nat.le_induction with
  | base => intro B; rw [partialTraceDown_self]; rfl
  | succ n hn ih =>
    intro B
    rw [partialTraceDown_succ_apply k n hn (Nat.le_succ_of_le hn),
        partialTraceStep_star, ih,
        partialTraceDown_succ_apply k n hn (Nat.le_succ_of_le hn)]

/-! ## §4 — The level maps to `M_{3^k}` and their cocone compatibility -/

open Classical in
/-- **Level map to the level-`k` corner.** For `k ≤ m` it is the partial
    trace `M_{3^m} → M_{3^k}`; for `m < k` it is the substrate embedding
    `M_{3^m} → M_{3^k}`. These agree on overlaps and form a cocone. -/
noncomputable def levelToLevelK (k m : ℕ) :
    Matrix (Fin (3^m)) (Fin (3^m)) ℂ → Matrix (Fin (3^k)) (Fin (3^k)) ℂ :=
  if h : k ≤ m then partialTraceDown k m h
  else substrateRingHomIter m k (le_of_not_le h)

theorem levelToLevelK_of_le (k m : ℕ) (h : k ≤ m)
    (A : Matrix (Fin (3^m)) (Fin (3^m)) ℂ) :
    levelToLevelK k m A = partialTraceDown k m h A := by
  unfold levelToLevelK; rw [dif_pos h]

theorem levelToLevelK_of_ge (k m : ℕ) (h : m ≤ k)
    (A : Matrix (Fin (3^m)) (Fin (3^m)) ℂ) :
    levelToLevelK k m A = substrateRingHomIter m k h A := by
  unfold levelToLevelK
  by_cases hk : k ≤ m
  · rw [dif_pos hk]
    have hmk : m = k := le_antisymm h hk
    subst hmk
    rw [partialTraceDown_self, substrateRingHomIter_self]; rfl
  · rw [dif_neg hk]

/-- **Cocone compatibility of the level maps** — the load-bearing
    well-definedness input for descending `E_k` to the direct limit:
    `levelToLevelK k i A = levelToLevelK k j (ι_{i→j} A)` for `i ≤ j`. -/
theorem levelToLevelK_compat (k i j : ℕ) (hij : i ≤ j)
    (A : Matrix (Fin (3^i)) (Fin (3^i)) ℂ) :
    levelToLevelK k i A =
      levelToLevelK k j (substrateRingHomIter i j hij A) := by
  by_cases hki : k ≤ i
  · -- Case A: k ≤ i ≤ j — both branches are partial traces.
    have hkj : k ≤ j := hki.trans hij
    rw [levelToLevelK_of_le k i hki, levelToLevelK_of_le k j hkj,
        partialTraceDown_substrateRingHomIter k i hki j hij A]
  · by_cases hkj : k ≤ j
    · -- Case B: i < k ≤ j.
      have hik : i ≤ k := le_of_not_le hki
      rw [levelToLevelK_of_ge k i hik, levelToLevelK_of_le k j hkj]
      -- ι_{i→j} A = ι_{k→j} (ι_{i→k} A), then partial trace inverts ι_{k→j}.
      rw [← substrateRingHomIter_comp_apply i k j hik hkj A,
          partialTraceDown_substrateRingHomIter_self k j hkj]
    · -- Case C: i ≤ j < k — both branches are embeddings.
      have hik : i ≤ k := le_trans hij (le_of_not_le hkj)
      have hjk : j ≤ k := le_of_not_le hkj
      rw [levelToLevelK_of_ge k i hik, levelToLevelK_of_ge k j hjk,
          substrateRingHomIter_comp_apply i j k hij hjk A]

/-! ## §5 — The substrate conditional expectation `E_k : T∞ → M_{3^k}` -/

/-- **★★★ r109 THE KEYSTONE — the substrate conditional expectation ★★★**
    `E_k : TimelessFieldRing → M_{3^k}`, descended from the level maps via
    the direct-limit universal property (`levelToLevelK_compat` is the
    well-definedness witness). -/
noncomputable def condExp (k : ℕ) :
    TimelessFieldRing → Matrix (Fin (3^k)) (Fin (3^k)) ℂ :=
  DirectLimit.lift
    (fun i j (h : i ≤ j) => substrateRingHomIter i j h)
    (fun m A => levelToLevelK k m A)
    (fun i j hij A => levelToLevelK_compat k i j hij A)

/-- `E_k` at a level representative equals the level map. -/
@[simp] theorem condExp_of_level (k m : ℕ)
    (A : Matrix (Fin (3^m)) (Fin (3^m)) ℂ) :
    condExp k (⟦⟨m, A⟩⟧ : TimelessFieldRing) = levelToLevelK k m A := rfl

/-- **E_k is TRACE-PRESERVING** (unconditional): the normalized level-`k`
    matrix trace of `E_k x` equals the substrate pre-trace of `x`. -/
theorem condExp_normalized_trace (k : ℕ) (x : TimelessFieldRing) :
    normalized_matrix_trace (condExp k x) = substrate_pre_trace x := by
  obtain ⟨m, A, rfl⟩ := DirectLimit.exists_eq_mk
    (fun i j (h : i ≤ j) => substrateRingHomIter i j h) x
  rw [condExp_of_level, substrate_pre_trace_of_level]
  by_cases hkm : k ≤ m
  · rw [levelToLevelK_of_le k m hkm, partialTraceDown_normalized_trace]
  · have hmk : m ≤ k := le_of_not_le hkm
    rw [levelToLevelK_of_ge k m hmk, substrateRingHomIter_normalized_trace]

/-- **E_k is the identity on the level-`k` corner** (construction 1d):
    `E_k (ι_k A) = A`. -/
theorem condExp_level_k (k : ℕ) (A : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    condExp k (substrateLevelToTimelessField k A) = A := by
  show condExp k (⟦⟨k, A⟩⟧ : TimelessFieldRing) = A
  rw [condExp_of_level, levelToLevelK_of_le k k le_rfl, partialTraceDown_self]
  rfl

/-- **E_k is the identity on lower levels** (construction 1d, general):
    for `m ≤ k`, `E_k (ι_m A) = ι_{m→k} A`, the honest level-`k` matrix
    representative of `ι_m A`. -/
theorem condExp_lower_level (k m : ℕ) (h : m ≤ k)
    (A : Matrix (Fin (3^m)) (Fin (3^m)) ℂ) :
    condExp k (substrateLevelToTimelessField m A) = substrateRingHomIter m k h A := by
  show condExp k (⟦⟨m, A⟩⟧ : TimelessFieldRing) = _
  rw [condExp_of_level, levelToLevelK_of_ge k m h]

/-! ## §5b — Construction 1a for `E_k`: ℂ-linear, unital, *-preserving. -/

theorem levelToLevelK_add (k m : ℕ)
    (A B : Matrix (Fin (3^m)) (Fin (3^m)) ℂ) :
    levelToLevelK k m (A + B) = levelToLevelK k m A + levelToLevelK k m B := by
  unfold levelToLevelK
  by_cases h : k ≤ m
  · rw [dif_pos h]; exact partialTraceDown_add k m h A B
  · rw [dif_neg h]; exact map_add _ A B

theorem levelToLevelK_smul (k m : ℕ) (c : ℂ)
    (A : Matrix (Fin (3^m)) (Fin (3^m)) ℂ) :
    levelToLevelK k m (c • A) = c • levelToLevelK k m A := by
  unfold levelToLevelK
  by_cases h : k ≤ m
  · rw [dif_pos h]; exact partialTraceDown_smul k m h c A
  · rw [dif_neg h]; exact substrateRingHomIter_smul m k _ c A

theorem levelToLevelK_one (k m : ℕ) :
    levelToLevelK k m (1 : Matrix (Fin (3^m)) (Fin (3^m)) ℂ) = 1 := by
  unfold levelToLevelK
  by_cases h : k ≤ m
  · rw [dif_pos h]; exact partialTraceDown_one k m h
  · rw [dif_neg h]; exact map_one _

theorem levelToLevelK_star (k m : ℕ)
    (A : Matrix (Fin (3^m)) (Fin (3^m)) ℂ) :
    levelToLevelK k m (star A) = star (levelToLevelK k m A) := by
  unfold levelToLevelK
  by_cases h : k ≤ m
  · rw [dif_pos h]; exact partialTraceDown_star k m h A
  · rw [dif_neg h]; exact substrateRingHomIter_star m k _ A

/-- **E_k is additive.** -/
theorem condExp_add (k : ℕ) (x y : TimelessFieldRing) :
    condExp k (x + y) = condExp k x + condExp k y := by
  obtain ⟨m, A, B, rfl, rfl⟩ :=
    DirectLimit.exists_eq_mk₂ (fun i j (h : i ≤ j) => substrateRingHomIter i j h) x y
  rw [substrate_quotient_add_same_level, condExp_of_level, condExp_of_level,
      condExp_of_level, levelToLevelK_add]

/-- **E_k is ℂ-homogeneous.** -/
theorem condExp_smul (k : ℕ) (c : ℂ) (x : TimelessFieldRing) :
    condExp k (c • x) = c • condExp k x := by
  obtain ⟨m, A, rfl⟩ :=
    DirectLimit.exists_eq_mk (fun i j (h : i ≤ j) => substrateRingHomIter i j h) x
  rw [substrate_quotient_smul_same_level, condExp_of_level, condExp_of_level,
      levelToLevelK_smul]

/-- **E_k is unital.** -/
theorem condExp_one (k : ℕ) : condExp k (1 : TimelessFieldRing) = 1 := by
  rw [DirectLimit.one_def
        (G := fun k : ℕ => Matrix (Fin (3^k)) (Fin (3^k)) ℂ)
        (f := fun i j (h : i ≤ j) => substrateRingHomIter i j h) 0,
      condExp_of_level, levelToLevelK_one]

/-- **E_k is *-preserving.** -/
theorem condExp_star (k : ℕ) (x : TimelessFieldRing) :
    condExp k (star x) = star (condExp k x) := by
  obtain ⟨m, A, rfl⟩ :=
    DirectLimit.exists_eq_mk (fun i j (h : i ≤ j) => substrateRingHomIter i j h) x
  rw [substrate_quotient_star_same_level, condExp_of_level, condExp_of_level,
      levelToLevelK_star]

/-! ## §6 — The honest obstruction map: the contraction, the extension,
    and the faithfulness assembly. -/

/-- **THE CRUX (construction step 2) — the `‖·‖₂` contraction / Kadison–
    Schwarz inequality for `E_k`.**

    On the level-`k` corner, `E_k` is a unital completely positive map, so it
    obeys the Schwarz inequality `(E_k x)⋆(E_k x) ≤ E_k(x⋆ x)` and hence the
    trace 2-seminorm contraction below. This is the single hard analytic
    input isolated by r108; it is NOT provided by mathlib (partial-trace
    Kadison–Schwarz on matrices is absent) and is stated here as the named
    residual. Once proved, together with `condExp_normalized_trace` it gives
    `τ(x⋆x) = 0 ⇒ ∀ k, normalized_matrix_trace ((E_k x)⋆(E_k x)) = 0`. -/
def CondExpL2Contraction : Prop :=
  ∀ (k : ℕ) (x : TimelessFieldRing),
    (normalized_matrix_trace (star (condExp k x) * condExp k x)).re ≤
      (substrate_pre_trace (star x * x)).re

/-- **The extension (construction step 3) — `E_k` extends by uniform
    continuity to the completion, with `ι_k (E_k x) → x`.**

    `E_k` is `‖·‖`-contractive (a ucp map is norm-1), so it extends to
    `TimelessFieldCompletion`; and `E_k x = x` on the dense level-`≤ k`
    image gives `ι_k (E_k x) → x`. This is the density/continuity step; it
    is stated as a named residual pending the norm-contraction bound. -/
def CondExpCompletionExtension : Prop :=
  ∃ E : ℕ → TimelessFieldCompletion → TimelessFieldCompletion,
    (∀ k, UniformContinuous (E k)) ∧
    (∀ k (a : TimelessFieldRing),
      E k (a : TimelessFieldCompletion) =
        ((substrateLevelToTimelessField k (condExp k a) : TimelessFieldRing) :
          TimelessFieldCompletion)) ∧
    (∀ x : TimelessFieldCompletion, Filter.Tendsto (fun k => E k x)
      Filter.atTop (nhds x))

/-! ## §7 — r109 capstone -/

/-- **★★★ r109 SUBSTRATE CONDITIONAL EXPECTATION CAPSTONE ★★★**

    THE KEYSTONE, landed in honest stages.

    **LANDED (unconditional, kernel-only):**

      (1a) The partial trace `E_k^{(m)}` (single-step `partialTraceStep` and
           iterated `partialTraceDown`) is ℂ-linear, unital and
           *-preserving — `partialTraceStep_{add,smul,one,star}` and
           `partialTraceDown_{add,smul,one,star}`.
      (1b) TRACE-PRESERVING: `partialTraceStep_normalized_trace`,
           `partialTraceDown_normalized_trace`, and at the direct-limit level
           `condExp_normalized_trace : normalized_matrix_trace (E_k x)
           = substrate_pre_trace x`.
      (1c) TOWER-COMPATIBLE: `levelToLevelK_compat` (the cocone condition)
           descends the level maps to `E_k : TimelessFieldRing → M_{3^k}`
           via the direct-limit universal property (`condExp`).
      (1d) IDENTITY ON LEVELS: `condExp_level_k : E_k (ι_k A) = A`, and more
           generally `condExp_lower_level`.
      Plus `E_k` itself is ℂ-linear, unital and *-preserving on `T∞`
      (`condExp_{add,smul,one,star}`).

    **ISOLATED RESIDUALS (the honest obstruction map):**

      (2) `CondExpL2Contraction` — the Kadison–Schwarz `‖·‖₂` contraction.
          This is the single hard analytic core; absent from mathlib.
      (3) `CondExpCompletionExtension` — the uniform-continuity extension of
          `E_k` to `TimelessFieldCompletion` with `ι_k(E_k x) → x`.

    Per r108's `traceDetects_iff_faithful`, discharging (2)+(3) closes the
    entire completion-tier faithfulness summit. The first stall is (2): the
    matrix partial-trace Kadison–Schwarz inequality.

    Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
    axioms. Zero sorries. -/
theorem r109_substrate_conditional_expectation_capstone :
    -- (1b) trace preservation at the direct-limit level
    (∀ (k : ℕ) (x : TimelessFieldRing),
      normalized_matrix_trace (condExp k x) = substrate_pre_trace x) ∧
    -- (1d) identity on the level-k corner
    (∀ (k : ℕ) (A : Matrix (Fin (3^k)) (Fin (3^k)) ℂ),
      condExp k (substrateLevelToTimelessField k A) = A) ∧
    -- (1a) E_k is ℂ-linear, unital, *-preserving on T∞
    (∀ (k : ℕ) (x y : TimelessFieldRing),
      condExp k (x + y) = condExp k x + condExp k y) ∧
    (∀ (k : ℕ) (c : ℂ) (x : TimelessFieldRing),
      condExp k (c • x) = c • condExp k x) ∧
    (∀ (k : ℕ), condExp k (1 : TimelessFieldRing) = 1) ∧
    (∀ (k : ℕ) (x : TimelessFieldRing),
      condExp k (star x) = star (condExp k x)) :=
  ⟨condExp_normalized_trace,
   condExp_level_k,
   condExp_add,
   condExp_smul,
   condExp_one,
   condExp_star⟩

/-! ## §8 — Axiom audit -/

#print axioms partialTraceStep_normalized_trace
#print axioms partialTraceStep_substrateEmbedMatrix
#print axioms partialTraceDown_normalized_trace
#print axioms partialTraceDown_substrateRingHomIter
#print axioms levelToLevelK_compat
#print axioms condExp
#print axioms condExp_normalized_trace
#print axioms condExp_level_k
#print axioms condExp_add
#print axioms condExp_smul
#print axioms condExp_one
#print axioms condExp_star
#print axioms r109_substrate_conditional_expectation_capstone

end SubstrateConditionalExpectation
end PrincipiaTractalis
