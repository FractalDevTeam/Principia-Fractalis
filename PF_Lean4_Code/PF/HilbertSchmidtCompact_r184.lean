/-
# PF.HilbertSchmidtCompact_r184

★★★ 2026-08-03 — M3 STONE 2: HILBERT–SCHMIDT OPERATORS ARE COMPACT ★★★

r183 built `hsOperator : ℓ² →L[ℂ] ℓ²` from a square-summable matrix with the
Hilbert–Schmidt norm bound.  This stone proves it is a **compact operator** —
the property the whole spectral program rests on, and the first compactness
theorem for an infinite-dimensional operator class in this corpus or (per the
2026-08-02 feasibility audit) in mathlib's ecosystem: mathlib defines
`IsCompactOperator` but has no finite-rank API and no nontrivial examples.

## Route (no Montel needed)

1. `isCompactOperator_of_mem_finiteDimensional` — a continuous linear map
   whose range lies in a finite-dimensional submodule is compact.  (The
   missing "finite rank ⟹ compact" lemma, proved from properness of
   finite-dimensional spaces.)
2. Row truncation: `A_k` keeps rows `m < k`.  Its operator has range inside
   the span of finitely many `lp.single`s ⟹ compact by (1).
3. `hsOperator hA = hsOperator (trunc) + hsOperator (tail)` exactly, and
   `‖tail_k‖_HS² = Σ_{m ≥ k} (row sums) → 0` as the tail of a convergent
   series ⟹ the truncations converge in operator norm.
4. `isCompactOperator_of_tendsto` (mathlib) closes it.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-08-03.
-/
import PF.HilbertSchmidtL2_r183
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option maxHeartbeats 1000000

namespace PrincipiaTractalis.HilbertSchmidtL2

open scoped ComplexOrder ENNReal NNReal
open lp Submodule

noncomputable section

local notation "ℓ²" => lp (fun _ : ℕ => ℂ) 2

local notation "⟪" x ", " y "⟫" => @inner ℂ _ _ x y

/-! ### Part 1: finite range ⟹ compact -/

/-- **A continuous linear map with range in a finite-dimensional submodule is
a compact operator.**  mathlib has `IsCompactOperator` but no finite-rank API;
this is the missing bridge. -/
theorem isCompactOperator_of_mem_finiteDimensional
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : E →L[ℂ] F) (S : Submodule ℂ F) [FiniteDimensional ℂ S]
    (hrange : ∀ x, f x ∈ S) : IsCompactOperator f := by
  refine ⟨closure (f '' Metric.ball 0 1), ?_, ?_⟩
  swap
  · -- f ⁻¹' K is a neighborhood of 0: it contains the unit ball
    apply Filter.mem_of_superset (Metric.ball_mem_nhds 0 one_pos)
    intro x hx
    exact subset_closure ⟨x, hx, rfl⟩
  set C := closure (f '' Metric.ball 0 1) with hC
  have hSclosed : IsClosed (S : Set F) := S.closed_of_finiteDimensional
  have hCS : C ⊆ (S : Set F) := by
    apply closure_minimal _ hSclosed
    rintro y ⟨x, -, rfl⟩
    exact hrange x
  have hCbdd : Bornology.IsBounded C := by
    apply Bornology.IsBounded.closure
    rw [isBounded_iff_forall_norm_le]
    refine ⟨‖f‖, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    calc ‖f x‖ ≤ ‖f‖ * ‖x‖ := f.le_opNorm x
      _ ≤ ‖f‖ * 1 := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg f)
          exact le_of_lt (mem_ball_zero_iff.mp hx)
      _ = ‖f‖ := mul_one _
  -- pull back to the finite-dimensional (hence proper) subspace
  haveI : ProperSpace S := FiniteDimensional.proper ℂ S
  set D : Set S := (Subtype.val : S → F) ⁻¹' C with hD
  have hDclosed : IsClosed D := (isClosed_closure).preimage continuous_subtype_val
  have hDbdd : Bornology.IsBounded D := by
    rw [isBounded_iff_forall_norm_le] at hCbdd ⊢
    obtain ⟨M, hM⟩ := hCbdd
    exact ⟨M, fun y hy => hM _ hy⟩
  have hDcompact : IsCompact D := Metric.isCompact_of_isClosed_isBounded hDclosed hDbdd
  have himg : Subtype.val '' D = C :=
    Set.image_preimage_eq_of_subset (by simpa using hCS)
  exact himg ▸ hDcompact.image continuous_subtype_val

/-! ### Part 2: row truncation -/

variable {A : ℕ → ℕ → ℂ}

/-- Rows `m < k` of `A`; the rest zeroed. -/
def trunc (A : ℕ → ℕ → ℂ) (k : ℕ) : ℕ → ℕ → ℂ :=
  fun m n => if m < k then A m n else 0

/-- Rows `m ≥ k` of `A`; the rest zeroed. -/
def tail (A : ℕ → ℕ → ℂ) (k : ℕ) : ℕ → ℕ → ℂ :=
  fun m n => if m < k then 0 else A m n

theorem trunc_add_tail (A : ℕ → ℕ → ℂ) (k : ℕ) :
    trunc A k + tail A k = A := by
  funext m n
  simp only [Pi.add_apply, trunc, tail]
  by_cases h : m < k <;> simp [h]

theorem hsSummable_trunc (hA : HSSummable A) (k : ℕ) :
    HSSummable (trunc A k) := by
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) hA
  simp only [trunc]
  by_cases h : p.1 < k <;> simp [h] <;> positivity

theorem hsSummable_tail (hA : HSSummable A) (k : ℕ) :
    HSSummable (tail A k) := by
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) hA
  simp only [tail]
  by_cases h : p.1 < k <;> simp [h] <;> positivity

/-- The operator splits exactly along the truncation. -/
theorem hsOperator_split (hA : HSSummable A) (k : ℕ) :
    hsOperator hA
      = hsOperator (hsSummable_trunc hA k) + hsOperator (hsSummable_tail hA k) := by
  ext x m
  have hrow : hsRow hA m
      = hsRow (hsSummable_trunc hA k) m + hsRow (hsSummable_tail hA k) m := by
    ext n
    simp only [hsRow_apply, lp.coeFn_add, Pi.add_apply, trunc, tail]
    by_cases h : m < k <;> simp [h]
  simp only [ContinuousLinearMap.add_apply, lp.coeFn_add, Pi.add_apply,
    hsOperator_apply, hrow]
  exact inner_add_left _ _ _

/-! ### Part 3: the truncated operator is compact (finite rank) -/

/-- The span of the first `k` coordinate vectors. -/
def coordSpan (k : ℕ) : Submodule ℂ ℓ² :=
  span ℂ ((fun m => lp.single 2 m (1 : ℂ)) '' ↑(Finset.range k))

instance (k : ℕ) : FiniteDimensional ℂ (coordSpan k) :=
  FiniteDimensional.span_of_finite ℂ ((Finset.range k).finite_toSet.image _)

theorem hsRow_trunc_eq_zero (hA : HSSummable A) {k m : ℕ} (h : ¬ m < k) :
    hsRow (hsSummable_trunc hA k) m = 0 := by
  ext n
  simp [hsRow_apply, trunc, h]

theorem trunc_mem_coordSpan (hA : HSSummable A) (k : ℕ) (x : ℓ²) :
    hsOperator (hsSummable_trunc hA k) x ∈ coordSpan k := by
  have hrepr : hsOperator (hsSummable_trunc hA k) x
      = ∑ m ∈ Finset.range k,
          (⟪hsRow (hsSummable_trunc hA k) m, x⟫ : ℂ) • lp.single 2 m (1 : ℂ) := by
    ext j
    rw [lp.coeFn_sum]
    simp only [Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, lp.single_apply,
      smul_eq_mul, hsOperator_apply]
    by_cases hj : j < k
    · rw [Finset.sum_eq_single j]
      · simp [Pi.single_apply]
      · intro b _ hbj
        simp [Pi.single_apply, Ne.symm hbj]
      · intro hnot
        exact absurd (Finset.mem_range.mpr hj) hnot
    · rw [Finset.sum_eq_zero, hsRow_trunc_eq_zero hA hj]
      · simp
      · intro b hb
        have : b ≠ j := fun hbj => hj (hbj ▸ Finset.mem_range.mp hb)
        simp [Pi.single_apply, Ne.symm this]
  rw [hrepr]
  apply Submodule.sum_mem
  intro m hm
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact Set.mem_image_of_mem _ (Finset.mem_coe.mpr hm)

theorem isCompactOperator_trunc (hA : HSSummable A) (k : ℕ) :
    IsCompactOperator (hsOperator (hsSummable_trunc hA k)) :=
  isCompactOperator_of_mem_finiteDimensional _ (coordSpan k)
    (trunc_mem_coordSpan hA k)

/-! ### Part 4: the tail vanishes in Hilbert–Schmidt norm -/

theorem tail_rowSum (hA : HSSummable A) (k m : ℕ) :
    (∑' n, ‖tail A k m n‖ ^ 2)
      = if m < k then 0 else ∑' n, ‖A m n‖ ^ 2 := by
  by_cases h : m < k
  · simp [tail, h]
  · simp only [tail, if_neg h]

theorem hsNorm_tail_sq (hA : HSSummable A) (k : ℕ) :
    hsNorm (tail A k) ^ 2
      = ∑' m, (if m < k then 0 else ∑' n, ‖A m n‖ ^ 2) := by
  have hsq : hsNorm (tail A k) ^ 2
      = ∑' p : ℕ × ℕ, ‖tail A k p.1 p.2‖ ^ 2 := by
    rw [hsNorm, Real.sq_sqrt]
    exact tsum_nonneg fun p => sq_nonneg _
  rw [hsq, (hsSummable_tail hA k).tsum_prod' ]
  · congr 1
    funext m
    exact tail_rowSum hA k m
  · exact fun m => row_summable (hsSummable_tail hA k) m

theorem tendsto_hsNorm_tail (hA : HSSummable A) :
    Filter.Tendsto (fun k => hsNorm (tail A k)) Filter.atTop (nhds 0) := by
  set s : ℕ → ℝ := fun m => ∑' n, ‖A m n‖ ^ 2 with hs
  have hsum : Summable s := rowSum_summable hA
  -- reindex the tail sum along j ↦ j + k
  have hg2 : ∀ k, (∑' m, (if m < k then (0 : ℝ) else s m)) = ∑' j, s (j + k) := by
    intro k
    have hinj : Function.Injective (fun j : ℕ => j + k) := add_left_injective k
    have hsupp : Function.support (fun m => if m < k then (0 : ℝ) else s m)
        ⊆ Set.range (fun j : ℕ => j + k) := by
      intro m hm
      simp only [Function.mem_support] at hm
      by_cases h : m < k
      · simp [h] at hm
      · exact ⟨m - k, by show m - k + k = m; omega⟩
    have hres := hinj.tsum_eq hsupp
    rw [← hres]
    congr 1; funext j
    have : ¬ (j + k < k) := by omega
    simp [this]
  -- the shifted sums are total minus partials, hence tend to zero
  have hgk : ∀ k, (∑' j, s (j + k))
      = (∑' i, s i) - ∑ i ∈ Finset.range k, s i := by
    intro k
    have h := hsum.sum_add_tsum_nat_add k
    linarith
  have hzero : Filter.Tendsto
      (fun k => (∑' i, s i) - ∑ i ∈ Finset.range k, s i)
      Filter.atTop (nhds 0) := by
    have hpart := hsum.hasSum.tendsto_sum_nat
    have := Filter.Tendsto.const_sub (∑' i, s i) hpart
    simpa using this
  have hsq : Filter.Tendsto (fun k => hsNorm (tail A k) ^ 2)
      Filter.atTop (nhds 0) := by
    have hEq : ∀ k, hsNorm (tail A k) ^ 2
        = (∑' i, s i) - ∑ i ∈ Finset.range k, s i := by
      intro k
      rw [hsNorm_tail_sq hA k, ← hgk k, ← hg2 k]
    simpa only [hEq] using hzero
  have hcomp := (Real.continuous_sqrt.tendsto 0).comp hsq
  simp only [Real.sqrt_zero, Function.comp_def] at hcomp
  refine hcomp.congr fun k => ?_
  rw [Real.sqrt_sq (hsNorm_nonneg)]

/-! ### Part 5: the theorem -/

/-- **Hilbert–Schmidt operators on ℓ² are compact.** -/
theorem isCompactOperator_hsOperator (hA : HSSummable A) :
    IsCompactOperator (hsOperator hA) := by
  apply isCompactOperator_of_tendsto
    (F := fun k => hsOperator (hsSummable_trunc hA k)) (l := Filter.atTop)
  · -- norm convergence of the truncations
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hbound : ∀ k, ‖hsOperator (hsSummable_trunc hA k) - hsOperator hA‖
        ≤ hsNorm (tail A k) := by
      intro k
      have hsplit := hsOperator_split hA k
      have : hsOperator (hsSummable_trunc hA k) - hsOperator hA
          = -(hsOperator (hsSummable_tail hA k)) := by
        rw [hsplit]; abel
      rw [this, _root_.norm_neg]
      exact hsOperator_norm_le _
    exact squeeze_zero (fun k => norm_nonneg _) hbound (tendsto_hsNorm_tail hA)
  · exact Filter.Eventually.of_forall (isCompactOperator_trunc hA)

end

end PrincipiaTractalis.HilbertSchmidtL2

#print axioms PrincipiaTractalis.HilbertSchmidtL2.isCompactOperator_of_mem_finiteDimensional
#print axioms PrincipiaTractalis.HilbertSchmidtL2.isCompactOperator_hsOperator
