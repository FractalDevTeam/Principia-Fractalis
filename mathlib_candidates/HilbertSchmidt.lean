/-
Copyright (c) 2026 Pablo Cohen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Cohen
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Hilbert–Schmidt operators on `lp (fun _ : ℕ => ℂ) 2`

A matrix `A : ℕ → ℕ → ℂ` with square-summable entries induces a bounded
operator on ℓ², with operator norm at most the Hilbert–Schmidt norm — and
that operator is **compact**.  mathlib has `IsCompactOperator` but no
finite-rank API, no matrix-to-operator construction on `lp`, and no
Hilbert–Schmidt theory; this file provides the base layer.

## Main definitions and results

* `HilbertSchmidt.HSSummable A` — square-summability of the entries.
* `HilbertSchmidt.hsOperator hA : lp _ 2 →L[ℂ] lp _ 2` — the operator, with
  `hsOperator_norm_le : ‖hsOperator hA‖ ≤ √(Σ' ‖A m n‖²)`.
* `HilbertSchmidt.isCompactOperator_of_mem_finiteDimensional` — a continuous
  linear map with range in a finite-dimensional submodule is compact (the
  "finite rank ⟹ compact" bridge).
* `HilbertSchmidt.isCompactOperator_hsOperator` — Hilbert–Schmidt operators
  are compact (finite-rank row truncations converge in operator norm).
* `HilbertSchmidt.hsSummable_of_geometric`, `hsNorm_le_of_geometric`,
  `isCompactOperator_of_geometric` — the double-geometric entry-decay
  criterion `‖A m n‖ ≤ C·r^m·ρ^n` with the explicit norm bound
  `C/√((1−r²)(1−ρ²))`.

The index type is fixed to `ℕ`; the truncation argument uses `Finset.range`.
Generalising to an arbitrary countable index is routine and deferred.
-/

set_option maxHeartbeats 1600000

namespace HilbertSchmidt

open scoped ComplexOrder ENNReal NNReal
open lp Submodule

noncomputable section

local notation "ℓ²" => lp (fun _ : ℕ => ℂ) 2

local notation "⟪" x ", " y "⟫" => @inner ℂ _ _ x y

variable (A : ℕ → ℕ → ℂ)

/-- The square-summability hypothesis: the matrix has finite Hilbert–Schmidt
norm. -/
def HSSummable : Prop := Summable fun p : ℕ × ℕ => ‖A p.1 p.2‖ ^ 2

variable {A}

theorem row_summable (hA : HSSummable A) (m : ℕ) :
    Summable fun n => ‖A m n‖ ^ 2 :=
  hA.prod_factor m

theorem rowSum_summable (hA : HSSummable A) :
    Summable fun m => ∑' n, ‖A m n‖ ^ 2 := by
  have h := (summable_prod_of_nonneg
    (fun p => sq_nonneg ‖A p.1 p.2‖)).mp hA
  exact h.2

/-- The `m`-th row, conjugated, as an ℓ² element (so that the inner product
against `x` produces `Σ_n A m n * x n` in mathlib's convention: `⟪f, g⟫ =
Σ conj (f n) * g n`). -/
def hsRow (hA : HSSummable A) (m : ℕ) : ℓ² :=
  ⟨fun n => (starRingEnd ℂ) (A m n), by
    apply memℓp_gen
    have : (fun n => ‖(starRingEnd ℂ) (A m n)‖ ^ (2 : ℝ≥0∞).toReal)
        = fun n => ‖A m n‖ ^ 2 := by
      funext n
      rw [RCLike.norm_conj]
      norm_num
    rw [this]
    exact row_summable hA m⟩

@[simp] theorem hsRow_apply (hA : HSSummable A) (m n : ℕ) :
    (hsRow hA m : ∀ _ : ℕ, ℂ) n = (starRingEnd ℂ) (A m n) := rfl

theorem norm_hsRow_sq (hA : HSSummable A) (m : ℕ) :
    ‖hsRow hA m‖ ^ 2 = ∑' n, ‖A m n‖ ^ 2 := by
  have h2 : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have := lp.norm_rpow_eq_tsum h2 (hsRow hA m)
  have e2 : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num
  rw [e2] at this
  calc ‖hsRow hA m‖ ^ 2
      = ‖hsRow hA m‖ ^ (2 : ℝ) := by
        rw [← Real.rpow_natCast ‖hsRow hA m‖ 2]; norm_num
    _ = ∑' n, ‖(hsRow hA m : ∀ _ : ℕ, ℂ) n‖ ^ (2 : ℝ) := this
    _ = ∑' n, ‖A m n‖ ^ 2 := by
        congr 1; funext n
        rw [hsRow_apply, RCLike.norm_conj, ← Real.rpow_natCast ‖A m n‖ 2]
        norm_num

/-- The candidate image function: `m ↦ ⟪row m, x⟫`. -/
def hsFun (hA : HSSummable A) (x : ℓ²) : ℕ → ℂ :=
  fun m => ⟪hsRow hA m, x⟫

theorem norm_hsFun_le (hA : HSSummable A) (x : ℓ²) (m : ℕ) :
    ‖hsFun hA x m‖ ≤ ‖hsRow hA m‖ * ‖x‖ :=
  norm_inner_le_norm _ _

theorem memℓp_hsFun (hA : HSSummable A) (x : ℓ²) :
    Memℓp (hsFun hA x) 2 := by
  apply memℓp_gen
  have e2 : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num
  rw [e2]
  have hbound : ∀ m, ‖hsFun hA x m‖ ^ (2 : ℝ)
      ≤ (∑' n, ‖A m n‖ ^ 2) * ‖x‖ ^ 2 := by
    intro m
    have h1 : ‖hsFun hA x m‖ ^ (2 : ℝ) = ‖hsFun hA x m‖ ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast ‖hsFun hA x m‖ 2]; norm_num
    rw [h1]
    calc ‖hsFun hA x m‖ ^ 2
        ≤ (‖hsRow hA m‖ * ‖x‖) ^ 2 := by
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_hsFun_le hA x m) 2
      _ = ‖hsRow hA m‖ ^ 2 * ‖x‖ ^ 2 := by ring
      _ = (∑' n, ‖A m n‖ ^ 2) * ‖x‖ ^ 2 := by rw [norm_hsRow_sq]
  refine Summable.of_nonneg_of_le (fun m => by positivity) hbound ?_
  exact (rowSum_summable hA).mul_right _

/-- The Hilbert–Schmidt operator, as a linear map. -/
def hsLinear (hA : HSSummable A) : ℓ² →ₗ[ℂ] ℓ² where
  toFun x := ⟨hsFun hA x, memℓp_hsFun hA x⟩
  map_add' x y := by
    ext m
    simp only [hsFun, lp.coeFn_add, Pi.add_apply]
    exact inner_add_right _ _ _
  map_smul' c x := by
    ext m
    simp only [hsFun, lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply,
      smul_eq_mul]
    exact inner_smul_right _ _ _

@[simp] theorem hsLinear_apply (hA : HSSummable A) (x : ℓ²) (m : ℕ) :
    (hsLinear hA x : ∀ _ : ℕ, ℂ) m = ⟪hsRow hA m, x⟫ := rfl

/-- The Hilbert–Schmidt norm (as a real number). -/
def hsNorm (A : ℕ → ℕ → ℂ) : ℝ :=
  Real.sqrt (∑' p : ℕ × ℕ, ‖A p.1 p.2‖ ^ 2)

theorem hsNorm_nonneg : 0 ≤ hsNorm A := Real.sqrt_nonneg _

theorem norm_hsLinear_le (hA : HSSummable A) (x : ℓ²) :
    ‖hsLinear hA x‖ ≤ hsNorm A * ‖x‖ := by
  have h2 : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  -- squares first
  have hsq : ‖hsLinear hA x‖ ^ 2 ≤ hsNorm A ^ 2 * ‖x‖ ^ 2 := by
    have hnorm := lp.norm_rpow_eq_tsum h2 (hsLinear hA x)
    have e2 : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num
    rw [e2] at hnorm
    have hpow : ‖hsLinear hA x‖ ^ 2 = ‖hsLinear hA x‖ ^ (2 : ℝ) := by
      rw [← Real.rpow_natCast ‖hsLinear hA x‖ 2]; norm_num
    rw [hpow, hnorm]
    -- Σ_m ‖⟪R m, x⟫‖² ≤ Σ_m (Σ_n ‖A m n‖²)·‖x‖²  =  hsNorm² ‖x‖²
    have hterm : ∀ m, ‖(hsLinear hA x : ∀ _ : ℕ, ℂ) m‖ ^ (2 : ℝ)
        ≤ (∑' n, ‖A m n‖ ^ 2) * ‖x‖ ^ 2 := by
      intro m
      have h1 : ‖(hsLinear hA x : ∀ _ : ℕ, ℂ) m‖ ^ (2 : ℝ)
          = ‖(hsLinear hA x : ∀ _ : ℕ, ℂ) m‖ ^ (2 : ℕ) := by
        rw [← Real.rpow_natCast _ 2]; norm_num
      rw [h1, hsLinear_apply]
      calc ‖⟪hsRow hA m, x⟫‖ ^ 2
          ≤ (‖hsRow hA m‖ * ‖x‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2
        _ = ‖hsRow hA m‖ ^ 2 * ‖x‖ ^ 2 := by ring
        _ = (∑' n, ‖A m n‖ ^ 2) * ‖x‖ ^ 2 := by rw [norm_hsRow_sq]
    have hsum : (∑' m, (∑' n, ‖A m n‖ ^ 2) * ‖x‖ ^ 2)
        = (∑' p : ℕ × ℕ, ‖A p.1 p.2‖ ^ 2) * ‖x‖ ^ 2 := by
      rw [tsum_mul_right]
      congr 1
      exact (hA.tsum_prod' (fun m => row_summable hA m)).symm ▸ rfl
    calc (∑' m, ‖(hsLinear hA x : ∀ _ : ℕ, ℂ) m‖ ^ (2 : ℝ))
        ≤ ∑' m, (∑' n, ‖A m n‖ ^ 2) * ‖x‖ ^ 2 := by
          refine Summable.tsum_le_tsum hterm ?_ ?_
          · exact ((memℓp_hsFun hA x).summable h2).congr (fun m => rfl)
          · exact (rowSum_summable hA).mul_right _
      _ = (∑' p : ℕ × ℕ, ‖A p.1 p.2‖ ^ 2) * ‖x‖ ^ 2 := hsum
      _ = hsNorm A ^ 2 * ‖x‖ ^ 2 := by
          rw [hsNorm, Real.sq_sqrt]
          exact tsum_nonneg fun p => sq_nonneg _
  -- take square roots
  have hL : (0 : ℝ) ≤ hsNorm A * ‖x‖ :=
    mul_nonneg (hsNorm_nonneg) (norm_nonneg _)
  nlinarith [norm_nonneg (hsLinear hA x), hsq]

/-- **The Hilbert–Schmidt operator on ℓ².**  A square-summable matrix induces
a bounded operator, with norm at most the Hilbert–Schmidt norm. -/
def hsOperator (hA : HSSummable A) : ℓ² →L[ℂ] ℓ² :=
  (hsLinear hA).mkContinuous (hsNorm A) (norm_hsLinear_le hA)

@[simp] theorem hsOperator_apply (hA : HSSummable A) (x : ℓ²) (m : ℕ) :
    (hsOperator hA x : ∀ _ : ℕ, ℂ) m = ⟪hsRow hA m, x⟫ := rfl

theorem hsOperator_norm_le (hA : HSSummable A) :
    ‖hsOperator hA‖ ≤ hsNorm A :=
  LinearMap.mkContinuous_norm_le _ (hsNorm_nonneg) _

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

variable {A : ℕ → ℕ → ℂ} {C r ρ : ℝ}

/-- The double-geometric decay hypothesis. -/
def GeomBound (A : ℕ → ℕ → ℂ) (C r ρ : ℝ) : Prop :=
  ∀ m n, ‖A m n‖ ≤ C * r ^ m * ρ ^ n

theorem GeomBound.sq_le (h : GeomBound A C r ρ) (hC : 0 ≤ C)
    (hr0 : 0 ≤ r) (hρ0 : 0 ≤ ρ) (m n : ℕ) :
    ‖A m n‖ ^ 2 ≤ C ^ 2 * (r ^ 2) ^ m * (ρ ^ 2) ^ n := by
  have h1 := h m n
  have h2 : ‖A m n‖ ^ 2 ≤ (C * r ^ m * ρ ^ n) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  calc ‖A m n‖ ^ 2 ≤ (C * r ^ m * ρ ^ n) ^ 2 := h2
    _ = C ^ 2 * (r ^ 2) ^ m * (ρ ^ 2) ^ n := by
        rw [← pow_mul, ← pow_mul, mul_comm 2 m, mul_comm 2 n,
          pow_mul r m 2, pow_mul ρ n 2]
        ring

/-- **Double-geometric entry decay implies Hilbert–Schmidt.** -/
theorem hsSummable_of_geometric (h : GeomBound A C r ρ) (hC : 0 ≤ C)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    HSSummable A := by
  have hr2 : r ^ 2 < 1 := by nlinarith
  have hρ2 : ρ ^ 2 < 1 := by nlinarith
  have hr2' : (0 : ℝ) ≤ r ^ 2 := sq_nonneg r
  have hρ2' : (0 : ℝ) ≤ ρ ^ 2 := sq_nonneg ρ
  -- the dominating product family is summable over ℕ × ℕ
  have hdom : Summable fun p : ℕ × ℕ =>
      C ^ 2 * (r ^ 2) ^ p.1 * (ρ ^ 2) ^ p.2 := by
    have hbase := Summable.mul_of_nonneg
      (((summable_geometric_of_lt_one hr2' hr2).mul_left (C ^ 2)))
      (summable_geometric_of_lt_one hρ2' hρ2)
      (fun m => by positivity) (fun n => pow_nonneg hρ2' n)
    exact hbase.congr fun p => by ring
  refine Summable.of_nonneg_of_le (fun p => by positivity)
    (fun p => h.sq_le hC hr0 hρ0 p.1 p.2) hdom

/-- The explicit Hilbert–Schmidt norm bound. -/
theorem hsNorm_le_of_geometric (h : GeomBound A C r ρ) (hC : 0 ≤ C)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    hsNorm A ≤ C / Real.sqrt ((1 - r ^ 2) * (1 - ρ ^ 2)) := by
  have hr2 : r ^ 2 < 1 := by nlinarith
  have hρ2 : ρ ^ 2 < 1 := by nlinarith
  have hr2' : (0 : ℝ) ≤ r ^ 2 := sq_nonneg r
  have hρ2' : (0 : ℝ) ≤ ρ ^ 2 := sq_nonneg ρ
  have hA : HSSummable A := hsSummable_of_geometric h hC hr0 hr1 hρ0 hρ1
  have hdenpos : (0 : ℝ) < (1 - r ^ 2) * (1 - ρ ^ 2) := by nlinarith
  -- bound the double sum by the product of geometric series
  have hsum : (∑' p : ℕ × ℕ, ‖A p.1 p.2‖ ^ 2)
      ≤ C ^ 2 / ((1 - r ^ 2) * (1 - ρ ^ 2)) := by
    have hdom : Summable fun p : ℕ × ℕ =>
        C ^ 2 * (r ^ 2) ^ p.1 * (ρ ^ 2) ^ p.2 := by
      have hbase := Summable.mul_of_nonneg
        (((summable_geometric_of_lt_one hr2' hr2).mul_left (C ^ 2)))
        (summable_geometric_of_lt_one hρ2' hρ2)
        (fun m => by positivity) (fun n => pow_nonneg hρ2' n)
      exact hbase.congr fun p => by ring
    have hle : (∑' p : ℕ × ℕ, ‖A p.1 p.2‖ ^ 2)
        ≤ ∑' p : ℕ × ℕ, C ^ 2 * (r ^ 2) ^ p.1 * (ρ ^ 2) ^ p.2 :=
      hA.tsum_le_tsum (fun p => h.sq_le hC hr0 hρ0 p.1 p.2) hdom
    refine hle.trans ?_
    -- evaluate the product sum
    have hval : (∑' p : ℕ × ℕ, C ^ 2 * (r ^ 2) ^ p.1 * (ρ ^ 2) ^ p.2)
        = C ^ 2 * (1 - r ^ 2)⁻¹ * (1 - ρ ^ 2)⁻¹ := by
      rw [hdom.tsum_prod' (fun m =>
        (((summable_geometric_of_lt_one hρ2' hρ2).mul_left
          (C ^ 2 * (r ^ 2) ^ m)).congr (fun c => by dsimp only)))]
      have hinner : ∀ m : ℕ, (∑' n, C ^ 2 * (r ^ 2) ^ m * (ρ ^ 2) ^ n)
          = C ^ 2 * (r ^ 2) ^ m * (1 - ρ ^ 2)⁻¹ := by
        intro m
        rw [tsum_mul_left, tsum_geometric_of_lt_one hρ2' hρ2]
      calc (∑' m, ∑' n, C ^ 2 * (r ^ 2) ^ m * (ρ ^ 2) ^ n)
          = ∑' m, C ^ 2 * (r ^ 2) ^ m * (1 - ρ ^ 2)⁻¹ := by
            congr 1; funext m; exact hinner m
        _ = C ^ 2 * (1 - ρ ^ 2)⁻¹ * ∑' m, (r ^ 2) ^ m := by
            rw [← tsum_mul_left]
            congr 1; funext m; ring
        _ = C ^ 2 * (1 - r ^ 2)⁻¹ * (1 - ρ ^ 2)⁻¹ := by
            rw [tsum_geometric_of_lt_one hr2' hr2]; ring
    rw [hval]
    rw [div_eq_mul_inv, mul_inv]
    exact le_of_eq (by ring)
  -- pass to square roots
  rw [hsNorm]
  refine (Real.sqrt_le_sqrt hsum).trans (le_of_eq ?_)
  rw [Real.sqrt_div (sq_nonneg C), Real.sqrt_sq hC]

/-- **Double-geometric entry decay implies the induced ℓ² operator is
compact.** -/
theorem isCompactOperator_of_geometric (h : GeomBound A C r ρ) (hC : 0 ≤ C)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    IsCompactOperator
      (hsOperator (hsSummable_of_geometric h hC hr0 hr1 hρ0 hρ1)) :=
  isCompactOperator_hsOperator _

end

end HilbertSchmidt
