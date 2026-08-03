/-
# PF.HilbertSchmidtL2_r183

★★★ 2026-08-03 — M3 STONE 1: HILBERT–SCHMIDT MATRICES ACT ON ℓ² ★★★

First stone of the Lean transfer-operator arc (RH front, milestone M3).
The numerics of M1/M2 rest on one functional-analytic fact: a matrix whose
entries are square-summable induces a bounded operator on ℓ²(ℕ, ℂ), with
operator norm at most the Hilbert–Schmidt norm.  mathlib has no
Hilbert–Schmidt theory, no matrix-to-operator construction on `lp`, and no
composition-operator theory (feasibility audit, 2026-08-02); this file starts
that program at its load-bearing point.

## Main definitions and results

* `hsRow A m` — the `m`-th row of the matrix, conjugated, as an element of ℓ².
* `hsFun A x` — the function `m ↦ ⟪row m, x⟫ = Σ_n A m n * x n`.
* `memℓp_hsFun` — the image is again in ℓ².
* `hsOperator A hA : lp _ 2 →L[ℂ] lp _ 2` — the bounded operator, with
* `hsOperator_norm_le : ‖hsOperator A hA‖ ≤ √(Σ'_{(m,n)} ‖A m n‖²)`.

Compactness (finite-rank truncation + norm limit) is the next stone (r184);
the transfer-operator entry bounds instantiating this are r185.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-08-03.
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

set_option maxHeartbeats 1000000

namespace PrincipiaTractalis.HilbertSchmidtL2

open scoped ComplexOrder ENNReal NNReal
open lp

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

end

end PrincipiaTractalis.HilbertSchmidtL2

#print axioms PrincipiaTractalis.HilbertSchmidtL2.hsOperator
#print axioms PrincipiaTractalis.HilbertSchmidtL2.hsOperator_norm_le
