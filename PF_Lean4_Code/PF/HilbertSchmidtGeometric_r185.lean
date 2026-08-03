/-
# PF.HilbertSchmidtGeometric_r185

★★★ 2026-08-03 — M3 STONE 3: THE GEOMETRIC-DECAY CRITERION ★★★

r183 (bounded) and r184 (compact) are stated for abstract square-summable
matrices.  The transfer operators of M1/M2 satisfy something much more
concrete: **double-geometric entry decay**, `‖A m n‖ ≤ C·r^m·ρ^n` with
`r, ρ < 1` — the row decay coming from the analyticity radius of the image
functions, the column decay from the strict contraction of the branches
(quantitatively: the M2 production matrix at `N = 56` was gate-certified
precisely because its entries decay this way).

This stone proves the criterion:

* `hsSummable_of_geometric` — double-geometric decay ⟹ `HSSummable`;
* `hsNorm_le_of_geometric` — with the explicit bound
  `‖A‖_HS ≤ C / √((1−r²)(1−ρ²))`;
* `isCompactOperator_of_geometric` — hence the induced operator on ℓ² is
  compact, by r184.

The remaining bridge — that a weighted composition system whose branches map
an enlarged disc strictly into the base disc has coefficient matrix with
exactly this decay (via Cauchy estimates) — is r186.  It is not assumed
anywhere here.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-08-03.
-/
import PF.HilbertSchmidtCompact_r184
import Mathlib.Analysis.Normed.Ring.InfiniteSum

set_option maxHeartbeats 1600000

namespace PrincipiaTractalis.HilbertSchmidtL2

open scoped ENNReal NNReal

noncomputable section

local notation "ℓ²" => lp (fun _ : ℕ => ℂ) 2

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

end PrincipiaTractalis.HilbertSchmidtL2

#print axioms PrincipiaTractalis.HilbertSchmidtL2.hsSummable_of_geometric
#print axioms PrincipiaTractalis.HilbertSchmidtL2.hsNorm_le_of_geometric
#print axioms PrincipiaTractalis.HilbertSchmidtL2.isCompactOperator_of_geometric
