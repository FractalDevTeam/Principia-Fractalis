/-
# PF.CanheightMultiple389a1_r151

★★★ 2026-07-28 — r151: THE MULTIPLE LAW `ĥ(kR) = k²·ĥ(R)` ★★★

The one-dimensional half of the quadratic-form structure.  r150's exact
parallelogram law at `((k+2)R, R)` gives the recurrence

    `ĥ((k+3)R) = 2·ĥ((k+2)R) + 2·ĥ(R) − ĥ((k+1)R)`,

whose four points are all nonzero multiples of `R` (hence non-torsion), so
no side condition is lost.  With the base values `ĥ(R)` and
`ĥ(2R) = 4ĥ(R)` (r147) the two-step induction yields

    `ĥ(k·R) = k²·ĥ(R)`   for every `k : ℤ`.

Two cheap ingredients that carry their own weight:

* `canheight_zero` — `ĥ(0) = 0` (the identity is torsion);
* `canheight_neg` — `ĥ(−R) = ĥ(R)`, because negation does not move the
  x-coordinate, so every term of the defining sequence agrees.

Note why the induction starts at `1` and not `0`: the parallelogram law at
`((k+1)R, R)` needs `kR` non-torsion, which fails at `k = 0`.  The `k = 1`
step is supplied instead by r147's `canheight_dbl`.

HONEST SCOPE.  The one-dimensional law only.  Bi-additivity of the pairing
(hence `ĥ(mP+nQ) = m²ĥP + 2mn⟨P,Q⟩ + n²ĥQ`) is r152; the regulator is r153.

Kernel axioms ⊆ `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-28.
-/
import PF.CanheightParallelogram389a1_r150

namespace PrincipiaTractalis.CanheightMultiple389a1

open PrincipiaTractalis.NaiveHeightQ
open PrincipiaTractalis.E389a1RankOne
open PrincipiaTractalis.CanonicalHeight389a1
open PrincipiaTractalis.CanheightParallelogram389a1
open WeierstrassCurve WeierstrassCurve.Affine
open Filter Topology

/-! ## §1 — `ĥ(0) = 0` and `ĥ(−R) = ĥ(R)` -/

/-- The identity is torsion. -/
theorem zero_isOfFinAddOrder :
    IsOfFinAddOrder (0 : E389a1.toAffine.Point) :=
  isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨1, one_ne_zero, by simp⟩

/-- `ĥ(0) = 0`. -/
theorem canheight_zero : canheight (0 : E389a1.toAffine.Point) = 0 :=
  canheight_of_torsion zero_isOfFinAddOrder

/-- Negation fixes the x-coordinate. -/
theorem X_neg (R : E389a1.toAffine.Point) : X (-R) = X R := by
  rcases R with _ | @⟨x, y, h⟩
  · rfl
  · rw [Point.neg_some]
    rfl

/-- Hence the log-naive height is negation-invariant. -/
theorem lognh_neg (R : E389a1.toAffine.Point) : lognh (-R) = lognh R := by
  unfold lognh
  rw [X_neg R]

/-- **`ĥ(−R) = ĥ(R)`** — every term of the defining sequence agrees. -/
theorem canheight_neg (R : E389a1.toAffine.Point) :
    canheight (-R) = canheight R := by
  have hseq_eq : hseq (-R) = hseq R := by
    funext n
    simp only [hseq]
    rw [smul_neg, lognh_neg]
  have h1 := tendsto_hseq (-R)
  rw [hseq_eq] at h1
  exact tendsto_nhds_unique h1 (tendsto_hseq R)

/-! ## §2 — nonzero multiples of a non-torsion point are non-torsion -/

theorem zsmul_nonTorsion {R : E389a1.toAffine.Point} (hR : ¬ IsOfFinAddOrder R)
    {k : ℤ} (hk : k ≠ 0) : ¬ IsOfFinAddOrder (k • R) := by
  intro hfin
  obtain ⟨m, hm0, hm⟩ := isOfFinAddOrder_iff_zsmul_eq_zero.mp hfin
  refine hR (isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨m * k, mul_ne_zero hm0 hk, ?_⟩)
  rw [mul_smul]
  exact hm

/-! ## §3 — smul bookkeeping -/

theorem smul_succ (k : ℤ) (R : E389a1.toAffine.Point) :
    (k + 1) • R = k • R + R := by
  rw [add_smul, one_smul]

theorem smul_pred (k : ℤ) (R : E389a1.toAffine.Point) :
    (k - 1) • R = k • R - R := by
  rw [sub_smul, one_smul]

/-! ## §4 — the recurrence -/

section Multiple

variable {R : E389a1.toAffine.Point}

/-- **The recurrence.**  For `n : ℕ`, applying r150's parallelogram law at
`((n+2)R, R)` — whose sum is `(n+3)R` and difference `(n+1)R`, all nonzero
multiples of `R` — gives the three-term relation. -/
theorem canheight_rec (hR : ¬ IsOfFinAddOrder R) (n : ℕ) :
    canheight ((((n : ℤ) + 3)) • R)
      = 2 * canheight ((((n : ℤ) + 2)) • R) + 2 * canheight R
        - canheight ((((n : ℤ) + 1)) • R) := by
  -- the four points, as sums/differences
  have hsum : (((n : ℤ) + 2)) • R + R = (((n : ℤ) + 3)) • R := by
    have h := smul_succ ((n : ℤ) + 2) R
    rw [show ((n : ℤ) + 2 + 1) = ((n : ℤ) + 3) from by ring] at h
    exact h.symm
  have hdif : (((n : ℤ) + 2)) • R - R = (((n : ℤ) + 1)) • R := by
    have h := smul_pred ((n : ℤ) + 2) R
    rw [show ((n : ℤ) + 2 - 1) = ((n : ℤ) + 1) from by ring] at h
    exact h.symm
  -- non-torsion for all four
  have h2 : ¬ IsOfFinAddOrder ((((n : ℤ) + 2)) • R) :=
    zsmul_nonTorsion hR (by positivity)
  have h3 : ¬ IsOfFinAddOrder ((((n : ℤ) + 2)) • R + R) := by
    rw [hsum]; exact zsmul_nonTorsion hR (by positivity)
  have h1 : ¬ IsOfFinAddOrder ((((n : ℤ) + 2)) • R - R) := by
    rw [hdif]; exact zsmul_nonTorsion hR (by positivity)
  have hpar := canheight_parallelogram h2 hR h3 h1
  rw [hsum, hdif] at hpar
  linarith [hpar]

/-! ## §5 — THE MULTIPLE LAW -/

/-- The two-step induction, carrying consecutive pairs. -/
theorem canheight_nat_pair (hR : ¬ IsOfFinAddOrder R) (n : ℕ) :
    canheight ((((n : ℤ) + 1)) • R) = ((n : ℝ) + 1) ^ 2 * canheight R ∧
    canheight ((((n : ℤ) + 2)) • R) = ((n : ℝ) + 2) ^ 2 * canheight R := by
  induction n with
  | zero =>
      refine ⟨?_, ?_⟩
      · have e : (((0 : ℕ) : ℤ) + 1) = 1 := by norm_num
        rw [e, one_smul]
        norm_num
      · have e : (((0 : ℕ) : ℤ) + 2) = 2 := by norm_num
        have h2 : (2 : ℤ) • R = R + R := by
          rw [show (2 : ℤ) = 1 + 1 from rfl, add_smul, one_smul]
        rw [e, h2, canheight_dbl R]
        norm_num
  | succ k ih =>
      obtain ⟨ih1, ih2⟩ := ih
      refine ⟨?_, ?_⟩
      · -- the (k+1)+1 = k+2 case is ih2, modulo cast normalisation
        have e : (((k : ℕ) + 1 : ℕ) : ℤ) + 1 = ((k : ℤ) + 2) := by push_cast; ring
        rw [e, ih2]
        push_cast
        ring
      · -- the new value, from the recurrence
        have hrec := canheight_rec hR k
        have e : (((k : ℕ) + 1 : ℕ) : ℤ) + 2 = ((k : ℤ) + 3) := by push_cast; ring
        rw [e, hrec, ih1, ih2]
        push_cast
        ring

/-- **★★★ r151 — THE MULTIPLE LAW (natural multiples) ★★★**
`ĥ(k·R) = k²·ĥ(R)` for every `k : ℕ`. -/
theorem canheight_nsmul (hR : ¬ IsOfFinAddOrder R) (k : ℕ) :
    canheight (((k : ℤ)) • R) = (k : ℝ) ^ 2 * canheight R := by
  cases k with
  | zero =>
      show canheight ((0 : ℤ) • R) = ((0 : ℕ) : ℝ) ^ 2 * canheight R
      rw [zero_smul, canheight_zero]
      norm_num
  | succ m =>
      have h := (canheight_nat_pair hR m).1
      have e : ((m : ℕ) + 1 : ℕ) = ((m : ℤ) + 1) := by push_cast; ring
      rw [show (((m + 1 : ℕ)) : ℤ) = ((m : ℤ) + 1) from by push_cast; ring, h]
      push_cast
      ring

/-- **★★★ THE MULTIPLE LAW (integer multiples) ★★★**
`ĥ(k·R) = k²·ĥ(R)` for every `k : ℤ`.  Negative `k` reduces to positive via
`ĥ(−R) = ĥ(R)`. -/
theorem canheight_zsmul (hR : ¬ IsOfFinAddOrder R) (k : ℤ) :
    canheight (k • R) = (k : ℝ) ^ 2 * canheight R := by
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk with m
    exact canheight_nsmul hR m
  · -- k < 0: write k = -(m) with m = (-k).toNat
    obtain ⟨m, hm⟩ : ∃ m : ℕ, k = -(m : ℤ) := ⟨(-k).toNat, by omega⟩
    rw [hm, neg_smul, canheight_neg, canheight_nsmul hR m]
    push_cast
    ring

end Multiple

end PrincipiaTractalis.CanheightMultiple389a1

#print axioms PrincipiaTractalis.CanheightMultiple389a1.canheight_zero
#print axioms PrincipiaTractalis.CanheightMultiple389a1.canheight_neg
#print axioms PrincipiaTractalis.CanheightMultiple389a1.canheight_rec
#print axioms PrincipiaTractalis.CanheightMultiple389a1.canheight_nsmul
#print axioms PrincipiaTractalis.CanheightMultiple389a1.canheight_zsmul
