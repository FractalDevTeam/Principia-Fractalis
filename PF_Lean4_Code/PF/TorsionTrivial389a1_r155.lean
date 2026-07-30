/-
# PF.TorsionTrivial389a1_r155

★★★ 2026-07-30 — THE TORSION SUBGROUP OF 389a1 IS TRIVIAL ★★★

`E389a1(ℚ)` has **no** nonzero torsion point:

  `IsOfFinAddOrder R → R = 0`

and consequently `R ≠ 0 → 0 < ĥ(R)`.

## The argument

Everything comes from the window already proved in r147, plus one arithmetic
accident:

  `1728 = 12³`.

r147's `naiveHeight_le_twelve_of_canheight_zero` says that if `ĥ(R) = 0` then
`log h(x(2ⁿR)) ≤ (log 1728)/3 = log 12` for *every* `n`, i.e.

  `h(x(2ⁿR)) ≤ 12`   for all `n`.

So a torsion point and all of its doublings are confined to the finite set of
rationals of naive height at most 12.  There are exactly **183** of them.

Now iterate the duplication map `x ↦ f x / g x` (r143) on that set:

  * of the 183, only `-1`, `0`, `1` still have height `≤ 12` after one step
    (they go to `10/9`, `3`, `6`);
  * all three escape on the second step, to `47503/16641`, `114/121`,
    `1431/961`.

So no rational of height `≤ 12` keeps height `≤ 12` for two doublings, and a
nonzero torsion point would have to.  Contradiction.

## Why this is cheap

The check needs **no curve equation and no square-testing**.  We never ask
which `x` carry a rational `y`; we only iterate a rational function and
compare heights.  That makes the whole finite verification a `decide +kernel`
over `ℚ` arithmetic — `Nat.gcd`, `+`, `*` — with no `Nat.sqrt` and no
existential.  (`Finset.Icc (-12 : ℤ) 12` does *not* work here: it is built
from `Nat.castEmbedding.trans (addLeftEmbedding _)`, which the kernel will not
unfold.  `Finset.range` does.)

`decide +kernel` performs the reduction in the kernel and elaborates to
`of_decide_eq_true rfl`; it is **not** `native_decide` and introduces no
`Lean.ofReduceBool`.  The axiom print below confirms this.

## Consequence

Every non-torsion side condition in the parallelogram law (r150) and the
multiple law (r151) is now automatic for 389a1: any nonzero point qualifies.

HONEST SCOPE.  This is 389a1 only.  The bound `h ≤ 12` is the cube root of
that curve's duplication constant 1728; for 5077a1 the constant is 105754 and
the corresponding bound is 47, a much larger enumeration.  Nothing here proves
Mazur's theorem, uses reduction mod p, or bounds torsion for any other curve.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-30.
-/
import PF.RegulatorPositive389a1_r153

namespace PrincipiaTractalis.TorsionTrivial389a1

open PrincipiaTractalis.NaiveHeightQ
open PrincipiaTractalis.E389a1RankOne
open PrincipiaTractalis.CanonicalHeight389a1
open PrincipiaTractalis.RegulatorPositive389a1
open WeierstrassCurve WeierstrassCurve.Affine

/-! ## §1 — the 183 rationals of naive height at most 12 -/

/-- Numerators `i - 12` for `i < 25`, denominators `j + 1` for `j < 12`.
Built on `Finset.range` so that the kernel can unfold it. -/
def cand : Finset ℚ :=
  ((Finset.range 25) ×ˢ (Finset.range 12)).image
    (fun p => ((p.1 : ℚ) - 12) / ((p.2 : ℚ) + 1))

/-- Every rational of naive height `≤ 12` is in `cand`. -/
theorem mem_cand {q : ℚ} (h : naiveHeight q ≤ 12) : q ∈ cand := by
  have hn : q.num.natAbs ≤ 12 := le_trans (le_max_left _ _) h
  have hd : q.den ≤ 12 := le_trans (le_max_right _ _) h
  have hd1 : 1 ≤ q.den := q.pos
  have hnum_lb : -12 ≤ q.num := by omega
  have hnum_ub : q.num ≤ 12 := by omega
  refine Finset.mem_image.mpr ⟨((q.num + 12).toNat, q.den - 1), ?_, ?_⟩
  · rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨by omega, by omega⟩
  · have hi : (((q.num + 12).toNat : ℕ) : ℚ) = (q.num : ℚ) + 12 := by
      have ht : ((q.num + 12).toNat : ℤ) = q.num + 12 :=
        Int.toNat_of_nonneg (by omega)
      have : (((q.num + 12).toNat : ℕ) : ℚ) = (((q.num + 12).toNat : ℤ) : ℚ) := by
        push_cast; ring
      rw [this, ht]; push_cast; ring
    have hj : (((q.den - 1 : ℕ) : ℚ)) + 1 = (q.den : ℚ) := by
      rw [Nat.cast_sub hd1]; push_cast; ring
    simp only []
    rw [hi, hj]
    have : (q.num : ℚ) + 12 - 12 = (q.num : ℚ) := by ring
    rw [this]
    exact Rat.num_div_den q

/-! ## §2 — the finite verification -/

set_option maxRecDepth 100000 in
/-- **The finite check.**  No rational of naive height `≤ 12` still has
height `≤ 12` after two applications of `x ↦ f x / g x`.

183 candidates, closed by kernel reduction.  Only `-1`, `0`, `1` survive the
first step (to `10/9`, `3`, `6`) and none survives the second. -/
theorem no_survivor : ∀ q ∈ cand, ¬ (naiveHeight (f q / g q) ≤ 12 ∧
    naiveHeight (f (f q / g q) / g (f q / g q)) ≤ 12) := by decide +kernel

/-! ## §3 — two doublings in `X`-form -/

/-- `X(2·R)` for an affine `R`. -/
theorem X_two_smul {x₀ y₀ : ℚ} (h₀ : E389a1.toAffine.Nonsingular x₀ y₀) :
    X ((2 : ℤ) • Point.some h₀) = f x₀ / g x₀ := by
  obtain ⟨x₁, y₁, h₁, e₁, hx₁⟩ := dbl_step h₀
  have s₁ : (2 : ℤ) • Point.some h₀ = Point.some h₁ := by
    rw [two_zsmul_eq]; exact e₁
  rw [s₁]
  show x₁ = _
  exact hx₁

/-- `X(4·R)` is the second iterate of `x ↦ f x / g x`. -/
theorem X_four_smul {x₀ y₀ : ℚ} (h₀ : E389a1.toAffine.Nonsingular x₀ y₀) :
    X (((2 : ℤ) ^ 2) • Point.some h₀)
      = f (f x₀ / g x₀) / g (f x₀ / g x₀) := by
  obtain ⟨x₁, y₁, h₁, e₁, hx₁⟩ := dbl_step h₀
  obtain ⟨x₂, y₂, h₂, e₂, hx₂⟩ := dbl_step h₁
  have h4 : ((2 : ℤ) ^ 2) • Point.some h₀
      = (2 : ℤ) • ((2 : ℤ) • Point.some h₀) := by
    rw [smul_smul]; norm_num
  have s₁ : (2 : ℤ) • Point.some h₀ = Point.some h₁ := by
    rw [two_zsmul_eq]; exact e₁
  have s₂ : (2 : ℤ) • Point.some h₁ = Point.some h₂ := by
    rw [two_zsmul_eq]; exact e₂
  rw [h4, s₁, s₂]
  show x₂ = _
  rw [hx₂, hx₁]

/-! ## §4 — the theorem -/

/-- **CAPSTONE — the torsion subgroup of `E389a1(ℚ)` is trivial.** -/
theorem torsion_eq_zero {R : E389a1.toAffine.Point}
    (h : IsOfFinAddOrder R) : R = 0 := by
  by_contra hne
  have h0 : canheight R = 0 := canheight_of_torsion h
  cases R with
  | zero => exact hne rfl
  | @some x y hxy =>
      have b0 := naiveHeight_le_twelve_of_canheight_zero h0 0
      have b1 := naiveHeight_le_twelve_of_canheight_zero h0 1
      have b2 := naiveHeight_le_twelve_of_canheight_zero h0 2
      rw [pow_zero, one_zsmul] at b0
      rw [pow_one, X_two_smul hxy] at b1
      rw [X_four_smul hxy] at b2
      have hx : X (Point.some hxy) = x := rfl
      rw [hx] at b0
      exact no_survivor x (mem_cand b0) ⟨b1, b2⟩

/-- Restated: a nonzero point of `E389a1(ℚ)` has infinite order. -/
theorem nonTorsion_of_ne_zero {R : E389a1.toAffine.Point} (h : R ≠ 0) :
    ¬ IsOfFinAddOrder R :=
  fun hfin => h (torsion_eq_zero hfin)

/-- **The payoff.**  Every nonzero point has strictly positive canonical
height.  This discharges the non-torsion side conditions of r150 and r151
for 389a1 outright. -/
theorem canheight_pos_of_ne_zero {R : E389a1.toAffine.Point} (h : R ≠ 0) :
    0 < canheight R := by
  rcases lt_or_eq_of_le (canheight_nonneg R) with hlt | heq
  · exact hlt
  · exact absurd (canheight_eq_zero_torsion heq.symm) (nonTorsion_of_ne_zero h)

end PrincipiaTractalis.TorsionTrivial389a1

#print axioms PrincipiaTractalis.TorsionTrivial389a1.mem_cand
#print axioms PrincipiaTractalis.TorsionTrivial389a1.no_survivor
#print axioms PrincipiaTractalis.TorsionTrivial389a1.X_four_smul
#print axioms PrincipiaTractalis.TorsionTrivial389a1.torsion_eq_zero
#print axioms PrincipiaTractalis.TorsionTrivial389a1.canheight_pos_of_ne_zero
