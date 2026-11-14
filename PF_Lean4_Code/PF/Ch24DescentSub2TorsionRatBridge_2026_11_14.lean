/-
# PF.Ch24DescentSub2TorsionRatBridge_2026_11_14

**The `Rat` bridge for `y² = x³ - x` — mirror of
Ch24Descent2TorsionRatBridge_2026_10_17, closing the second exact
rank-0 BSD curve in the corpus.**

## The computation

For `(x, y) ∈ ℚ²` on `y² = x³ - x`, write `a = x.num`, `b = x.den > 0`,
coprime.  From `x·b = a`,

    `((b²)·y)²  =  b⁴·y²  =  b⁴(x³ - x)
                =  (xb)³b - (xb)b³  =  a³b - ab³  =  a·b·(a² - b²)`.

So `Y := b²y` has `Y² ∈ ℤ`.  Since `ℤ` is integrally closed in `ℚ`,
`Y ∈ ℤ`, and `descent_sub_lowest_terms` then forces `a = 0 ∨ a² = b²`,
hence `y = 0` in all three cases (the three 2-torsion points).

## What this file concludes

§4: `solutions_have_y_zero` — every rational solution of `y² = x³ - x`
has `y = 0` (equivalently, `(x, y) ∈ {(0, 0), (1, 0), (-1, 0)}`).

§5: **`Ecurve32a2_rank_eq_zero : Module.rank ℤ Ecurve.toAffine.Point = 0`**

for `Ecurve = ⟨0, 0, 0, -1, 0⟩` (LMFDB 32.a2, conductor 32, rank 0).
**This is the SECOND exact rank theorem in the corpus**, after
`Ch24Descent2TorsionRatBridge_2026_10_17.Ecurve_rank_eq_zero` for
`y² = x³ + x` (2026-10-17).  The two together establish rank 0 for
both quadratic twists of the arithmetic-geometric curve of the
congruent-number problem at `n = 1`.

The chain: `descent_sub_core` → `descent_sub_lowest_terms` → `Rat`
bridge here → `rank_eq_zero_of_two_torsion`, with
`PF.not_fermat_42_sub` (landed 2026-11-14) as the Diophantine engine.

Three-axiom bar: `[propext, Classical.choice, Quot.sound]`.  No
`sorry`, no project axioms, no `native_decide`.

Authors: Pablo Cohen. 2026-11-14.
-/

import PF.Ch24DescentSub2TorsionBookkeeping_2026_11_14
import Mathlib.Data.Real.Irrational
import Mathlib.Data.Rat.Lemmas
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

namespace PrincipiaTractalis.Ch24DescentSubRatBridge20261114

open PrincipiaTractalis.Ch24DescentSubBookkeeping20261114

/-! ## §1 — integrality: a rational whose square is an integer is an integer -/

theorem rat_sq_int_is_int {Y : ℚ} {k : ℤ} (h : Y ^ 2 = (k : ℚ)) :
    ∃ n : ℤ, Y = (n : ℚ) := by
  by_contra hc
  push_neg at hc
  have hreal : ((Y : ℝ)) ^ 2 = (k : ℝ) := by
    have := congrArg (fun q : ℚ => (q : ℝ)) h
    push_cast at this
    exact this
  have hnot : ¬ ∃ z : ℤ, (Y : ℝ) = (z : ℝ) := by
    rintro ⟨z, hz⟩
    exact hc z (by exact_mod_cast hz)
  have hirr : Irrational (Y : ℝ) :=
    irrational_nrt_of_notint_nrt 2 k hreal hnot (by norm_num)
  exact hirr ⟨Y, rfl⟩

/-! ## §2 — the numerator and denominator of a rational are coprime over `ℤ` -/

theorem isCoprime_num_den (x : ℚ) : IsCoprime x.num ((x.den : ℤ)) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  simpa [Int.gcd] using x.reduced

/-! ## §3 — the Rat bridge (mirror form) -/

/-- Every rational solution of `y² = x³ - x` has `y = 0`.

Proof route: build the integer `Y₀` with `Y₀² = a·b·(a² - b²)` from the Rat
equation + `rat_sq_int_is_int`.  Apply `descent_sub_lowest_terms` to get
`a = 0 ∨ a² = b²`, which in both cases forces `a·b·(a² - b²) = 0`, hence
`Y₀² = 0`, `Y₀ = 0`, hence `b² · y = 0` (as rationals), hence `y = 0`
(since `b > 0`). -/
theorem solutions_have_y_zero {x y : ℚ} (h : y ^ 2 = x ^ 3 - x) : y = 0 := by
  set a : ℤ := x.num with ha
  set b : ℤ := (x.den : ℤ) with hb
  have hbpos : 0 < b := by
    rw [hb]; exact_mod_cast x.pos
  have hbne : (b : ℚ) ≠ 0 := by
    have : b ≠ 0 := Int.ne_of_gt hbpos
    exact_mod_cast this
  have hco : IsCoprime a b := isCoprime_num_den x
  have hxb : x * (b : ℚ) = (a : ℚ) := by
    rw [hb, ha]
    exact_mod_cast x.mul_den_eq_num
  -- Key algebraic identity: (b²·y)² = a·b·(a² - b²) in ℚ.
  have hY : ((b : ℚ) ^ 2 * y) ^ 2 = ((a * b * (a ^ 2 - b ^ 2) : ℤ) : ℚ) := by
    have e1 : ((b : ℚ) ^ 2 * y) ^ 2 = (b : ℚ) ^ 4 * y ^ 2 := by ring
    have e2 : (b : ℚ) ^ 4 * y ^ 2 = (b : ℚ) ^ 4 * (x ^ 3 - x) := by rw [h]
    have e3 : (b : ℚ) ^ 4 * (x ^ 3 - x)
        = (x * (b : ℚ)) ^ 3 * (b : ℚ) - (x * (b : ℚ)) * (b : ℚ) ^ 3 := by ring
    rw [hxb] at e3
    push_cast
    rw [e1, e2, e3]
    ring
  obtain ⟨Y₀, hY₀⟩ := rat_sq_int_is_int hY
  have hint : Y₀ ^ 2 = a * b * (a ^ 2 - b ^ 2) := by
    have : ((Y₀ : ℚ)) ^ 2 = ((a * b * (a ^ 2 - b ^ 2) : ℤ) : ℚ) := by
      rw [← hY₀]; exact hY
    exact_mod_cast this
  have hclass : a = 0 ∨ a ^ 2 = b ^ 2 := descent_sub_lowest_terms hbpos hco hint
  -- Either way, a·b·(a² - b²) = 0, hence Y₀² = 0, hence Y₀ = 0.
  have h_prod_zero : a * b * (a ^ 2 - b ^ 2) = 0 := by
    rcases hclass with h_num_zero | h_sq_eq
    · rw [h_num_zero]; ring
    · have : a ^ 2 - b ^ 2 = 0 := by linarith [h_sq_eq]
      rw [this]; ring
  have hY0_sq_zero : Y₀ ^ 2 = 0 := by rw [hint, h_prod_zero]
  have hY0_zero : Y₀ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hY0_sq_zero
  -- Y₀ = b²·y as rationals, so b²·y = 0, hence y = 0 (since b ≠ 0).
  have h_by : (b : ℚ) ^ 2 * y = 0 := by
    rw [hY₀, hY0_zero]; push_cast; ring
  have hb2_ne : (b : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 hbne
  exact (mul_eq_zero.mp h_by).resolve_left hb2_ne

/-! ## §4 — the capstone: `Module.rank ℤ E(ℚ) = 0` -/

/-- `E : y² = x³ - x` as a Weierstrass curve: `⟨0, 0, 0, -1, 0⟩`. -/
def Ecurve : WeierstrassCurve ℚ := ⟨0, 0, 0, -1, 0⟩

/-- Every rational point of `E` is killed by `2`. -/
theorem Ecurve_two_torsion (P : Ecurve.toAffine.Point) : P + P = 0 := by
  cases P with
  | zero => exact add_zero 0
  | some h =>
      rename_i x y
      have heq : y ^ 2 = x ^ 3 - x := by
        have h1 := h.left
        rw [WeierstrassCurve.Affine.equation_iff] at h1
        simp only [Ecurve] at h1
        linarith [h1]
      have hy0 : y = 0 := solutions_have_y_zero heq
      refine WeierstrassCurve.Affine.Point.add_self_of_Y_eq ?_
      simp [WeierstrassCurve.Affine.negY, Ecurve, hy0]

/-- **★ SECOND EXACT RANK IN THE REPOSITORY ★**

`Module.rank ℤ E(ℚ) = 0` for `E : y² = x³ - x` (LMFDB 32.a2,
conductor 32).

Together with `Ch24Descent2TorsionRatBridge_2026_10_17.Ecurve_rank_eq_zero`
(for `y² = x³ + x`, 2026-10-17), this establishes rank 0 for both
quadratic twists of the arithmetic-geometric curve of the congruent-number
problem at `n = 1` — both curves being the two rational 2-isogenies of the
congruent-number elliptic curve `E_1 : y² = x³ - x`.

The chain: `descent_sub_core` + `descent_sub_lowest_terms` + the `Rat`
bridge above + `rank_eq_zero_of_two_torsion`, with `PF.not_fermat_42_sub`
(the classical difference-form Fermat n = 4 theorem, landed 2026-11-14)
as the Diophantine engine.  No `L`-function appears anywhere. -/
theorem Ecurve32a2_rank_eq_zero : Module.rank ℤ Ecurve.toAffine.Point = 0 :=
  rank_eq_zero_of_two_torsion Ecurve_two_torsion

end PrincipiaTractalis.Ch24DescentSubRatBridge20261114

/-! ## §Axiom check -/
#print axioms PrincipiaTractalis.Ch24DescentSubRatBridge20261114.rat_sq_int_is_int
#print axioms PrincipiaTractalis.Ch24DescentSubRatBridge20261114.isCoprime_num_den
#print axioms PrincipiaTractalis.Ch24DescentSubRatBridge20261114.solutions_have_y_zero
#print axioms PrincipiaTractalis.Ch24DescentSubRatBridge20261114.Ecurve_two_torsion
#print axioms PrincipiaTractalis.Ch24DescentSubRatBridge20261114.Ecurve32a2_rank_eq_zero
