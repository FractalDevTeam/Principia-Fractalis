/-
# PF.Ch24Descent2TorsionRatBridge_2026_10_17

**The `Rat` bridge: the last brick. `y² = x³ + x` has no rational point with
`x ≠ 0`.**

`descent_core` (5ea7e0e9) gave the arithmetic heart; the two bookkeeping layers
(4028e3c0) gave the lowest-terms form and rank-zero-from-2-torsion. The gap
between them was the `Rat`-level step. This file closes it.

## The computation

For `x ≠ 0` on `y² = x³ + x`, write `a = x.num`, `b = x.den > 0`, coprime.
From `x·b = a`,

    `((b²)·y)²  =  b⁴·y²  =  b⁴(x³ + x)  =  (xb)³b + (xb)b³  =  a³b + ab³
                =  a·b·(a² + b²)`.

So `Y := b²y` has `Y² ∈ ℤ`. Since `ℤ` is integrally closed in `ℚ`, `Y ∈ ℤ`,
and `descent_lowest_terms` then forces `a = 0`, i.e. `x = 0`.

## What this file concludes

§4 gives `solutions_are_origin`: the only rational solution of `y² = x³ + x` is
`(0, 0)`. §5 then plumbs that into the Mordell–Weil group and concludes

    **`Ecurve_rank_eq_zero : Module.rank ℤ Ecurve.toAffine.Point = 0`**

for `Ecurve = ⟨0, 0, 0, 1, 0⟩`. **This is the first EXACT rank in the
repository** — every other rank theorem in the tree is a lower bound
`n ≤ rank`. It uses no `L`-function anywhere: the chain is `descent_core`
(5ea7e0e9) → `descent_lowest_terms` (4028e3c0) → the `Rat` bridge here →
`rank_eq_zero_of_two_torsion`, with mathlib's `not_fermat_42` as the engine.

For the 2-torsion step, `Ecurve` has `a₁ = a₃ = 0`, so
`negY x y = -y - a₁x - a₃ = -y`; at `y = 0` that is `y = negY x y`, and
`WeierstrassCurve.Affine.Point.add_self_of_Y_eq` gives `P + P = 0` directly —
no dependent rewriting of the point's coordinates is needed.

## The integrality step

`rat_sq_int_is_int` : a rational whose square is an integer is an integer. The
`Rat.den`-of-a-power route needs reduced-form uniqueness lemmas I could not
locate at this pin; instead this is obtained from mathlib's
`irrational_nrt_of_notint_nrt` by contradiction — a rational cannot be
irrational. Cheaper than proving reduced-form uniqueness by hand, and it is the
same mathematics.

Three-axiom bar: `[propext, Classical.choice, Quot.sound]`. No `sorry`,
no `axiom`, no `native_decide`.

Author: Pablo Cohen + Claude Opus 5. 2026-10-17.
-/
import PF.Ch24Descent2TorsionBookkeeping_2026_10_17
import Mathlib.Data.Real.Irrational
import Mathlib.Data.Rat.Lemmas
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

namespace PrincipiaTractalis.Ch24DescentRatBridge20261017

open PrincipiaTractalis.Ch24DescentBookkeeping20261017

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

/-! ## §3 — the bridge -/

/-- **The last brick.** `y² = x³ + x` has no rational point with `x ≠ 0`. -/
theorem no_rational_point_x_ne_zero {x y : ℚ} (h : y ^ 2 = x ^ 3 + x) : x = 0 := by
  set a : ℤ := x.num with ha
  set b : ℤ := (x.den : ℤ) with hb
  have hbpos : 0 < b := by
    rw [hb]; exact_mod_cast x.pos
  have hco : IsCoprime a b := isCoprime_num_den x
  -- `x * b = a` over `ℚ`
  have hxb : x * (b : ℚ) = (a : ℚ) := by
    rw [hb, ha]
    exact_mod_cast x.mul_den_eq_num
  -- the key algebraic identity
  have hY : ((b : ℚ) ^ 2 * y) ^ 2 = ((a * b * (a ^ 2 + b ^ 2) : ℤ) : ℚ) := by
    have e1 : ((b : ℚ) ^ 2 * y) ^ 2 = (b : ℚ) ^ 4 * y ^ 2 := by ring
    have e2 : (b : ℚ) ^ 4 * y ^ 2 = (b : ℚ) ^ 4 * (x ^ 3 + x) := by rw [h]
    have e3 : (b : ℚ) ^ 4 * (x ^ 3 + x)
        = (x * (b : ℚ)) ^ 3 * (b : ℚ) + (x * (b : ℚ)) * (b : ℚ) ^ 3 := by ring
    rw [hxb] at e3
    push_cast
    rw [e1, e2, e3]
    ring
  -- integrality, then the descent
  obtain ⟨Y₀, hY₀⟩ := rat_sq_int_is_int hY
  have hint : Y₀ ^ 2 = a * b * (a ^ 2 + b ^ 2) := by
    have : ((Y₀ : ℚ)) ^ 2 = ((a * b * (a ^ 2 + b ^ 2) : ℤ) : ℚ) := by
      rw [← hY₀]; exact hY
    exact_mod_cast this
  have hazero : a = 0 := descent_lowest_terms hbpos hco hint
  -- `x.num = 0` forces `x = 0`
  rw [ha] at hazero
  exact Rat.zero_iff_num_zero.mpr hazero

/-! ## §4 — the capstone: every rational point is 2-torsion, hence rank 0 -/

/-- The only rational solution of `y² = x³ + x` is `(0, 0)`. -/
theorem solutions_are_origin {x y : ℚ} (h : y ^ 2 = x ^ 3 + x) : x = 0 ∧ y = 0 := by
  have hx : x = 0 := no_rational_point_x_ne_zero h
  refine ⟨hx, ?_⟩
  rw [hx] at h
  simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by simpa using h)


/-! ## §5 — the capstone: `Module.rank ℤ E(ℚ) = 0`

`E : y² = x³ + x` as a `WeierstrassCurve ℚ` is `⟨0, 0, 0, 1, 0⟩` (so
`a₁ = a₂ = a₃ = a₆ = 0`, `a₄ = 1`), for which `negY x y = -y - a₁x - a₃ = -y`.

Every affine rational point is `(0, 0)` by §4, and there `y = -y`, so
`add_self_of_Y_eq` gives `P + P = 0`. With the point at infinity that covers
every point, and `rank_eq_zero_of_two_torsion` concludes. -/

/-- `E : y² = x³ + x`, conductor 64. -/
def Ecurve : WeierstrassCurve ℚ := ⟨0, 0, 0, 1, 0⟩

/-- Every rational point of `E` is killed by `2`. -/
theorem Ecurve_two_torsion (P : Ecurve.toAffine.Point) : P + P = 0 := by
  cases P with
  | zero => exact add_zero 0
  | some h =>
      rename_i x y
      have heq : y ^ 2 = x ^ 3 + x := by
        have h1 := h.left
        rw [WeierstrassCurve.Affine.equation_iff] at h1
        simp only [Ecurve] at h1
        linarith [h1]
      have hy0 : y = 0 := (solutions_are_origin heq).2
      refine WeierstrassCurve.Affine.Point.add_self_of_Y_eq ?_
      simp [WeierstrassCurve.Affine.negY, Ecurve, hy0]

/-- **★ FIRST EXACT RANK IN THE REPOSITORY ★**

`Module.rank ℤ E(ℚ) = 0` for `E : y² = x³ + x`.

Every other rank theorem in the tree is a lower bound `n ≤ rank`. This is an
exact value, and it is obtained with no `L`-function: descent core
(`descent_core`) + lowest-terms form (`descent_lowest_terms`) + the `Rat`
bridge (`no_rational_point_x_ne_zero`) + rank-zero-from-2-torsion
(`rank_eq_zero_of_two_torsion`), with Fermat's `a⁴ + b⁴ ≠ c²` from mathlib as
the engine. -/
theorem Ecurve_rank_eq_zero : Module.rank ℤ Ecurve.toAffine.Point = 0 :=
  rank_eq_zero_of_two_torsion Ecurve_two_torsion

end PrincipiaTractalis.Ch24DescentRatBridge20261017

/-! ## §Axiom check -/
#print axioms PrincipiaTractalis.Ch24DescentRatBridge20261017.rat_sq_int_is_int
#print axioms PrincipiaTractalis.Ch24DescentRatBridge20261017.isCoprime_num_den
#print axioms PrincipiaTractalis.Ch24DescentRatBridge20261017.no_rational_point_x_ne_zero
#print axioms PrincipiaTractalis.Ch24DescentRatBridge20261017.solutions_are_origin
#print axioms PrincipiaTractalis.Ch24DescentRatBridge20261017.Ecurve_two_torsion
#print axioms PrincipiaTractalis.Ch24DescentRatBridge20261017.Ecurve_rank_eq_zero
