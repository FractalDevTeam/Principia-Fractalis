/-
# PF.DuplicationHeightBound37a1_r133

★★★ 2026-07-27 — B4 OF THE NON-TORSION ARC ★★★

The duplication height inequality for the curve 37a1 (`y² + y = x³ − x`):
stone B4 of the arc mapped in `codex/BSD_NONTORSION_ARC_PLAN_2026-07-27.md`,
joining B2 (`DuplicationFormula37a1_r132`: `x(2P) = f(x)/g(x)`) and B3
(`DuplicationBezout37a1_r131`: gcd/size bounds for the homogenized pair
`F, D`) into the exact quartic step that B1's driver
(`NaiveHeightQ_r130.infinite_of_duplication_step`, with `κ = 171`) consumes.

The capstone:

  `duplication_height_bound : naiveHeight x ^ 4 ≤ 171 * naiveHeight (f x / g x)`

for EVERY rational `x` — no on-curve hypothesis is needed, because `g` has no
rational roots (r132) so the fraction `f x / g x` is always defined and the
homogenized denominator `D` never vanishes.

The bookkeeping heart is `naiveHeight_div_int`: for `Q ≠ 0` the reduced
fraction of `p/Q` has numerator and denominator EXACTLY `p/gcd` and `Q/gcd`
(up to sign) — proved elementarily from `Rat.num_div_den` cross-multiplication
plus coprimality of the reduced pair, avoiding any `Rat.divInt` internals.

Also exported: `dbl_height`, the driver-ready corollary through r132's
`dbl_x` — for a rational affine point `P` of 37a1, `P + P = some h'` with
`naiveHeight (x P) ^ 4 ≤ 171 * naiveHeight (x (2P))`.

HONEST SCOPE. This file proves the height inequality for the duplication
RATIONAL MAP of the one curve 37a1 and its transport along r132's group-law
formula. It does not compute any concrete point (B5), does not certify any
point as non-torsion, and does not touch `Module.rank` (r129).

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-27.
-/
import PF.NaiveHeightQ_r130
import PF.DuplicationBezout37a1_r131
import PF.DuplicationFormula37a1_r132
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

namespace PrincipiaTractalis.DuplicationHeightBound37a1

open PrincipiaTractalis.NaiveHeightQ
open PrincipiaTractalis.DuplicationBezout37a1
open PrincipiaTractalis.DuplicationFormula37a1

/-! ## §1 — the reduction bookkeeping: `naiveHeight (p/Q)` exactly

For integers `p, Q` with `Q ≠ 0`, the rational `p/Q` in lowest terms has
`|num| = |p|/d` and `den = |Q|/d` for `d = gcd(p, Q)` — an exact equality,
proved without touching `Rat.divInt` internals: cross-multiplying
`p/Q = num/den` gives `p·den = num·Q`; coprimality of `(num, den)` forces
`den ∣ Q`, and the quotient `k = Q/den` satisfies `p = num·k`, `Q = den·k`,
`gcd(p, Q) = |k|`. -/

section Reduction

/-- **Structure of the unreduced fraction.** For `Q ≠ 0` and
`r = (p : ℚ)/(Q : ℚ)`, there is a common factor `k ≠ 0` with
`p = num(r)·k` and `Q = den(r)·k`. -/
theorem exists_common_factor (p Q : ℤ) (hQ : Q ≠ 0) :
    ∃ k : ℤ, k ≠ 0 ∧ p = ((p : ℚ) / (Q : ℚ)).num * k
      ∧ Q = (((p : ℚ) / (Q : ℚ)).den : ℤ) * k := by
  set r : ℚ := (p : ℚ) / (Q : ℚ) with hr
  have hQQ : (Q : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hQ
  have hdenQ : ((r.den : ℚ)) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hden0 : ((r.den : ℤ)) ≠ 0 := by exact_mod_cast r.den_ne_zero
  -- cross-multiplication: p · den(r) = num(r) · Q
  have h1 : (p : ℚ) / (Q : ℚ) = (r.num : ℚ) / (r.den : ℚ) := by
    rw [← hr]; exact (Rat.num_div_den r).symm
  have hcross : p * (r.den : ℤ) = r.num * Q := by
    exact_mod_cast (div_eq_div_iff hQQ hdenQ).mp h1
  -- coprimality of the reduced pair
  have hcop : IsCoprime r.num (r.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd, Int.natAbs_natCast] using r.reduced
  -- den(r) ∣ Q, and the quotient is the common factor
  have hnum_mul : (r.den : ℤ) ∣ r.num * Q := ⟨p, by linear_combination -hcross⟩
  have hdvd : (r.den : ℤ) ∣ Q := hcop.symm.dvd_of_dvd_mul_left hnum_mul
  refine ⟨Q / (r.den : ℤ), ?_, ?_, (Int.mul_ediv_cancel' hdvd).symm⟩
  · intro h0
    exact hQ (by rw [← Int.mul_ediv_cancel' hdvd, h0, mul_zero])
  · refine mul_right_cancel₀ hden0 ?_
    have hQk : Q = (r.den : ℤ) * (Q / (r.den : ℤ)) :=
      (Int.mul_ediv_cancel' hdvd).symm
    linear_combination hcross + r.num * hQk

/-- **The exact height of an unreduced fraction.** For `Q ≠ 0` and
`d = gcd(p, Q)`: `naiveHeight (p/Q) = max |p/d| |Q/d|`. This is the bridge
between r131's reduced max (stated on `F/gcd`, `D/gcd`) and r130's
`naiveHeight` (stated on `num`, `den`). -/
theorem naiveHeight_div_int (p Q : ℤ) (hQ : Q ≠ 0) :
    naiveHeight ((p : ℚ) / (Q : ℚ))
      = max ((p / (Int.gcd p Q : ℤ)).natAbs) ((Q / (Int.gcd p Q : ℤ)).natAbs) := by
  obtain ⟨k, hk0, hpk, hQk⟩ := exists_common_factor p Q hQ
  set r : ℚ := (p : ℚ) / (Q : ℚ) with hr
  -- gcd(p, Q) = |k|
  have hd : Int.gcd p Q = k.natAbs := by
    rw [hpk, hQk]
    unfold Int.gcd
    rw [Int.natAbs_mul, Int.natAbs_mul, Nat.gcd_mul_right, Int.natAbs_natCast,
      r.reduced.gcd_eq_one, one_mul]
  have hdpos : 0 < Int.gcd p Q := by
    rw [hd]; exact Int.natAbs_pos.mpr hk0
  -- |p/d|·d = |p| and |Q/d|·d = |Q| (exact division by the gcd)
  have ep : (p / (Int.gcd p Q : ℤ)).natAbs * Int.gcd p Q = p.natAbs := by
    calc (p / (Int.gcd p Q : ℤ)).natAbs * Int.gcd p Q
        = (p / (Int.gcd p Q : ℤ)).natAbs * ((Int.gcd p Q : ℤ)).natAbs := by
          rw [Int.natAbs_natCast]
      _ = ((p / (Int.gcd p Q : ℤ)) * (Int.gcd p Q : ℤ)).natAbs :=
          (Int.natAbs_mul _ _).symm
      _ = p.natAbs := by rw [Int.ediv_mul_cancel (Int.gcd_dvd_left _ _)]
  have eQ : (Q / (Int.gcd p Q : ℤ)).natAbs * Int.gcd p Q = Q.natAbs := by
    calc (Q / (Int.gcd p Q : ℤ)).natAbs * Int.gcd p Q
        = (Q / (Int.gcd p Q : ℤ)).natAbs * ((Int.gcd p Q : ℤ)).natAbs := by
          rw [Int.natAbs_natCast]
      _ = ((Q / (Int.gcd p Q : ℤ)) * (Int.gcd p Q : ℤ)).natAbs :=
          (Int.natAbs_mul _ _).symm
      _ = Q.natAbs := by rw [Int.ediv_mul_cancel (Int.gcd_dvd_right _ _)]
  -- |p| = |num(r)|·d and |Q| = den(r)·d
  have hpabs : p.natAbs = r.num.natAbs * Int.gcd p Q := by
    rw [hd, hpk, Int.natAbs_mul]
  have hQabs : Q.natAbs = r.den * Int.gcd p Q := by
    rw [hd, hQk, Int.natAbs_mul, Int.natAbs_natCast]
  -- cancel d
  have hnum_eq : (p / (Int.gcd p Q : ℤ)).natAbs = r.num.natAbs :=
    Nat.eq_of_mul_eq_mul_right hdpos (by rw [ep, hpabs])
  have hden_eq : (Q / (Int.gcd p Q : ℤ)).natAbs = r.den :=
    Nat.eq_of_mul_eq_mul_right hdpos (by rw [eQ, hQabs])
  simp only [naiveHeight]
  rw [hnum_eq, hden_eq]

end Reduction

/-! ## §2 — the height bound in homogenized coordinates

Composing §1 with r131's `reduced_height_bound'`: for coprime `(a, b)` with
`b ≠ 0` and `D a b ≠ 0`, the height of `F/D : ℚ` dominates `H⁴/171`. -/

/-- The B3 bound transported to `naiveHeight`:
`H⁴ ≤ 171 · naiveHeight (F/D)` for `H = max |a| |b|`. -/
theorem height_bound_of_coprime {a b : ℤ} (hcop : IsCoprime a b) (hb : b ≠ 0)
    (hD : D a b ≠ 0) :
    (max a.natAbs b.natAbs) ^ 4
      ≤ 171 * naiveHeight ((F a b : ℚ) / (D a b : ℚ)) := by
  rw [naiveHeight_div_int (F a b) (D a b) hD]
  exact reduced_height_bound' hcop hb hD

/-! ## §3 — dehomogenization: `f x / g x = F/D` for `x = num/den` -/

section Cast

private theorem F_cast (a b : ℤ) (hb : (b : ℚ) ≠ 0) :
    ((F a b : ℤ) : ℚ) = (b : ℚ) ^ 4 * f ((a : ℚ) / (b : ℚ)) := by
  simp only [F, f]
  push_cast
  field_simp

private theorem D_cast (a b : ℤ) (hb : (b : ℚ) ≠ 0) :
    ((D a b : ℤ) : ℚ) = (b : ℚ) ^ 4 * g ((a : ℚ) / (b : ℚ)) := by
  simp only [D, G3, g]
  push_cast
  field_simp

end Cast

/-! ## §4 — THE CAPSTONE: the duplication height inequality on 37a1

For every rational `x` (no on-curve hypothesis: `g` never vanishes on ℚ
by r132's `g_ne_zero`, so the fraction and the homogeneous denominator are
always honest):

  `naiveHeight x ^ 4 ≤ 171 * naiveHeight (f x / g x)`.

This is exactly the quartic step `h(P)⁴ ≤ κ · h(2P)` with `κ = 171` that
r130's `infinite_of_duplication_step` consumes. -/

/-- **The duplication height inequality for 37a1.** -/
theorem duplication_height_bound (x : ℚ) :
    naiveHeight x ^ 4 ≤ 171 * naiveHeight (f x / g x) := by
  -- the reduced coordinates of x
  have hb : ((x.den : ℤ)) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have hbQ : (((x.den : ℤ)) : ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have hcop : IsCoprime x.num ((x.den : ℤ)) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd, Int.natAbs_natCast] using x.reduced
  have hx : x = (x.num : ℚ) / (((x.den : ℤ)) : ℚ) := by
    rw [Int.cast_natCast]
    exact (Rat.num_div_den x).symm
  -- dehomogenize F and D against f and g
  have hfval : ((F x.num (x.den : ℤ) : ℤ) : ℚ)
      = (((x.den : ℤ)) : ℚ) ^ 4 * f x := by
    have h := F_cast x.num (x.den : ℤ) hbQ
    rw [← hx] at h
    exact h
  have hDval : ((D x.num (x.den : ℤ) : ℤ) : ℚ)
      = (((x.den : ℤ)) : ℚ) ^ 4 * g x := by
    have h := D_cast x.num (x.den : ℤ) hbQ
    rw [← hx] at h
    exact h
  -- the homogeneous denominator never vanishes (g has no rational roots)
  have hgx : g x ≠ 0 := g_ne_zero x
  have hD : D x.num (x.den : ℤ) ≠ 0 := by
    intro h0
    apply mul_ne_zero (pow_ne_zero 4 hbQ) hgx
    rw [← hDval, h0, Int.cast_zero]
  -- the fraction identity
  have hfg : f x / g x
      = ((F x.num (x.den : ℤ) : ℤ) : ℚ) / ((D x.num (x.den : ℤ) : ℤ) : ℚ) := by
    rw [hfval, hDval, mul_div_mul_left _ _ (pow_ne_zero 4 hbQ)]
  -- naiveHeight x in homogenized form
  have hHx : max x.num.natAbs ((x.den : ℤ)).natAbs = naiveHeight x := by
    simp only [naiveHeight, Int.natAbs_natCast]
  calc naiveHeight x ^ 4
      = (max x.num.natAbs ((x.den : ℤ)).natAbs) ^ 4 := by rw [hHx]
    _ ≤ 171 * naiveHeight
          ((F x.num (x.den : ℤ) : ℚ) / (D x.num (x.den : ℤ) : ℚ)) :=
        height_bound_of_coprime hcop hb hD
    _ = 171 * naiveHeight (f x / g x) := by rw [← hfg]

/-! ## §5 — the driver-ready corollary through the group law (B2 + B4)

For a rational affine point `P` of 37a1, doubling stays affine (r132) and the
new x-coordinate's height satisfies the quartic step. -/

open WeierstrassCurve WeierstrassCurve.Affine in
/-- **Duplication height step on the curve.** For any rational affine point
`P = some h` of 37a1 at `(x, y)`: `P + P` is an affine point `some h'` at
some `(x', y')` with `naiveHeight x ^ 4 ≤ 171 * naiveHeight x'`. This is the
exact shape B5 feeds into r130's `infinite_of_duplication_step` (κ = 171). -/
theorem dbl_height {x y : ℚ} (h : E37a1.toAffine.Nonsingular x y) :
    ∃ (x' y' : ℚ) (h' : E37a1.toAffine.Nonsingular x' y'),
      Point.some h + Point.some h = Point.some h' ∧
        naiveHeight x ^ 4 ≤ 171 * naiveHeight x' := by
  obtain ⟨x', y', h', hadd, hx'⟩ := dbl_x h
  refine ⟨x', y', h', hadd, ?_⟩
  rw [hx']
  exact duplication_height_bound x

end PrincipiaTractalis.DuplicationHeightBound37a1

#print axioms PrincipiaTractalis.DuplicationHeightBound37a1.exists_common_factor
#print axioms PrincipiaTractalis.DuplicationHeightBound37a1.naiveHeight_div_int
#print axioms PrincipiaTractalis.DuplicationHeightBound37a1.height_bound_of_coprime
#print axioms PrincipiaTractalis.DuplicationHeightBound37a1.duplication_height_bound
#print axioms PrincipiaTractalis.DuplicationHeightBound37a1.dbl_height
