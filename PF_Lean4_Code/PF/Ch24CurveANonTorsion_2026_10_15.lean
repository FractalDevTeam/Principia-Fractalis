/-
# PF.Ch24CurveANonTorsion_2026_10_15

**Discharges the non-torsion certificate for ch24's curve A, making
`1 ≤ Module.rank ℤ curveA.toAffine.Point` UNCONDITIONAL.**

Companion to `Ch24CurveARankGeOne_2026_10_15.lean`, which set up
`curveA : WeierstrassCurve ℚ := ⟨0,0,0,0,-2⟩` (`y² = x³ − 2`), the point
`P_A = (3,5)`, and the duplication map `x ↦ f x / g x` with
`f x = x⁴ + 16x`, `g x = 4x³ − 8`. That file left
`¬ IsOfFinAddOrder P_A` as an explicit hypothesis. This file proves it, and
with it the rank bound, with **no appeal to Mazur's torsion bound** (which is
not formalized in mathlib) and no appeal to Nagell–Lutz.

## The argument

Height growth along the doubling orbit, via r130's generic engine
`NaiveHeightQ.infinite_of_duplication_step`. Two Bézout identities over
`ℤ[a,b]` for the homogenised duplication pair
`F = a⁴ + 16ab³`, `D = 4a³b − 8b⁴` do all the work:

* `bezout_a` : `(144a³ − 256b³)·F + (−512ab²)·D = 144·a⁷`
* `bezout_b` : `(4a²b)·F − (a³ + 18b³)·D = 144·b⁷`

Both are one `ring` call. They were found by dehomogenising both ways and
running a one-variable Bézout (the primitive forms are
`4x²·f(x) − (x³+18)·g(x) = 144` and `(9a³−16b³)F − 32ab²D = 9a⁷`, the latter
scaled by 16 to share the constant 144).

From them:

* **`gcd_dvd_144`** — `gcd(F,D) ∣ 144`, since `gcd` divides both `144a⁷` and
  `144b⁷` and `IsCoprime a b` gives `IsCoprime (a⁷) (b⁷)`.
* **`size_bound`** — `144·H⁷ ≤ 912·H³·max |F| |D|` with `H = max |a| |b|`,
  from the cofactor coefficient sums: `a`-side `400 + 512 = 912`, `b`-side
  `4 + 19 = 23`, so `κ = 912`.
* **`duplication_height_bound`** — `H(x)⁴ ≤ 912 · H(f x / g x)`.

The orbit of `x = 3` then clears the threshold immediately:
`x(2P) = 129/100`, `x(4P) = 2340922881/58675600`, and
`H(x(4P)) = 2340922881 > 912`, so from `n = 2` the heights grow strictly and
the `x`-coordinate range is infinite. A torsion point would have finite
`zmultiples`, hence finite `x`-image — contradiction.

## What this settles, and what it does not

**Settles, unconditionally:** `1 ≤ Module.rank ℤ curveA.toAffine.Point`, hence
`ch24_birch_swinnerton_dyer.tex:594`'s printed `rank E(ℚ) = 0 (proven)` is
**false**, and the chapter's own correction note is confirmed without its
unformalized Mazur input.

**Does not settle:** the exact rank (this is `≥ 1`, not `= 1`); any upper
bound (that needs full descent / Šafarevič–Tate); and anything whatsoever
about `L(E,s)` — mathlib has no elliptic-curve L-function at this pin, so
`ord_{s=1} L(E,s)` is not even statable, and **no part of BSD is claimed**.
The chapter's `L(E,1) = 0.8251329… ≠ 0` remains unreconciled with this
rank bound and is an authorial item: analytic rank 0 would force algebraic
rank 0, which this theorem now refutes.

No sorry, native_decide, axiom, Prop := True. autoImplicit off. Additive.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-15.
-/

import PF.Ch24CurveARankGeOne_2026_10_15
import PF.NaiveHeightQ_r130
import PF.DuplicationHeightBound37a1_r133
import Mathlib.Tactic.NormNum.GCD

set_option autoImplicit false

namespace PrincipiaTractalis
namespace Ch24CurveANonTorsion20261015

open WeierstrassCurve WeierstrassCurve.Affine
open PrincipiaTractalis.NaiveHeightQ
open PrincipiaTractalis.MordellWeilRankLowerBound
open PrincipiaTractalis.Ch24CurveARankGeOne20261015

noncomputable section

/-! ## §1 — the homogenised duplication pair and its Bézout identities -/

/-- Homogeneous numerator of the duplication map: `F a b = a⁴ + 16ab³`. -/
def Fform (a b : ℤ) : ℤ := a ^ 4 + 16 * a * b ^ 3

/-- Homogeneous denominator of the duplication map: `D a b = 4a³b − 8b⁴`. -/
def Dform (a b : ℤ) : ℤ := 4 * a ^ 3 * b - 8 * b ^ 4

/-- **Bézout, `a`-side:** `(144a³ − 256b³)·F + (−512ab²)·D = 144·a⁷`. -/
theorem bezout_a (a b : ℤ) :
    (144 * a ^ 3 - 256 * b ^ 3) * Fform a b + (-512 * a * b ^ 2) * Dform a b
      = 144 * a ^ 7 := by
  unfold Fform Dform; ring

/-- **Bézout, `b`-side:** `(4a²b)·F − (a³ + 18b³)·D = 144·b⁷`. -/
theorem bezout_b (a b : ℤ) :
    (4 * a ^ 2 * b) * Fform a b + (-(a ^ 3 + 18 * b ^ 3)) * Dform a b
      = 144 * b ^ 7 := by
  unfold Fform Dform; ring

/-! ## §2 — `gcd(F, D) ∣ 144` -/

/-- **The common factor is bounded:** for coprime `a, b`, `gcd(F,D) ∣ 144`. -/
theorem gcd_dvd_144 {a b : ℤ} (h : IsCoprime a b) :
    (Int.gcd (Fform a b) (Dform a b) : ℤ) ∣ 144 := by
  have hdF := Int.gcd_dvd_left (Fform a b) (Dform a b)
  have hdD := Int.gcd_dvd_right (Fform a b) (Dform a b)
  have ha7 : (Int.gcd (Fform a b) (Dform a b) : ℤ) ∣ 144 * a ^ 7 := by
    rw [← bezout_a a b]
    exact dvd_add (hdF.mul_left _) (hdD.mul_left _)
  have hb7 : (Int.gcd (Fform a b) (Dform a b) : ℤ) ∣ 144 * b ^ 7 := by
    rw [← bezout_b a b]
    exact dvd_add (hdF.mul_left _) (hdD.mul_left _)
  have h7 : IsCoprime (a ^ 7) (b ^ 7) := h.pow
  obtain ⟨u, v, huv⟩ := h7
  have key : (144 : ℤ) = u * (144 * a ^ 7) + v * (144 * b ^ 7) := by
    linear_combination (-144 : ℤ) * huv
  rw [key]
  exact dvd_add (ha7.mul_left u) (hb7.mul_left v)

/-- `gcd_dvd_144` in `ℕ`-form. -/
theorem gcd_dvd_144_nat {a b : ℤ} (h : IsCoprime a b) :
    Int.gcd (Fform a b) (Dform a b) ∣ 144 := by
  exact_mod_cast gcd_dvd_144 h

/-! ## §3 — the size lower bound `144·H⁷ ≤ 912·H³·max |F| |D|` -/

/-- Generic cofactor estimate: a `ℤ`-combination of `F` and `D` with cofactors
bounded by `p·H` and `q·H` has size at most `(p+q)·H·M`. -/
private theorem bound_combo {P Q Fv Dv : ℤ} {H M p q : ℕ}
    (hP : P.natAbs ≤ p * H) (hQ : Q.natAbs ≤ q * H)
    (hF : Fv.natAbs ≤ M) (hD : Dv.natAbs ≤ M) :
    (P * Fv + Q * Dv).natAbs ≤ (p + q) * H * M := by
  calc (P * Fv + Q * Dv).natAbs
      ≤ (P * Fv).natAbs + (Q * Dv).natAbs := Int.natAbs_add_le _ _
    _ = P.natAbs * Fv.natAbs + Q.natAbs * Dv.natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_mul]
    _ ≤ p * H * M + q * H * M :=
        Nat.add_le_add (Nat.mul_le_mul hP hF) (Nat.mul_le_mul hQ hD)
    _ = (p + q) * H * M := by ring

/-- `|c·a³ ± d·b³| ≤ (c+d)·H³`. -/
private theorem cube_combo_bound (c d : ℕ) (a b : ℤ) :
    ((c : ℤ) * a ^ 3 - (d : ℤ) * b ^ 3).natAbs
      ≤ (c + d) * (max a.natAbs b.natAbs) ^ 3 := by
  have ha : a.natAbs ^ 3 ≤ (max a.natAbs b.natAbs) ^ 3 :=
    Nat.pow_le_pow_left (le_max_left _ _) 3
  have hb : b.natAbs ^ 3 ≤ (max a.natAbs b.natAbs) ^ 3 :=
    Nat.pow_le_pow_left (le_max_right _ _) 3
  calc ((c : ℤ) * a ^ 3 - (d : ℤ) * b ^ 3).natAbs
      ≤ ((c : ℤ) * a ^ 3).natAbs + ((d : ℤ) * b ^ 3).natAbs :=
        Int.natAbs_sub_le _ _
    _ = c * a.natAbs ^ 3 + d * b.natAbs ^ 3 := by
        rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow]
        simp
    _ ≤ c * (max a.natAbs b.natAbs) ^ 3 + d * (max a.natAbs b.natAbs) ^ 3 :=
        Nat.add_le_add (Nat.mul_le_mul_left _ ha) (Nat.mul_le_mul_left _ hb)
    _ = (c + d) * (max a.natAbs b.natAbs) ^ 3 := by ring

/-- `|512·a·b²| ≤ 512·H³`. -/
private theorem mixed_bound (a b : ℤ) :
    (-512 * a * b ^ 2).natAbs ≤ 512 * (max a.natAbs b.natAbs) ^ 3 := by
  have ha : a.natAbs ≤ max a.natAbs b.natAbs := le_max_left _ _
  have hb : b.natAbs ≤ max a.natAbs b.natAbs := le_max_right _ _
  have h : (-512 * a * b ^ 2).natAbs = 512 * (a.natAbs * b.natAbs ^ 2) := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow]
    simp [mul_assoc]
  rw [h]
  have : a.natAbs * b.natAbs ^ 2
      ≤ (max a.natAbs b.natAbs) * (max a.natAbs b.natAbs) ^ 2 :=
    Nat.mul_le_mul ha (Nat.pow_le_pow_left hb 2)
  calc 512 * (a.natAbs * b.natAbs ^ 2)
      ≤ 512 * ((max a.natAbs b.natAbs) * (max a.natAbs b.natAbs) ^ 2) :=
        Nat.mul_le_mul_left _ this
    _ = 512 * (max a.natAbs b.natAbs) ^ 3 := by ring

/-- `|4·a²·b| ≤ 4·H³`. -/
private theorem mixed_bound_b (a b : ℤ) :
    (4 * a ^ 2 * b).natAbs ≤ 4 * (max a.natAbs b.natAbs) ^ 3 := by
  have ha : a.natAbs ≤ max a.natAbs b.natAbs := le_max_left _ _
  have hb : b.natAbs ≤ max a.natAbs b.natAbs := le_max_right _ _
  have h : (4 * a ^ 2 * b).natAbs = 4 * (a.natAbs ^ 2 * b.natAbs) := by
    rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow]
    simp [mul_assoc]
  rw [h]
  have : a.natAbs ^ 2 * b.natAbs
      ≤ (max a.natAbs b.natAbs) ^ 2 * (max a.natAbs b.natAbs) :=
    Nat.mul_le_mul (Nat.pow_le_pow_left ha 2) hb
  calc 4 * (a.natAbs ^ 2 * b.natAbs)
      ≤ 4 * ((max a.natAbs b.natAbs) ^ 2 * (max a.natAbs b.natAbs)) :=
        Nat.mul_le_mul_left _ this
    _ = 4 * (max a.natAbs b.natAbs) ^ 3 := by ring

/-- `|a³ + 18b³| ≤ 19·H³`. -/
private theorem neg_sum_bound (a b : ℤ) :
    (-(a ^ 3 + 18 * b ^ 3)).natAbs ≤ 19 * (max a.natAbs b.natAbs) ^ 3 := by
  have h : (-(a ^ 3 + 18 * b ^ 3)).natAbs
      = ((1 : ℤ) * a ^ 3 - (-18 : ℤ) * b ^ 3).natAbs := by
    rw [Int.natAbs_neg]; congr 1; ring
  rw [h]
  have := cube_combo_bound 1 18 a b
  calc ((1 : ℤ) * a ^ 3 - (-18 : ℤ) * b ^ 3).natAbs
      = ((1 : ℤ) * a ^ 3 - ((18 : ℕ) : ℤ) * (-b) ^ 3).natAbs := by
        congr 1; push_cast; ring
    _ ≤ (1 + 18) * (max a.natAbs (-b).natAbs) ^ 3 := cube_combo_bound 1 18 a (-b)
    _ = 19 * (max a.natAbs b.natAbs) ^ 3 := by rw [Int.natAbs_neg]

/-- **The size lower bound.** `144·H⁷ ≤ 912·H³·max |F| |D|`. -/
theorem size_bound (a b : ℤ) :
    144 * (max a.natAbs b.natAbs) ^ 7
      ≤ 912 * (max a.natAbs b.natAbs) ^ 3
          * max (Fform a b).natAbs (Dform a b).natAbs := by
  set H := max a.natAbs b.natAbs with hH
  set M := max (Fform a b).natAbs (Dform a b).natAbs with hM
  have hFM : (Fform a b).natAbs ≤ M := le_max_left _ _
  have hDM : (Dform a b).natAbs ≤ M := le_max_right _ _
  -- the a-side
  have hA : 144 * a.natAbs ^ 7 ≤ 912 * H ^ 3 * M := by
    have hcof1 : (144 * a ^ 3 - 256 * b ^ 3).natAbs ≤ 400 * H ^ 3 := by
      have := cube_combo_bound 144 256 a b
      simpa [hH] using this
    have hcof2 : (-512 * a * b ^ 2).natAbs ≤ 512 * H ^ 3 := by
      simpa [hH] using mixed_bound a b
    have hb := bound_combo (p := 400) (q := 512) (H := H ^ 3) (M := M)
      hcof1 hcof2 hFM hDM
    rw [bezout_a a b] at hb
    have h144 : (144 * a ^ 7).natAbs = 144 * a.natAbs ^ 7 := by
      rw [Int.natAbs_mul, Int.natAbs_pow]; simp
    rw [h144] at hb
    calc 144 * a.natAbs ^ 7 ≤ (400 + 512) * H ^ 3 * M := hb
      _ = 912 * H ^ 3 * M := by norm_num
  -- the b-side
  have hB : 144 * b.natAbs ^ 7 ≤ 912 * H ^ 3 * M := by
    have hcof1 : (4 * a ^ 2 * b).natAbs ≤ 4 * H ^ 3 := by
      simpa [hH] using mixed_bound_b a b
    have hcof2 : (-(a ^ 3 + 18 * b ^ 3)).natAbs ≤ 19 * H ^ 3 := by
      simpa [hH] using neg_sum_bound a b
    have hb := bound_combo (p := 4) (q := 19) (H := H ^ 3) (M := M)
      hcof1 hcof2 hFM hDM
    rw [bezout_b a b] at hb
    have h144 : (144 * b ^ 7).natAbs = 144 * b.natAbs ^ 7 := by
      rw [Int.natAbs_mul, Int.natAbs_pow]; simp
    rw [h144] at hb
    calc 144 * b.natAbs ^ 7 ≤ (4 + 19) * H ^ 3 * M := hb
      _ ≤ 912 * H ^ 3 * M := by
          refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ?_)
          norm_num
  -- combine: H is one of |a|, |b|
  rcases max_cases a.natAbs b.natAbs with ⟨he, _⟩ | ⟨he, _⟩
  · have h7 : H ^ 7 = a.natAbs ^ 7 := by simp only [hH, he]
    rw [h7]; exact hA
  · have h7 : H ^ 7 = b.natAbs ^ 7 := by simp only [hH, he]
    rw [h7]; exact hB

/-! ## §4 — descent to the reduced height bound `H⁴ ≤ 912 · H(F/D)` -/

/-- Splitting a `max` of absolute values by a common divisor. -/
private theorem max_natAbs_split {x y : ℤ} {n : ℕ}
    (hx : (n : ℤ) ∣ x) (hy : (n : ℤ) ∣ y) :
    max x.natAbs y.natAbs
      = max ((x / (n : ℤ)).natAbs) ((y / (n : ℤ)).natAbs) * n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, zero_dvd_iff] at hx hy
    simp [hx, hy]
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨kx, hkx⟩ := hx
  obtain ⟨ky, hky⟩ := hy
  have ex : (x / (n : ℤ)).natAbs * n = x.natAbs := by
    subst hkx
    rw [Int.mul_ediv_cancel_left _ hn0, Int.natAbs_mul, Int.natAbs_natCast]
    ring
  have ey : (y / (n : ℤ)).natAbs * n = y.natAbs := by
    subst hky
    rw [Int.mul_ediv_cancel_left _ hn0, Int.natAbs_mul, Int.natAbs_natCast]
    ring
  rw [← ex, ← ey]
  rcases le_total (x / (n : ℤ)).natAbs (y / (n : ℤ)).natAbs with hle | hle
  · rw [max_eq_right hle, max_eq_right (Nat.mul_le_mul hle (le_refl n))]
  · rw [max_eq_left hle, max_eq_left (Nat.mul_le_mul hle (le_refl n))]

/-- Pure-`ℕ` descent: from `144·H⁷ ≤ 912·H³·(M·d)` with `d ≤ 144` and
`1 ≤ H`, cancel `H³` and then `144`. -/
private theorem descend {H M d : ℕ} (hd : d ≤ 144) (hH : 1 ≤ H)
    (hkey : 144 * H ^ 7 ≤ 912 * H ^ 3 * (M * d)) : H ^ 4 ≤ 912 * M := by
  have hH0 : 0 < H := hH
  have h2 : (144 * H ^ 4) * H ^ 3 ≤ (144 * (912 * M)) * H ^ 3 := by
    calc (144 * H ^ 4) * H ^ 3 = 144 * H ^ 7 := by ring
      _ ≤ 912 * H ^ 3 * (M * d) := hkey
      _ ≤ 912 * H ^ 3 * (M * 144) := Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hd)
      _ = (144 * (912 * M)) * H ^ 3 := by ring
  have h3 := Nat.le_of_mul_le_mul_right h2 (pow_pos hH0 3)
  exact Nat.le_of_mul_le_mul_left h3 (by norm_num : 0 < 144)

/-- **The reduced height bound.** `H⁴ ≤ 912 · max |F/g| |D/g|`. -/
theorem reduced_height_bound {a b : ℤ} (h : IsCoprime a b) (hb : b ≠ 0) :
    (max a.natAbs b.natAbs) ^ 4
      ≤ 912 *
          max ((Fform a b / (Int.gcd (Fform a b) (Dform a b) : ℤ)).natAbs)
              ((Dform a b / (Int.gcd (Fform a b) (Dform a b) : ℤ)).natAbs) := by
  have hd144 : Int.gcd (Fform a b) (Dform a b) ≤ 144 :=
    Nat.le_of_dvd (by norm_num) (gcd_dvd_144_nat h)
  have hH1 : 1 ≤ max a.natAbs b.natAbs :=
    le_trans (Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hb))
      (le_max_right _ _)
  have hsplit :=
    max_natAbs_split (n := Int.gcd (Fform a b) (Dform a b))
      (Int.gcd_dvd_left _ _) (Int.gcd_dvd_right _ _)
  have key := size_bound a b
  rw [hsplit] at key
  exact descend hd144 hH1 key

/-! ## §5 — the duplication height inequality over ℚ -/

private theorem Fform_cast (a b : ℤ) (hb : (b : ℚ) ≠ 0) :
    ((Fform a b : ℤ) : ℚ) = (b : ℚ) ^ 4 * f ((a : ℚ) / (b : ℚ)) := by
  simp only [Fform, f]
  push_cast
  field_simp

private theorem Dform_cast (a b : ℤ) (hb : (b : ℚ) ≠ 0) :
    ((Dform a b : ℤ) : ℚ) = (b : ℚ) ^ 4 * g ((a : ℚ) / (b : ℚ)) := by
  simp only [Dform, g]
  push_cast
  field_simp

/-- **The duplication height inequality for curve A.** For every rational `x`
(no on-curve hypothesis — `g` never vanishes on ℚ):
`H(x)⁴ ≤ 912 · H(f x / g x)`. -/
theorem duplication_height_bound (x : ℚ) :
    naiveHeight x ^ 4 ≤ 912 * naiveHeight (f x / g x) := by
  have hb : ((x.den : ℤ)) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have hbQ : (((x.den : ℤ)) : ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have hcop : IsCoprime x.num ((x.den : ℤ)) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd, Int.natAbs_natCast] using x.reduced
  have hx : x = (x.num : ℚ) / (((x.den : ℤ)) : ℚ) := by
    rw [Int.cast_natCast]
    exact (Rat.num_div_den x).symm
  have hfval : ((Fform x.num (x.den : ℤ) : ℤ) : ℚ)
      = (((x.den : ℤ)) : ℚ) ^ 4 * f x := by
    have h := Fform_cast x.num (x.den : ℤ) hbQ
    rw [← hx] at h
    exact h
  have hDval : ((Dform x.num (x.den : ℤ) : ℤ) : ℚ)
      = (((x.den : ℤ)) : ℚ) ^ 4 * g x := by
    have h := Dform_cast x.num (x.den : ℤ) hbQ
    rw [← hx] at h
    exact h
  have hgx : g x ≠ 0 := g_ne_zero x
  have hD : Dform x.num (x.den : ℤ) ≠ 0 := by
    intro h0
    apply mul_ne_zero (pow_ne_zero 4 hbQ) hgx
    rw [← hDval, h0, Int.cast_zero]
  have hfg : f x / g x
      = ((Fform x.num (x.den : ℤ) : ℤ) : ℚ)
          / ((Dform x.num (x.den : ℤ) : ℤ) : ℚ) := by
    rw [hfval, hDval, mul_div_mul_left _ _ (pow_ne_zero 4 hbQ)]
  have hHx : max x.num.natAbs ((x.den : ℤ)).natAbs = naiveHeight x := by
    simp only [naiveHeight, Int.natAbs_natCast]
  calc naiveHeight x ^ 4
      = (max x.num.natAbs ((x.den : ℤ)).natAbs) ^ 4 := by rw [hHx]
    _ ≤ 912 *
          max ((Fform x.num (x.den : ℤ)
                  / (Int.gcd (Fform x.num (x.den : ℤ))
                       (Dform x.num (x.den : ℤ)) : ℤ)).natAbs)
              ((Dform x.num (x.den : ℤ)
                  / (Int.gcd (Fform x.num (x.den : ℤ))
                       (Dform x.num (x.den : ℤ)) : ℤ)).natAbs) :=
        reduced_height_bound hcop hb
    _ = 912 * naiveHeight
          ((Fform x.num (x.den : ℤ) : ℚ) / (Dform x.num (x.den : ℤ) : ℚ)) := by
        rw [DuplicationHeightBound37a1.naiveHeight_div_int
          (Fform x.num (x.den : ℤ)) (Dform x.num (x.den : ℤ)) hD]
    _ = 912 * naiveHeight (f x / g x) := by rw [← hfg]

/-! ## §6 — the doubling chain -/

/-- Duplication height step on the curve. -/
theorem dbl_height {x y : ℚ} (h : curveA.toAffine.Nonsingular x y) :
    ∃ (x' y' : ℚ) (h' : curveA.toAffine.Nonsingular x' y'),
      Point.some h + Point.some h = Point.some h' ∧
        naiveHeight x ^ 4 ≤ 912 * naiveHeight x' := by
  obtain ⟨x', y', h', hadd, hx'⟩ := dbl_x h
  refine ⟨x', y', h', hadd, ?_⟩
  rw [hx']
  exact duplication_height_bound x

/-- The doubling chain starting at `(3,5)`. -/
def chain : ℕ → Σ' (x y : ℚ), curveA.toAffine.Nonsingular x y :=
  Nat.rec (motive := fun _ => Σ' (x y : ℚ), curveA.toAffine.Nonsingular x y)
    ⟨3, 5, P_A_nonsingular⟩
    fun _ c =>
      ⟨(dbl_height c.2.2).choose,
       (dbl_height c.2.2).choose_spec.choose,
       (dbl_height c.2.2).choose_spec.choose_spec.choose⟩

/-- The `x`-coordinate along the chain. -/
def xs (n : ℕ) : ℚ := (chain n).1

/-- The chain as points of `curveA(ℚ)`. -/
def pts (n : ℕ) : curveA.toAffine.Point := Point.some (chain n).2.2

@[simp] lemma xs_zero : xs 0 = 3 := rfl

lemma pts_zero : pts 0 = P_A := rfl

lemma pts_succ (n : ℕ) : pts (n + 1) = pts n + pts n :=
  ((dbl_height (chain n).2.2).choose_spec.choose_spec.choose_spec.1).symm

lemma height_step (n : ℕ) :
    naiveHeight (xs n) ^ 4 ≤ 912 * naiveHeight (xs (n + 1)) :=
  (dbl_height (chain n).2.2).choose_spec.choose_spec.choose_spec.2

lemma pts_eq_two_pow_smul (n : ℕ) : pts n = ((2 : ℤ) ^ n) • P_A := by
  induction n with
  | zero => rw [pow_zero, one_zsmul, pts_zero]
  | succ k ih =>
      have h2 : ((2 : ℤ) ^ (k + 1)) = 2 ^ k + 2 ^ k := by ring
      rw [pts_succ, ih, h2, add_zsmul]

lemma xs_succ (n : ℕ) : xs (n + 1) = f (xs n) / g (xs n) := by
  obtain ⟨x', y', h', hadd, hx⟩ := dbl_x (chain n).2.2
  have hpt : Point.some (chain (n + 1)).2.2 = Point.some h' :=
    (pts_succ n).trans hadd
  have hxeq : (chain (n + 1)).1 = x' := (Point.some.inj hpt).left
  exact hxeq.trans hx

/-! ## §7 — the orbit clears the threshold `κ = 912` -/

/-- `x(2P) = 129/100`. -/
lemma xs_one : xs 1 = 129 / 100 := by
  rw [xs_succ, xs_zero, f, g]; norm_num

/-- `x(4P) = 2340922881/58675600`. -/
lemma xs_two : xs 2 = 2340922881 / 58675600 := by
  rw [xs_succ, xs_one, f, g]; norm_num

lemma naiveHeight_xs_two : naiveHeight (xs 2) = 2340922881 := by
  have h2 : xs 2 = ((2340922881 : ℤ) : ℚ) / ((58675600 : ℤ) : ℚ) := by
    rw [xs_two]; norm_num
  have hg : Int.gcd 2340922881 58675600 = 1 := by norm_num
  rw [h2, DuplicationHeightBound37a1.naiveHeight_div_int
    (2340922881 : ℤ) (58675600 : ℤ) (by norm_num), hg]
  norm_num

/-- The threshold check: `x(4P)` clears `κ = 912`. -/
lemma threshold : 912 < naiveHeight (xs 2) := by
  rw [naiveHeight_xs_two]; norm_num

/-! ## §8 — infinitely many `x`-coordinates -/

/-- From `4P` on, the chain's `x`-range is infinite. -/
theorem xs_shifted_infinite : (Set.range fun n => xs (n + 2)).Infinite :=
  infinite_of_duplication_step (κ := 912) (fun n => xs (n + 2))
    (by norm_num) (fun n => height_step (n + 2)) threshold

/-! ## §9 — ★ non-torsion, and the UNCONDITIONAL rank ★ -/

/-- The `x`-coordinate projection (`0` at the identity). -/
def X : curveA.toAffine.Point → ℚ
  | .zero => 0
  | @Point.some _ _ _ x _ _ => x

lemma X_pts (n : ℕ) : X (pts n) = xs n := rfl

/-- **`P_A = (3,5)` has infinite order on curve A.** A torsion point has
finite `zmultiples`, whose `X`-image would be finite — but it contains the
infinite range of §8. -/
theorem P_A_nonTorsion : ¬ IsOfFinAddOrder P_A := by
  intro hfin
  have hfinite := hfin.finite_zmultiples
  have hsub : (Set.range fun n => xs (n + 2))
      ⊆ X '' (AddSubgroup.zmultiples P_A : Set _) := by
    rintro q ⟨n, rfl⟩
    refine ⟨pts (n + 2), ?_, X_pts (n + 2)⟩
    exact AddSubgroup.mem_zmultiples_iff.mpr
      ⟨(2 : ℤ) ^ (n + 2), (pts_eq_two_pow_smul (n + 2)).symm⟩
  exact xs_shifted_infinite ((hfinite.image X).subset hsub)

/-- The r129 certificate, discharged. -/
theorem P_A_certificate : NonTorsionCertificate curveA.toAffine P_A :=
  P_A_nonTorsion

/-- **★★★★★ `1 ≤ Module.rank ℤ curveA.toAffine.Point` — UNCONDITIONAL ★★★★★**

The Mordell–Weil rank of `y² = x³ − 2` is at least 1. No hypotheses, no
Mazur, no Nagell–Lutz. This refutes `ch24_birch_swinnerton_dyer.tex:594`'s
printed `rank E(ℚ) = 0 (proven)`. -/
theorem curveA_rank_ge_one : 1 ≤ Module.rank ℤ curveA.toAffine.Point :=
  mordellWeil_rank_ge_one curveA.toAffine P_A P_A_nonTorsion

end

/-! ## §Axiom check -/

#print axioms bezout_a
#print axioms bezout_b
#print axioms gcd_dvd_144
#print axioms size_bound
#print axioms reduced_height_bound
#print axioms duplication_height_bound
#print axioms xs_one
#print axioms xs_two
#print axioms naiveHeight_xs_two
#print axioms threshold
#print axioms xs_shifted_infinite
#print axioms P_A_nonTorsion
#print axioms P_A_certificate
#print axioms curveA_rank_ge_one

end Ch24CurveANonTorsion20261015
end PrincipiaTractalis
