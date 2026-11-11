/-
# PF.E141a1RankOneCapstone_2026_11_11 — the rank bound for 141a1

The tail of `PF/E141a1RankOne_2026_11_11.lean`: from the per-curve facts
proved there (no rational 2-torsion, `Ψ ≠ 0` at every rational, the
b-invariants, the discriminant) to

  `1 ≤ Module.rank ℤ E_141a1(ℚ)`.

**Delta from the earlier capstones.**  E_141a1 has trivial torsion, so
the r200 wrapper `X_dbl_of_ne_zero` + `smul_ne_zero_of_two_torsion_free`
apply directly — same pattern as 91a1 and 131a1.  The base point is
not at the origin (unlike 91a1, 131a1), so `P141_nonsingular` goes via
`equation_iff_nonsingular_of_Δ_ne_zero` + a `norm_num` equation check.

**The base point.**  `P141 = (−3, 4)`, LMFDB's rank-1 generator of
E_141a1(ℚ).

**The orbit.** `x(2ⁿ P141) : −3 → 6 → 3 → 42 → 38931/3721 →
3827889230143098/1190145743283121`, heights
`3, 6, 3, 42, 38931, 3827889230143098`.  CL(4, −24, 9, −135) =
460,689,196,788; the threshold bites at `n = 5` — two steps later than
the 91a1/102a1 capstones (shift 4) and three later than 131a1 (shift 3),
because the orbit heights grow more slowly here.

**κ is never transcribed.** `kap` is defined as
`(CL 4 (-24) 9 (-135)).toNat` and `norm_num` computes it; a wrong
hand-copied value cannot sit here undetected.

HONEST SCOPE.  A LOWER bound on the rank of one curve.  It does not
compute the exact rank, says nothing about `L(E, s)`, and proves no part
of BSD.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-11.
-/

import PF.E141a1RankOne_2026_11_11
import PF.DuplicationFormula_r178
import PF.DuplicationHeightBound37a1_r133
import PF.NonTorsionFromOrbit_2026_10_21
import Mathlib.Tactic.NormNum.GCD

namespace PrincipiaTractalis
namespace E141a1RankOneCapstone20261111

open WeierstrassCurve WeierstrassCurve.Affine
open PrincipiaTractalis.BSD_HeegnerRank1ProofE141a1
open PrincipiaTractalis.E141a1RankOne20261111
open PrincipiaTractalis.NaiveHeightQ
open PrincipiaTractalis.CanonicalHeightGeneric
open PrincipiaTractalis.DuplicationBezout
open PrincipiaTractalis.DuplicationSize
open PrincipiaTractalis.DuplicationHeight
open PrincipiaTractalis.DuplicationFormula
open PrincipiaTractalis.PointParallelogramUniversal
open PrincipiaTractalis.CanheightParallelogramUniversal

/-! ## §1 — the base point `P141 = (−3, 4)` -/

/-- `(−3, 4)` is a nonsingular rational point of 141a1.  Since the
discriminant is nonzero, `Equation ↔ Nonsingular`, and the equation at
`(−3, 4)` is `16 + 4 = 20 = −27 + 9 + 36 + 2`. -/
theorem P141_nonsingular : E_141a1.toAffine.Nonsingular (-3) 4 := by
  have hΔ : E_141a1.toAffine.Δ ≠ 0 := E_141a1_Δ_ne_zero
  have hEq : E_141a1.toAffine.Equation (-3) 4 := by
    rw [WeierstrassCurve.Affine.equation_iff]
    unfold E_141a1
    norm_num
  exact (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp hEq

/-- **The base point** `P141 = (−3, 4) ∈ E_141a1(ℚ)`. -/
noncomputable def P141 : E_141a1.toAffine.Point := Point.some P141_nonsingular

theorem P141_ne_zero : P141 ≠ 0 := some_ne_zero _

theorem X_P141 : X P141 = -3 := rfl

/-! ## §2 — `dblQ` on 141a1, dehomogenised -/

/-- Duplication numerator on 141a1: `x⁴ + 24x² − 18x + 135`. -/
def f141 (x : ℚ) : ℚ := x ^ 4 + 24 * x ^ 2 - 18 * x + 135

/-- Duplication denominator on 141a1: `4x³ + 4x² − 48x + 9` — the
2-torsion cubic. -/
def g141 (x : ℚ) : ℚ := 4 * x ^ 3 + 4 * x ^ 2 - 48 * x + 9

/-- The denominator never vanishes on ℚ.  This is part 1's
`no_rat_solution`, i.e. exactly the absence of rational 2-torsion. -/
theorem g141_ne_zero (x : ℚ) : g141 x ≠ 0 := by
  simpa [g141] using no_rat_solution x

theorem phiX_eq_f141 (x : ℚ) : phiX (E_141a1.toAffine) x = f141 x := by
  simp only [phiX, f141, b₄_eq, b₆_eq, b₈_eq]
  push_cast
  ring

theorem psiX_eq_g141 (x : ℚ) : psiX (E_141a1.toAffine) x = g141 x := by
  simp only [psiX, g141, b₂_eq, b₄_eq, b₆_eq]
  push_cast
  ring

/-- **The duplication map on 141a1, as a rational function.** -/
theorem dblQ_eq_fg141 (x : ℚ) :
    dblQ 4 (-24) 9 (-135) x = f141 x / g141 x := by
  rw [dblQ_eq_phiX_div_psiX b₂_eq.symm b₄_eq.symm b₆_eq.symm b₈_eq.symm x,
      phiX_eq_f141, psiX_eq_g141]

/-! ## §3 — the arithmetic chain and its first six values -/

/-- The x-coordinates of the doubling orbit of `P141`, as pure arithmetic. -/
def xs : ℕ → ℚ
  | 0 => -3
  | n + 1 => dblQ 4 (-24) 9 (-135) (xs n)

theorem xs_zero : xs 0 = -3 := rfl

theorem xs_succ (n : ℕ) : xs (n + 1) = dblQ 4 (-24) 9 (-135) (xs n) := rfl

theorem xs_one : xs 1 = 6 := by
  show xs (0 + 1) = 6
  rw [xs_succ, xs_zero, dblQ_eq_fg141]
  norm_num [f141, g141]

theorem xs_two : xs 2 = 3 := by
  show xs (1 + 1) = 3
  rw [xs_succ, xs_one, dblQ_eq_fg141]
  norm_num [f141, g141]

theorem xs_three : xs 3 = 42 := by
  show xs (2 + 1) = 42
  rw [xs_succ, xs_two, dblQ_eq_fg141]
  norm_num [f141, g141]

theorem xs_four : xs 4 = 38931 / 3721 := by
  show xs (3 + 1) = 38931 / 3721
  rw [xs_succ, xs_three, dblQ_eq_fg141]
  norm_num [f141, g141]

/-- `x(32 P141) = 3827889230143098 / 1190145743283121`. -/
theorem xs_five :
    xs 5 = 3827889230143098 / 1190145743283121 := by
  show xs (4 + 1) = 3827889230143098 / 1190145743283121
  rw [xs_succ, xs_four, dblQ_eq_fg141]
  norm_num [f141, g141]

/-! ## §4 — the height step, straight from the universal layer -/

/-- The curve constant, **computed** rather than copied: r175's `CL` at
141a1's b-invariants.  Nothing downstream depends on its decimal value. -/
def kap : ℕ := (CL 4 (-24) 9 (-135)).toNat

theorem kap_cast : ((kap : ℤ)) = CL 4 (-24) 9 (-135) :=
  Int.toNat_of_nonneg (CL_nonneg 4 (-24) 9 (-135))

/-- **The quartic duplication step, for every element of the chain.** -/
theorem height_step (n : ℕ) :
    naiveHeight (xs n) ^ 4 ≤ kap * naiveHeight (xs (n + 1)) := by
  have h := nh_pow_le_of_disc_ne_zero (hrel := hrel141) (x := xs n)
    (hΨ := Psi_ne_zero_at (xs n)) hΔ141
  rw [← xs_succ n] at h
  have hgoal : ((naiveHeight (xs n) : ℤ)) ^ 4
      ≤ (kap : ℤ) * ((naiveHeight (xs (n + 1)) : ℤ)) := by
    rw [naiveHeight_eq_nh, naiveHeight_eq_nh, kap_cast]
    exact h
  exact_mod_cast hgoal

/-! ## §5 — the threshold -/

/-- `naiveHeight (x(32 P141)) = 3 827 889 230 143 098`; the fraction is
already reduced, certified by `norm_num`'s gcd extension. -/
theorem naiveHeight_xs_five :
    naiveHeight (xs 5) = 3827889230143098 := by
  have h5 : xs 5 =
      ((3827889230143098 : ℤ) : ℚ) / ((1190145743283121 : ℤ) : ℚ) := by
    rw [xs_five]; norm_num
  have hg : Int.gcd 3827889230143098 1190145743283121 = 1 := by norm_num
  rw [h5, DuplicationHeightBound37a1.naiveHeight_div_int 3827889230143098
    1190145743283121 (by norm_num), hg]
  norm_num

theorem kap_pos : 0 < kap := by
  show 0 < (CL 4 (-24) 9 (-135)).toNat
  norm_num [CL, SF1, SG1, SF2, SG2, cF10, cF11, cF12, cF13, cG10, cG11,
    cG12, cG13, cF20, cF21, cF22, cF23, cG20, cG21, cG22, cG23]

/-- **The threshold check**: the orbit clears the curve constant at `n = 5`. -/
theorem threshold : kap < naiveHeight (xs 5) := by
  rw [naiveHeight_xs_five]
  show (CL 4 (-24) 9 (-135)).toNat < 3827889230143098
  norm_num [CL, SF1, SG1, SF2, SG2, cF10, cF11, cF12, cF13, cG10, cG11,
    cG12, cG13, cF20, cF21, cF22, cF23, cG20, cG21, cG22, cG23]

/-! ## §6 — firing r130's driver -/

/-- **The chain from `32 P141` on takes infinitely many values.** -/
theorem xs_shifted_infinite : (Set.range fun n => xs (n + 5)).Infinite :=
  infinite_of_duplication_step (κ := kap) (fun n => xs (n + 5)) kap_pos
    (fun n => height_step (n + 5)) threshold

/-! ## §7 — transporting the chain onto the point group -/

/-- `X` intertwines doubling with `dblQ` all the way up the dyadic tower. -/
theorem X_two_pow_smul (n : ℕ) : X (((2 : ℤ) ^ n) • P141) = xs n := by
  induction n with
  | zero => simpa using X_P141
  | succ k ih =>
      have hk : ((2 : ℤ) ^ k) • P141 ≠ 0 :=
        smul_ne_zero_of_two_torsion_free h2tor P141_ne_zero k
      rw [two_pow_succ_zsmul,
          X_dbl_of_ne_zero b₂_eq b₄_eq b₆_eq b₈_eq h2tor _ hk, ih, xs_succ k]

/-- Bridge between r199's generic `X` and `NonTorsionFromOrbit`'s local
`X`.  Both are the same `match`, so they agree by `rfl` pointwise. -/
theorem X_bridge (R : E_141a1.toAffine.Point) :
    NonTorsionFromOrbit20261021.X R = X R := by
  cases R <;> rfl

theorem orbit_infinite :
    (Set.range fun n =>
      NonTorsionFromOrbit20261021.X (((2 : ℤ) ^ (n + 5)) • P141)).Infinite := by
  have hfun : (fun n : ℕ =>
      NonTorsionFromOrbit20261021.X (((2 : ℤ) ^ (n + 5)) • P141))
      = fun n : ℕ => xs (n + 5) := by
    funext n
    rw [X_bridge, X_two_pow_smul]
  rw [hfun]
  exact xs_shifted_infinite

/-! ## §8 — the capstones -/

/-- **`P141 = (−3, 4)` has infinite order in `E_141a1(ℚ)`.** -/
theorem P141_nonTorsion : ¬ IsOfFinAddOrder P141 :=
  NonTorsionFromOrbit20261021.nonTorsion_of_doubling_orbit_infinite P141 5
    orbit_infinite

/-- **THE FLAG — `rank E_141a1(ℚ) ≥ 1`.**  A lower bound, nothing more. -/
theorem E141a1_rank_ge_one : 1 ≤ Module.rank ℤ E_141a1.toAffine.Point :=
  NonTorsionFromOrbit20261021.rank_ge_one_of_doubling_orbit_infinite P141 5
    orbit_infinite

end E141a1RankOneCapstone20261111
end PrincipiaTractalis

/-! ## §Axiom check -/

#print axioms PrincipiaTractalis.E141a1RankOneCapstone20261111.P141_nonsingular
#print axioms PrincipiaTractalis.E141a1RankOneCapstone20261111.dblQ_eq_fg141
#print axioms PrincipiaTractalis.E141a1RankOneCapstone20261111.xs_five
#print axioms PrincipiaTractalis.E141a1RankOneCapstone20261111.height_step
#print axioms PrincipiaTractalis.E141a1RankOneCapstone20261111.naiveHeight_xs_five
#print axioms PrincipiaTractalis.E141a1RankOneCapstone20261111.threshold
#print axioms PrincipiaTractalis.E141a1RankOneCapstone20261111.xs_shifted_infinite
#print axioms PrincipiaTractalis.E141a1RankOneCapstone20261111.X_two_pow_smul
#print axioms PrincipiaTractalis.E141a1RankOneCapstone20261111.X_bridge
#print axioms PrincipiaTractalis.E141a1RankOneCapstone20261111.P141_nonTorsion
#print axioms PrincipiaTractalis.E141a1RankOneCapstone20261111.E141a1_rank_ge_one

-- The computed curve constant, for the record: kap = 460689196788.
#eval PrincipiaTractalis.E141a1RankOneCapstone20261111.kap
