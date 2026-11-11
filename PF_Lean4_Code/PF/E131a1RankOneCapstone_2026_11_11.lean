/-
# PF.E131a1RankOneCapstone_2026_11_11 — the rank bound for 131a1

The tail of `PF/E131a1RankOne_2026_11_11.lean`: from the per-curve facts
proved there (no rational 2-torsion, `Ψ ≠ 0` at every rational, the
b-invariants, the discriminant) to

  `1 ≤ Module.rank ℤ E_131a1(ℚ)`.

**Assembled, not transcribed.**  Every general step is an existing
universal layer; this file supplies only 131a1's own arithmetic.

| obligation | discharged by |
|---|---|
| no rational 2-torsion | `E131a1RankOne20261111.h2tor` (part 1) |
| `Ψ ≠ 0` at every rational `x` | `E131a1RankOne20261111.Psi_ne_zero_at` (part 1) |
| `dblQ` is the dehomogenised duplication map | r178 `dblQ_eq_phiX_div_psiX` |
| `H(x)⁴ ≤ CL · H(x(2P))` | r176 `nh_pow_le_of_disc_ne_zero` |
| `naiveHeight` ↔ `nh` | r199 `naiveHeight_eq_nh` |
| `X(R+R) = dblQ (X R)` | r200 `X_dbl_of_ne_zero` |
| `2ⁿ·R ≠ 0` | r200 `smul_ne_zero_of_two_torsion_free` |
| infinite height ⇒ infinite range | r130 `infinite_of_duplication_step` |
| infinite x-orbit ⇒ rank ≥ 1 | `NonTorsionFromOrbit_2026_10_21` + r129 |

**The base point.**  `P131 = (0, 0)`, LMFDB's rank-1 generator of
E_131a1(ℚ).  Torsion is trivial (prime conductor).

**The orbit.**  `x(2ⁿ P131) : 0 → 2 → 6/25 → 550046/697225`,
heights `1, 2, 25, 697225`.  CL(-4, 2, 1, -2) = 73,491, and the
threshold bites at `n = 3` — one step earlier than the 91a1/102a1
capstones, because the first orbit height already exceeds `κ`.

**κ is never transcribed.** `kap` is defined as `(CL (-4) 2 1 (-2)).toNat`
and `norm_num` computes it; a wrong hand-copied value cannot sit here
undetected.

HONEST SCOPE.  A LOWER bound on the rank of one curve.  It does not
compute the exact rank, says nothing about `L(E, s)`, and proves no part
of BSD.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-11.
-/

import PF.E131a1RankOne_2026_11_11
import PF.DuplicationFormula_r178
import PF.DuplicationHeightBound37a1_r133
import PF.NonTorsionFromOrbit_2026_10_21
import Mathlib.Tactic.NormNum.GCD

namespace PrincipiaTractalis
namespace E131a1RankOneCapstone20261111

open WeierstrassCurve WeierstrassCurve.Affine
open PrincipiaTractalis.BSD_HeegnerRank1ProofE131a1
open PrincipiaTractalis.E131a1RankOne20261111
open PrincipiaTractalis.NaiveHeightQ
open PrincipiaTractalis.CanonicalHeightGeneric
open PrincipiaTractalis.DuplicationBezout
open PrincipiaTractalis.DuplicationSize
open PrincipiaTractalis.DuplicationHeight
open PrincipiaTractalis.DuplicationFormula
open PrincipiaTractalis.PointParallelogramUniversal
open PrincipiaTractalis.CanheightParallelogramUniversal

/-! ## §1 — the base point `P131 = (0, 0)` -/

/-- `(0, 0)` is a nonsingular rational point of 131a1: the equation at
`(0, 0)` reads `0 = a₆ = 0`, and the `Y`-partial there is `a₃ = 1 ≠ 0`. -/
theorem P131_nonsingular : E_131a1.toAffine.Nonsingular 0 0 := by
  rw [Affine.nonsingular_zero]
  refine ⟨rfl, Or.inl ?_⟩
  show (1 : ℚ) ≠ 0
  norm_num

/-- **The base point** `P131 = (0, 0) ∈ E_131a1(ℚ)`. -/
noncomputable def P131 : E_131a1.toAffine.Point := Point.some P131_nonsingular

theorem P131_ne_zero : P131 ≠ 0 := some_ne_zero _

theorem X_P131 : X P131 = 0 := rfl

/-! ## §2 — `dblQ` on 131a1, dehomogenised

Instantiating the b-invariants `(-4, 2, 1, -2)` into r178's `phiX`/`psiX`
produces two concrete rational polynomials. -/

/-- Duplication numerator on 131a1: `x⁴ - 2x² - 2x + 2`. -/
def f131 (x : ℚ) : ℚ := x ^ 4 - 2 * x ^ 2 - 2 * x + 2

/-- Duplication denominator on 131a1: `4x³ - 4x² + 4x + 1` — the
2-torsion cubic. -/
def g131 (x : ℚ) : ℚ := 4 * x ^ 3 - 4 * x ^ 2 + 4 * x + 1

/-- The denominator never vanishes on ℚ.  This is part 1's
`no_rat_solution`, i.e. exactly the absence of rational 2-torsion. -/
theorem g131_ne_zero (x : ℚ) : g131 x ≠ 0 := by
  simpa [g131] using no_rat_solution x

theorem phiX_eq_f131 (x : ℚ) : phiX (E_131a1.toAffine) x = f131 x := by
  simp only [phiX, f131, b₄_eq, b₆_eq, b₈_eq]
  push_cast
  ring

theorem psiX_eq_g131 (x : ℚ) : psiX (E_131a1.toAffine) x = g131 x := by
  simp only [psiX, g131, b₂_eq, b₄_eq, b₆_eq]
  push_cast
  ring

/-- **The duplication map on 131a1, as a rational function.** -/
theorem dblQ_eq_fg131 (x : ℚ) :
    dblQ (-4) 2 1 (-2) x = f131 x / g131 x := by
  rw [dblQ_eq_phiX_div_psiX b₂_eq.symm b₄_eq.symm b₆_eq.symm b₈_eq.symm x,
      phiX_eq_f131, psiX_eq_g131]

/-! ## §3 — the arithmetic chain and its first four values -/

/-- The x-coordinates of the doubling orbit of `P131`, as pure arithmetic. -/
def xs : ℕ → ℚ
  | 0 => 0
  | n + 1 => dblQ (-4) 2 1 (-2) (xs n)

theorem xs_zero : xs 0 = 0 := rfl

theorem xs_succ (n : ℕ) : xs (n + 1) = dblQ (-4) 2 1 (-2) (xs n) := rfl

theorem xs_one : xs 1 = 2 := by
  show xs (0 + 1) = 2
  rw [xs_succ, xs_zero, dblQ_eq_fg131]
  norm_num [f131, g131]

theorem xs_two : xs 2 = 6 / 25 := by
  show xs (1 + 1) = 6 / 25
  rw [xs_succ, xs_one, dblQ_eq_fg131]
  norm_num [f131, g131]

/-- `x(8 P131) = 550046 / 697225`. -/
theorem xs_three : xs 3 = 550046 / 697225 := by
  show xs (2 + 1) = 550046 / 697225
  rw [xs_succ, xs_two, dblQ_eq_fg131]
  norm_num [f131, g131]

/-! ## §4 — the height step, straight from the universal layer -/

/-- The curve constant, **computed** rather than copied: r175's `CL` at
131a1's b-invariants.  Nothing downstream depends on its decimal value. -/
def kap : ℕ := (CL (-4) 2 1 (-2)).toNat

theorem kap_cast : ((kap : ℤ)) = CL (-4) 2 1 (-2) :=
  Int.toNat_of_nonneg (CL_nonneg (-4) 2 1 (-2))

/-- **The quartic duplication step, for every element of the chain.** -/
theorem height_step (n : ℕ) :
    naiveHeight (xs n) ^ 4 ≤ kap * naiveHeight (xs (n + 1)) := by
  have h := nh_pow_le_of_disc_ne_zero (hrel := hrel131) (x := xs n)
    (hΨ := Psi_ne_zero_at (xs n)) hΔ131
  rw [← xs_succ n] at h
  have hgoal : ((naiveHeight (xs n) : ℤ)) ^ 4
      ≤ (kap : ℤ) * ((naiveHeight (xs (n + 1)) : ℤ)) := by
    rw [naiveHeight_eq_nh, naiveHeight_eq_nh, kap_cast]
    exact h
  exact_mod_cast hgoal

/-! ## §5 — the threshold -/

/-- `naiveHeight (x(8 P131)) = 697 225`; the fraction is already reduced,
certified by `norm_num`'s gcd extension. -/
theorem naiveHeight_xs_three : naiveHeight (xs 3) = 697225 := by
  have h3 : xs 3 = ((550046 : ℤ) : ℚ) / ((697225 : ℤ) : ℚ) := by
    rw [xs_three]; norm_num
  have hg : Int.gcd 550046 697225 = 1 := by norm_num
  rw [h3, DuplicationHeightBound37a1.naiveHeight_div_int 550046 697225
    (by norm_num), hg]
  norm_num

theorem kap_pos : 0 < kap := by
  show 0 < (CL (-4) 2 1 (-2)).toNat
  norm_num [CL, SF1, SG1, SF2, SG2, cF10, cF11, cF12, cF13, cG10, cG11,
    cG12, cG13, cF20, cF21, cF22, cF23, cG20, cG21, cG22, cG23]

/-- **The threshold check**: the orbit clears the curve constant at `n = 3`. -/
theorem threshold : kap < naiveHeight (xs 3) := by
  rw [naiveHeight_xs_three]
  show (CL (-4) 2 1 (-2)).toNat < 697225
  norm_num [CL, SF1, SG1, SF2, SG2, cF10, cF11, cF12, cF13, cG10, cG11,
    cG12, cG13, cF20, cF21, cF22, cF23, cG20, cG21, cG22, cG23]

/-! ## §6 — firing r130's driver -/

/-- **The chain from `8 P131` on takes infinitely many values.** -/
theorem xs_shifted_infinite : (Set.range fun n => xs (n + 3)).Infinite :=
  infinite_of_duplication_step (κ := kap) (fun n => xs (n + 3)) kap_pos
    (fun n => height_step (n + 3)) threshold

/-! ## §7 — transporting the chain onto the point group -/

/-- `X` intertwines doubling with `dblQ` all the way up the dyadic tower,
so the geometric orbit and the arithmetic chain agree at every level. -/
theorem X_two_pow_smul (n : ℕ) : X (((2 : ℤ) ^ n) • P131) = xs n := by
  induction n with
  | zero => simpa using X_P131
  | succ k ih =>
      have hk : ((2 : ℤ) ^ k) • P131 ≠ 0 :=
        smul_ne_zero_of_two_torsion_free h2tor P131_ne_zero k
      rw [two_pow_succ_zsmul,
          X_dbl_of_ne_zero b₂_eq b₄_eq b₆_eq b₈_eq h2tor _ hk, ih, xs_succ k]

/-- The duplicate-`X` bridge. `NonTorsionFromOrbit_2026_10_21` defines
its own `X`, and the two definitions are the same `match`, so they agree
by `rfl` pointwise; this lemma is what lets the capstone below be stated
with the universal `X` while the driver consumes the duplicate. -/
theorem X_bridge (R : E_131a1.toAffine.Point) :
    NonTorsionFromOrbit20261021.X R = X R := by
  cases R <;> rfl

theorem orbit_infinite :
    (Set.range fun n =>
      NonTorsionFromOrbit20261021.X (((2 : ℤ) ^ (n + 3)) • P131)).Infinite := by
  have hfun : (fun n : ℕ =>
      NonTorsionFromOrbit20261021.X (((2 : ℤ) ^ (n + 3)) • P131))
      = fun n : ℕ => xs (n + 3) := by
    funext n
    rw [X_bridge, X_two_pow_smul]
  rw [hfun]
  exact xs_shifted_infinite

/-! ## §8 — the capstones -/

/-- **`P131 = (0,0)` has infinite order in `E_131a1(ℚ)`.** -/
theorem P131_nonTorsion : ¬ IsOfFinAddOrder P131 :=
  NonTorsionFromOrbit20261021.nonTorsion_of_doubling_orbit_infinite P131 3
    orbit_infinite

/-- **THE FLAG — `rank E_131a1(ℚ) ≥ 1`.**  A lower bound, nothing more. -/
theorem E131a1_rank_ge_one : 1 ≤ Module.rank ℤ E_131a1.toAffine.Point :=
  NonTorsionFromOrbit20261021.rank_ge_one_of_doubling_orbit_infinite P131 3
    orbit_infinite

end E131a1RankOneCapstone20261111
end PrincipiaTractalis

/-! ## §Axiom check -/

#print axioms PrincipiaTractalis.E131a1RankOneCapstone20261111.P131_nonsingular
#print axioms PrincipiaTractalis.E131a1RankOneCapstone20261111.dblQ_eq_fg131
#print axioms PrincipiaTractalis.E131a1RankOneCapstone20261111.xs_three
#print axioms PrincipiaTractalis.E131a1RankOneCapstone20261111.height_step
#print axioms PrincipiaTractalis.E131a1RankOneCapstone20261111.naiveHeight_xs_three
#print axioms PrincipiaTractalis.E131a1RankOneCapstone20261111.threshold
#print axioms PrincipiaTractalis.E131a1RankOneCapstone20261111.xs_shifted_infinite
#print axioms PrincipiaTractalis.E131a1RankOneCapstone20261111.X_two_pow_smul
#print axioms PrincipiaTractalis.E131a1RankOneCapstone20261111.X_bridge
#print axioms PrincipiaTractalis.E131a1RankOneCapstone20261111.P131_nonTorsion
#print axioms PrincipiaTractalis.E131a1RankOneCapstone20261111.E131a1_rank_ge_one

-- The computed curve constant, for the record: kap = 73491.
#eval PrincipiaTractalis.E131a1RankOneCapstone20261111.kap
