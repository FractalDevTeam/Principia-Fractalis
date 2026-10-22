/-
# PF.E91a1RankOne_2026_10_21 — part 1: curve facts and no rational 2-torsion

The per-curve obligations for feeding 91a1 into the universal layers
(r176 window, r179 fixed window, r199/r200 point-level machinery, r130 driver).
Everything else is supposed to come from those layers; this file holds only
what is genuinely specific to `y² + y = x³ + x`.

`E_91a1` and its discriminant already exist in
`PF/BSD_HeegnerRank1ProofE91a1.lean` (that file's *headline* is one of the
§0.4-flagged Prop-level mirrors with `True` hypotheses, but its curve
definition and `Δ = −91` computation are ordinary arithmetic and are reused
here rather than restated).

THE ONE REAL OBLIGATION is no rational 2-torsion. r200's universal layer takes
it as `h2tor : ∀ R ≠ 0, 2 • R ≠ 0` and supplies everything downstream
(`PsiX_ne_zero`, `X_dbl_of_ne_zero`, `heightWindow_universal`). For 91a1 a
2-torsion point needs `y = negY x y = −y − 1`, i.e. `y = −1/2`, and then the
curve equation forces `4x³ + 4x + 1 = 0`, which has no rational solution by a
two-line parity argument on `x.num` / `x.den`.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-21.
-/

import PF.BSD_HeegnerRank1ProofE91a1
import PF.PointParallelogramUniversal_r199
import PF.CanheightParallelogramUniversal_r200
import PF.NonTorsionFromOrbit_2026_10_21

namespace PrincipiaTractalis
namespace E91a1RankOne20261021

open WeierstrassCurve WeierstrassCurve.Affine
open PrincipiaTractalis.BSD_HeegnerRank1ProofE91a1
open PrincipiaTractalis.CanonicalHeightGeneric
open PrincipiaTractalis.DuplicationBezout
open PrincipiaTractalis.DuplicationSize
open PrincipiaTractalis.DuplicationHeight
open PrincipiaTractalis.DuplicationLogWindow
open PrincipiaTractalis.PointParallelogramUniversal
open PrincipiaTractalis.CanheightParallelogramUniversal
open PrincipiaTractalis.NaiveHeightQ

/-! ## §1 — the b-invariants, in the integer form the universal layers want -/

theorem b₂_eq : (E_91a1.toAffine).b₂ = ((0 : ℤ) : ℚ) := by
  simp [WeierstrassCurve.b₂, E_91a1]

theorem b₄_eq : (E_91a1.toAffine).b₄ = ((2 : ℤ) : ℚ) := by
  simp [WeierstrassCurve.b₄, E_91a1]

theorem b₆_eq : (E_91a1.toAffine).b₆ = ((1 : ℤ) : ℚ) := by
  simp [WeierstrassCurve.b₆, E_91a1]

theorem b₈_eq : (E_91a1.toAffine).b₈ = ((-1 : ℤ) : ℚ) := by
  simp [WeierstrassCurve.b₈, E_91a1]

/-! ## §2 — `4x³ + 4x + 1 = 0` has no rational solution -/

/-- The cubic that a rational 2-torsion point would have to solve, cleared of
denominators: `4p³ + 4pq² + q³ = 0` with `p`, `q` coprime and `q > 0`.

Parity kills it in three cases:
* `q` odd — then `4p³ + 4pq²` is even and `q³` is odd, so the sum is odd;
* `q` even and `p` even — contradicts coprimality;
* `q` even and `p` odd — write `q = 2m`; dividing by `2` gives
  `2p³ + 4pm² + 4m³ = 0`, so `p³` is even, so `p` is even. -/
theorem no_int_solution (p q : ℤ) (hcop : IsCoprime p q) :
    4 * p ^ 3 + 4 * p * q ^ 2 + q ^ 3 ≠ 0 := by
  intro heq
  rcases Int.even_or_odd q with hqe | hqo
  · -- q even: write q = m + m and divide the equation by 4
    obtain ⟨m, hm⟩ := hqe
    subst hm
    -- cannot divide by 4 in ℤ, so clear it the other way: prove 4 * (...) = 0
    -- and cancel the unit-free factor.
    have h4z : 4 * (p ^ 3 + 4 * (p * m ^ 2) + 2 * m ^ 3) = 0 := by
      linear_combination heq
    have hdiv : p ^ 3 + 4 * (p * m ^ 2) + 2 * m ^ 3 = 0 := by
      rcases mul_eq_zero.mp h4z with h | h
      · norm_num at h
      · exact h
    -- so p ^ 3 is even, hence p is even
    have hev3 : Even (p ^ 3) := ⟨-(2 * (p * m ^ 2) + m ^ 3), by linarith⟩
    have hevp : Even p := (Int.even_pow.mp hev3).1
    -- but then 2 divides both p and q, contradicting coprimality
    obtain ⟨k, hk⟩ := hevp
    have h2p : (2 : ℤ) ∣ p := ⟨k, by linarith⟩
    have h2q : (2 : ℤ) ∣ (m + m) := ⟨m, by ring⟩
    have hu : IsUnit (2 : ℤ) := hcop.isUnit_of_dvd' h2p h2q
    rw [Int.isUnit_iff] at hu
    omega
  · -- q odd: the left-hand side is odd, so it cannot be 0
    have hq3 : Odd (q ^ 3) := hqo.pow
    have h4 : Even (4 * p ^ 3 + 4 * p * q ^ 2) :=
      ⟨2 * p ^ 3 + 2 * p * q ^ 2, by ring⟩
    have hodd : Odd (4 * p ^ 3 + 4 * p * q ^ 2 + q ^ 3) := h4.add_odd hq3
    rw [heq] at hodd
    simpa using hodd


/-! ## §3 — no rational 2-torsion on 91a1 -/

/-- `4x³ + 4x + 1 = 0` has no rational solution: clear denominators and apply
the parity argument to `(x.num, x.den)`, which are coprime. -/
theorem no_rat_solution (x : ℚ) : 4 * x ^ 3 + 4 * x + 1 ≠ 0 := by
  intro h
  have hd : ((x.den : ℚ)) ≠ 0 := by
    exact_mod_cast Rat.den_ne_zero x
  -- the same step r178 uses: num = x * den, from num/den = x
  have hnum : (x.num : ℚ) = x * (x.den : ℚ) :=
    (div_eq_iff hd).mp (Rat.num_div_den x)
  have key : ((4 * x.num ^ 3 + 4 * x.num * (x.den : ℤ) ^ 2
      + (x.den : ℤ) ^ 3 : ℤ) : ℚ) = 0 := by
    push_cast
    rw [hnum]
    linear_combination ((x.den : ℚ)) ^ 3 * h
  exact no_int_solution x.num (x.den : ℤ) (isCoprime_num_den x)
    (by exact_mod_cast key)

/-- **91a1 has no rational 2-torsion, at the coordinate level.** A 2-torsion
point needs `y = negY x y = −y − 1`, i.e. `2y + 1 = 0`; substituting into
`y² + y = x³ + x` forces `4x³ + 4x + 1 = 0`. -/
theorem y_ne_negY {x y : ℚ} (h : (E_91a1.toAffine).Equation x y) :
    y ≠ (E_91a1.toAffine).negY x y := by
  intro hy
  rw [WeierstrassCurve.Affine.equation_iff] at h
  simp only [WeierstrassCurve.Affine.negY, E_91a1] at hy h
  -- hy : y = -y - 1  (a₁ = 0, a₃ = 1);  h : the curve equation
  exact no_rat_solution x (by linear_combination (-4) * h + (2 * y + 1) * hy)

/-- **`h2tor` in the ∀-form the universal layers take** (r200's hypothesis). -/
theorem h2tor : ∀ R : (E_91a1.toAffine).Point, R ≠ 0 → (2 : ℕ) • R ≠ 0 := by
  intro R hR
  obtain ⟨x, y, hns, rfl⟩ := exists_affine hR
  rw [two_nsmul]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne (y_ne_negY hns.left)]
  exact some_ne_zero _


/-! ## §4 — the curve-level constants the universal layers ask for -/

theorem hrel91 : 4 * (-1 : ℤ) = 0 * 1 - 2 ^ 2 := by decide

theorem hΔ91 : Disc 0 2 1 (-1) ≠ 0 := by decide

/-- **The universal height window, instantiated on 91a1.** Everything on the
right-hand side comes from r200; the only 91a1 input is `h2tor`. -/
theorem heightWindow_91a1 :
    HeightWindow (fun R : (E_91a1.toAffine).Point =>
      lognh (PointParallelogramUniversal.X R)) ((kappa 0 2 1 (-1) : ℤ) : ℝ) :=
  heightWindow_universal b₂_eq b₄_eq b₆_eq b₈_eq hΔ91 h2tor

/-! ## §5 — `Ψ ≠ 0` at every rational `x`, from the same parity fact -/

/-- `Psi 0 2 1 X Y = Y · (4X³ + 4XY² + Y³)`, so the 2-torsion cubic and the
duplication denominator are the same object. -/
theorem Psi_ne_zero_at (x : ℚ) : Psi 0 2 1 x.num (x.den : ℤ) ≠ 0 := by
  have hd : (x.den : ℤ) ≠ 0 := by exact_mod_cast x.den_nz
  intro h
  refine no_int_solution x.num (x.den : ℤ) (isCoprime_num_den x) ?_
  have hfac : (x.den : ℤ) * (4 * x.num ^ 3 + 4 * x.num * (x.den : ℤ) ^ 2
      + (x.den : ℤ) ^ 3) = 0 := by
    simp only [Psi] at h
    linear_combination h
  rcases mul_eq_zero.mp hfac with h1 | h2
  · exact absurd h1 hd
  · exact h2

end E91a1RankOne20261021
end PrincipiaTractalis

#print axioms PrincipiaTractalis.E91a1RankOne20261021.b₂_eq
#print axioms PrincipiaTractalis.E91a1RankOne20261021.b₈_eq
#print axioms PrincipiaTractalis.E91a1RankOne20261021.no_int_solution
#print axioms PrincipiaTractalis.E91a1RankOne20261021.no_rat_solution
#print axioms PrincipiaTractalis.E91a1RankOne20261021.y_ne_negY
#print axioms PrincipiaTractalis.E91a1RankOne20261021.h2tor
#print axioms PrincipiaTractalis.E91a1RankOne20261021.hΔ91
#print axioms PrincipiaTractalis.E91a1RankOne20261021.heightWindow_91a1
#print axioms PrincipiaTractalis.E91a1RankOne20261021.Psi_ne_zero_at
