/-
# PF.E141a1RankOne_2026_11_11 — part 1: curve facts and no rational 2-torsion

The per-curve obligations for feeding 141a1 into the universal layers
(r176 window, r179 fixed window, r199/r200 point-level machinery, r130
driver). Everything else comes from those layers; this file holds only
what is genuinely specific to `y² + y = x³ + x² − 12x + 2`.

`E_141a1` and its discriminant already exist in
`PF/BSD_HeegnerRank1ProofE141a1.lean` (that file's headline is one of
the §0.4-flagged Prop-level mirrors with `True` hypotheses, but its
curve definition and `Δ = 102789` computation are ordinary arithmetic
and are reused here rather than restated).

THE ONE REAL OBLIGATION is no rational 2-torsion. r200's universal
layer takes it as `h2tor : ∀ R ≠ 0, 2 • R ≠ 0` and supplies everything
downstream (`PsiX_ne_zero`, `X_dbl_of_ne_zero`,
`heightWindow_universal`). For 141a1 a 2-torsion point needs
`y = negY x y = −y − 1`, i.e. `y = −1/2`, and then the curve equation
forces `4x³ + 4x² − 48x + 9 = 0`, which has no rational solution by a
standard mod-2 descent on `x.num` / `x.den`.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-11.
-/

import PF.BSD_HeegnerRank1ProofE141a1
import PF.PointParallelogramUniversal_r199
import PF.CanheightParallelogramUniversal_r200
import PF.NonTorsionFromOrbit_2026_10_21

namespace PrincipiaTractalis
namespace E141a1RankOne20261111

open WeierstrassCurve WeierstrassCurve.Affine
open PrincipiaTractalis.BSD_HeegnerRank1ProofE141a1
open PrincipiaTractalis.CanonicalHeightGeneric
open PrincipiaTractalis.DuplicationBezout
open PrincipiaTractalis.DuplicationSize
open PrincipiaTractalis.DuplicationHeight
open PrincipiaTractalis.DuplicationLogWindow
open PrincipiaTractalis.PointParallelogramUniversal
open PrincipiaTractalis.CanheightParallelogramUniversal
open PrincipiaTractalis.NaiveHeightQ

/-! ## §1 — the b-invariants, in the integer form the universal layers want -/

theorem b₂_eq : (E_141a1.toAffine).b₂ = ((4 : ℤ) : ℚ) := by
  simp [WeierstrassCurve.b₂, E_141a1]

theorem b₄_eq : (E_141a1.toAffine).b₄ = ((-24 : ℤ) : ℚ) := by
  simp [WeierstrassCurve.b₄, E_141a1]
  norm_num

theorem b₆_eq : (E_141a1.toAffine).b₆ = ((9 : ℤ) : ℚ) := by
  simp [WeierstrassCurve.b₆, E_141a1]
  norm_num

theorem b₈_eq : (E_141a1.toAffine).b₈ = ((-135 : ℤ) : ℚ) := by
  simp [WeierstrassCurve.b₈, E_141a1]
  norm_num

/-! ## §2 — `4x³ + 4x² − 48x + 9 = 0` has no rational solution

The cubic that a rational 2-torsion point would have to solve, cleared
of denominators: `4p³ + 4p²q − 48pq² + 9q³ = 0` with `p`, `q` coprime
and `q > 0`.  Mod-2 descent: q odd makes LHS odd; q even forces p odd,
then dividing the equation by 4 shows p³ is even — contradiction. -/

theorem no_int_solution (p q : ℤ) (hcop : IsCoprime p q) :
    4 * p ^ 3 + 4 * p ^ 2 * q - 48 * p * q ^ 2 + 9 * q ^ 3 ≠ 0 := by
  intro heq
  rcases Int.even_or_odd q with hqe | hqo
  · -- q even: write q = m + m
    obtain ⟨m, hm⟩ := hqe
    subst hm
    -- 4p^3 + 4p^2·(2m) - 48p·(2m)^2 + 9·(2m)^3
    --   = 4p^3 + 8p^2·m - 192p·m^2 + 72m^3
    --   = 4·(p^3 + 2·p^2·m - 48·p·m^2 + 18·m^3)
    have h4z : 4 * (p ^ 3 + 2 * (p ^ 2 * m) - 48 * (p * m ^ 2) + 18 * m ^ 3) = 0 := by
      linear_combination heq
    have hdiv : p ^ 3 + 2 * (p ^ 2 * m) - 48 * (p * m ^ 2) + 18 * m ^ 3 = 0 := by
      rcases mul_eq_zero.mp h4z with h | h
      · norm_num at h
      · exact h
    -- p^3 = -(2 p^2 m - 48 p m^2 + 18 m^3) = 2·(-p^2 m + 24 p m^2 - 9 m^3),
    -- so p^3 is even, hence p is even.
    have hev3 : Even (p ^ 3) :=
      ⟨-(p ^ 2 * m) + 24 * (p * m ^ 2) - 9 * m ^ 3, by linarith⟩
    have hevp : Even p := (Int.even_pow.mp hev3).1
    obtain ⟨k, hk⟩ := hevp
    have h2p : (2 : ℤ) ∣ p := ⟨k, by linarith⟩
    have h2q : (2 : ℤ) ∣ (m + m) := ⟨m, by ring⟩
    have hu : IsUnit (2 : ℤ) := hcop.isUnit_of_dvd' h2p h2q
    rw [Int.isUnit_iff] at hu
    omega
  · -- q odd: 9q^3 is odd, rest is even, so LHS is odd ≠ 0.
    have hq3 : Odd (q ^ 3) := hqo.pow
    have h9q3 : Odd (9 * q ^ 3) := by
      rcases hq3 with ⟨r, hr⟩
      exact ⟨9 * r + 4, by linarith⟩
    have h4 : Even (4 * p ^ 3 + 4 * p ^ 2 * q - 48 * p * q ^ 2) :=
      ⟨2 * p ^ 3 + 2 * p ^ 2 * q - 24 * p * q ^ 2, by ring⟩
    have hodd : Odd (4 * p ^ 3 + 4 * p ^ 2 * q - 48 * p * q ^ 2 + 9 * q ^ 3) :=
      h4.add_odd h9q3
    rw [heq] at hodd
    simpa using hodd

/-! ## §3 — no rational 2-torsion on 141a1 -/

/-- `4x³ + 4x² − 48x + 9 = 0` has no rational solution: clear denominators
and apply the mod-2 descent to `(x.num, x.den)`, which are coprime. -/
theorem no_rat_solution (x : ℚ) :
    4 * x ^ 3 + 4 * x ^ 2 - 48 * x + 9 ≠ 0 := by
  intro h
  have hd : ((x.den : ℚ)) ≠ 0 := by
    exact_mod_cast Rat.den_ne_zero x
  have hnum : (x.num : ℚ) = x * (x.den : ℚ) :=
    (div_eq_iff hd).mp (Rat.num_div_den x)
  have key : ((4 * x.num ^ 3 + 4 * x.num ^ 2 * (x.den : ℤ)
      - 48 * x.num * (x.den : ℤ) ^ 2 + 9 * (x.den : ℤ) ^ 3 : ℤ) : ℚ) = 0 := by
    push_cast
    rw [hnum]
    linear_combination ((x.den : ℚ)) ^ 3 * h
  exact no_int_solution x.num (x.den : ℤ) (isCoprime_num_den x)
    (by exact_mod_cast key)

/-- **141a1 has no rational 2-torsion, at the coordinate level.** A
2-torsion point needs `y = negY x y = −y − 1`, i.e. `2y + 1 = 0`;
substituting into `y² + y = x³ + x² − 12x + 2` forces
`4x³ + 4x² − 48x + 9 = 0`. -/
theorem y_ne_negY {x y : ℚ} (h : (E_141a1.toAffine).Equation x y) :
    y ≠ (E_141a1.toAffine).negY x y := by
  intro hy
  rw [WeierstrassCurve.Affine.equation_iff] at h
  simp only [WeierstrassCurve.Affine.negY, E_141a1] at hy h
  exact no_rat_solution x (by linear_combination (-4) * h + (2 * y + 1) * hy)

/-- **`h2tor` in the ∀-form the universal layers take** (r200's hypothesis). -/
theorem h2tor : ∀ R : (E_141a1.toAffine).Point, R ≠ 0 → (2 : ℕ) • R ≠ 0 := by
  intro R hR
  obtain ⟨x, y, hns, rfl⟩ := exists_affine hR
  rw [two_nsmul]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne (y_ne_negY hns.left)]
  exact some_ne_zero _

/-! ## §4 — the curve-level constants the universal layers ask for -/

theorem hrel141 : 4 * (-135 : ℤ) = 4 * 9 - (-24) ^ 2 := by decide

theorem hΔ141 : Disc 4 (-24) 9 (-135) ≠ 0 := by decide

/-- **The universal height window, instantiated on 141a1.** -/
theorem heightWindow_141a1 :
    HeightWindow (fun R : (E_141a1.toAffine).Point =>
      lognh (PointParallelogramUniversal.X R))
      ((kappa 4 (-24) 9 (-135) : ℤ) : ℝ) :=
  heightWindow_universal b₂_eq b₄_eq b₆_eq b₈_eq hΔ141 h2tor

/-! ## §5 — `Ψ ≠ 0` at every rational `x`, from the same parity fact -/

/-- `Psi 4 (-24) 9 X Y = Y · (4X³ + 4X²Y − 48XY² + 9Y³)`, so the
2-torsion cubic and the duplication denominator are the same object. -/
theorem Psi_ne_zero_at (x : ℚ) : Psi 4 (-24) 9 x.num (x.den : ℤ) ≠ 0 := by
  have hd : (x.den : ℤ) ≠ 0 := by exact_mod_cast x.den_nz
  intro h
  refine no_int_solution x.num (x.den : ℤ) (isCoprime_num_den x) ?_
  have hfac : (x.den : ℤ) * (4 * x.num ^ 3 + 4 * x.num ^ 2 * (x.den : ℤ)
      - 48 * x.num * (x.den : ℤ) ^ 2 + 9 * (x.den : ℤ) ^ 3) = 0 := by
    simp only [Psi] at h
    linear_combination h
  rcases mul_eq_zero.mp hfac with h1 | h2
  · exact absurd h1 hd
  · exact h2

end E141a1RankOne20261111
end PrincipiaTractalis

#print axioms PrincipiaTractalis.E141a1RankOne20261111.b₂_eq
#print axioms PrincipiaTractalis.E141a1RankOne20261111.b₈_eq
#print axioms PrincipiaTractalis.E141a1RankOne20261111.no_int_solution
#print axioms PrincipiaTractalis.E141a1RankOne20261111.no_rat_solution
#print axioms PrincipiaTractalis.E141a1RankOne20261111.y_ne_negY
#print axioms PrincipiaTractalis.E141a1RankOne20261111.h2tor
#print axioms PrincipiaTractalis.E141a1RankOne20261111.hΔ141
#print axioms PrincipiaTractalis.E141a1RankOne20261111.heightWindow_141a1
#print axioms PrincipiaTractalis.E141a1RankOne20261111.Psi_ne_zero_at
