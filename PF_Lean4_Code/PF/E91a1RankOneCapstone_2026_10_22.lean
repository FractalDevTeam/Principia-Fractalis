/-
# PF.E91a1RankOneCapstone_2026_10_22 — the rank bound for 91a1

The tail of `PF/E91a1RankOne_2026_10_21.lean`: from the per-curve facts proved
there (no rational 2-torsion, `Ψ ≠ 0` at every rational, the b-invariants, the
discriminant) to

  `1 ≤ Module.rank ℤ E_91a1(ℚ)`.

**Assembled, not transcribed.** Every general step is an existing universal
layer; this file supplies only 91a1's own arithmetic. For contrast, the
equivalent per-curve file for 43a1 (`E43a1RankOne_r135`) is 815 lines because it
re-derives the Bézout layer, the size bound, the height join and the driver
glue by hand. Here:

| obligation | discharged by |
|---|---|
| no rational 2-torsion | `E91a1RankOne20261021.h2tor` (part 1) |
| `Ψ ≠ 0` at every rational `x` | `E91a1RankOne20261021.Psi_ne_zero_at` (part 1) |
| `dblQ` is the dehomogenised duplication map | r178 `dblQ_eq_phiX_div_psiX` |
| `H(x)⁴ ≤ CL · H(x(2P))` | r176 `nh_pow_le_of_disc_ne_zero` |
| `naiveHeight` ↔ `nh` | r199 `naiveHeight_eq_nh` |
| `X(R+R) = dblQ (X R)` | r200 `X_dbl_of_ne_zero` |
| `2ⁿ·R ≠ 0` | r200 `smul_ne_zero_of_two_torsion_free` |
| infinite height ⇒ infinite range | r130 `infinite_of_duplication_step` |
| infinite x-orbit ⇒ rank ≥ 1 | `NonTorsionFromOrbit_2026_10_21` + r129 |

The only genuinely new arithmetic is the orbit of `P = (0,0)`:

  `x(2ⁿP) : 0 → 1 → −2/9 → 8845/441 → 6088653225047446/1223724862004841`,

whose heights are `1, 1, 9, 8845, 6088653225047446`. The threshold bites at
`n = 4` — the same shift `E43a1RankOne_r135` needed, for the same reason: the
first few doublings do not yet outgrow the curve constant.

**κ is never transcribed.** `kap` is *defined* as `(CL 0 2 1 (-1)).toNat` and
the two facts about it (`0 < kap`, `kap < 6088653225047446`) are proved by
`norm_num` unfolding r175's cofactor sums. So Lean computes the constant; a
wrong hand-copied value cannot sit in this file undetected.

**Why `Ψ ≠ 0` is the whole curve-specific story.** On 91a1,
`Psi 0 2 1 X Y = Y·(4X³ + 4XY² + Y³)`, so the duplication denominator *is* the
2-torsion cubic. Part 1's `no_int_solution` kills it by parity for every
coprime pair, which is why `Psi_ne_zero_at` holds at every rational — no
case analysis along the orbit, and the orbit can never hit the identity.

HONEST SCOPE. A LOWER bound on the rank of one curve. It does not compute the
exact rank, says nothing about `L(E, s)`, and proves no part of BSD.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-22.
-/

import PF.E91a1RankOne_2026_10_21
import PF.DuplicationFormula_r178
import PF.DuplicationHeightBound37a1_r133
import Mathlib.Tactic.NormNum.GCD

namespace PrincipiaTractalis
namespace E91a1RankOneCapstone20261022

open WeierstrassCurve WeierstrassCurve.Affine
open PrincipiaTractalis.BSD_HeegnerRank1ProofE91a1
open PrincipiaTractalis.E91a1RankOne20261021
open PrincipiaTractalis.NaiveHeightQ
open PrincipiaTractalis.CanonicalHeightGeneric
open PrincipiaTractalis.DuplicationBezout
open PrincipiaTractalis.DuplicationSize
open PrincipiaTractalis.DuplicationHeight
open PrincipiaTractalis.DuplicationFormula
open PrincipiaTractalis.PointParallelogramUniversal
open PrincipiaTractalis.CanheightParallelogramUniversal

/-! ## §1 — the base point `P = (0, 0)` -/

/-- `(0,0)` is a nonsingular rational point of 91a1: the equation at `(0,0)`
reads `0 = a₆ = 0`, and the `Y`-partial there is `a₃ = 1 ≠ 0`. -/
theorem P91_nonsingular : E_91a1.toAffine.Nonsingular 0 0 := by
  rw [Affine.nonsingular_zero]
  refine ⟨rfl, Or.inl ?_⟩
  show (1 : ℚ) ≠ 0
  norm_num

/-- **The base point** `P91 = (0, 0) ∈ E_91a1(ℚ)`. -/
noncomputable def P91 : E_91a1.toAffine.Point := Point.some P91_nonsingular

theorem P91_ne_zero : P91 ≠ 0 := some_ne_zero _

theorem X_P91 : X P91 = 0 := rfl

/-! ## §2 — `dblQ` on 91a1, dehomogenised

`phiX` and `psiX` are r178's dehomogenised duplication numerator and
denominator. Instantiating the b-invariants proved in part 1 turns them into
two concrete polynomials, which makes the orbit computable by `norm_num`. -/

/-- Duplication numerator on 91a1: `x⁴ − 2x² − 2x + 1`. -/
def f91 (x : ℚ) : ℚ := x ^ 4 - 2 * x ^ 2 - 2 * x + 1

/-- Duplication denominator on 91a1: `4x³ + 4x + 1` — the 2-torsion cubic. -/
def g91 (x : ℚ) : ℚ := 4 * x ^ 3 + 4 * x + 1

/-- The denominator never vanishes on ℚ. This is part 1's `no_rat_solution`,
i.e. exactly the absence of rational 2-torsion. -/
theorem g91_ne_zero (x : ℚ) : g91 x ≠ 0 := by
  simpa [g91] using no_rat_solution x

theorem phiX_eq_f91 (x : ℚ) : phiX (E_91a1.toAffine) x = f91 x := by
  simp only [phiX, f91, b₄_eq, b₆_eq, b₈_eq]
  push_cast
  ring

theorem psiX_eq_g91 (x : ℚ) : psiX (E_91a1.toAffine) x = g91 x := by
  simp only [psiX, g91, b₂_eq, b₄_eq, b₆_eq]
  push_cast
  ring

/-- **The duplication map on 91a1, as a rational function.** -/
theorem dblQ_eq_fg91 (x : ℚ) : dblQ 0 2 1 (-1) x = f91 x / g91 x := by
  rw [dblQ_eq_phiX_div_psiX b₂_eq.symm b₄_eq.symm b₆_eq.symm b₈_eq.symm x,
    phiX_eq_f91, psiX_eq_g91]

/-! ## §3 — the arithmetic chain and its first five values -/

/-- The x-coordinates of the doubling orbit of `P91`, as pure arithmetic. -/
def xs : ℕ → ℚ
  | 0 => 0
  | n + 1 => dblQ 0 2 1 (-1) (xs n)

theorem xs_zero : xs 0 = 0 := rfl

theorem xs_succ (n : ℕ) : xs (n + 1) = dblQ 0 2 1 (-1) (xs n) := rfl

theorem xs_one : xs 1 = 1 := by
  show xs (0 + 1) = 1
  rw [xs_succ, xs_zero, dblQ_eq_fg91]
  norm_num [f91, g91]

theorem xs_two : xs 2 = -2 / 9 := by
  show xs (1 + 1) = -2 / 9
  rw [xs_succ, xs_one, dblQ_eq_fg91]
  norm_num [f91, g91]

theorem xs_three : xs 3 = 8845 / 441 := by
  show xs (2 + 1) = 8845 / 441
  rw [xs_succ, xs_two, dblQ_eq_fg91]
  norm_num [f91, g91]

/-- `x(16P) = 6088653225047446 / 1223724862004841`. -/
theorem xs_four : xs 4 = 6088653225047446 / 1223724862004841 := by
  show xs (3 + 1) = 6088653225047446 / 1223724862004841
  rw [xs_succ, xs_three, dblQ_eq_fg91]
  norm_num [f91, g91]

/-! ## §4 — the height step, straight from the universal layer -/

/-- The curve constant, **computed** rather than copied: r175's `CL` at 91a1's
b-invariants. Nothing downstream depends on its decimal value. -/
def kap : ℕ := (CL 0 2 1 (-1)).toNat

theorem kap_cast : ((kap : ℤ)) = CL 0 2 1 (-1) :=
  Int.toNat_of_nonneg (CL_nonneg 0 2 1 (-1))

/-- **The quartic duplication step, for every element of the chain.** r176
proves this for every rational on every curve with nonzero discriminant; the
only 91a1 input is that `Ψ` never vanishes, which part 1 proved at *every*
rational, so there is no case analysis along the orbit. -/
theorem height_step (n : ℕ) :
    naiveHeight (xs n) ^ 4 ≤ kap * naiveHeight (xs (n + 1)) := by
  have h := nh_pow_le_of_disc_ne_zero (hrel := hrel91) (x := xs n)
    (hΨ := Psi_ne_zero_at (xs n)) hΔ91
  rw [← xs_succ n] at h
  have hgoal : ((naiveHeight (xs n) : ℤ)) ^ 4
      ≤ (kap : ℤ) * ((naiveHeight (xs (n + 1)) : ℤ)) := by
    rw [naiveHeight_eq_nh, naiveHeight_eq_nh, kap_cast]
    exact h
  exact_mod_cast hgoal

/-! ## §5 — the threshold -/

/-- `naiveHeight (x(16P)) = 6088653225047446`; the fraction is already
reduced, certified by `norm_num`'s gcd extension. -/
theorem naiveHeight_xs_four : naiveHeight (xs 4) = 6088653225047446 := by
  have h4 : xs 4 = ((6088653225047446 : ℤ) : ℚ) / ((1223724862004841 : ℤ) : ℚ) := by
    rw [xs_four]; norm_num
  have hg : Int.gcd 6088653225047446 1223724862004841 = 1 := by norm_num
  rw [h4, DuplicationHeightBound37a1.naiveHeight_div_int 6088653225047446
    1223724862004841 (by norm_num), hg]
  norm_num

theorem kap_pos : 0 < kap := by
  show 0 < (CL 0 2 1 (-1)).toNat
  norm_num [CL, SF1, SG1, SF2, SG2, cF10, cF11, cF12, cF13, cG10, cG11, cG12,
    cG13, cF20, cF21, cF22, cF23, cG20, cG21, cG22, cG23]

/-- **The threshold check**: the orbit clears the curve constant at `n = 4`. -/
theorem threshold : kap < naiveHeight (xs 4) := by
  rw [naiveHeight_xs_four]
  show (CL 0 2 1 (-1)).toNat < 6088653225047446
  norm_num [CL, SF1, SG1, SF2, SG2, cF10, cF11, cF12, cF13, cG10, cG11, cG12,
    cG13, cF20, cF21, cF22, cF23, cG20, cG21, cG22, cG23]

/-! ## §6 — firing r130's driver -/

/-- **The chain from `16P` on takes infinitely many values.** -/
theorem xs_shifted_infinite : (Set.range fun n => xs (n + 4)).Infinite :=
  infinite_of_duplication_step (κ := kap) (fun n => xs (n + 4)) kap_pos
    (fun n => height_step (n + 4)) threshold

/-! ## §7 — transporting the chain onto the point group -/

/-- `X` intertwines doubling with `dblQ` all the way up the dyadic tower, so
the geometric orbit and the arithmetic chain agree at every level. -/
theorem X_two_pow_smul (n : ℕ) : X (((2 : ℤ) ^ n) • P91) = xs n := by
  induction n with
  | zero => simpa using X_P91
  | succ k ih =>
      have hk : ((2 : ℤ) ^ k) • P91 ≠ 0 :=
        smul_ne_zero_of_two_torsion_free h2tor P91_ne_zero k
      rw [two_pow_succ_zsmul, X_dbl_of_ne_zero b₂_eq b₄_eq b₆_eq b₈_eq h2tor _ hk,
        ih, xs_succ k]

/-- The duplicate-`X` bridge. `NonTorsionFromOrbit_2026_10_21` defines its own
`X`, which r199:63 already had — a defect recorded on 2026-10-21 and still
pending retirement. The two definitions are the same `match`, so they agree by
`rfl` pointwise; this lemma is what lets the capstone below be stated with the
universal `X` while the driver consumes the duplicate. -/
theorem X_bridge (R : E_91a1.toAffine.Point) :
    NonTorsionFromOrbit20261021.X R = X R := by
  cases R <;> rfl

theorem orbit_infinite :
    (Set.range fun n =>
      NonTorsionFromOrbit20261021.X (((2 : ℤ) ^ (n + 4)) • P91)).Infinite := by
  have hfun : (fun n : ℕ =>
      NonTorsionFromOrbit20261021.X (((2 : ℤ) ^ (n + 4)) • P91))
      = fun n : ℕ => xs (n + 4) := by
    funext n
    rw [X_bridge, X_two_pow_smul]
  rw [hfun]
  exact xs_shifted_infinite

/-! ## §8 — the capstones -/

/-- **`P91 = (0,0)` has infinite order in `E_91a1(ℚ)`.** -/
theorem P91_nonTorsion : ¬ IsOfFinAddOrder P91 :=
  NonTorsionFromOrbit20261021.nonTorsion_of_doubling_orbit_infinite P91 4
    orbit_infinite

/-- **THE FLAG — `rank E_91a1(ℚ) ≥ 1`.** A lower bound, nothing more. -/
theorem E91a1_rank_ge_one : 1 ≤ Module.rank ℤ E_91a1.toAffine.Point :=
  NonTorsionFromOrbit20261021.rank_ge_one_of_doubling_orbit_infinite P91 4
    orbit_infinite

end E91a1RankOneCapstone20261022
end PrincipiaTractalis

/-! ## §Axiom check -/

#print axioms PrincipiaTractalis.E91a1RankOneCapstone20261022.P91_nonsingular
#print axioms PrincipiaTractalis.E91a1RankOneCapstone20261022.dblQ_eq_fg91
#print axioms PrincipiaTractalis.E91a1RankOneCapstone20261022.xs_four
#print axioms PrincipiaTractalis.E91a1RankOneCapstone20261022.height_step
#print axioms PrincipiaTractalis.E91a1RankOneCapstone20261022.naiveHeight_xs_four
#print axioms PrincipiaTractalis.E91a1RankOneCapstone20261022.threshold
#print axioms PrincipiaTractalis.E91a1RankOneCapstone20261022.xs_shifted_infinite
#print axioms PrincipiaTractalis.E91a1RankOneCapstone20261022.X_two_pow_smul
#print axioms PrincipiaTractalis.E91a1RankOneCapstone20261022.X_bridge
#print axioms PrincipiaTractalis.E91a1RankOneCapstone20261022.P91_nonTorsion
#print axioms PrincipiaTractalis.E91a1RankOneCapstone20261022.E91a1_rank_ge_one

-- The computed curve constant, for the record: kap = 24388.
-- A doc comment cannot precede #eval (it expects a declaration), and a block
-- comment quoting one would nest, so these are line comments.
#eval PrincipiaTractalis.E91a1RankOneCapstone20261022.kap
