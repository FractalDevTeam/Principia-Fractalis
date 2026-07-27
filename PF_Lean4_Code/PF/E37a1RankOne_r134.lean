/-
# PF.E37a1RankOne_r134

★★★ 2026-07-27 — B5, THE FINAL STONE OF THE NON-TORSION ARC ★★★

The arc mapped in `codex/BSD_NONTORSION_ARC_PLAN_2026-07-27.md` closes here.
For the rank-1 curve **37a1** (`y² + y = x³ − x`) and its rational point
`P = (0, 0)`, this file proves the corpus's first kernel-verified literal
Mordell–Weil rank bound for an LMFDB curve:

  * `P_nonTorsion : ¬ IsOfFinAddOrder P37` — the point `(0, 0)` has infinite
    order in `E37a1(ℚ)`;
  * `E37a1_rank_ge_one : 1 ≤ Module.rank ℤ E37a1.toAffine.Point` — the FLAG.

Construction (B1–B4 assembled):

  1. `(0, 0)` is a nonsingular point of 37a1 (`nonsingular_zero`: `a₆ = 0`,
     `a₃ = 1 ≠ 0`).
  2. A doubling chain `chain : ℕ → Σ' x y, Nonsingular x y` is built by
     recursion through B4's `dbl_height` (r133): each step doubles the point
     and carries the quartic height inequality
     `naiveHeight (xs n)⁴ ≤ 171 · naiveHeight (xs (n+1))`.
     By induction `pts n = 2ⁿ • P37`.
  3. B2's `dbl_x` (r132) pins the chain's x-coordinates exactly:
     `xs (n+1) = f (xs n) / g (xs n)`, so they are computable by `norm_num`:
     `xs 0 = 0, xs 1 = 1, xs 2 = 2, xs 3 = 21/25, xs 4 = 480106/4225`,
     and `naiveHeight (xs 4) = 480106 > 171` (gcd(480106, 4225) = 1).
  4. B1's driver (r130, `infinite_of_duplication_step`, κ = 171) applied to
     the shifted sequence `n ↦ xs (n + 4)` gives an infinite range of
     x-coordinates.
  5. If `P37` were torsion, `AddSubgroup.zmultiples P37` would be a finite
     set, and the x-coordinate image of that finite set would contain the
     infinite range of step 4 — contradiction.  Hence `P_nonTorsion`, and
     r129's `mordellWeil_rank_ge_one` fires.

HONEST SCOPE. This file certifies ONE point on ONE curve as non-torsion and
concludes `1 ≤ Module.rank ℤ E37a1(ℚ)` — a LOWER bound only.  It does not
compute the exact rank (upper bounds need Mordell–Weil finiteness + descent,
absent from mathlib v4.24), says nothing about any other curve of the
17-cohort, and proves no statement about L-functions or BSD.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-27.
-/
import PF.NaiveHeightQ_r130
import PF.DuplicationFormula37a1_r132
import PF.DuplicationHeightBound37a1_r133
import PF.MordellWeilRankLowerBound_r129
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.DivMod

namespace PrincipiaTractalis.E37a1RankOne

open PrincipiaTractalis.NaiveHeightQ
open PrincipiaTractalis.DuplicationFormula37a1
open PrincipiaTractalis.DuplicationHeightBound37a1
open PrincipiaTractalis.MordellWeilRankLowerBound
open WeierstrassCurve WeierstrassCurve.Affine

/-! ## §1 — the base point `P = (0, 0)` on 37a1 -/

/-- `(0, 0)` is a nonsingular rational point of 37a1: the equation reads
`0 + 0 = 0 − 0` (i.e. `a₆ = 0`), and the Y-partial there is `a₃ = 1 ≠ 0`. -/
theorem P37_nonsingular : E37a1.toAffine.Nonsingular 0 0 := by
  rw [Affine.nonsingular_zero]
  refine ⟨rfl, Or.inl ?_⟩
  show (1 : ℚ) ≠ 0
  norm_num

/-- **The base point** `P37 = (0, 0) ∈ E37a1(ℚ)`. -/
noncomputable def P37 : E37a1.toAffine.Point := Point.some P37_nonsingular

/-! ## §2 — the doubling chain

`chain n` carries the full data of the `n`-fold double of `P37`: the affine
coordinates and the nonsingularity proof, produced step-by-step by r133's
`dbl_height` (whose existential also certifies the group-law equation and the
quartic height step, extracted below from `choose_spec`). -/

/-- The doubling chain: `chain 0 = (0, 0, proof)`, and `chain (n+1)` is the
affine data of `chain n + chain n` chosen from `dbl_height`. -/
noncomputable def chain : ℕ → Σ' (x y : ℚ), E37a1.toAffine.Nonsingular x y :=
  Nat.rec (motive := fun _ => Σ' (x y : ℚ), E37a1.toAffine.Nonsingular x y)
    ⟨0, 0, P37_nonsingular⟩
    fun _ c =>
      ⟨(dbl_height c.2.2).choose,
       (dbl_height c.2.2).choose_spec.choose,
       (dbl_height c.2.2).choose_spec.choose_spec.choose⟩

/-- The x-coordinate along the chain. -/
noncomputable def xs (n : ℕ) : ℚ := (chain n).1

/-- The chain as points of the group `E37a1(ℚ)`. -/
noncomputable def pts (n : ℕ) : E37a1.toAffine.Point := Point.some (chain n).2.2

@[simp] lemma xs_zero : xs 0 = 0 := rfl

lemma pts_zero : pts 0 = P37 := rfl

/-- Each chain step doubles the point (from `dbl_height`'s `choose_spec`). -/
lemma pts_succ (n : ℕ) : pts (n + 1) = pts n + pts n :=
  ((dbl_height (chain n).2.2).choose_spec.choose_spec.choose_spec.1).symm

/-- Each chain step satisfies the quartic height inequality (κ = 171). -/
lemma height_step (n : ℕ) :
    naiveHeight (xs n) ^ 4 ≤ 171 * naiveHeight (xs (n + 1)) :=
  (dbl_height (chain n).2.2).choose_spec.choose_spec.choose_spec.2

/-- The chain is the `2ⁿ`-multiples of the base point: `pts n = 2ⁿ • P37`. -/
lemma pts_eq_two_pow_smul (n : ℕ) : pts n = ((2 : ℤ) ^ n) • P37 := by
  induction n with
  | zero => rw [pow_zero, one_zsmul, pts_zero]
  | succ k ih =>
      have h2 : ((2 : ℤ) ^ (k + 1)) = 2 ^ k + 2 ^ k := by ring
      rw [pts_succ, ih, h2, add_zsmul]

/-! ## §3 — the x-coordinates are pinned exactly: `xs (n+1) = f (xs n) / g (xs n)`

`dbl_height`'s witnesses come from `choose`, but r132's `dbl_x` plus
injectivity of the `Point.some` constructor determine them uniquely, so the
concrete chain values are provable by `norm_num`. -/

/-- The chain's x-coordinate recursion, made explicit via `dbl_x` and
`Point.some`-injectivity. -/
lemma xs_succ (n : ℕ) : xs (n + 1) = f (xs n) / g (xs n) := by
  obtain ⟨x', y', h', hadd, hx⟩ := dbl_x (chain n).2.2
  have hpt : Point.some (chain (n + 1)).2.2 = Point.some h' :=
    (pts_succ n).trans hadd
  have hxeq : (chain (n + 1)).1 = x' := (Point.some.inj hpt).left
  exact hxeq.trans hx

/-- `x(2P) = 1`. -/
lemma xs_one : xs 1 = 1 := by
  rw [xs_succ 0, xs_zero]; norm_num [f, g]

/-- `x(4P) = 2`. -/
lemma xs_two : xs 2 = 2 := by
  rw [xs_succ 1, xs_one]; norm_num [f, g]

/-- `x(8P) = 21/25`. -/
lemma xs_three : xs 3 = 21 / 25 := by
  rw [xs_succ 2, xs_two]; norm_num [f, g]

/-- `x(16P) = 480106/4225`. -/
lemma xs_four : xs 4 = 480106 / 4225 := by
  rw [xs_succ 3, xs_three]; norm_num [f, g]

/-- `naiveHeight (x(16P)) = 480106` — the fraction is already reduced:
`gcd(480106, 4225) = 1` (`4225 = 5²·13²` and `480106` is divisible by
neither 5 nor 13). -/
lemma naiveHeight_xs_four : naiveHeight (xs 4) = 480106 := by
  have h4 : xs 4 = ((480106 : ℤ) : ℚ) / ((4225 : ℤ) : ℚ) := by
    rw [xs_four]; norm_num
  have hg : Int.gcd 480106 4225 = 1 := by norm_num
  rw [h4, naiveHeight_div_int 480106 4225 (by norm_num), hg]
  norm_num

/-- The B5 threshold check: `x(16P)` clears the curve constant `κ = 171`. -/
lemma threshold : 171 < naiveHeight (xs 4) := by
  rw [naiveHeight_xs_four]; norm_num

/-! ## §4 — firing B1's driver: infinitely many x-coordinates -/

/-- **The chain from `16P` on has infinite x-coordinate range**: the quartic
step (§2) starts above the threshold (§3), so r130's growth engine applies. -/
theorem xs_shifted_infinite : (Set.range fun n => xs (n + 4)).Infinite :=
  infinite_of_duplication_step (κ := 171) (fun n => xs (n + 4))
    (by norm_num) (fun n => height_step (n + 4)) threshold

/-! ## §5 — non-torsion: a finite orbit cannot contain an infinite image -/

/-- The x-coordinate projection on the point group (`0` at the identity). -/
def X : E37a1.toAffine.Point → ℚ
  | .zero => 0
  | @Point.some _ _ _ x _ _ => x

lemma X_pts (n : ℕ) : X (pts n) = xs n := rfl

/-- **CAPSTONE 1 — `P = (0, 0)` is non-torsion on 37a1.** If `P37` had
finite order, `AddSubgroup.zmultiples P37` would be a finite set; its image
under `X` would be finite, yet it contains the infinite range of §4 (every
`pts (n+4) = 2^(n+4) • P37` is a `ℤ`-multiple of `P37`). -/
theorem P_nonTorsion : ¬ IsOfFinAddOrder P37 := by
  intro hfin
  have hfinite := hfin.finite_zmultiples
  have hsub : (Set.range fun n => xs (n + 4))
      ⊆ X '' (AddSubgroup.zmultiples P37 : Set _) := by
    rintro q ⟨n, rfl⟩
    refine ⟨pts (n + 4), ?_, X_pts (n + 4)⟩
    exact AddSubgroup.mem_zmultiples_iff.mpr
      ⟨(2 : ℤ) ^ (n + 4), (pts_eq_two_pow_smul (n + 4)).symm⟩
  exact xs_shifted_infinite ((hfinite.image X).subset hsub)

/-! ## §6 — THE FLAG: rank ≥ 1 for 37a1 -/

/-- The r129 certificate, discharged: `P37` has infinite order in
`E37a1(ℚ)`. -/
theorem P37_certificate : NonTorsionCertificate E37a1.toAffine P37 :=
  P_nonTorsion

/-- **CAPSTONE 2 — the Mordell–Weil rank of 37a1 is at least 1**: the
corpus's first kernel-verified literal rank bound for an LMFDB curve. -/
theorem E37a1_rank_ge_one : 1 ≤ Module.rank ℤ E37a1.toAffine.Point :=
  mordellWeil_rank_ge_one E37a1.toAffine P37 P_nonTorsion

end PrincipiaTractalis.E37a1RankOne

#print axioms PrincipiaTractalis.E37a1RankOne.P37_nonsingular
#print axioms PrincipiaTractalis.E37a1RankOne.pts_eq_two_pow_smul
#print axioms PrincipiaTractalis.E37a1RankOne.xs_four
#print axioms PrincipiaTractalis.E37a1RankOne.naiveHeight_xs_four
#print axioms PrincipiaTractalis.E37a1RankOne.xs_shifted_infinite
#print axioms PrincipiaTractalis.E37a1RankOne.P_nonTorsion
#print axioms PrincipiaTractalis.E37a1RankOne.P37_certificate
#print axioms PrincipiaTractalis.E37a1RankOne.E37a1_rank_ge_one
