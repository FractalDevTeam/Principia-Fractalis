/-
# PF.E389a1RankTwo_r154

★★★★★ 2026-07-30 — `2 ≤ Module.rank ℤ E389a1(ℚ)` — THE FLAG ★★★★★

The independence arc closes.  For the LMFDB generators of 389a1 (the
smallest-conductor rank-2 elliptic curve)

    `P = (0, 0)`,   `Q = (1, 0)`,

r153's interval machine is instantiated at level 3 of the dyadic chain.
Each chain value is an explicit rational, computed by `norm_num` through
three iterations of `x ↦ f x / g x` (r143's duplication formula):

| point | `x(8·)` | naive height `H` | bracket |
|---|---|---|---|
| `P`   | `1169154495/76860289` | `1169154495` | `2³⁰ ≤ H < 2³¹` |
| `Q`   | `11776563836346/9521600032681` | `11776563836346` | `2⁴³ ≤ H < 2⁴⁴` |
| `P+Q` | `30157844295583882647192303/13139629878047776942118401` | numerator | `2⁸⁴ ≤ H < 2⁸⁵` |
| `P−Q` | `7383740148384742954/7960116832793145801` | denominator | `2⁶² ≤ H < 2⁶³` |

(`x(P+Q) = −2`, `x(P−Q) = −1`, both obtained from mathlib's secant
construction, not assumed.)

`canheight_bracket` turns those into rational intervals

    `ĥP ∈ [0.2851, 0.3756]`,      `ĥQ ∈ [0.4259, 0.5163]`
    `ĥ(P+Q) ∈ [0.8700, 0.9604]`,  `ĥ(P−Q) ∈ [0.6317, 0.7221]`

from which everything follows:

* all four lower bounds are **positive**, so all four points are
  non-torsion — exactly the side conditions r150/r152 require, obtained
  without any separate chain-growth argument;
* `ĥP·ĥQ ≥ 0.1214` while `⟨P,Q⟩² ≤ 0.0156`, hence `regDet P Q > 0`;
* r152's `rank_ge_two_of_regDet_ne_zero` then gives the flag.

## What is proved

    `2 ≤ Module.rank ℤ E389a1.toAffine.Point`

on mathlib's *literal* Mordell–Weil group, with `#print axioms` reporting
only `[propext, Classical.choice, Quot.sound]`.

Point independence had not previously been formalized in any proof
assistant, nor had a canonical height on an elliptic curve (r147).  The
whole route is elementary: no descent, no formal groups, no Mazur, no
Gross–Zagier — only explicit integer certificates, the dyadic chain, and one
limit.

HONEST SCOPE.  A rank **lower** bound for one curve.  It is *not* rank
equality (that needs descent, absent from every prover), says nothing about
L-functions or analytic rank, and proves no part of BSD.  For orientation
only, never used in a proof: 389a1's true regulator is ≈ 0.15246, consistent
with the interval above.

Kernel axioms ⊆ `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-30.
-/
import PF.RegulatorPositive389a1_r153

namespace PrincipiaTractalis.E389a1RankTwo

open PrincipiaTractalis.NaiveHeightQ
open PrincipiaTractalis.E389a1RankOne
open PrincipiaTractalis.CanonicalHeight389a1
open PrincipiaTractalis.CanheightParallelogram389a1
open PrincipiaTractalis.SecantBridge389a1
open PrincipiaTractalis.QuasiParallelogramLower389a1
open PrincipiaTractalis.PointQuasiParallelogram389a1
open PrincipiaTractalis.RegulatorIndependence389a1
open PrincipiaTractalis.RegulatorPositive389a1
open WeierstrassCurve WeierstrassCurve.Affine

/-! ## §1 — the two generators -/

/-- `Q = (1, 0)` is a nonsingular rational point of 389a1: the equation reads
`0 = 1 + 1 − 2`, and the X-partial there is `−3 ≠ 0`. -/
theorem Q_nonsingular : E389a1.toAffine.Nonsingular 1 0 := by
  rw [Affine.nonsingular_iff]
  refine ⟨?_, Or.inl ?_⟩
  · rw [Affine.equation_iff]
    simp only [E389a1_a₁, E389a1_a₂, E389a1_a₃, E389a1_a₄, E389a1_a₆]
    norm_num
  · simp only [E389a1_a₁, E389a1_a₂, E389a1_a₄]
    norm_num

/-- The second generator. -/
noncomputable def Q389 : E389a1.toAffine.Point := Point.some Q_nonsingular

theorem P_ne_Q_x : (0 : ℚ) ≠ 1 := by norm_num

/-! ## §2 — the level-3 chain value from an x-coordinate -/

/-- `X(8·R)` for an affine `R` whose x-coordinate is known. -/
theorem X_eight_of_x {R : E389a1.toAffine.Point} {x y : ℚ}
    (h : E389a1.toAffine.Nonsingular x y) (hR : R = Point.some h) :
    X ((((2 : ℤ)) ^ 3) • R)
      = f (f (f x / g x) / g (f x / g x)) / g (f (f x / g x) / g (f x / g x)) := by
  rw [hR]
  exact X_eight_smul h

/-- The naive height of a reduced rational, from r133's exact formula. -/
theorem naiveHeight_of_reduced (a b : ℤ) (hb : b ≠ 0) (hg : Int.gcd a b = 1) :
    naiveHeight ((a : ℚ) / (b : ℚ)) = max a.natAbs b.natAbs := by
  rw [DuplicationHeightBound37a1.naiveHeight_div_int a b hb, hg]
  norm_num

/-! ## §3 — the four chain values -/

/-- `x(8P) = 1169154495/76860289` for `P = (0,0)`. -/
theorem chainP : f (f (f 0 / g 0) / g (f 0 / g 0))
    / g (f (f 0 / g 0) / g (f 0 / g 0))
      = ((1169154495 : ℤ) : ℚ) / ((76860289 : ℤ) : ℚ) := by
  norm_num [f, g]

/-- `x(8Q) = 11776563836346/9521600032681` for `Q = (1,0)`. -/
theorem chainQ : f (f (f 1 / g 1) / g (f 1 / g 1))
    / g (f (f 1 / g 1) / g (f 1 / g 1))
      = ((11776563836346 : ℤ) : ℚ) / ((9521600032681 : ℤ) : ℚ) := by
  norm_num [f, g]

/-- `x(8(P+Q))` for `x(P+Q) = −2`. -/
theorem chainS : f (f (f (-2) / g (-2)) / g (f (-2) / g (-2)))
    / g (f (f (-2) / g (-2)) / g (f (-2) / g (-2)))
      = ((30157844295583882647192303 : ℤ) : ℚ)
          / ((13139629878047776942118401 : ℤ) : ℚ) := by
  norm_num [f, g]

/-- `x(8(P−Q))` for `x(P−Q) = −1`. -/
theorem chainD : f (f (f (-1) / g (-1)) / g (f (-1) / g (-1)))
    / g (f (f (-1) / g (-1)) / g (f (-1) / g (-1)))
      = ((7383740148384742954 : ℤ) : ℚ) / ((7960116832793145801 : ℤ) : ℚ) := by
  norm_num [f, g]

/-! ## §4 — the x-coordinates of `P ± Q` -/

/-- `x(P+Q) = −2`, from mathlib's secant construction. -/
theorem X_sum_eq : X (Point.some P389_nonsingular + Q389) = -2 := by
  rw [Q389, X_add_eq P389_nonsingular Q_nonsingular P_ne_Q_x]
  simp only [xAdd, Affine.slope_of_X_ne P_ne_Q_x, Affine.addX,
    E389a1_a₁, E389a1_a₂]
  norm_num

/-- `x(P−Q) = −1`, from mathlib's secant construction through `−Q`. -/
theorem X_dif_eq : X (Point.some P389_nonsingular - Q389) = -1 := by
  rw [Q389, X_sub_eq P389_nonsingular Q_nonsingular P_ne_Q_x]
  simp only [xAdd, Affine.slope_of_X_ne P_ne_Q_x, Affine.addX,
    negY_eq, E389a1_a₁, E389a1_a₂]
  norm_num

/-! ## §5 — the four height brackets -/

/-- Package: from the affine form and the x-coordinate, the level-3 naive
height. -/
theorem height_from_x {R : E389a1.toAffine.Point} {x y : ℚ}
    (h : E389a1.toAffine.Nonsingular x y) (hR : R = Point.some h)
    {a b : ℤ} (hb : b ≠ 0) (hg : Int.gcd a b = 1)
    (hchain : f (f (f x / g x) / g (f x / g x))
        / g (f (f x / g x) / g (f x / g x)) = ((a : ℚ) / (b : ℚ))) :
    naiveHeight (X ((((2 : ℤ)) ^ 3) • R)) = max a.natAbs b.natAbs := by
  rw [X_eight_of_x h hR, hchain, naiveHeight_of_reduced a b hb hg]

/-! ## §6 — the four brackets, instantiated -/

/-- `ĥ(P) ∈ [0.2851, 0.3755]`. -/
theorem bracket_P :
    (30 : ℝ) * 0.6931471803 / 64 - 7.625 / 192
        ≤ canheight (Point.some P389_nonsingular) ∧
      canheight (Point.some P389_nonsingular)
        ≤ ((30 : ℝ) + 1) * 0.6931471808 / 64 + 7.625 / 192 := by
  have hH := height_from_x P389_nonsingular rfl (a := 1169154495) (b := 76860289)
    (by norm_num) (by norm_num) chainP
  exact canheight_bracket (j := 30) hH (by norm_num) (by norm_num)

/-- `ĥ(Q) ∈ [0.4259, 0.5163]`. -/
theorem bracket_Q :
    (43 : ℝ) * 0.6931471803 / 64 - 7.625 / 192 ≤ canheight Q389 ∧
      canheight Q389 ≤ ((43 : ℝ) + 1) * 0.6931471808 / 64 + 7.625 / 192 := by
  have hH := height_from_x Q_nonsingular (R := Q389) rfl
    (a := 11776563836346) (b := 9521600032681) (by norm_num) (by norm_num) chainQ
  exact canheight_bracket (j := 43) hH (by norm_num) (by norm_num)

/-- `ĥ(P+Q) ∈ [0.8700, 0.9605]`. -/
theorem bracket_S :
    (84 : ℝ) * 0.6931471803 / 64 - 7.625 / 192
        ≤ canheight (Point.some P389_nonsingular + Q389) ∧
      canheight (Point.some P389_nonsingular + Q389)
        ≤ ((84 : ℝ) + 1) * 0.6931471808 / 64 + 7.625 / 192 := by
  have hne : Point.some P389_nonsingular + Q389 ≠ 0 := by
    rw [Q389]; exact add_ne_zero P389_nonsingular Q_nonsingular P_ne_Q_x
  obtain ⟨xs, ys, hs, hPQ⟩ := exists_affine hne
  have hxs : xs = -2 := by rw [← X_sum_eq, hPQ]; rfl
  subst hxs
  have hH := height_from_x hs hPQ (a := 30157844295583882647192303)
    (b := 13139629878047776942118401) (by norm_num) (by norm_num) chainS
  exact canheight_bracket (j := 84) hH (by norm_num) (by norm_num)

/-- `ĥ(P−Q) ∈ [0.6317, 0.7221]`. -/
theorem bracket_D :
    (62 : ℝ) * 0.6931471803 / 64 - 7.625 / 192
        ≤ canheight (Point.some P389_nonsingular - Q389) ∧
      canheight (Point.some P389_nonsingular - Q389)
        ≤ ((62 : ℝ) + 1) * 0.6931471808 / 64 + 7.625 / 192 := by
  have hne : Point.some P389_nonsingular - Q389 ≠ 0 := by
    rw [Q389]; exact sub_ne_zero' P389_nonsingular Q_nonsingular P_ne_Q_x
  obtain ⟨xd, yd, hd, hPQ⟩ := exists_affine hne
  have hxd : xd = -1 := by rw [← X_dif_eq, hPQ]; rfl
  subst hxd
  have hH := height_from_x hd hPQ (a := 7383740148384742954)
    (b := 7960116832793145801) (by norm_num) (by norm_num) chainD
  exact canheight_bracket (j := 62) hH (by norm_num) (by norm_num)

/-! ## §7 — the four non-torsion facts -/

theorem P_nonTorsion' : ¬ IsOfFinAddOrder (Point.some P389_nonsingular) := by
  intro hfin
  have h0 := canheight_of_torsion hfin
  obtain ⟨hlo, _⟩ := bracket_P
  rw [h0] at hlo
  norm_num at hlo

theorem Q_nonTorsion : ¬ IsOfFinAddOrder Q389 := by
  intro hfin
  have h0 := canheight_of_torsion hfin
  obtain ⟨hlo, _⟩ := bracket_Q
  rw [h0] at hlo
  norm_num at hlo

theorem S_nonTorsion : ¬ IsOfFinAddOrder (Point.some P389_nonsingular + Q389) := by
  intro hfin
  have h0 := canheight_of_torsion hfin
  obtain ⟨hlo, _⟩ := bracket_S
  rw [h0] at hlo
  norm_num at hlo

theorem D_nonTorsion : ¬ IsOfFinAddOrder (Point.some P389_nonsingular - Q389) := by
  intro hfin
  have h0 := canheight_of_torsion hfin
  obtain ⟨hlo, _⟩ := bracket_D
  rw [h0] at hlo
  norm_num at hlo

/-! ## §8 — the regulator is positive -/

/-- **★★ `regDet P Q > 0` by interval arithmetic. ★★**
`ĥP·ĥQ ≥ 0.1214` and `⟨P,Q⟩² ≤ 0.0156`. -/
theorem regDet_pos : 0 < regDet (Point.some P389_nonsingular) Q389 := by
  obtain ⟨hPlo, hPhi⟩ := bracket_P
  obtain ⟨hQlo, hQhi⟩ := bracket_Q
  obtain ⟨hSlo, hShi⟩ := bracket_S
  norm_num at hPlo hPhi hQlo hQhi hSlo hShi
  -- the pairing is bracketed
  have hpairlo : (-0.011 : ℝ) ≤ pairing (Point.some P389_nonsingular) Q389 := by
    simp only [pairing]
    linarith [hSlo, hPhi, hQhi]
  have hpairhi : pairing (Point.some P389_nonsingular) Q389 ≤ (0.125 : ℝ) := by
    simp only [pairing]
    linarith [hShi, hPlo, hQlo]
  have hsq : pairing (Point.some P389_nonsingular) Q389 ^ 2 ≤ (0.0157 : ℝ) := by
    nlinarith [hpairlo, hpairhi]
  have hprod : (0.1214 : ℝ)
      ≤ canheight (Point.some P389_nonsingular) * canheight Q389 := by
    nlinarith [hPlo, hQlo, hPhi, hQhi]
  simp only [regDet]
  linarith [hprod, hsq]

/-! ## §9 — ★★★★★ THE FLAG ★★★★★ -/

/-- **★★★★★ `2 ≤ Module.rank ℤ E389a1(ℚ)` ★★★★★**

The Mordell–Weil rank of 389a1 — the smallest-conductor rank-2 elliptic
curve — is at least `2`, on mathlib's literal point group.

`P = (0,0)` and `Q = (1,0)` are independent because their regulator
determinant is positive (§8), which r152 converts into an injective
`ℤ² → E389a1(ℚ)`.

Route, end to end: duplication formula (r143) → two-sided height window
(r145) → Bézout content bound (r148a–c) → secant bridge (r148d) →
root-height lemma (r148e) → quasi-parallelogram (r148f/g, r149) → canonical
height as a limit (r147) → exact parallelogram law (r150) → multiple law
(r151) → independence criterion (r152) → interval machine (r153) → here.

No descent, no formal groups, no Mazur, no Gross–Zagier.  Kernel axioms
only. -/
theorem E389a1_rank_ge_two : 2 ≤ Module.rank ℤ E389a1.toAffine.Point :=
  rank_ge_two_of_regDet_ne_zero P_nonTorsion' Q_nonTorsion S_nonTorsion
    D_nonTorsion (ne_of_gt regDet_pos)

end PrincipiaTractalis.E389a1RankTwo

#print axioms PrincipiaTractalis.E389a1RankTwo.bracket_P
#print axioms PrincipiaTractalis.E389a1RankTwo.bracket_S
#print axioms PrincipiaTractalis.E389a1RankTwo.regDet_pos
#print axioms PrincipiaTractalis.E389a1RankTwo.E389a1_rank_ge_two
