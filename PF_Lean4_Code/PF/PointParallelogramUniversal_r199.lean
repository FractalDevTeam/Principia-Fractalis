/-
# PF.PointParallelogramUniversal_r199

★★★ 2026-08-05 — THE QUASI-PARALLELOGRAM AT THE POINT LEVEL, UNIVERSALLY ★★★

r149 proved the two-sided point-level quasi-parallelogram for 389a1 with
hand-built certificates.  This stone proves it for EVERY Weierstrass curve
over ℚ with integer b-invariants: for two affine points with distinct
x-coordinates, and neither point 2-torsion,

  `H(x_P)²·H(x_Q)² ≤ Cpar · H(x(P+Q))·H(x(P−Q))
                   ≤ Cpar·2·CUsec · H(x_P)²·H(x_Q)²`

with `Cpar = (CL² + 1)·(2·CUsec)` — coefficients only.  In logarithmic form
the parallelogram defect is bounded by `log Cpar`.

The chain is exactly the committed pattern, now with zero per-curve input:

* UPPER — r198's `secant_upper_window` applied to `(P, Q)`;
* LOWER — r198's upper bound applied to the pair `(P+Q, P−Q)`, whose sum
  and difference are `2P` and `2Q`, chained with r176's universal
  duplication lower window `H(x)⁴ ≤ CL·H(x(2P))`, lifted to the point
  group by r178's `addX_self_eq_dblQ`.

Unlike the per-curve file (where trivial 2-torsion was a theorem), the
universal statement TAKES `2•P ≠ 0` and `2•Q ≠ 0` as hypotheses — general
curves have rational 2-torsion.  It also takes `Disc ≠ 0` (r176's lower
window needs the discriminant, as it must).

HONEST SCOPE.  A height inequality on the point group of any rational
Weierstrass curve with integer b-invariants and nonzero discriminant.  No
canonical-height parallelogram (that is the limit, a later stone), no rank
claim.

Kernel axioms ⊆ `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-08-05.
-/
import PF.SecantUpperWindow_r198
import PF.DuplicationFormula_r178
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option maxHeartbeats 1600000

namespace PrincipiaTractalis.PointParallelogramUniversal

open PrincipiaTractalis.NaiveHeightQ
open PrincipiaTractalis.SecantUpperWindow
open PrincipiaTractalis.DuplicationBezout
open PrincipiaTractalis.DuplicationSize
open PrincipiaTractalis.DuplicationHeight
open PrincipiaTractalis.DuplicationFormula
open WeierstrassCurve WeierstrassCurve.Affine

variable {W : WeierstrassCurve.Affine ℚ} {B₂ B₄ B₆ B₈ : ℤ}
variable {xP yP xQ yQ : ℚ}

/-! ## §0 — the x-coordinate projection, for every curve -/

/-- The x-coordinate projection on the point group of any Weierstrass
curve over ℚ (r143's per-curve `X`, made generic). -/
def X : W.Point → ℚ
  | .zero => 0
  | @Point.some _ _ _ x _ _ => x

@[simp]
theorem X_some {x y : ℚ} (h : W.Nonsingular x y) : X (Point.some h) = x := rfl

/-- The naive height, cast to ℤ, is r176's `nh`. -/
theorem naiveHeight_eq_nh (x : ℚ) : (naiveHeight x : ℤ) = nh x :=
  naiveHeight_cast x

/-! ## §1 — the sum and difference are affine -/

/-- With distinct x-coordinates, `P + Q` is an affine point. -/
theorem add_ne_zero (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ)
    (hne : xP ≠ xQ) : Point.some hP + Point.some hQ ≠ 0 := by
  rw [Point.add_of_X_ne hne]
  exact fun hc => Point.noConfusion hc

/-- With distinct x-coordinates, `P − Q` is an affine point. -/
theorem sub_ne_zero' (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ)
    (hne : xP ≠ xQ) : Point.some hP - Point.some hQ ≠ 0 := by
  have hneg : -Point.some hQ
      = Point.some ((Affine.nonsingular_neg ..).mpr hQ) := Point.neg_some hQ
  rw [sub_eq_add_neg, hneg, Point.add_of_X_ne hne]
  exact fun hc => Point.noConfusion hc

/-! ## §2 — the X-layer: `x(P ± Q)` is mathlib's `addX ∘ slope` -/

/-- `x(P+Q)` for distinct x-coordinates is the secant `addX ∘ slope`. -/
theorem X_add (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ)
    (hne : xP ≠ xQ) :
    X (Point.some hP + Point.some hQ)
      = W.addX xP xQ (W.slope xP xQ yP yQ) := by
  rw [Point.add_of_X_ne hne, X_some]

/-- `x(P−Q)` is the secant `addX ∘ slope` through `−Q = (x_Q, negY)`. -/
theorem X_sub (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ)
    (hne : xP ≠ xQ) :
    X (Point.some hP - Point.some hQ)
      = W.addX xP xQ (W.slope xP xQ yP (W.negY xQ yQ)) := by
  have hneg : -Point.some hQ
      = Point.some ((Affine.nonsingular_neg ..).mpr hQ) := Point.neg_some hQ
  rw [sub_eq_add_neg, hneg, Point.add_of_X_ne hne, X_some]

/-! ## §3 — group bookkeeping: `(P+Q) ± (P−Q) = 2P, 2Q` -/

/-- The sum of the output pair is `2P`. -/
theorem out_add (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ) :
    (Point.some hP + Point.some hQ) + (Point.some hP - Point.some hQ)
      = (2 : ℕ) • Point.some hP := by
  rw [two_nsmul]
  abel

/-- The difference of the output pair is `2Q`. -/
theorem out_sub (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ) :
    (Point.some hP + Point.some hQ) - (Point.some hP - Point.some hQ)
      = (2 : ℕ) • Point.some hQ := by
  rw [two_nsmul]
  abel

/-- Non-2-torsion at the point level forces `y ≠ negY`. -/
theorem y_ne_negY_of_two_smul_ne_zero (hP : W.Nonsingular xP yP)
    (h2P : (2 : ℕ) • Point.some hP ≠ 0) : yP ≠ W.negY xP yP := by
  rw [two_nsmul] at h2P
  exact fun hy => h2P (Point.add_self_of_Y_eq hy)

/-- `X (P + P) = dblQ` — the universal duplication formula (r178) in
`X`-form, for any curve with the given integer b-invariants. -/
theorem X_dbl (h₂ : W.b₂ = (B₂ : ℚ)) (h₄ : W.b₄ = (B₄ : ℚ))
    (h₆ : W.b₆ = (B₆ : ℚ)) (h₈ : W.b₈ = (B₈ : ℚ))
    (hP : W.Nonsingular xP yP) (hy : yP ≠ W.negY xP yP) :
    X (Point.some hP + Point.some hP) = dblQ B₂ B₄ B₆ B₈ xP := by
  rw [Point.add_self_of_Y_ne hy, X_some]
  exact addX_self_eq_dblQ h₂.symm h₄.symm h₆.symm h₈.symm hP.left hy

/-! ## §4 — equal x-coordinates force equal or opposite points -/

/-- Two affine points of any curve with the same x-coordinate are equal or
negatives of each other (r148g, made generic). -/
theorem eq_or_eq_neg_of_x_eq {x y₁ y₂ : ℚ}
    (h₁ : W.Nonsingular x y₁) (h₂ : W.Nonsingular x y₂) :
    Point.some h₁ = Point.some h₂ ∨ Point.some h₁ = -Point.some h₂ := by
  rcases Affine.Y_eq_of_X_eq h₁.left h₂.left rfl with hy | hy
  · left
    subst hy
    rfl
  · right
    rw [Point.neg_some]
    subst hy
    rfl

/-! ## §5 — `x(P+Q) ≠ x(P−Q)`, from the explicit 2-torsion hypotheses -/

/-- The x-coordinates of `P + Q` and `P − Q` are distinct as long as
neither `P` nor `Q` is 2-torsion.  Equality would force `2Q = 0` or
`2P = 0`. -/
theorem X_add_ne_X_sub (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ)
    (hne : xP ≠ xQ) (h2P : (2 : ℕ) • Point.some hP ≠ 0)
    (h2Q : (2 : ℕ) • Point.some hQ ≠ 0) :
    X (Point.some hP + Point.some hQ)
      ≠ X (Point.some hP - Point.some hQ) := by
  rw [two_nsmul] at h2P h2Q
  intro hEq
  set R := Point.some hP + Point.some hQ with hRdef
  set S := Point.some hP - Point.some hQ with hSdef
  obtain ⟨xr, yr, hr, hRs⟩ : ∃ xr yr, ∃ h : W.Nonsingular xr yr,
      R = Point.some h := by
    rcases R with _ | @⟨xr, yr, hr⟩
    · exact absurd hRdef.symm (add_ne_zero hP hQ hne)
    · exact ⟨xr, yr, hr, rfl⟩
  obtain ⟨xs, ys, hs, hSs⟩ : ∃ xs ys, ∃ h : W.Nonsingular xs ys,
      S = Point.some h := by
    rcases S with _ | @⟨xs, ys, hs⟩
    · exact absurd hSdef.symm (sub_ne_zero' hP hQ hne)
    · exact ⟨xs, ys, hs, rfl⟩
  have hxr : xr = X R := by rw [hRs, X_some]
  have hxs : xs = X S := by rw [hSs, X_some]
  have hxx : xr = xs := by rw [hxr, hxs, hEq]
  subst hxx
  rcases eq_or_eq_neg_of_x_eq hr hs with h | h
  · -- R = S ⟹ 2Q = 0
    have hRS : R = S := by rw [hRs, hSs]; exact h
    have h0 : Point.some hQ + Point.some hQ = 0 := by
      have hsub : R - S = 0 := sub_eq_zero.mpr hRS
      rw [hRdef, hSdef] at hsub
      calc Point.some hQ + Point.some hQ
          = (Point.some hP + Point.some hQ)
            - (Point.some hP - Point.some hQ) := by abel
        _ = 0 := hsub
    exact h2Q h0
  · -- R = −S ⟹ 2P = 0
    have hRS : R = -S := by rw [hRs, hSs]; exact h
    have h0 : Point.some hP + Point.some hP = 0 := by
      have hadd : R + S = 0 := by rw [hRS]; abel
      rw [hRdef, hSdef] at hadd
      calc Point.some hP + Point.some hP
          = (Point.some hP + Point.some hQ)
            + (Point.some hP - Point.some hQ) := by abel
        _ = 0 := hadd
    exact h2P h0

/-! ## §6 — `Ψ ≠ 0` at a non-2-torsion point -/

/-- The duplication denominator does not vanish at a non-2-torsion affine
point: `Ψ = den⁴·ψ` (r178) and `ψ = (y − negY)²` on the curve. -/
theorem Psi_ne_zero (h₂ : W.b₂ = (B₂ : ℚ)) (h₄ : W.b₄ = (B₄ : ℚ))
    (h₆ : W.b₆ = (B₆ : ℚ)) (hP : W.Nonsingular xP yP)
    (hy : yP ≠ W.negY xP yP) :
    Psi B₂ B₄ B₆ xP.num (xP.den : ℤ) ≠ 0 := by
  intro h0
  have hcast := Psi_eq_den_pow_mul (W := W) h₂.symm h₄.symm h₆.symm xP
  rw [h0] at hcast
  have hd : ((xP.den : ℚ)) ≠ 0 := by exact_mod_cast Rat.den_ne_zero xP
  have hpsi0 : psiX W xP ≠ 0 := by
    rw [psiX_eq_sq hP.left]
    exact pow_ne_zero 2 (sub_ne_zero.mpr hy)
  exact (mul_ne_zero (pow_ne_zero 4 hd) hpsi0) (by exact_mod_cast hcast.symm)

/-! ## §7 — the arithmetic core of the lower bound -/

private theorem le_of_sq_le_sq_int {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  nlinarith [h, ha, hb]

/-- The universal quasi-parallelogram constant:
`Cpar = (CL² + 1)·(2·CUsec)`.  The `+1` makes `Cpar ≥ 2·CUsec`
unconditionally, so ONE constant serves both sides of the window. -/
def Cpar (B₂ B₄ B₆ B₈ : ℤ) : ℤ :=
  (CL B₂ B₄ B₆ B₈ ^ 2 + 1) * (2 * CUsec B₂ B₄ B₆ B₈)

theorem Cpar_eq (B₂ B₄ B₆ B₈ : ℤ) :
    Cpar B₂ B₄ B₆ B₈
      = (CL B₂ B₄ B₆ B₈ ^ 2 + 1) * (2 * CUsec B₂ B₄ B₆ B₈) := rfl

/-- **The arithmetic core.**  Two duplication lower windows plus one upper
window on the output pair pin the input heights squared. -/
theorem lower_core {cl k a b r s p q : ℤ}
    (hcl : 0 ≤ cl) (hk : 1 ≤ k)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (hp : 1 ≤ p) (_hq : 1 ≤ q)
    (hdupa : a ^ 4 ≤ cl * p) (hdupb : b ^ 4 ≤ cl * q)
    (hup : p * q ≤ k * (r ^ 2 * s ^ 2)) :
    a ^ 2 * b ^ 2 ≤ cl ^ 2 * k * (r * s) := by
  have ha2 : 1 ≤ a ^ 2 := by nlinarith
  have ha4 : 1 ≤ a ^ 4 := by nlinarith [ha2, sq_nonneg (a ^ 2 - 1)]
  have hcl1 : 1 ≤ cl := by
    by_contra hc
    push_neg at hc
    have hcl0 : cl = 0 := le_antisymm (by omega) hcl
    rw [hcl0, zero_mul] at hdupa
    linarith
  have hcl2 : 1 ≤ cl ^ 2 := by nlinarith
  have hm : 1 ≤ cl ^ 2 * k := by nlinarith [hcl2, hk]
  have s1 : a ^ 4 * b ^ 4 ≤ (cl * p) * (cl * q) :=
    mul_le_mul hdupa hdupb (by positivity)
      (mul_nonneg hcl (by linarith : (0 : ℤ) ≤ p))
  have s3 : (cl * p) * (cl * q) ≤ cl ^ 2 * (k * (r ^ 2 * s ^ 2)) := by
    have h1 : (cl * p) * (cl * q) = cl ^ 2 * (p * q) := by ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left hup (by positivity)
  have s4 : cl ^ 2 * (k * (r ^ 2 * s ^ 2)) ≤ (cl ^ 2 * k * (r * s)) ^ 2 := by
    have e : (cl ^ 2 * k * (r * s)) ^ 2 = (cl ^ 2 * k) ^ 2 * (r ^ 2 * s ^ 2) := by
      ring
    have e2 : cl ^ 2 * (k * (r ^ 2 * s ^ 2))
        = (cl ^ 2 * k) * (r ^ 2 * s ^ 2) := by ring
    rw [e, e2]
    have hmm : cl ^ 2 * k ≤ (cl ^ 2 * k) ^ 2 := by
      nlinarith [hm, sq_nonneg (cl ^ 2 * k - 1)]
    exact mul_le_mul_of_nonneg_right hmm (by positivity)
  have hkey : (a ^ 2 * b ^ 2) ^ 2 ≤ (cl ^ 2 * k * (r * s)) ^ 2 := by
    have e : (a ^ 2 * b ^ 2) ^ 2 = a ^ 4 * b ^ 4 := by ring
    rw [e]
    exact le_trans s1 (le_trans s3 s4)
  exact le_of_sq_le_sq_int (by positivity) (by positivity) hkey

/-! ## §8 — THE CAPSTONE: the two-sided window on the point group -/

/-- **★★★ r199 — THE UNIVERSAL POINT-LEVEL TWO-SIDED QUASI-PARALLELOGRAM ★★★**

On ANY Weierstrass curve over ℚ with integer b-invariants and nonzero
discriminant, for two affine points with distinct x-coordinates, neither
2-torsion:

  `H(x_P)²·H(x_Q)² ≤ Cpar · H(x(P+Q))·H(x(P−Q))`   and
  `H(x(P+Q))·H(x(P−Q)) ≤ 2·CUsec · H(x_P)²·H(x_Q)²`

with `Cpar = (CL²+1)·2·CUsec` from the coefficients alone. -/
theorem point_two_sided (h₂ : W.b₂ = (B₂ : ℚ)) (h₄ : W.b₄ = (B₄ : ℚ))
    (h₆ : W.b₆ = (B₆ : ℚ)) (h₈ : W.b₈ = (B₈ : ℚ))
    (hΔ : Disc B₂ B₄ B₆ B₈ ≠ 0)
    (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ) (hne : xP ≠ xQ)
    (h2P : (2 : ℕ) • Point.some hP ≠ 0)
    (h2Q : (2 : ℕ) • Point.some hQ ≠ 0) :
    (naiveHeight xP : ℤ) ^ 2 * (naiveHeight xQ : ℤ) ^ 2
        ≤ Cpar B₂ B₄ B₆ B₈
          * ((naiveHeight (X (Point.some hP + Point.some hQ)) : ℤ)
              * (naiveHeight (X (Point.some hP - Point.some hQ)) : ℤ)) ∧
    (naiveHeight (X (Point.some hP + Point.some hQ)) : ℤ)
        * (naiveHeight (X (Point.some hP - Point.some hQ)) : ℤ)
      ≤ 2 * CUsec B₂ B₄ B₆ B₈
          * ((naiveHeight xP : ℤ) ^ 2 * (naiveHeight xQ : ℤ) ^ 2) := by
  have hRS_ne : X (Point.some hP + Point.some hQ)
      ≠ X (Point.some hP - Point.some hQ) :=
    X_add_ne_X_sub hP hQ hne h2P h2Q
  have hyP : yP ≠ W.negY xP yP := y_ne_negY_of_two_smul_ne_zero hP h2P
  have hyQ : yQ ≠ W.negY xQ yQ := y_ne_negY_of_two_smul_ne_zero hQ h2Q
  -- the b-relation over ℤ, from mathlib's over ℚ
  have hrel : 4 * B₈ = B₂ * B₆ - B₄ ^ 2 := by
    have h := W.b_relation
    rw [h₂, h₄, h₆, h₈] at h
    exact_mod_cast h
  -- the duplication lower windows (r176), in cast form
  have hΨP := Psi_ne_zero h₂ h₄ h₆ hP hyP
  have hΨQ := Psi_ne_zero h₂ h₄ h₆ hQ hyQ
  have hdupP : (naiveHeight xP : ℤ) ^ 4
      ≤ CL B₂ B₄ B₆ B₈ * (naiveHeight (dblQ B₂ B₄ B₆ B₈ xP) : ℤ) := by
    simp only [naiveHeight_eq_nh]
    exact nh_pow_le_of_disc_ne_zero hrel xP hΨP hΔ
  have hdupQ : (naiveHeight xQ : ℤ) ^ 4
      ≤ CL B₂ B₄ B₆ B₈ * (naiveHeight (dblQ B₂ B₄ B₆ B₈ xQ) : ℤ) := by
    simp only [naiveHeight_eq_nh]
    exact nh_pow_le_of_disc_ne_zero hrel xQ hΨQ hΔ
  -- the doubling x-coordinates at the point level (r178)
  have hX2P : X (Point.some hP + Point.some hP) = dblQ B₂ B₄ B₆ B₈ xP :=
    X_dbl h₂ h₄ h₆ h₈ hP hyP
  have hX2Q : X (Point.some hQ + Point.some hQ) = dblQ B₂ B₄ B₆ B₈ xQ :=
    X_dbl h₂ h₄ h₆ h₈ hQ hyQ
  -- the UPPER half is r198 applied directly
  have hupper : (naiveHeight (X (Point.some hP + Point.some hQ)) : ℤ)
      * (naiveHeight (X (Point.some hP - Point.some hQ)) : ℤ)
      ≤ 2 * CUsec B₂ B₄ B₆ B₈
        * ((naiveHeight xP : ℤ) ^ 2 * (naiveHeight xQ : ℤ) ^ 2) := by
    rw [X_add hP hQ hne, X_sub hP hQ hne]
    exact secant_upper_window h₂ h₄ h₆ h₈ hP.left hQ.left hne
  refine ⟨?_, hupper⟩
  -- the LOWER half: extract the affine data of the output pair
  set R := Point.some hP + Point.some hQ with hRdef
  set S := Point.some hP - Point.some hQ with hSdef
  obtain ⟨xr, yr, hr, hRs⟩ : ∃ xr yr, ∃ h : W.Nonsingular xr yr,
      R = Point.some h := by
    rcases R with _ | @⟨xr, yr, hr⟩
    · exact absurd hRdef.symm (add_ne_zero hP hQ hne)
    · exact ⟨xr, yr, hr, rfl⟩
  obtain ⟨xs, ys, hs, hSs⟩ : ∃ xs ys, ∃ h : W.Nonsingular xs ys,
      S = Point.some h := by
    rcases S with _ | @⟨xs, ys, hs⟩
    · exact absurd hSdef.symm (sub_ne_zero' hP hQ hne)
    · exact ⟨xs, ys, hs, rfl⟩
  have hXr : X R = xr := by rw [hRs, X_some]
  have hXs : X S = xs := by rw [hSs, X_some]
  have hrs : xr ≠ xs := by
    rw [← hXr, ← hXs]
    exact hRS_ne
  -- the output pair realizes (2P, 2Q)
  have hsum : Point.some hr + Point.some hs
      = Point.some hP + Point.some hP := by
    rw [← hRs, ← hSs, hRdef, hSdef]
    abel
  have hdiff : Point.some hr - Point.some hs
      = Point.some hQ + Point.some hQ := by
    rw [← hRs, ← hSs, hRdef, hSdef]
    abel
  have e1 : W.addX xr xs (W.slope xr xs yr ys) = dblQ B₂ B₄ B₆ B₈ xP := by
    rw [← X_add hr hs hrs, hsum, hX2P]
  have e2 : W.addX xr xs (W.slope xr xs yr (W.negY xs ys))
      = dblQ B₂ B₄ B₆ B₈ xQ := by
    rw [← X_sub hr hs hrs, hdiff, hX2Q]
  -- r198's upper window applied to the PAIR (R, S)
  have hpair := secant_upper_window (W := W) h₂ h₄ h₆ h₈ hr.left hs.left hrs
  rw [e1, e2] at hpair
  -- assemble
  have hone : ∀ z : ℚ, (1 : ℤ) ≤ (naiveHeight z : ℤ) := fun z => by
    exact_mod_cast one_le_naiveHeight z
  have hcore := lower_core (CL_nonneg B₂ B₄ B₆ B₈)
    (by linarith [four_le_CUsec B₂ B₄ B₆ B₈] :
      (1 : ℤ) ≤ 2 * CUsec B₂ B₄ B₆ B₈)
    (hone xP) (hone xQ) (hone xr) (hone xs)
    (hone (dblQ B₂ B₄ B₆ B₈ xP)) (hone (dblQ B₂ B₄ B₆ B₈ xQ))
    hdupP hdupQ hpair
  rw [hXr, hXs]
  refine le_trans hcore ?_
  rw [Cpar_eq]
  have h1 : (0 : ℤ) ≤ (naiveHeight xr : ℤ) * (naiveHeight xs : ℤ) := by
    positivity
  have h2 : (0 : ℤ) ≤ 2 * CUsec B₂ B₄ B₆ B₈ := by
    linarith [four_le_CUsec B₂ B₄ B₆ B₈]
  nlinarith [h1, h2, sq_nonneg (CL B₂ B₄ B₆ B₈)]

/-! ## §9 — logarithmic form, ready for the limit -/

/-- The logarithmic naive height on the point group. -/
noncomputable def lognhX (P : W.Point) : ℝ := Real.log (naiveHeight (X P))

/-- **The parallelogram defect is bounded by `log Cpar`**, universally. -/
theorem lognhX_defect_le (h₂ : W.b₂ = (B₂ : ℚ)) (h₄ : W.b₄ = (B₄ : ℚ))
    (h₆ : W.b₆ = (B₆ : ℚ)) (h₈ : W.b₈ = (B₈ : ℚ))
    (hΔ : Disc B₂ B₄ B₆ B₈ ≠ 0)
    (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ) (hne : xP ≠ xQ)
    (h2P : (2 : ℕ) • Point.some hP ≠ 0)
    (h2Q : (2 : ℕ) • Point.some hQ ≠ 0) :
    |lognhX (Point.some hP + Point.some hQ)
        + lognhX (Point.some hP - Point.some hQ)
        - 2 * lognhX (Point.some hP) - 2 * lognhX (Point.some hQ)|
      ≤ Real.log (Cpar B₂ B₄ B₆ B₈) := by
  obtain ⟨hlow, hup⟩ := point_two_sided h₂ h₄ h₆ h₈ hΔ hP hQ hne h2P h2Q
  have hXP : X (Point.some hP) = xP := rfl
  have hXQ : X (Point.some hQ) = xQ := rfl
  set R := Point.some hP + Point.some hQ
  set S := Point.some hP - Point.some hQ
  have p1 : (0 : ℝ) < (naiveHeight (X R) : ℝ) := by
    exact_mod_cast naiveHeight_pos _
  have p2 : (0 : ℝ) < (naiveHeight (X S) : ℝ) := by
    exact_mod_cast naiveHeight_pos _
  have p3 : (0 : ℝ) < (naiveHeight xP : ℝ) := by
    exact_mod_cast naiveHeight_pos _
  have p4 : (0 : ℝ) < (naiveHeight xQ : ℝ) := by
    exact_mod_cast naiveHeight_pos _
  -- the constants
  have hCU2 : (8 : ℤ) ≤ 2 * CUsec B₂ B₄ B₆ B₈ := by
    linarith [four_le_CUsec B₂ B₄ B₆ B₈]
  have hCUR : (0 : ℝ) < 2 * (CUsec B₂ B₄ B₆ B₈ : ℝ) := by
    have h : (8 : ℝ) ≤ 2 * (CUsec B₂ B₄ B₆ B₈ : ℝ) := by exact_mod_cast hCU2
    linarith
  have hCparZ : 2 * CUsec B₂ B₄ B₆ B₈ ≤ Cpar B₂ B₄ B₆ B₈ := by
    rw [Cpar_eq]
    nlinarith [sq_nonneg (CL B₂ B₄ B₆ B₈), hCU2]
  have hCparR : (0 : ℝ) < (Cpar B₂ B₄ B₆ B₈ : ℝ) := by
    have h1 : (0 : ℤ) < Cpar B₂ B₄ B₆ B₈ :=
      lt_of_lt_of_le (by linarith [hCU2]) hCparZ
    exact_mod_cast h1
  -- cast the window to ℝ
  have hupR := (Int.cast_le (R := ℝ)).mpr hup
  have hlowR := (Int.cast_le (R := ℝ)).mpr hlow
  push_cast at hupR hlowR
  have logU := Real.log_le_log (mul_pos p1 p2) hupR
  have logL := Real.log_le_log (mul_pos (pow_pos p3 2) (pow_pos p4 2)) hlowR
  rw [Real.log_mul (ne_of_gt p1) (ne_of_gt p2),
    Real.log_mul (ne_of_gt hCUR)
      (mul_ne_zero (pow_ne_zero 2 (ne_of_gt p3)) (pow_ne_zero 2 (ne_of_gt p4))),
    Real.log_mul (pow_ne_zero 2 (ne_of_gt p3)) (pow_ne_zero 2 (ne_of_gt p4)),
    Real.log_pow, Real.log_pow] at logU
  rw [Real.log_mul (pow_ne_zero 2 (ne_of_gt p3)) (pow_ne_zero 2 (ne_of_gt p4)),
    Real.log_pow, Real.log_pow,
    Real.log_mul (ne_of_gt hCparR) (mul_ne_zero (ne_of_gt p1) (ne_of_gt p2)),
    Real.log_mul (ne_of_gt p1) (ne_of_gt p2)] at logL
  have hlogC : Real.log (2 * (CUsec B₂ B₄ B₆ B₈ : ℝ))
      ≤ Real.log (Cpar B₂ B₄ B₆ B₈ : ℝ) :=
    Real.log_le_log hCUR (by exact_mod_cast hCparZ)
  rw [abs_le]
  constructor
  · unfold lognhX
    rw [hXP, hXQ]
    push_cast at logL ⊢
    linarith [logL]
  · unfold lognhX
    rw [hXP, hXQ]
    push_cast at logU ⊢
    linarith [logU, hlogC]

end PrincipiaTractalis.PointParallelogramUniversal

#print axioms PrincipiaTractalis.PointParallelogramUniversal.X_add
#print axioms PrincipiaTractalis.PointParallelogramUniversal.X_sub
#print axioms PrincipiaTractalis.PointParallelogramUniversal.add_ne_zero
#print axioms PrincipiaTractalis.PointParallelogramUniversal.sub_ne_zero'
#print axioms PrincipiaTractalis.PointParallelogramUniversal.out_add
#print axioms PrincipiaTractalis.PointParallelogramUniversal.out_sub
#print axioms PrincipiaTractalis.PointParallelogramUniversal.eq_or_eq_neg_of_x_eq
#print axioms PrincipiaTractalis.PointParallelogramUniversal.X_add_ne_X_sub
#print axioms PrincipiaTractalis.PointParallelogramUniversal.X_dbl
#print axioms PrincipiaTractalis.PointParallelogramUniversal.Psi_ne_zero
#print axioms PrincipiaTractalis.PointParallelogramUniversal.lower_core
#print axioms PrincipiaTractalis.PointParallelogramUniversal.point_two_sided
#print axioms PrincipiaTractalis.PointParallelogramUniversal.lognhX_defect_le
