/-
# PF.QuasiParallelogramLower5077a1_r162

★★★ 2026-07-30 — r162: THE LOWER QUASI-PARALLELOGRAM BOUND FOR 5077a1 ★★★

The other half of W2 for the rank-3 curve — and it needs **no new
certificates**.  Apply r161's *upper* bound to the pair `(R, S) = (P+Q, P−Q)`,
whose sum and difference are `2P` and `2Q`, then feed in r144's duplication
*lower* bound:

  `h(x_P)⁴·h(x_Q)⁴ / 105754² ≤ h(x(2P))·h(x(2Q)) ≤ 228·h(x_R)²·h(x_S)²`

so `(h(x_P)²h(x_Q)²)² ≤ 105754²·228·(h(x_R)h(x_S))²`, and since
`105754² · 228 = 2 549 931 141 648 ≤ 2 863 080 580 096 = (105754·16)²`,
taking square roots in ℕ gives

    `h(x_P)² · h(x_Q)² ≤ 1692064 · h(x_R) · h(x_S)`.

The constant is `1692064 = 105754 · 16`, and the numeric step reduces to
`228 ≤ 256 = 16²` — exactly parallel to 389a1, where `10368 = 1728 · 6` and
the step was `34 ≤ 36`.  Choosing `m = 16` rather than the true ceiling
`⌈105754·√228⌉ = 1596851` costs about 6% in the constant and buys a
`norm_num` goal that is a one-digit comparison.

Supporting facts proved here (both reusable):

* `add_self_ne_zero` — no rational affine point of 5077a1 is 2-torsion at the
  *point* level: `P + P ≠ 0`, straight from r144's `dbl_x`, which always lands
  in the `some` branch.
* `eq_or_eq_neg_of_x_eq` — two affine points with equal x-coordinate are equal
  or negatives (mathlib's `Y_eq_of_X_eq` + `neg_some`).

Together these give `R, S` affine with `x_R ≠ x_S`, the hypotheses r161 needs
— so the lower bound really is free.

## What this completes

W2 is now closed for 5077a1 on both sides: the height product of
`(x(P+Q), x(P−Q))` is pinned between explicit constants,

  `h(x₁)²h(x₂)² / 1692064 ≤ h(x_R)h(x_S) ≤ 228 · h(x₁)²h(x₂)²`

(`two_sided`).  This is precisely the input a canonical-height limit consumes,
where the constants disappear under `4ⁿ`-scaling and the parallelogram law
becomes exact.

HONEST SCOPE.  A height inequality on naive heights.  NO canonical-height
statement — the limit is a separate stone, the analogue of r149/r150 — and no
rank claim.  In particular this does **not** prove the parallelogram law for
`ĥ` on 5077a1, and it says nothing about the 3×3 independence step, which
remains open.

Kernel axioms ⊆ `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-30.
-/
import PF.QuasiParallelogramUpper5077a1_r161

namespace PrincipiaTractalis.QuasiParallelogramLower5077a1

open PrincipiaTractalis.NaiveHeightQ
open PrincipiaTractalis.E5077a1RankOne
open PrincipiaTractalis.SecantBridge5077a1
open PrincipiaTractalis.QuasiParallelogramUpper5077a1
open WeierstrassCurve WeierstrassCurve.Affine

/-! ## §0 — the curve equation in usable form -/

/-- Extract the plain Weierstrass relation from a `Nonsingular` hypothesis. -/
theorem eqn_of_nonsingular {x y : ℚ} (h : E5077a1.toAffine.Nonsingular x y) :
    y ^ 2 + y = x ^ 3 - 7 * x + 6 := by
  have h' := h.left
  rw [Affine.equation_iff] at h'
  simp only [E5077a1_a₁, E5077a1_a₂, E5077a1_a₃, E5077a1_a₄, E5077a1_a₆] at h'
  linarith [h']

/-! ## §1 — the arithmetic core -/

/-- `a² ≤ b² → a ≤ b` in `ℕ`. -/
private theorem le_of_sq_le_sq {a b : ℕ} (h : a * a ≤ b * b) : a ≤ b := by
  by_contra hc
  push_neg at hc
  have : b * b < a * a := Nat.mul_lt_mul_of_lt_of_le hc (le_of_lt hc) (by omega)
  omega

/-- **The arithmetic core of the lower bound.**  From the two duplication
lower bounds and one application of the upper bound, the product of the
input heights squared is controlled by the product of the output heights. -/
theorem lower_from_bounds {hP hQ h2P h2Q hR hS : ℕ}
    (hdupP : hP ^ 4 ≤ 105754 * h2P) (hdupQ : hQ ^ 4 ≤ 105754 * h2Q)
    (hup : h2P * h2Q ≤ 228 * hR ^ 2 * hS ^ 2) :
    hP ^ 2 * hQ ^ 2 ≤ 1692064 * (hR * hS) := by
  have step1 : hP ^ 4 * hQ ^ 4 ≤ (105754 * h2P) * (105754 * h2Q) :=
    Nat.mul_le_mul hdupP hdupQ
  have step2 : (105754 * h2P) * (105754 * h2Q) = 105754 ^ 2 * (h2P * h2Q) := by ring
  have step3 : 105754 ^ 2 * (h2P * h2Q) ≤ 105754 ^ 2 * (228 * hR ^ 2 * hS ^ 2) :=
    Nat.mul_le_mul_left _ hup
  have step4 : 105754 ^ 2 * (228 * hR ^ 2 * hS ^ 2)
      ≤ (1692064 * (hR * hS)) * (1692064 * (hR * hS)) := by
    have e : (1692064 * (hR * hS)) * (1692064 * (hR * hS))
        = 2863080580096 * (hR ^ 2 * hS ^ 2) := by ring
    have e2 : 105754 ^ 2 * (228 * hR ^ 2 * hS ^ 2)
        = 2549931141648 * (hR ^ 2 * hS ^ 2) := by ring
    rw [e, e2]
    exact Nat.mul_le_mul_right _ (by norm_num)
  have key : (hP ^ 2 * hQ ^ 2) * (hP ^ 2 * hQ ^ 2)
      ≤ (1692064 * (hR * hS)) * (1692064 * (hR * hS)) := by
    have e : (hP ^ 2 * hQ ^ 2) * (hP ^ 2 * hQ ^ 2) = hP ^ 4 * hQ ^ 4 := by ring
    rw [e]
    calc hP ^ 4 * hQ ^ 4 ≤ (105754 * h2P) * (105754 * h2Q) := step1
      _ = 105754 ^ 2 * (h2P * h2Q) := step2
      _ ≤ 105754 ^ 2 * (228 * hR ^ 2 * hS ^ 2) := step3
      _ ≤ (1692064 * (hR * hS)) * (1692064 * (hR * hS)) := step4
  exact le_of_sq_le_sq key

/-! ## §2 — no rational 2-torsion, at the point level -/

/-- **`P + P ≠ 0` for every rational affine point of 5077a1.**  `dbl_x` always
lands in the `some` branch, and `some ≠ zero`. -/
theorem add_self_ne_zero {x y : ℚ} (h : E5077a1.toAffine.Nonsingular x y) :
    Point.some h + Point.some h ≠ 0 := by
  obtain ⟨x', y', h', hadd, _⟩ := dbl_x h
  rw [hadd]
  exact fun hc => Point.noConfusion hc

/-! ## §3 — equal x-coordinates force equal or opposite points -/

/-- Two rational affine points of 5077a1 with the same x-coordinate are equal
or negatives of each other. -/
theorem eq_or_eq_neg_of_x_eq {x y₁ y₂ : ℚ}
    (h₁ : E5077a1.toAffine.Nonsingular x y₁) (h₂ : E5077a1.toAffine.Nonsingular x y₂) :
    Point.some h₁ = Point.some h₂ ∨ Point.some h₁ = -Point.some h₂ := by
  rcases Affine.Y_eq_of_X_eq h₁.left h₂.left rfl with hy | hy
  · left
    subst hy
    rfl
  · right
    rw [Point.neg_some]
    subst hy
    rfl

/-! ## §4 — the sum and difference are affine with distinct x -/

section Pair

variable {xP yP xQ yQ : ℚ}

/-- `x(P+Q)` for two affine points with distinct x is mathlib's secant
`xAdd`. -/
theorem X_add_eq (hP : E5077a1.toAffine.Nonsingular xP yP)
    (hQ : E5077a1.toAffine.Nonsingular xQ yQ) (hne : xP ≠ xQ) :
    X (Point.some hP + Point.some hQ) = xAdd xP xQ yP yQ := by
  rw [Point.add_of_X_ne hne]
  rfl

/-- `x(P−Q)` is the secant `xAdd` through `−Q`. -/
theorem X_sub_eq (hP : E5077a1.toAffine.Nonsingular xP yP)
    (hQ : E5077a1.toAffine.Nonsingular xQ yQ) (hne : xP ≠ xQ) :
    X (Point.some hP - Point.some hQ)
      = xAdd xP xQ yP (E5077a1.toAffine.negY xQ yQ) := by
  have hneg : -Point.some hQ
      = Point.some ((Affine.nonsingular_neg ..).mpr hQ) := Point.neg_some hQ
  rw [sub_eq_add_neg, hneg, Point.add_of_X_ne hne]
  rfl

end Pair

/-! ## §5 — THE CAPSTONE: the lower quasi-parallelogram bound -/

/-- **★★★ r148g — THE LOWER QUASI-PARALLELOGRAM BOUND ★★★**

For two rational affine points of 5077a1 with distinct x-coordinates:

  `h(x_P)² · h(x_Q)² ≤ 1692064 · h(x(P+Q)) · h(x(P−Q))`.

Proved by applying r148f's *upper* bound to the pair `(P+Q, P−Q)` — whose
sum and difference are `2P` and `2Q` — and combining with r143's duplication
lower bound.  No new certificates were needed.
(`_hP`, `_hQ` are carried for interface symmetry — the duplication bound is
unconditional on ℚ, so they are not needed in the proof.) -/
theorem height_prod_lower {xP yP xQ yQ xR yR xS yS : ℚ}
    (_hP : E5077a1.toAffine.Nonsingular xP yP)
    (_hQ : E5077a1.toAffine.Nonsingular xQ yQ)
    (hR : E5077a1.toAffine.Nonsingular xR yR)
    (hS : E5077a1.toAffine.Nonsingular xS yS)
    (hRS : xR ≠ xS)
    -- the pair (R,S) realizes (P+Q, P−Q):
    (hsumP : xAdd xR xS yR yS = f xP / g xP)
    (hsumQ : xAdd xR xS yR (E5077a1.toAffine.negY xS yS) = f xQ / g xQ) :
    naiveHeight xP ^ 2 * naiveHeight xQ ^ 2
      ≤ 1692064 * (naiveHeight xR * naiveHeight xS) := by
  -- the duplication lower bounds (r143)
  have hdupP : naiveHeight xP ^ 4 ≤ 105754 * naiveHeight (f xP / g xP) :=
    duplication_height_bound xP
  have hdupQ : naiveHeight xQ ^ 4 ≤ 105754 * naiveHeight (f xQ / g xQ) :=
    duplication_height_bound xQ
  -- the upper bound (r148f) applied to the pair (R, S)
  have hup0 := height_prod_upper (x₁ := xR) (x₂ := xS) (y₁ := yR) (y₂ := yS)
    hRS (eqn_of_nonsingular hR) (eqn_of_nonsingular hS)
  -- rewrite the two outputs as x(2P) and x(2Q)
  rw [hsumP, hsumQ] at hup0
  exact lower_from_bounds hdupP hdupQ hup0

/-- **The two-sided quasi-parallelogram, packaged.**  Combining r148f and
r148g: for the input pair `(P₁,P₂)` and the output pair `(R,S)` realizing
`(P₁+P₂, P₁−P₂)`, the height product is pinned within explicit constants:

  `h(x₁)²h(x₂)²/1692064 ≤ h(x_R)h(x_S)`  and  `h(x_R)h(x_S) ≤ 228h(x₁)²h(x₂)²`.

This is the input to r149's canonical-height limit, where the constants
disappear under `4ⁿ`-scaling and the parallelogram becomes exact. -/
theorem two_sided {x₁ y₁ x₂ y₂ xR yR xS yS : ℚ}
    (h₁ : E5077a1.toAffine.Nonsingular x₁ y₁)
    (h₂ : E5077a1.toAffine.Nonsingular x₂ y₂)
    (hR : E5077a1.toAffine.Nonsingular xR yR)
    (hS : E5077a1.toAffine.Nonsingular xS yS)
    (hx : x₁ ≠ x₂) (hRS : xR ≠ xS)
    (hxR : xR = xAdd x₁ x₂ y₁ y₂)
    (hxS : xS = xAdd x₁ x₂ y₁ (E5077a1.toAffine.negY x₂ y₂))
    (hsumP : xAdd xR xS yR yS = f x₁ / g x₁)
    (hsumQ : xAdd xR xS yR (E5077a1.toAffine.negY xS yS) = f x₂ / g x₂) :
    naiveHeight x₁ ^ 2 * naiveHeight x₂ ^ 2
        ≤ 1692064 * (naiveHeight xR * naiveHeight xS) ∧
    naiveHeight xR * naiveHeight xS
        ≤ 228 * naiveHeight x₁ ^ 2 * naiveHeight x₂ ^ 2 := by
  refine ⟨height_prod_lower h₁ h₂ hR hS hRS hsumP hsumQ, ?_⟩
  rw [hxR, hxS]
  exact height_prod_upper hx (eqn_of_nonsingular h₁) (eqn_of_nonsingular h₂)

end PrincipiaTractalis.QuasiParallelogramLower5077a1

#print axioms PrincipiaTractalis.QuasiParallelogramLower5077a1.lower_from_bounds
#print axioms PrincipiaTractalis.QuasiParallelogramLower5077a1.add_self_ne_zero
#print axioms PrincipiaTractalis.QuasiParallelogramLower5077a1.eq_or_eq_neg_of_x_eq
#print axioms PrincipiaTractalis.QuasiParallelogramLower5077a1.X_add_eq
#print axioms PrincipiaTractalis.QuasiParallelogramLower5077a1.X_sub_eq
#print axioms PrincipiaTractalis.QuasiParallelogramLower5077a1.height_prod_lower
#print axioms PrincipiaTractalis.QuasiParallelogramLower5077a1.two_sided
