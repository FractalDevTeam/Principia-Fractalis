/-
# PF.QuasiParallelogramCerts5077a1_r157

★★★ 2026-07-30 — W2 OF THE RANK-3 ARC: THE 5077a1 ADDITION FORMS ★★★

The bihomogeneous addition forms for the Buhler–Gross–Zagier rank-3 curve
`y² + y = x³ − 7x + 6`, and the level-1 Cramer certificates that bound their
content.

With `x₁ = a₁/b₁` and `x₂ = a₂/b₂` reduced, `x(P₁+P₂)` and `x(P₁−P₂)` are the
two roots of

  `DD·T² − Sf·T + Pf = 0`

where all three forms are bidegree (2,2) in the pairs `(a₁,b₁)`, `(a₂,b₂)`.
The affine shapes are

  `s(x₁,x₂) = 2x₁²x₂ + 2x₁x₂² − 14x₁ − 14x₂ + 25`
  `p(x₁,x₂) = x₁²x₂² + 14x₁x₂ − 25x₁ − 25x₂ + 49`

derived from `λ₊λ₋ = (x₁²+x₁x₂+x₂²−7)/(x₁−x₂)` and
`λ₊² + λ₋² = (2x₁³+2x₂³−14x₁−14x₂+25)/dd`, using `a₁ = a₂ = 0` (so
`x(P+Q) = λ² − x₁ − x₂`) and `negY x y = −y − 1` (since `a₃ = 1`).

## The structural fact that drives everything

On the diagonal the forms degenerate to r144's duplication pair:

  `Sf a b a b = b · G3 a b`      and      `Pf a b a b = F a b`

(`Sf_diagonal`, `Pf_diagonal` below). Equivalently `s(x,x) = g x` and
`p(x,x) = f x`. So a prime dividing all three forms and not dividing `b₁b₂`
forces `x₁ ≡ x₂`, and then divides both `f` and `g` at that residue, hence
divides `Res(f,g) = 5077²`. That is why the content is controlled by a power
of 5077 — exactly as for 389a1, where `Res(f,g) = 389²`.

## Level 1, at the minimal exponent m = 2

The 3×3 matrix of `(a₁², a₁b₁, b₁²)`-coefficients of `(DD, Sf, Pf)` has
determinant `−R6(a₂,b₂)` with

  `R6 a b = 2a⁶ − 70a⁴b² + 250a³b³ − 490a²b⁴ + 350ab⁵ + 61b⁶`

irreducible over ℚ with content 1. Cramer's rule gives `cert_b1` and
`cert_a1`, and since both carry the *same* form `R6`, coprimality of
`(a₁, b₁)` collapses them to `dvd_R6_of_dvd_forms`.

`m = 2` is optimal: `m = 1` would force a common projective zero of three
quadratic forms. The cofactors here are degree 4 with coefficients at most
350 — much smaller than 389a1's degree-7, ~10⁶ cofactors, because the
level-1 step needs no pairwise resultant route on this curve.

All data sympy-verified in `codex/W2_CERTIFICATES_5077a1.md`: every identity
by `expand() == 0`, plus exact-rational group-law checks that
`x₃+x₄ = Sf/DD` and `x₃x₄ = Pf/DD` on all ten distinct pairs drawn from
`{P, 2P, 3P, 4P, 5P}`, `P = (−2,3)`.

HONEST SCOPE. Level 1 only: the forms, the diagonal identities, the two
Cramer certificates, and the resulting divisibility. NO level-2 control of
`R6` itself (the resultants are `(R6,F) = 5⁴·5077³` and
`(R6,G3) = 2³·5077³`), so NO content bound by a power of 5077 yet, NO size
bounds, NO secant bridge, NO parallelogram law, and NO rank-3 statement.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-30.
-/
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace PrincipiaTractalis.QuasiParallelogramCerts5077a1

/-! ## §1 — the bihomogeneous addition forms (bidegree (2,2)) -/

/-- `DD = (a₁b₂ − a₂b₁)²` — the denominator form of the addition quadratic. -/
def DD (a₁ b₁ a₂ b₂ : ℤ) : ℤ := (a₁ * b₂ - a₂ * b₁) ^ 2

/-- `Sf` — the homogenization of `x(P₁+P₂) + x(P₁−P₂)` times `DD`. -/
def Sf (a₁ b₁ a₂ b₂ : ℤ) : ℤ :=
  2 * a₁ ^ 2 * a₂ * b₂ + 2 * a₁ * a₂ ^ 2 * b₁ - 14 * a₁ * b₁ * b₂ ^ 2
    - 14 * a₂ * b₁ ^ 2 * b₂ + 25 * b₁ ^ 2 * b₂ ^ 2

/-- `Pf` — the homogenization of `x(P₁+P₂) · x(P₁−P₂)` times `DD`. -/
def Pf (a₁ b₁ a₂ b₂ : ℤ) : ℤ :=
  a₁ ^ 2 * a₂ ^ 2 + 14 * a₁ * a₂ * b₁ * b₂ - 25 * a₁ * b₁ * b₂ ^ 2
    - 25 * a₂ * b₁ ^ 2 * b₂ + 49 * b₁ ^ 2 * b₂ ^ 2

/-- The irreducible sextic `R6 = -det M`, `M` the `(a₁², a₁b₁, b₁²)`-coefficient
matrix of `(DD, Sf, Pf)`. -/
def R6 (a b : ℤ) : ℤ :=
  2 * a ^ 6 - 70 * a ^ 4 * b ^ 2 + 250 * a ^ 3 * b ^ 3 - 490 * a ^ 2 * b ^ 4
    + 350 * a * b ^ 5 + 61 * b ^ 6

/-! ## §2 — the diagonal degenerations are r144's duplication pair -/

/-- `Sf a b a b = b · G3 a b` with `G3 a b = 4a³ − 28ab² + 25b³` (r144). -/
theorem Sf_diagonal (a b : ℤ) :
    Sf a b a b = b * (4 * a ^ 3 - 28 * a * b ^ 2 + 25 * b ^ 3) := by
  simp only [Sf]; ring

/-- `Pf a b a b = F a b = a⁴ + 14a²b² − 50ab³ + 49b⁴` (r144). -/
theorem Pf_diagonal (a b : ℤ) :
    Pf a b a b = a ^ 4 + 14 * a ^ 2 * b ^ 2 - 50 * a * b ^ 3 + 49 * b ^ 4 := by
  simp only [Pf]; ring

/-- The forms are symmetric under swapping the two points. -/
theorem DD_swap (a₁ b₁ a₂ b₂ : ℤ) : DD a₂ b₂ a₁ b₁ = DD a₁ b₁ a₂ b₂ := by
  simp only [DD]; ring

theorem Sf_swap (a₁ b₁ a₂ b₂ : ℤ) : Sf a₂ b₂ a₁ b₁ = Sf a₁ b₁ a₂ b₂ := by
  simp only [Sf]; ring

theorem Pf_swap (a₁ b₁ a₂ b₂ : ℤ) : Pf a₂ b₂ a₁ b₁ = Pf a₁ b₁ a₂ b₂ := by
  simp only [Pf]; ring

/-! ## §3 — the level-1 Cramer certificates (sympy-verified, `ring`-certified) -/

/-- **cert_b1**: eliminates `(a₁, b₁)` down to `R6(a₂,b₂)·b₁²`. -/
theorem cert_b1 (a₁ b₁ a₂ b₂ : ℤ) :
    (2 * a₂ ^ 4 - 42 * a₂ ^ 2 * b₂ ^ 2 + 50 * a₂ * b₂ ^ 3) * DD a₁ b₁ a₂ b₂
      + (2 * a₂ ^ 3 * b₂ + 14 * a₂ * b₂ ^ 3 - 25 * b₂ ^ 4) * Sf a₁ b₁ a₂ b₂
      + (-6 * a₂ ^ 2 * b₂ ^ 2 + 14 * b₂ ^ 4) * Pf a₁ b₁ a₂ b₂
      = R6 a₂ b₂ * b₁ ^ 2 := by
  simp only [DD, Sf, Pf, R6]; ring

/-- **cert_a1**: eliminates `(a₁, b₁)` down to `R6(a₂,b₂)·a₁²`. -/
theorem cert_a1 (a₁ b₁ a₂ b₂ : ℤ) :
    (50 * a₂ ^ 3 * b₂ - 294 * a₂ ^ 2 * b₂ ^ 2 + 350 * a₂ * b₂ ^ 3 + 61 * b₂ ^ 4)
        * DD a₁ b₁ a₂ b₂
      + (-14 * a₂ ^ 3 * b₂ + 75 * a₂ ^ 2 * b₂ ^ 2 - 98 * a₂ * b₂ ^ 3)
          * Sf a₁ b₁ a₂ b₂
      + (2 * a₂ ^ 4 - 42 * a₂ ^ 2 * b₂ ^ 2 + 50 * a₂ * b₂ ^ 3) * Pf a₁ b₁ a₂ b₂
      = R6 a₂ b₂ * a₁ ^ 2 := by
  simp only [DD, Sf, Pf, R6]; ring

/-! ## §4 — the gcd consequence: content divides `R6(a₂,b₂)` -/

/-- **The level-1 content bound.** For `(a₁, b₁)` coprime, any common divisor
of the three addition forms divides `R6(a₂, b₂)`.  Both certificates carry the
same `R6`, so `IsCoprime (a₁^2) (b₁^2)` collapses them. -/
theorem dvd_R6_of_dvd_forms {a₁ b₁ a₂ b₂ d : ℤ} (h : IsCoprime a₁ b₁)
    (hDD : d ∣ DD a₁ b₁ a₂ b₂) (hS : d ∣ Sf a₁ b₁ a₂ b₂)
    (hP : d ∣ Pf a₁ b₁ a₂ b₂) : d ∣ R6 a₂ b₂ := by
  have hb : d ∣ R6 a₂ b₂ * b₁ ^ 2 := by
    rw [← cert_b1 a₁ b₁ a₂ b₂]
    exact dvd_add (dvd_add (hDD.mul_left _) (hS.mul_left _)) (hP.mul_left _)
  have ha : d ∣ R6 a₂ b₂ * a₁ ^ 2 := by
    rw [← cert_a1 a₁ b₁ a₂ b₂]
    exact dvd_add (dvd_add (hDD.mul_left _) (hS.mul_left _)) (hP.mul_left _)
  have h22 : IsCoprime (a₁ ^ 2) (b₁ ^ 2) := h.pow
  obtain ⟨u, v, huv⟩ := h22
  have key : R6 a₂ b₂ = u * (R6 a₂ b₂ * a₁ ^ 2) + v * (R6 a₂ b₂ * b₁ ^ 2) := by
    linear_combination (-(R6 a₂ b₂) : ℤ) * huv
  rw [key]
  exact dvd_add (ha.mul_left u) (hb.mul_left v)

/-- By symmetry (`*_swap`), the content also divides `R6(a₁, b₁)`. -/
theorem dvd_R6_of_dvd_forms' {a₁ b₁ a₂ b₂ d : ℤ} (h : IsCoprime a₂ b₂)
    (hDD : d ∣ DD a₁ b₁ a₂ b₂) (hS : d ∣ Sf a₁ b₁ a₂ b₂)
    (hP : d ∣ Pf a₁ b₁ a₂ b₂) : d ∣ R6 a₁ b₁ := by
  refine dvd_R6_of_dvd_forms h ?_ ?_ ?_
  · rw [DD_swap]; exact hDD
  · rw [Sf_swap]; exact hS
  · rw [Pf_swap]; exact hP

end PrincipiaTractalis.QuasiParallelogramCerts5077a1

#print axioms PrincipiaTractalis.QuasiParallelogramCerts5077a1.Sf_diagonal
#print axioms PrincipiaTractalis.QuasiParallelogramCerts5077a1.Pf_diagonal
#print axioms PrincipiaTractalis.QuasiParallelogramCerts5077a1.cert_b1
#print axioms PrincipiaTractalis.QuasiParallelogramCerts5077a1.cert_a1
#print axioms PrincipiaTractalis.QuasiParallelogramCerts5077a1.dvd_R6_of_dvd_forms
#print axioms PrincipiaTractalis.QuasiParallelogramCerts5077a1.dvd_R6_of_dvd_forms'
