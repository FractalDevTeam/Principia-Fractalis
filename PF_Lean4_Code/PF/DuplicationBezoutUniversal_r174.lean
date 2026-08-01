/-
# PF.DuplicationBezoutUniversal_r174

★★★ 2026-07-31 — THE DUPLICATION CONTENT BOUND, FOR EVERY CURVE AT ONCE ★★★

r157–r163 built the quasi-parallelogram layer for 5077a1 by hand: level-1
certificates, a content bound `d ∣ 5⁴·5077⁴` whose extra factor of 5 had to be
shown forced by a Hermite-normal-form argument, then size bounds and the
upper/lower products.  Seven stones, all curve-specific, and r147/r156 needed
the same seven again for 389a1.

**None of it was necessary.**  Write `x = X/Y` in lowest terms and homogenise
the duplication map `x(2P) = φ(x)/ψ(x)`:

  Φ(X,Y) = X⁴ − b₄X²Y² − 2b₆XY³ − b₈Y⁴
  Ψ(X,Y) = 4X³Y + b₂X²Y² + 2b₄XY³ + b₆Y⁴

Then `Res_x(φ, ψ) = Δ²` — a *universal* polynomial identity — and the Sylvester
cofactors give two explicit Bézout witnesses

  F₁·Φ + G₁·Ψ = Δ²·X⁷        F₂·Φ + G₂·Ψ = Δ²·Y⁷

so for coprime X,Y any common divisor of Φ and Ψ divides Δ²·gcd(X⁷,Y⁷) = Δ².
**One lemma, every rational elliptic curve, no per-curve content analysis.**

## What made this tractable

Stating it over `a₁..a₆` gives cofactors of 1853 monomials at degree 18 — too
big to be comfortable.  Φ, Ψ and Δ mention *only* the b-invariants, so working
in `ℤ[b₂,b₄,b₆,b₈]` instead drops that to **168 monomials at degree 9**.

In that free basis `Res` is not literally `Δ²`; the two agree exactly modulo
mathlib's `WeierstrassCurve.b_relation`, `4b₈ = b₂b₆ − b₄²`.  The correction
multiplier is only 8 monomials, so each identity closes with a single
`linear_combination`.

Every coefficient here was produced and re-verified by `codex/gen_r174.py`;
nothing was transcribed by hand.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-31.
-/
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

-- The cofactor defs are a few hundred integer monomials each; elaborating them
-- exceeds the default budget on instance unification alone.
set_option maxHeartbeats 4000000

namespace PrincipiaTractalis.DuplicationBezout

section Defs
variable (b₂ b₄ b₆ b₈ X Y : ℤ)

/-- Numerator of the duplication map, homogenised at `x = X/Y`. -/
def Phi : ℤ := X^4 - X^2 * Y^2 * b₄ - 2 * X * Y^3 * b₆ - Y^4 * b₈

/-- Denominator of the duplication map, homogenised at `x = X/Y`. -/
def Psi : ℤ := 4 * X^3 * Y + X^2 * Y^2 * b₂ + 2 * X * Y^3 * b₄ + Y^4 * b₆

/-- The discriminant, in terms of the b-invariants. -/
def Disc : ℤ := -b₂^2 * b₈ + 9 * b₂ * b₄ * b₆ - 8 * b₄^3 - 27 * b₆^2

/-- Bézout cofactor of `Phi` for the `X⁷` identity. -/
def F1 : ℤ :=
    X^3 * b₂^4 * b₈^2 - 6 * X^3 * b₂^3 * b₄ * b₆ * b₈ + 4 * X^3 * b₂^3 * b₆^3 + 4 * X^3 *
      b₂^2 * b₄^3 * b₈ - 3 * X^3 * b₂^2 * b₄^2 * b₆^2 - 48 * X^3 * b₂^2 * b₄ * b₈^2 + 6 * X^3
      * b₂^2 * b₆^2 * b₈ + 240 * X^3 * b₂ * b₄^2 * b₆ * b₈ - 162 * X^3 * b₂ * b₄ * b₆^3 + 192
      * X^3 * b₂ * b₆ * b₈^2 - 144 * X^3 * b₄^4 * b₈ + 108 * X^3 * b₄^3 * b₆^2 + 384 * X^3 *
      b₄^2 * b₈^2 - 1296 * X^3 * b₄ * b₆^2 * b₈ + 729 * X^3 * b₆^4 - 256 * X^3 * b₈^3 - 4 *
      X^2 * Y * b₂^3 * b₄ * b₈^2 + 24 * X^2 * Y * b₂^2 * b₄^2 * b₆ * b₈ - 16 * X^2 * Y * b₂^2
      * b₄ * b₆^3 + 36 * X^2 * Y * b₂^2 * b₆ * b₈^2 - 16 * X^2 * Y * b₂ * b₄^4 * b₈ + 12 *
      X^2 * Y * b₂ * b₄^3 * b₆^2 + 48 * X^2 * Y * b₂ * b₄^2 * b₈^2 - 240 * X^2 * Y * b₂ * b₄
      * b₆^2 * b₈ + 144 * X^2 * Y * b₂ * b₆^4 - 64 * X^2 * Y * b₂ * b₈^3 + 48 * X^2 * Y *
      b₄^3 * b₆ * b₈ - 36 * X^2 * Y * b₄^2 * b₆^3 + 64 * X^2 * Y * b₄ * b₆ * b₈^2 - 36 * X^2
      * Y * b₆^3 * b₈ + X * Y^2 * b₂^3 * b₆ * b₈^2 - 12 * X * Y^2 * b₂^2 * b₄^2 * b₈^2 - 6 *
      X * Y^2 * b₂^2 * b₄ * b₆^2 * b₈ + 4 * X * Y^2 * b₂^2 * b₆^4 + 76 * X * Y^2 * b₂ * b₄^3
      * b₆ * b₈ - 51 * X * Y^2 * b₂ * b₄^2 * b₆^3 + 64 * X * Y^2 * b₂ * b₄ * b₆ * b₈^2 + 7 *
      X * Y^2 * b₂ * b₆^3 * b₈ - 48 * X * Y^2 * b₄^5 * b₈ + 36 * X * Y^2 * b₄^4 * b₆^2 + 160
      * X * Y^2 * b₄^3 * b₈^2 - 528 * X * Y^2 * b₄^2 * b₆^2 * b₈ + 297 * X * Y^2 * b₄ * b₆^4
      - 128 * X * Y^2 * b₄ * b₈^3 + 16 * X * Y^2 * b₆^2 * b₈^2 - 6 * Y^3 * b₂^2 * b₄ * b₆ *
      b₈^2 + 36 * Y^3 * b₂ * b₄^2 * b₆^2 * b₈ - 24 * Y^3 * b₂ * b₄ * b₆^4 + 40 * Y^3 * b₂ *
      b₆^2 * b₈^2 - 24 * Y^3 * b₄^4 * b₆ * b₈ + 18 * Y^3 * b₄^3 * b₆^3 + 80 * Y^3 * b₄^2 * b₆
      * b₈^2 - 282 * Y^3 * b₄ * b₆^3 * b₈ + 162 * Y^3 * b₆^5 - 64 * Y^3 * b₆ * b₈^3

/-- Bézout cofactor of `Psi` for the `X⁷` identity. -/
def G1 : ℤ :=
    X^3 * b₂^3 * b₄ * b₈^2 - 6 * X^3 * b₂^2 * b₄^2 * b₆ * b₈ + 4 * X^3 * b₂^2 * b₄ * b₆^3 - 9
      * X^3 * b₂^2 * b₆ * b₈^2 + 4 * X^3 * b₂ * b₄^4 * b₈ - 3 * X^3 * b₂ * b₄^3 * b₆^2 - 12 *
      X^3 * b₂ * b₄^2 * b₈^2 + 60 * X^3 * b₂ * b₄ * b₆^2 * b₈ - 36 * X^3 * b₂ * b₆^4 + 16 *
      X^3 * b₂ * b₈^3 - 12 * X^3 * b₄^3 * b₆ * b₈ + 9 * X^3 * b₄^2 * b₆^3 - 16 * X^3 * b₄ *
      b₆ * b₈^2 + 9 * X^3 * b₆^3 * b₈ + 2 * X^2 * Y * b₂^3 * b₆ * b₈^2 - 6 * X^2 * Y * b₂^2 *
      b₄^2 * b₈^2 - 12 * X^2 * Y * b₂^2 * b₄ * b₆^2 * b₈ + 8 * X^2 * Y * b₂^2 * b₆^4 - 4 *
      X^2 * Y * b₂^2 * b₈^3 + 44 * X^2 * Y * b₂ * b₄^3 * b₆ * b₈ - 30 * X^2 * Y * b₂ * b₄^2 *
      b₆^3 + 36 * X^2 * Y * b₂ * b₄ * b₆ * b₈^2 - 4 * X^2 * Y * b₂ * b₆^3 * b₈ - 24 * X^2 * Y
      * b₄^5 * b₈ + 18 * X^2 * Y * b₄^4 * b₆^2 + 56 * X^2 * Y * b₄^3 * b₈^2 - 192 * X^2 * Y *
      b₄^2 * b₆^2 * b₈ + 108 * X^2 * Y * b₄ * b₆^4 - 32 * X^2 * Y * b₄ * b₈^3 - 4 * X^2 * Y *
      b₆^2 * b₈^2 + X * Y^2 * b₂^3 * b₈^3 - 18 * X * Y^2 * b₂^2 * b₄ * b₆ * b₈^2 + 4 * X *
      Y^2 * b₂^2 * b₆^3 * b₈ + 4 * X * Y^2 * b₂ * b₄^3 * b₈^2 + 69 * X * Y^2 * b₂ * b₄^2 *
      b₆^2 * b₈ - 48 * X * Y^2 * b₂ * b₄ * b₆^4 - 16 * X * Y^2 * b₂ * b₄ * b₈^3 + 87 * X *
      Y^2 * b₂ * b₆^2 * b₈^2 - 48 * X * Y^2 * b₄^4 * b₆ * b₈ + 36 * X * Y^2 * b₄^3 * b₆^3 +
      196 * X * Y^2 * b₄^2 * b₆ * b₈^2 - 591 * X * Y^2 * b₄ * b₆^3 * b₈ + 324 * X * Y^2 *
      b₆^5 - 112 * X * Y^2 * b₆ * b₈^3 - 6 * Y^3 * b₂^2 * b₄ * b₈^3 + 36 * Y^3 * b₂ * b₄^2 *
      b₆ * b₈^2 - 24 * Y^3 * b₂ * b₄ * b₆^3 * b₈ + 40 * Y^3 * b₂ * b₆ * b₈^3 - 24 * Y^3 *
      b₄^4 * b₈^2 + 18 * Y^3 * b₄^3 * b₆^2 * b₈ + 80 * Y^3 * b₄^2 * b₈^3 - 282 * Y^3 * b₄ *
      b₆^2 * b₈^2 + 162 * Y^3 * b₆^4 * b₈ - 64 * Y^3 * b₈^4

/-- Bézout cofactor of `Phi` for the `Y⁷` identity. -/
def F2 : ℤ :=
    8 * X^2 * Y * b₂^3 * b₆ - 8 * X^2 * Y * b₂^2 * b₄^2 + 16 * X^2 * Y * b₂^2 * b₈ - 336 *
      X^2 * Y * b₂ * b₄ * b₆ + 288 * X^2 * Y * b₄^3 - 384 * X^2 * Y * b₄ * b₈ + 1296 * X^2 *
      Y * b₆^2 + 2 * X * Y^2 * b₂^4 * b₆ - 2 * X * Y^2 * b₂^3 * b₄^2 - 80 * X * Y^2 * b₂^2 *
      b₄ * b₆ + 72 * X * Y^2 * b₂ * b₄^3 + 32 * X * Y^2 * b₂ * b₄ * b₈ + 360 * X * Y^2 * b₂ *
      b₆^2 - 144 * X * Y^2 * b₄^2 * b₆ - 576 * X * Y^2 * b₆ * b₈ - Y^3 * b₂^4 * b₈ + 5 * Y^3
      * b₂^3 * b₄ * b₆ - 4 * Y^3 * b₂^2 * b₄^3 + 48 * Y^3 * b₂^2 * b₄ * b₈ + Y^3 * b₂^2 *
      b₆^2 - 204 * Y^3 * b₂ * b₄^2 * b₆ - 176 * Y^3 * b₂ * b₆ * b₈ + 144 * Y^3 * b₄^4 - 384 *
      Y^3 * b₄^2 * b₈ + 864 * Y^3 * b₄ * b₆^2 + 256 * Y^3 * b₈^2

/-- Bézout cofactor of `Psi` for the `Y⁷` identity. -/
def G2 : ℤ :=
    -2 * X^3 * b₂^3 * b₆ + 2 * X^3 * b₂^2 * b₄^2 - 4 * X^3 * b₂^2 * b₈ + 84 * X^3 * b₂ * b₄ *
      b₆ - 72 * X^3 * b₄^3 + 96 * X^3 * b₄ * b₈ - 324 * X^3 * b₆^2 + X^2 * Y * b₂^3 * b₈ -
      X^2 * Y * b₂^2 * b₄ * b₆ - 32 * X^2 * Y * b₂ * b₄ * b₈ - 9 * X^2 * Y * b₂ * b₆^2 + 36 *
      X^2 * Y * b₄^2 * b₆ + 144 * X^2 * Y * b₆ * b₈ + 2 * X * Y^2 * b₂^3 * b₄ * b₆ - 2 * X *
      Y^2 * b₂^2 * b₄^3 + 2 * X * Y^2 * b₂^2 * b₄ * b₈ + 2 * X * Y^2 * b₂^2 * b₆^2 - 84 * X *
      Y^2 * b₂ * b₄^2 * b₆ + 8 * X * Y^2 * b₂ * b₆ * b₈ + 72 * X * Y^2 * b₄^4 - 48 * X * Y^2
      * b₄^2 * b₈ + 270 * X * Y^2 * b₄ * b₆^2 - 64 * X * Y^2 * b₈^2 - Y^3 * b₂^3 * b₄ * b₈ +
      4 * Y^3 * b₂^3 * b₆^2 - 3 * Y^3 * b₂^2 * b₄^2 * b₆ + 7 * Y^3 * b₂^2 * b₆ * b₈ + 36 *
      Y^3 * b₂ * b₄^2 * b₈ - 162 * Y^3 * b₂ * b₄ * b₆^2 + 16 * Y^3 * b₂ * b₈^2 + 108 * Y^3 *
      b₄^3 * b₆ - 432 * Y^3 * b₄ * b₆ * b₈ + 729 * Y^3 * b₆^3

end Defs

/-- **Bézout, X-side.**  Holds for every curve, given only mathlib's b-relation. -/
theorem bezout_X (b₂ b₄ b₆ b₈ X Y : ℤ) (hrel : 4 * b₈ = b₂ * b₆ - b₄ ^ 2) :
    F1 b₂ b₄ b₆ b₈ X Y * Phi b₄ b₆ b₈ X Y
      + G1 b₂ b₄ b₆ b₈ X Y * Psi b₂ b₄ b₆ X Y
      = Disc b₂ b₄ b₆ b₈ ^ 2 * X ^ 7 := by
  simp only [F1, G1, Phi, Psi, Disc]
  -- multiplier = (Res - Δ²)/(4b₈ - b₂b₆ + b₄²), inlined: it enters only here,
  -- after `simp`, so a `def` for it would never get unfolded.
  linear_combination (
    -12 * b₂^2 * b₄ * b₈ - 4 * b₂^2 * b₆^2 + 80 * b₂ * b₄^2 * b₆ + 32 * b₂ * b₆ * b₈ - 64 *
      b₄^4 + 112 * b₄^2 * b₈ - 324 * b₄ * b₆^2 - 64 * b₈^2) * X ^ 7 * hrel

/-- **Bézout, Y-side.** -/
theorem bezout_Y (b₂ b₄ b₆ b₈ X Y : ℤ) (hrel : 4 * b₈ = b₂ * b₆ - b₄ ^ 2) :
    F2 b₂ b₄ b₆ b₈ X Y * Phi b₄ b₆ b₈ X Y
      + G2 b₂ b₄ b₆ b₈ X Y * Psi b₂ b₄ b₆ X Y
      = Disc b₂ b₄ b₆ b₈ ^ 2 * Y ^ 7 := by
  simp only [F2, G2, Phi, Psi, Disc]
  linear_combination (
    -12 * b₂^2 * b₄ * b₈ - 4 * b₂^2 * b₆^2 + 80 * b₂ * b₄^2 * b₆ + 32 * b₂ * b₆ * b₈ - 64 *
      b₄^4 + 112 * b₄^2 * b₈ - 324 * b₄ * b₆^2 - 64 * b₈^2) * Y ^ 7 * hrel

/-- **THE CONTENT BOUND, UNIFORMLY IN THE CURVE.**  For `x = X/Y` in lowest
terms, the numerator and denominator of `x(2P)` share no factor beyond `Δ²`.

This is what r158 proved for 5077a1 alone, at the cost of a Hermite-normal-form
argument to show the stray factor of 5 was forced.  Here it is free. -/
theorem dvd_disc_sq_of_isCoprime (b₂ b₄ b₆ b₈ : ℤ)
    (hrel : 4 * b₈ = b₂ * b₆ - b₄ ^ 2) {X Y d : ℤ}
    (hXY : IsCoprime X Y) (hP : d ∣ Phi b₄ b₆ b₈ X Y) (hQ : d ∣ Psi b₂ b₄ b₆ X Y) :
    d ∣ Disc b₂ b₄ b₆ b₈ ^ 2 := by
  obtain ⟨s, u, hsu⟩ : IsCoprime (X ^ 7) (Y ^ 7) := hXY.pow
  have hX : d ∣ Disc b₂ b₄ b₆ b₈ ^ 2 * X ^ 7 := by
    rw [← bezout_X b₂ b₄ b₆ b₈ X Y hrel]; exact dvd_add (hP.mul_left _) (hQ.mul_left _)
  have hY : d ∣ Disc b₂ b₄ b₆ b₈ ^ 2 * Y ^ 7 := by
    rw [← bezout_Y b₂ b₄ b₆ b₈ X Y hrel]; exact dvd_add (hP.mul_left _) (hQ.mul_left _)
  have : Disc b₂ b₄ b₆ b₈ ^ 2
      = s * (Disc b₂ b₄ b₆ b₈ ^ 2 * X ^ 7) + u * (Disc b₂ b₄ b₆ b₈ ^ 2 * Y ^ 7) := by
    linear_combination (Disc b₂ b₄ b₆ b₈ ^ 2) * hsu.symm
  rw [this]
  exact dvd_add (hX.mul_left _) (hY.mul_left _)


/-! ### Validation against the two curves already built by hand.

Not decoration: these are the exact curves whose content bounds cost r158 (and
its 389a1 predecessor) a hand-built Hermite-normal-form argument each.  If the
universal statement did not specialise to them, it would be wrong. -/

section Validation

/-- 389a1: `(a₁,a₂,a₃,a₄,a₆) = (0,1,1,-2,0)`, giving `(b₂,b₄,b₆,b₈) = (4,-4,1,-3)`. -/
theorem b_relation_389a1 : (4 : ℤ) * (-3) = 4 * 1 - (-4) ^ 2 := by decide

theorem disc_389a1 : Disc 4 (-4) 1 (-3) = 389 := by decide

/-- The content bound for 389a1 is `Δ² = 389² = 151321`, with no curve-specific
argument of any kind. -/
theorem content_389a1 {X Y d : ℤ} (hXY : IsCoprime X Y)
    (hP : d ∣ Phi (-4) 1 (-3) X Y) (hQ : d ∣ Psi 4 (-4) 1 X Y) :
    d ∣ 151321 := by
  have := dvd_disc_sq_of_isCoprime 4 (-4) 1 (-3) b_relation_389a1 hXY hP hQ
  rwa [disc_389a1] at this

/-- 5077a1: `(a₁,a₂,a₃,a₄,a₆) = (0,0,1,-7,6)`, giving `(b₂,b₄,b₆,b₈) = (0,-14,25,-49)`. -/
theorem b_relation_5077a1 : (4 : ℤ) * (-49) = 0 * 25 - (-14) ^ 2 := by decide

theorem disc_5077a1 : Disc 0 (-14) 25 (-49) = 5077 := by decide

/-- The content bound for 5077a1 is `Δ² = 5077² = 25775929`.  Compare r158,
which proved `d ∣ 5⁴·5077⁴` and needed a Hermite-normal-form argument to show
the stray factor of 5 was forced. -/
theorem content_5077a1 {X Y d : ℤ} (hXY : IsCoprime X Y)
    (hP : d ∣ Phi (-14) 25 (-49) X Y) (hQ : d ∣ Psi 0 (-14) 25 X Y) :
    d ∣ 25775929 := by
  have := dvd_disc_sq_of_isCoprime 0 (-14) 25 (-49) b_relation_5077a1 hXY hP hQ
  rwa [disc_5077a1] at this

end Validation

end PrincipiaTractalis.DuplicationBezout

#print axioms PrincipiaTractalis.DuplicationBezout.bezout_X
#print axioms PrincipiaTractalis.DuplicationBezout.bezout_Y
#print axioms PrincipiaTractalis.DuplicationBezout.dvd_disc_sq_of_isCoprime
#print axioms PrincipiaTractalis.DuplicationBezout.content_389a1
#print axioms PrincipiaTractalis.DuplicationBezout.content_5077a1
