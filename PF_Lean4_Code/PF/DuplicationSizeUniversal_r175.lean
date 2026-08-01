/-
# PF.DuplicationSizeUniversal_r175

★★★ 2026-07-31 — THE SIZE HALF OF κ_E, ALSO FOR EVERY CURVE ★★★

r174 gave the *content* half of the universal duplication window: for `x = X/Y`
in lowest terms, `gcd(Φ(X,Y), Ψ(X,Y)) ∣ Δ²`, uniformly in the curve.  This file
gives the *size* half, again with no curve-specific input:

  **upper**  `max |Φ| |Ψ| ≤ CU · M⁴`
  **lower**  `Δ² · M⁴ ≤ CL · max |Φ| |Ψ|`          where `M = max |X| |Y|`

`CU` is the obvious coefficient sum.  `CL` comes from r174's own Bézout pair:
`Δ²X⁷ = F₁Φ + G₁Ψ` and `Δ²Y⁷ = F₂Φ + G₂Ψ`, and each cofactor is a binary cubic,
so `Δ²M⁷ ≤ CL·M³·max |Φ| |Ψ|`; cancelling `M³` gives the bound.  The same
identity that killed the content analysis kills the archimedean one.

Together with r174 these are exactly the ingredients of `HeightWindow` (r171),
which r173 showed is all the canonical height ever needed.

## What κ this actually gives, honestly

Chaining the two with r174's `gcd ∣ Δ²`:

  `H(x(2P)) = max|Φ||Ψ| / gcd ≤ CU · M⁴`      (since `gcd ≥ 1`)
  `H(x(2P)) ≥ max|Φ||Ψ| / Δ² ≥ M⁴ / CL`       (the `Δ²` cancels)

so `κ_E = max(CU, CL)`.  Measured:

| curve  | CU  | CL          | universal κ | hand-built κ |
|--------|-----|-------------|-------------|--------------|
| 389a1  | 17  | 672192      | 672192      | 1728         |
| 5077a1 | 114 | 536913058   | 536913058   | 105754       |

**The universal κ is worse than the hand-built one**, by ~400× and ~5000×.
That is the honest price of uniformity: `CL` sums absolute values of the Bézout
cofactors, which is far from tight.  It matters downstream — the torsion
enumeration bound is `κ^(1/3)`, so 389a1 goes from 12 candidates-wide to ~88.

Two things make it worth having anyway.  The `CU` side *is* sharp: 17 and 114
are exactly the size constants r159 and its 389a1 predecessor derived by hand.
And a κ that is automatic for every curve beats a sharp κ that costs seven
stones — sharpening a specific curve later is optional, deriving it at all is
not.

Every coefficient produced and re-verified by `codex/gen_r175.py`.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-31.
-/
import PF.DuplicationBezoutUniversal_r174
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity

set_option maxHeartbeats 4000000

namespace PrincipiaTractalis.DuplicationSize

open PrincipiaTractalis.DuplicationBezout

/-! ### Binary form bounds -/

/-- A binary quartic is bounded by its coefficient sum times `max |X| |Y| ^ 4`. -/
theorem abs_form4_le (c₀ c₁ c₂ c₃ c₄ X Y : ℤ) :
    |c₀ * X ^ 4 + c₁ * X ^ 3 * Y + c₂ * X ^ 2 * Y ^ 2 + c₃ * X * Y ^ 3 + c₄ * Y ^ 4|
      ≤ (|c₀| + |c₁| + |c₂| + |c₃| + |c₄|) * max |X| |Y| ^ 4 := by
  have hX : |X| ≤ max |X| |Y| := le_max_left _ _
  have hY : |Y| ≤ max |Y| |X| := le_max_left _ _
  rw [max_comm |Y| |X|] at hY
  have h0 : (0 : ℤ) ≤ |X| := abs_nonneg _
  have h1 : (0 : ℤ) ≤ |Y| := abs_nonneg _
  have hM0 : (0 : ℤ) ≤ max |X| |Y| := le_trans h0 (le_max_left _ _)
  calc |c₀ * X ^ 4 + c₁ * X ^ 3 * Y + c₂ * X ^ 2 * Y ^ 2 + c₃ * X * Y ^ 3 + c₄ * Y ^ 4|
      ≤ |c₀ * X ^ 4| + |c₁ * X ^ 3 * Y| + |c₂ * X ^ 2 * Y ^ 2| + |c₃ * X * Y ^ 3|
          + |c₄ * Y ^ 4| := by
        refine (abs_add _ _).trans (add_le_add_right ((abs_add _ _).trans
          (add_le_add_right ((abs_add _ _).trans
            (add_le_add_right (abs_add _ _) _)) _)) _)
    _ = |c₀| * |X| ^ 4 + |c₁| * |X| ^ 3 * |Y| + |c₂| * |X| ^ 2 * |Y| ^ 2
          + |c₃| * |X| * |Y| ^ 3 + |c₄| * |Y| ^ 4 := by
        simp only [abs_mul, abs_pow]
    _ ≤ (|c₀| + |c₁| + |c₂| + |c₃| + |c₄|) * max |X| |Y| ^ 4 := by
        have e : (|c₀| + |c₁| + |c₂| + |c₃| + |c₄|) * max |X| |Y| ^ 4
            = |c₀| * max |X| |Y| ^ 4 + |c₁| * max |X| |Y| ^ 3 * max |X| |Y|
              + |c₂| * max |X| |Y| ^ 2 * max |X| |Y| ^ 2
              + |c₃| * max |X| |Y| * max |X| |Y| ^ 3 + |c₄| * max |X| |Y| ^ 4 := by ring
        rw [e]; gcongr <;>
          first
            | assumption
            | positivity
            | exact mul_nonneg (abs_nonneg _) (pow_nonneg hM0 _)

/-- A binary cubic is bounded by its coefficient sum times `max |X| |Y| ^ 3`. -/
theorem abs_form3_le (c₀ c₁ c₂ c₃ X Y : ℤ) :
    |c₀ * X ^ 3 + c₁ * X ^ 2 * Y + c₂ * X * Y ^ 2 + c₃ * Y ^ 3|
      ≤ (|c₀| + |c₁| + |c₂| + |c₃|) * max |X| |Y| ^ 3 := by
  have hX : |X| ≤ max |X| |Y| := le_max_left _ _
  have hY : |Y| ≤ max |Y| |X| := le_max_left _ _
  rw [max_comm |Y| |X|] at hY
  have h0 : (0 : ℤ) ≤ |X| := abs_nonneg _
  have h1 : (0 : ℤ) ≤ |Y| := abs_nonneg _
  have hM0 : (0 : ℤ) ≤ max |X| |Y| := le_trans h0 (le_max_left _ _)
  calc |c₀ * X ^ 3 + c₁ * X ^ 2 * Y + c₂ * X * Y ^ 2 + c₃ * Y ^ 3|
      ≤ |c₀ * X ^ 3| + |c₁ * X ^ 2 * Y| + |c₂ * X * Y ^ 2| + |c₃ * Y ^ 3| := by
        refine (abs_add _ _).trans (add_le_add_right ((abs_add _ _).trans
          (add_le_add_right (abs_add _ _) _)) _)
    _ = |c₀| * |X| ^ 3 + |c₁| * |X| ^ 2 * |Y| + |c₂| * |X| * |Y| ^ 2
          + |c₃| * |Y| ^ 3 := by simp only [abs_mul, abs_pow]
    _ ≤ (|c₀| + |c₁| + |c₂| + |c₃|) * max |X| |Y| ^ 3 := by
        have e : (|c₀| + |c₁| + |c₂| + |c₃|) * max |X| |Y| ^ 3
            = |c₀| * max |X| |Y| ^ 3 + |c₁| * max |X| |Y| ^ 2 * max |X| |Y|
              + |c₂| * max |X| |Y| * max |X| |Y| ^ 2 + |c₃| * max |X| |Y| ^ 3 := by ring
        rw [e]; gcongr <;>
          first
            | assumption
            | positivity
            | exact mul_nonneg (abs_nonneg _) (pow_nonneg hM0 _)

/-- Coefficient of `X^3 Y^0` in `F1`. -/
def cF10 (b₂ b₄ b₆ b₈ : ℤ) : ℤ :=
    b₂^4 * b₈^2 - 6 * b₂^3 * b₄ * b₆ * b₈ + 4 * b₂^3 * b₆^3 + 4 * b₂^2 * b₄^3 * b₈ - 3 *
      b₂^2 * b₄^2 * b₆^2 - 48 * b₂^2 * b₄ * b₈^2 + 6 * b₂^2 * b₆^2 * b₈ + 240 * b₂ * b₄^2 *
      b₆ * b₈ - 162 * b₂ * b₄ * b₆^3 + 192 * b₂ * b₆ * b₈^2 - 144 * b₄^4 * b₈ + 108 * b₄^3
      * b₆^2 + 384 * b₄^2 * b₈^2 - 1296 * b₄ * b₆^2 * b₈ + 729 * b₆^4 - 256 * b₈^3

/-- Coefficient of `X^2 Y^1` in `F1`. -/
def cF11 (b₂ b₄ b₆ b₈ : ℤ) : ℤ :=
    -4 * b₂^3 * b₄ * b₈^2 + 24 * b₂^2 * b₄^2 * b₆ * b₈ - 16 * b₂^2 * b₄ * b₆^3 + 36 * b₂^2
      * b₆ * b₈^2 - 16 * b₂ * b₄^4 * b₈ + 12 * b₂ * b₄^3 * b₆^2 + 48 * b₂ * b₄^2 * b₈^2 -
      240 * b₂ * b₄ * b₆^2 * b₈ + 144 * b₂ * b₆^4 - 64 * b₂ * b₈^3 + 48 * b₄^3 * b₆ * b₈ -
      36 * b₄^2 * b₆^3 + 64 * b₄ * b₆ * b₈^2 - 36 * b₆^3 * b₈

/-- Coefficient of `X^1 Y^2` in `F1`. -/
def cF12 (b₂ b₄ b₆ b₈ : ℤ) : ℤ :=
    b₂^3 * b₆ * b₈^2 - 12 * b₂^2 * b₄^2 * b₈^2 - 6 * b₂^2 * b₄ * b₆^2 * b₈ + 4 * b₂^2 *
      b₆^4 + 76 * b₂ * b₄^3 * b₆ * b₈ - 51 * b₂ * b₄^2 * b₆^3 + 64 * b₂ * b₄ * b₆ * b₈^2 +
      7 * b₂ * b₆^3 * b₈ - 48 * b₄^5 * b₈ + 36 * b₄^4 * b₆^2 + 160 * b₄^3 * b₈^2 - 528 *
      b₄^2 * b₆^2 * b₈ + 297 * b₄ * b₆^4 - 128 * b₄ * b₈^3 + 16 * b₆^2 * b₈^2

/-- Coefficient of `X^0 Y^3` in `F1`. -/
def cF13 (b₂ b₄ b₆ b₈ : ℤ) : ℤ :=
    -6 * b₂^2 * b₄ * b₆ * b₈^2 + 36 * b₂ * b₄^2 * b₆^2 * b₈ - 24 * b₂ * b₄ * b₆^4 + 40 * b₂
      * b₆^2 * b₈^2 - 24 * b₄^4 * b₆ * b₈ + 18 * b₄^3 * b₆^3 + 80 * b₄^2 * b₆ * b₈^2 - 282
      * b₄ * b₆^3 * b₈ + 162 * b₆^5 - 64 * b₆ * b₈^3

/-- Sum of absolute coefficients of `F1`, the constant in its size bound. -/
def SF1 (b₂ b₄ b₆ b₈ : ℤ) : ℤ := |cF10 b₂ b₄ b₆ b₈| + |cF11 b₂ b₄ b₆ b₈| + |cF12 b₂ b₄ b₆ b₈| + |cF13 b₂ b₄ b₆ b₈|

/-- Coefficient of `X^3 Y^0` in `G1`. -/
def cG10 (b₂ b₄ b₆ b₈ : ℤ) : ℤ :=
    b₂^3 * b₄ * b₈^2 - 6 * b₂^2 * b₄^2 * b₆ * b₈ + 4 * b₂^2 * b₄ * b₆^3 - 9 * b₂^2 * b₆ *
      b₈^2 + 4 * b₂ * b₄^4 * b₈ - 3 * b₂ * b₄^3 * b₆^2 - 12 * b₂ * b₄^2 * b₈^2 + 60 * b₂ *
      b₄ * b₆^2 * b₈ - 36 * b₂ * b₆^4 + 16 * b₂ * b₈^3 - 12 * b₄^3 * b₆ * b₈ + 9 * b₄^2 *
      b₆^3 - 16 * b₄ * b₆ * b₈^2 + 9 * b₆^3 * b₈

/-- Coefficient of `X^2 Y^1` in `G1`. -/
def cG11 (b₂ b₄ b₆ b₈ : ℤ) : ℤ :=
    2 * b₂^3 * b₆ * b₈^2 - 6 * b₂^2 * b₄^2 * b₈^2 - 12 * b₂^2 * b₄ * b₆^2 * b₈ + 8 * b₂^2 *
      b₆^4 - 4 * b₂^2 * b₈^3 + 44 * b₂ * b₄^3 * b₆ * b₈ - 30 * b₂ * b₄^2 * b₆^3 + 36 * b₂ *
      b₄ * b₆ * b₈^2 - 4 * b₂ * b₆^3 * b₈ - 24 * b₄^5 * b₈ + 18 * b₄^4 * b₆^2 + 56 * b₄^3 *
      b₈^2 - 192 * b₄^2 * b₆^2 * b₈ + 108 * b₄ * b₆^4 - 32 * b₄ * b₈^3 - 4 * b₆^2 * b₈^2

/-- Coefficient of `X^1 Y^2` in `G1`. -/
def cG12 (b₂ b₄ b₆ b₈ : ℤ) : ℤ :=
    b₂^3 * b₈^3 - 18 * b₂^2 * b₄ * b₆ * b₈^2 + 4 * b₂^2 * b₆^3 * b₈ + 4 * b₂ * b₄^3 * b₈^2
      + 69 * b₂ * b₄^2 * b₆^2 * b₈ - 48 * b₂ * b₄ * b₆^4 - 16 * b₂ * b₄ * b₈^3 + 87 * b₂ *
      b₆^2 * b₈^2 - 48 * b₄^4 * b₆ * b₈ + 36 * b₄^3 * b₆^3 + 196 * b₄^2 * b₆ * b₈^2 - 591 *
      b₄ * b₆^3 * b₈ + 324 * b₆^5 - 112 * b₆ * b₈^3

/-- Coefficient of `X^0 Y^3` in `G1`. -/
def cG13 (b₂ b₄ b₆ b₈ : ℤ) : ℤ :=
    -6 * b₂^2 * b₄ * b₈^3 + 36 * b₂ * b₄^2 * b₆ * b₈^2 - 24 * b₂ * b₄ * b₆^3 * b₈ + 40 * b₂
      * b₆ * b₈^3 - 24 * b₄^4 * b₈^2 + 18 * b₄^3 * b₆^2 * b₈ + 80 * b₄^2 * b₈^3 - 282 * b₄
      * b₆^2 * b₈^2 + 162 * b₆^4 * b₈ - 64 * b₈^4

/-- Sum of absolute coefficients of `G1`, the constant in its size bound. -/
def SG1 (b₂ b₄ b₆ b₈ : ℤ) : ℤ := |cG10 b₂ b₄ b₆ b₈| + |cG11 b₂ b₄ b₆ b₈| + |cG12 b₂ b₄ b₆ b₈| + |cG13 b₂ b₄ b₆ b₈|

/-- Coefficient of `X^3 Y^0` in `F2`. -/
def cF20 (b₂ b₄ b₆ b₈ : ℤ) : ℤ :=
    0

/-- Coefficient of `X^2 Y^1` in `F2`. -/
def cF21 (b₂ b₄ b₆ b₈ : ℤ) : ℤ :=
    8 * b₂^3 * b₆ - 8 * b₂^2 * b₄^2 + 16 * b₂^2 * b₈ - 336 * b₂ * b₄ * b₆ + 288 * b₄^3 -
      384 * b₄ * b₈ + 1296 * b₆^2

/-- Coefficient of `X^1 Y^2` in `F2`. -/
def cF22 (b₂ b₄ b₆ b₈ : ℤ) : ℤ :=
    2 * b₂^4 * b₆ - 2 * b₂^3 * b₄^2 - 80 * b₂^2 * b₄ * b₆ + 72 * b₂ * b₄^3 + 32 * b₂ * b₄ *
      b₈ + 360 * b₂ * b₆^2 - 144 * b₄^2 * b₆ - 576 * b₆ * b₈

/-- Coefficient of `X^0 Y^3` in `F2`. -/
def cF23 (b₂ b₄ b₆ b₈ : ℤ) : ℤ :=
    -b₂^4 * b₈ + 5 * b₂^3 * b₄ * b₆ - 4 * b₂^2 * b₄^3 + 48 * b₂^2 * b₄ * b₈ + b₂^2 * b₆^2 -
      204 * b₂ * b₄^2 * b₆ - 176 * b₂ * b₆ * b₈ + 144 * b₄^4 - 384 * b₄^2 * b₈ + 864 * b₄ *
      b₆^2 + 256 * b₈^2

/-- Sum of absolute coefficients of `F2`, the constant in its size bound. -/
def SF2 (b₂ b₄ b₆ b₈ : ℤ) : ℤ := |cF20 b₂ b₄ b₆ b₈| + |cF21 b₂ b₄ b₆ b₈| + |cF22 b₂ b₄ b₆ b₈| + |cF23 b₂ b₄ b₆ b₈|

/-- Coefficient of `X^3 Y^0` in `G2`. -/
def cG20 (b₂ b₄ b₆ b₈ : ℤ) : ℤ :=
    -2 * b₂^3 * b₆ + 2 * b₂^2 * b₄^2 - 4 * b₂^2 * b₈ + 84 * b₂ * b₄ * b₆ - 72 * b₄^3 + 96 *
      b₄ * b₈ - 324 * b₆^2

/-- Coefficient of `X^2 Y^1` in `G2`. -/
def cG21 (b₂ b₄ b₆ b₈ : ℤ) : ℤ :=
    b₂^3 * b₈ - b₂^2 * b₄ * b₆ - 32 * b₂ * b₄ * b₈ - 9 * b₂ * b₆^2 + 36 * b₄^2 * b₆ + 144 *
      b₆ * b₈

/-- Coefficient of `X^1 Y^2` in `G2`. -/
def cG22 (b₂ b₄ b₆ b₈ : ℤ) : ℤ :=
    2 * b₂^3 * b₄ * b₆ - 2 * b₂^2 * b₄^3 + 2 * b₂^2 * b₄ * b₈ + 2 * b₂^2 * b₆^2 - 84 * b₂ *
      b₄^2 * b₆ + 8 * b₂ * b₆ * b₈ + 72 * b₄^4 - 48 * b₄^2 * b₈ + 270 * b₄ * b₆^2 - 64 *
      b₈^2

/-- Coefficient of `X^0 Y^3` in `G2`. -/
def cG23 (b₂ b₄ b₆ b₈ : ℤ) : ℤ :=
    -b₂^3 * b₄ * b₈ + 4 * b₂^3 * b₆^2 - 3 * b₂^2 * b₄^2 * b₆ + 7 * b₂^2 * b₆ * b₈ + 36 * b₂
      * b₄^2 * b₈ - 162 * b₂ * b₄ * b₆^2 + 16 * b₂ * b₈^2 + 108 * b₄^3 * b₆ - 432 * b₄ * b₆
      * b₈ + 729 * b₆^3

/-- Sum of absolute coefficients of `G2`, the constant in its size bound. -/
def SG2 (b₂ b₄ b₆ b₈ : ℤ) : ℤ := |cG20 b₂ b₄ b₆ b₈| + |cG21 b₂ b₄ b₆ b₈| + |cG22 b₂ b₄ b₆ b₈| + |cG23 b₂ b₄ b₆ b₈|

section Defs
variable (b₂ b₄ b₆ b₈ : ℤ)

/-- The upper constant. -/
def CU : ℤ := max (1 + |b₄| + 2 * |b₆| + |b₈|) (4 + |b₂| + 2 * |b₄| + |b₆|)

/-- The lower constant, from r174's Bézout cofactors. -/
def CL : ℤ := max (SF1 b₂ b₄ b₆ b₈ + SG1 b₂ b₄ b₆ b₈) (SF2 b₂ b₄ b₆ b₈ + SG2 b₂ b₄ b₆ b₈)

/-- `CL` is a max of sums of absolute values, hence nonnegative. -/
theorem CL_nonneg (b₂ b₄ b₆ b₈ : ℤ) : 0 ≤ CL b₂ b₄ b₆ b₈ :=
  le_max_of_le_left (by simp only [SF1, SG1]; positivity)

end Defs

variable {b₂ b₄ b₆ b₈ : ℤ}

/-! ### Upper bounds -/

theorem abs_Phi_le (X Y : ℤ) :
    |Phi b₄ b₆ b₈ X Y| ≤ (1 + |b₄| + 2 * |b₆| + |b₈|) * max |X| |Y| ^ 4 := by
  have h := abs_form4_le 1 0 (-b₄) (-(2 * b₆)) (-b₈) X Y
  have e1 : (1 : ℤ) * X ^ 4 + 0 * X ^ 3 * Y + (-b₄) * X ^ 2 * Y ^ 2
      + (-(2 * b₆)) * X * Y ^ 3 + (-b₈) * Y ^ 4 = Phi b₄ b₆ b₈ X Y := by
    simp only [Phi]; ring
  have e2 : |(1 : ℤ)| + |(0 : ℤ)| + |-b₄| + |-(2 * b₆)| + |-b₈|
      = 1 + |b₄| + 2 * |b₆| + |b₈| := by
    simp only [abs_neg, abs_mul, abs_zero, abs_one]; norm_num
  rwa [e1, e2] at h

theorem abs_Psi_le (X Y : ℤ) :
    |Psi b₂ b₄ b₆ X Y| ≤ (4 + |b₂| + 2 * |b₄| + |b₆|) * max |X| |Y| ^ 4 := by
  have h := abs_form4_le 0 4 b₂ (2 * b₄) b₆ X Y
  have e1 : (0 : ℤ) * X ^ 4 + 4 * X ^ 3 * Y + b₂ * X ^ 2 * Y ^ 2
      + (2 * b₄) * X * Y ^ 3 + b₆ * Y ^ 4 = Psi b₂ b₄ b₆ X Y := by
    simp only [Psi]; ring
  have e2 : |(0 : ℤ)| + |(4 : ℤ)| + |b₂| + |2 * b₄| + |b₆|
      = 4 + |b₂| + 2 * |b₄| + |b₆| := by
    simp only [abs_mul, abs_zero]; norm_num
  rwa [e1, e2] at h

/-- **The upper bound**: `max |Φ| |Ψ| ≤ CU · M⁴`. -/
theorem max_abs_le (X Y : ℤ) :
    max |Phi b₄ b₆ b₈ X Y| |Psi b₂ b₄ b₆ X Y| ≤ CU b₂ b₄ b₆ b₈ * max |X| |Y| ^ 4 := by
  have hM : (0 : ℤ) ≤ max |X| |Y| ^ 4 := by positivity
  refine max_le ((abs_Phi_le X Y).trans (mul_le_mul_of_nonneg_right ?_ hM))
    ((abs_Psi_le X Y).trans (mul_le_mul_of_nonneg_right ?_ hM))
  · exact le_max_left _ _
  · exact le_max_right _ _

/-! ### Lower bound -/

theorem abs_F1_le (X Y : ℤ) :
    |F1 b₂ b₄ b₆ b₈ X Y| ≤ SF1 b₂ b₄ b₆ b₈ * max |X| |Y| ^ 3 := by
  have h := abs_form3_le (cF10 b₂ b₄ b₆ b₈) (cF11 b₂ b₄ b₆ b₈) (cF12 b₂ b₄ b₆ b₈)
    (cF13 b₂ b₄ b₆ b₈) X Y
  have e : cF10 b₂ b₄ b₆ b₈ * X ^ 3 + cF11 b₂ b₄ b₆ b₈ * X ^ 2 * Y
      + cF12 b₂ b₄ b₆ b₈ * X * Y ^ 2 + cF13 b₂ b₄ b₆ b₈ * Y ^ 3
      = F1 b₂ b₄ b₆ b₈ X Y := by
    simp only [F1, cF10, cF11, cF12, cF13]; ring
  rw [e] at h
  exact h.trans_eq (by simp only [SF1])

theorem abs_G1_le (X Y : ℤ) :
    |G1 b₂ b₄ b₆ b₈ X Y| ≤ SG1 b₂ b₄ b₆ b₈ * max |X| |Y| ^ 3 := by
  have h := abs_form3_le (cG10 b₂ b₄ b₆ b₈) (cG11 b₂ b₄ b₆ b₈) (cG12 b₂ b₄ b₆ b₈)
    (cG13 b₂ b₄ b₆ b₈) X Y
  have e : cG10 b₂ b₄ b₆ b₈ * X ^ 3 + cG11 b₂ b₄ b₆ b₈ * X ^ 2 * Y
      + cG12 b₂ b₄ b₆ b₈ * X * Y ^ 2 + cG13 b₂ b₄ b₆ b₈ * Y ^ 3
      = G1 b₂ b₄ b₆ b₈ X Y := by
    simp only [G1, cG10, cG11, cG12, cG13]; ring
  rw [e] at h
  exact h.trans_eq (by simp only [SG1])

theorem abs_F2_le (X Y : ℤ) :
    |F2 b₂ b₄ b₆ b₈ X Y| ≤ SF2 b₂ b₄ b₆ b₈ * max |X| |Y| ^ 3 := by
  have h := abs_form3_le (cF20 b₂ b₄ b₆ b₈) (cF21 b₂ b₄ b₆ b₈) (cF22 b₂ b₄ b₆ b₈)
    (cF23 b₂ b₄ b₆ b₈) X Y
  have e : cF20 b₂ b₄ b₆ b₈ * X ^ 3 + cF21 b₂ b₄ b₆ b₈ * X ^ 2 * Y
      + cF22 b₂ b₄ b₆ b₈ * X * Y ^ 2 + cF23 b₂ b₄ b₆ b₈ * Y ^ 3
      = F2 b₂ b₄ b₆ b₈ X Y := by
    simp only [F2, cF20, cF21, cF22, cF23]; ring
  rw [e] at h
  exact h.trans_eq (by simp only [SF2])

theorem abs_G2_le (X Y : ℤ) :
    |G2 b₂ b₄ b₆ b₈ X Y| ≤ SG2 b₂ b₄ b₆ b₈ * max |X| |Y| ^ 3 := by
  have h := abs_form3_le (cG20 b₂ b₄ b₆ b₈) (cG21 b₂ b₄ b₆ b₈) (cG22 b₂ b₄ b₆ b₈)
    (cG23 b₂ b₄ b₆ b₈) X Y
  have e : cG20 b₂ b₄ b₆ b₈ * X ^ 3 + cG21 b₂ b₄ b₆ b₈ * X ^ 2 * Y
      + cG22 b₂ b₄ b₆ b₈ * X * Y ^ 2 + cG23 b₂ b₄ b₆ b₈ * Y ^ 3
      = G2 b₂ b₄ b₆ b₈ X Y := by
    simp only [G2, cG20, cG21, cG22, cG23]; ring
  rw [e] at h
  exact h.trans_eq (by simp only [SG2])

/-- **The lower bound**: `Δ² · M⁴ ≤ CL · max |Φ| |Ψ|`.

The Bézout pair of r174 does double duty: it bounded the content, and it bounds
the archimedean size from below too. -/
theorem disc_sq_mul_le (hrel : 4 * b₈ = b₂ * b₆ - b₄ ^ 2) (X Y : ℤ) :
    Disc b₂ b₄ b₆ b₈ ^ 2 * max |X| |Y| ^ 4
      ≤ CL b₂ b₄ b₆ b₈ * max |Phi b₄ b₆ b₈ X Y| |Psi b₂ b₄ b₆ X Y| := by
  set M := max |X| |Y| with hMdef
  set P := max |Phi b₄ b₆ b₈ X Y| |Psi b₂ b₄ b₆ X Y| with hPdef
  have hM0 : (0 : ℤ) ≤ M := le_trans (abs_nonneg X) (le_max_left _ _)
  have hP0 : (0 : ℤ) ≤ P := le_trans (abs_nonneg _) (le_max_left _ _)
  rcases eq_or_lt_of_le hM0 with hM | hMpos
  · -- M = 0 forces X = Y = 0; the left side vanishes.
    have : M ^ 4 = 0 := by rw [← hM]; ring
    rw [this, mul_zero]
    exact mul_nonneg (CL_nonneg b₂ b₄ b₆ b₈) hP0
  -- The two Bézout identities, each bounded termwise.
  have key : ∀ (Z : ℤ) (F G SF SG : ℤ),
      Disc b₂ b₄ b₆ b₈ ^ 2 * Z ^ 7 = F * Phi b₄ b₆ b₈ X Y + G * Psi b₂ b₄ b₆ X Y →
      |F| ≤ SF * M ^ 3 → |G| ≤ SG * M ^ 3 → |Z| = M →
      Disc b₂ b₄ b₆ b₈ ^ 2 * M ^ 7 ≤ (SF + SG) * M ^ 3 * P := by
    intro Z F G SF G' hid hF hG hZ
    have hD0 : (0 : ℤ) ≤ Disc b₂ b₄ b₆ b₈ ^ 2 := sq_nonneg _
    have hSF : (0 : ℤ) ≤ SF * M ^ 3 := le_trans (abs_nonneg _) hF
    have hSG : (0 : ℤ) ≤ G' * M ^ 3 := le_trans (abs_nonneg _) hG
    have habs : Disc b₂ b₄ b₆ b₈ ^ 2 * M ^ 7 = |Disc b₂ b₄ b₆ b₈ ^ 2 * Z ^ 7| := by
      rw [abs_mul, abs_of_nonneg hD0, abs_pow, hZ]
    rw [habs, hid]
    calc |F * Phi b₄ b₆ b₈ X Y + G * Psi b₂ b₄ b₆ X Y|
        ≤ |F * Phi b₄ b₆ b₈ X Y| + |G * Psi b₂ b₄ b₆ X Y| := abs_add _ _
      _ = |F| * |Phi b₄ b₆ b₈ X Y| + |G| * |Psi b₂ b₄ b₆ X Y| := by
          rw [abs_mul, abs_mul]
      _ ≤ (SF * M ^ 3) * P + (G' * M ^ 3) * P := by
          exact add_le_add
            (mul_le_mul hF (le_max_left _ _) (abs_nonneg _) hSF)
            (mul_le_mul hG (le_max_right _ _) (abs_nonneg _) hSG)
      _ = (SF + G') * M ^ 3 * P := by ring
  have hM3 : (0 : ℤ) < M ^ 3 := by positivity
  have hstep : Disc b₂ b₄ b₆ b₈ ^ 2 * M ^ 7 ≤ CL b₂ b₄ b₆ b₈ * M ^ 3 * P := by
    rcases max_cases |X| |Y| with ⟨hmax, _⟩ | ⟨hmax, _⟩
    · refine (key X (F1 b₂ b₄ b₆ b₈ X Y) (G1 b₂ b₄ b₆ b₈ X Y) _ _
        (bezout_X b₂ b₄ b₆ b₈ X Y hrel).symm (abs_F1_le X Y) (abs_G1_le X Y)
        (by rw [hMdef, hmax])).trans ?_
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (le_of_lt hM3)) hP0
    · refine (key Y (F2 b₂ b₄ b₆ b₈ X Y) (G2 b₂ b₄ b₆ b₈ X Y) _ _
        (bezout_Y b₂ b₄ b₆ b₈ X Y hrel).symm (abs_F2_le X Y) (abs_G2_le X Y)
        (by rw [hMdef, hmax])).trans ?_
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (le_of_lt hM3)) hP0
  refine le_of_mul_le_mul_right ?_ hM3
  calc Disc b₂ b₄ b₆ b₈ ^ 2 * M ^ 4 * M ^ 3
      = Disc b₂ b₄ b₆ b₈ ^ 2 * M ^ 7 := by ring
    _ ≤ CL b₂ b₄ b₆ b₈ * M ^ 3 * P := hstep
    _ = CL b₂ b₄ b₆ b₈ * P * M ^ 3 := by ring

end PrincipiaTractalis.DuplicationSize

#print axioms PrincipiaTractalis.DuplicationSize.abs_form4_le
#print axioms PrincipiaTractalis.DuplicationSize.max_abs_le
#print axioms PrincipiaTractalis.DuplicationSize.disc_sq_mul_le
