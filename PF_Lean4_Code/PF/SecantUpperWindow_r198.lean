/-
# PF.SecantUpperWindow_r198

★★★ 2026-08-05 — THE UNIVERSAL SECANT UPPER WINDOW, AT THE POINT LEVEL ★★★

The first assembly stone of the universal quasi-parallelogram: for ANY
Weierstrass curve over ℚ with integer b-invariants, and any two affine
points with distinct x-coordinates,

  `H(x(P+Q)) · H(x(P−Q))  ≤  2 · CUsec · H(x₁)² · H(x₂)²`

with `CUsec = max(4, 4+|b₂|+2|b₄|+|b₆|, 1+|b₄|+2|b₆|+|b₈|)` — coefficients
only (`secant_upper_window`).

This is the r148f/r149-upper analogue, universally: what the per-curve arc
proved for 389a1 and 5077a1 with hand-built size tables is now one theorem.
The chain is exactly the committed pattern:

  r181 (`addX_add_addX_negY`, `addX_mul_addX_negY`):
      x(P+Q) + x(P−Q) and x(P+Q)·x(P−Q) as universal rational functions;
  r193 (`DDz_spec`, `Sfz_spec`, `Prz_spec`): bihomogenization —
      `DDz·(x₃+x₄) = Sfz` and `DDz·x₃x₄ = Prz` over the integers;
  r148e (`naiveHeight_mul_le_of_quadratic`): the roots of an integer
      quadratic have height product ≤ 2·max coefficient;
  r193 (`abs_DDz_le`, `abs_Sfz_le`, `abs_Prz_le`): the coefficients are
      ≤ CUsec·H₁²H₂².

What remains for the full quasi-parallelogram (next stones): the LOWER half
via the doubling trick recorded in r148e's header — apply THIS upper bound
to the pair (P+Q, P−Q), whose sum and difference are 2P and 2Q, and chain
with the universal duplication window (r176/r179); then the log form and
the limit into r171's generic canonical height.

Kernel axioms ⊆ `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-08-05.
-/
import PF.SecantSizeUniversal_r193
import PF.QuadraticRootHeights_r148e

set_option maxHeartbeats 1600000

namespace PrincipiaTractalis.SecantUpperWindow

open PrincipiaTractalis.SecantUniversal
open PrincipiaTractalis.SecantSizeUniversal
open PrincipiaTractalis.QuadraticRootHeights
open PrincipiaTractalis.NaiveHeightQ

/-! ### §1 — the coefficient constant -/

/-- The universal secant upper constant. -/
def CUsec (B₂ B₄ B₆ B₈ : ℤ) : ℤ :=
  max (max 4 (4 + |B₂| + 2 * |B₄| + |B₆|)) (1 + |B₄| + 2 * |B₆| + |B₈|)

theorem CUsec_nonneg (B₂ B₄ B₆ B₈ : ℤ) : 0 ≤ CUsec B₂ B₄ B₆ B₈ :=
  le_trans (by norm_num) (le_trans (le_max_left 4 _) (le_max_left _ _))

theorem four_le_CUsec (B₂ B₄ B₆ B₈ : ℤ) : 4 ≤ CUsec B₂ B₄ B₆ B₈ :=
  le_trans (le_max_left 4 _) (le_max_left _ _)

theorem sf_le_CUsec (B₂ B₄ B₆ B₈ : ℤ) :
    4 + |B₂| + 2 * |B₄| + |B₆| ≤ CUsec B₂ B₄ B₆ B₈ :=
  le_trans (le_max_right 4 _) (le_max_left _ _)

theorem pr_le_CUsec (B₂ B₄ B₆ B₈ : ℤ) :
    1 + |B₄| + 2 * |B₆| + |B₈| ≤ CUsec B₂ B₄ B₆ B₈ :=
  le_max_right _ _

/-! ### §2 — the naive height is the coordinate max -/

theorem naiveHeight_cast (x : ℚ) :
    (naiveHeight x : ℤ) = max |x.num| ((x.den : ℤ)) := by
  rw [naiveHeight, Nat.cast_max, Int.abs_eq_natAbs]

theorem naiveHeight_cast' (x : ℚ) :
    (naiveHeight x : ℤ) = max |x.num| |((x.den : ℤ))| := by
  rw [naiveHeight_cast, abs_of_nonneg (by positivity : (0:ℤ) ≤ ((x.den : ℤ)))]

/-! ### §3 — the denominator form does not vanish for distinct points -/

theorem den_cast_ne_zero (x : ℚ) : (((x.den : ℤ)) : ℚ) ≠ 0 := by
  have h := x.den_nz
  exact_mod_cast Nat.cast_ne_zero.mpr h

theorem num_div_den' (x : ℚ) : ((x.num : ℚ)) / (((x.den : ℤ)) : ℚ) = x := by
  push_cast
  exact Rat.num_div_den x

theorem DDz_ne_zero {x₁ x₂ : ℚ} (hx : x₁ ≠ x₂) :
    DDz x₁.num (x₁.den : ℤ) x₂.num (x₂.den : ℤ) ≠ 0 := by
  rw [DDz]
  intro h0
  apply hx
  have hbase : x₁.num * ((x₂.den : ℤ)) - x₂.num * ((x₁.den : ℤ)) = 0 :=
    pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0) |>.mp h0
  rw [← Rat.num_div_den x₁, ← Rat.num_div_den x₂,
    div_eq_div_iff (Nat.cast_ne_zero.mpr x₁.den_nz) (Nat.cast_ne_zero.mpr x₂.den_nz)]
  exact_mod_cast (by linarith : x₁.num * ((x₂.den : ℤ)) = x₂.num * ((x₁.den : ℤ)))

/-! ### §4 — the integer quadratic relations for the addition pair -/

section Main

variable {W : WeierstrassCurve.Affine ℚ} {B₂ B₄ B₆ B₈ : ℤ}
variable {x₁ x₂ y₁ y₂ : ℚ}

theorem sum_relation (h₂ : W.b₂ = (B₂ : ℚ)) (h₄ : W.b₄ = (B₄ : ℚ))
    (h₆ : W.b₆ = (B₆ : ℚ))
    (hE₁ : W.Equation x₁ y₁) (hE₂ : W.Equation x₂ y₂) (hx : x₁ ≠ x₂) :
    ((DDz x₁.num (x₁.den : ℤ) x₂.num (x₂.den : ℤ) : ℤ) : ℚ)
        * (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)
            + W.addX x₁ x₂ (W.slope x₁ x₂ y₁ (W.negY x₂ y₂)))
      = ((Sfz B₂ B₄ B₆ x₁.num (x₁.den : ℤ) x₂.num (x₂.den : ℤ) : ℤ) : ℚ) := by
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have hd2 : (x₁ - x₂) ^ 2 ≠ 0 := pow_ne_zero 2 hd
  have hb₁ := den_cast_ne_zero x₁
  have hb₂ := den_cast_ne_zero x₂
  have hDDcast : ((DDz x₁.num (x₁.den : ℤ) x₂.num (x₂.den : ℤ) : ℤ) : ℚ)
      = (x₁ - x₂) ^ 2
        * ((((x₁.den : ℤ)) : ℚ) ^ 2 * (((x₂.den : ℤ)) : ℚ) ^ 2) := by
    rw [← DDz_spec hb₁ hb₂, num_div_den', num_div_den']
  have hSfcast : sumNum W x₁ x₂
      * ((((x₁.den : ℤ)) : ℚ) ^ 2 * (((x₂.den : ℤ)) : ℚ) ^ 2)
      = ((Sfz B₂ B₄ B₆ x₁.num (x₁.den : ℤ) x₂.num (x₂.den : ℤ) : ℤ) : ℚ) := by
    have h := Sfz_spec (W := W) (a₁ := x₁.num) (a₂ := x₂.num) h₂ h₄ h₆ hb₁ hb₂
    rwa [num_div_den', num_div_den'] at h
  rw [addX_add_addX_negY hE₁ hE₂ hx, hDDcast, ← hSfcast]
  field_simp

theorem prod_relation (h₄ : W.b₄ = (B₄ : ℚ)) (h₆ : W.b₆ = (B₆ : ℚ))
    (h₈ : W.b₈ = (B₈ : ℚ))
    (hE₁ : W.Equation x₁ y₁) (hE₂ : W.Equation x₂ y₂) (hx : x₁ ≠ x₂) :
    ((DDz x₁.num (x₁.den : ℤ) x₂.num (x₂.den : ℤ) : ℤ) : ℚ)
        * (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)
            * W.addX x₁ x₂ (W.slope x₁ x₂ y₁ (W.negY x₂ y₂)))
      = ((Prz B₄ B₆ B₈ x₁.num (x₁.den : ℤ) x₂.num (x₂.den : ℤ) : ℤ) : ℚ) := by
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have hd2 : (x₁ - x₂) ^ 2 ≠ 0 := pow_ne_zero 2 hd
  have hb₁ := den_cast_ne_zero x₁
  have hb₂ := den_cast_ne_zero x₂
  have hDDcast : ((DDz x₁.num (x₁.den : ℤ) x₂.num (x₂.den : ℤ) : ℤ) : ℚ)
      = (x₁ - x₂) ^ 2
        * ((((x₁.den : ℤ)) : ℚ) ^ 2 * (((x₂.den : ℤ)) : ℚ) ^ 2) := by
    rw [← DDz_spec hb₁ hb₂, num_div_den', num_div_den']
  have hPrcast : prdNum W x₁ x₂
      * ((((x₁.den : ℤ)) : ℚ) ^ 2 * (((x₂.den : ℤ)) : ℚ) ^ 2)
      = ((Prz B₄ B₆ B₈ x₁.num (x₁.den : ℤ) x₂.num (x₂.den : ℤ) : ℤ) : ℚ) := by
    have h := Prz_spec (W := W) (a₁ := x₁.num) (a₂ := x₂.num) h₄ h₆ h₈ hb₁ hb₂
    rwa [num_div_den', num_div_den'] at h
  rw [addX_mul_addX_negY hE₁ hE₂ hx, hDDcast, ← hPrcast]
  field_simp

/-! ### §5 — THE UNIVERSAL SECANT UPPER WINDOW -/

/-- **The universal secant upper window**: on any Weierstrass curve over ℚ
with integer b-invariants, the height product of the two addition
x-coordinates is bounded by `2·CUsec·H(x₁)²·H(x₂)²`. -/
theorem secant_upper_window (h₂ : W.b₂ = (B₂ : ℚ)) (h₄ : W.b₄ = (B₄ : ℚ))
    (h₆ : W.b₆ = (B₆ : ℚ)) (h₈ : W.b₈ = (B₈ : ℚ))
    (hE₁ : W.Equation x₁ y₁) (hE₂ : W.Equation x₂ y₂) (hx : x₁ ≠ x₂) :
    (naiveHeight (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)) : ℤ)
        * (naiveHeight (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ (W.negY x₂ y₂))) : ℤ)
      ≤ 2 * CUsec B₂ B₄ B₆ B₈
          * ((naiveHeight x₁ : ℤ) ^ 2 * (naiveHeight x₂ : ℤ) ^ 2) := by
  set A := DDz x₁.num (x₁.den : ℤ) x₂.num (x₂.den : ℤ) with hAdef
  set B := Sfz B₂ B₄ B₆ x₁.num (x₁.den : ℤ) x₂.num (x₂.den : ℤ) with hBdef
  set C := Prz B₄ B₆ B₈ x₁.num (x₁.den : ℤ) x₂.num (x₂.den : ℤ) with hCdef
  -- the r148e height bound, in ℤ
  have h148e := naiveHeight_mul_le_of_quadratic (DDz_ne_zero hx)
    (sum_relation h₂ h₄ h₆ hE₁ hE₂ hx) (prod_relation h₄ h₆ h₈ hE₁ hE₂ hx)
  have hZ : (naiveHeight (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)) : ℤ)
      * (naiveHeight (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ (W.negY x₂ y₂))) : ℤ)
      ≤ 2 * max (max |A| |B|) |C| := by
    have h := h148e
    have hcast : ((naiveHeight (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂))
        * naiveHeight (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ (W.negY x₂ y₂))) : ℕ) : ℤ)
        ≤ ((2 * max (max A.natAbs B.natAbs) C.natAbs : ℕ) : ℤ) := by
      exact_mod_cast h
    push_cast [Int.natCast_natAbs] at hcast
    exact_mod_cast hcast
  -- the r193 size bounds, funneled through CUsec
  set K : ℤ := max |x₁.num| |((x₁.den : ℤ))| ^ 2
      * max |x₂.num| |((x₂.den : ℤ))| ^ 2 with hKdef
  have hK0 : (0:ℤ) ≤ K := by positivity
  have hDD : |A| ≤ CUsec B₂ B₄ B₆ B₈ * K := by
    calc |A| ≤ 4 * K := abs_DDz_le _ _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (four_le_CUsec B₂ B₄ B₆ B₈) hK0
  have hSf : |B| ≤ CUsec B₂ B₄ B₆ B₈ * K := by
    calc |B| ≤ (4 + |B₂| + 2 * |B₄| + |B₆|) * K := abs_Sfz_le _ _ _ _ B₂ B₄ B₆
      _ ≤ _ := mul_le_mul_of_nonneg_right (sf_le_CUsec B₂ B₄ B₆ B₈) hK0
  have hPr : |C| ≤ CUsec B₂ B₄ B₆ B₈ * K := by
    calc |C| ≤ (1 + |B₄| + 2 * |B₆| + |B₈|) * K := abs_Prz_le _ _ _ _ B₄ B₆ B₈
      _ ≤ _ := mul_le_mul_of_nonneg_right (pr_le_CUsec B₂ B₄ B₆ B₈) hK0
  have hmax : max (max |A| |B|) |C| ≤ CUsec B₂ B₄ B₆ B₈ * K :=
    max_le (max_le hDD hSf) hPr
  -- assemble and rewrite the heights
  calc (naiveHeight (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)) : ℤ)
      * (naiveHeight (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ (W.negY x₂ y₂))) : ℤ)
      ≤ 2 * max (max |A| |B|) |C| := hZ
    _ ≤ 2 * (CUsec B₂ B₄ B₆ B₈ * K) := by linarith [hmax]
    _ = 2 * CUsec B₂ B₄ B₆ B₈
        * ((naiveHeight x₁ : ℤ) ^ 2 * (naiveHeight x₂ : ℤ) ^ 2) := by
      rw [hKdef, naiveHeight_cast' x₁, naiveHeight_cast' x₂]
      ring

end Main

end PrincipiaTractalis.SecantUpperWindow

#print axioms PrincipiaTractalis.SecantUpperWindow.DDz_ne_zero
#print axioms PrincipiaTractalis.SecantUpperWindow.sum_relation
#print axioms PrincipiaTractalis.SecantUpperWindow.prod_relation
#print axioms PrincipiaTractalis.SecantUpperWindow.secant_upper_window
