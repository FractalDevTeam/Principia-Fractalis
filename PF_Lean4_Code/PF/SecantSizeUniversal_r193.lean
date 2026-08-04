/-
# PF.SecantSizeUniversal_r193

★★★ 2026-08-04 — SECANT SIZE BOUNDS, FOR EVERY CURVE ★★★

r181 derived the universal secant formulas — `x(P+Q) + x(P−Q)` and
`x(P+Q)·x(P−Q)` in the b-invariant basis, over any field.  This stone is the
r175 analogue on the secant side: the **integer bihomogeneous forms** behind
those formulas, their specialization identities, and the triangle-inequality
size bounds with coefficient-only constants.

For `x₁ = a₁/b₁`, `x₂ = a₂/b₂` the three bidegree-(2,2) forms are

  `DDz = (a₁b₂ − a₂b₁)²`                                   (the denominator)
  `Sfz = 2a₁a₂(a₁b₂+a₂b₁) + B₂a₁a₂b₁b₂ + B₄(a₁b₂+a₂b₁)b₁b₂ + B₆b₁²b₂²`
  `Prz = a₁²a₂² − B₄a₁a₂b₁b₂ − B₆(a₁b₂+a₂b₁)b₁b₂ − B₈b₁²b₂²`

(sympy-verified against r181's field formulas, and — at
`(B₂,B₄,B₆,B₈) = (0,−14,25,−49)` — against r160's hand-derived 5077a1 forms,
the third independent confirmation on this axis).  With `Hᵢ = max |aᵢ| |bᵢ|`:

  `|DDz| ≤ 4·H₁²H₂²`
  `|Sfz| ≤ (4 + |B₂| + 2|B₄| + |B₆|)·H₁²H₂²`
  `|Prz| ≤ (1 + |B₄| + 2|B₆| + |B₈|)·H₁²H₂²`

The constants are sharp against the hand-built curves: at 5077a1 the `Sfz`
constant is `4+0+28+25 = 57` and the `Prz` constant `1+14+50+49 = 114` —
compare r161's per-curve sizes.  These are the CU-side ingredients of the
universal quasi-parallelogram window; the content/Bézout lower half (the
r174 analogue: universal Cramer certificates for the secant triple) is the
next stone, after which the window feeds r171's generic canonical-height
machinery to make bi-additivity — and hence the whole rank pipeline —
coefficient-only.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-08-04.
-/
import PF.SecantUniversal_r181
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

set_option maxHeartbeats 1600000

namespace PrincipiaTractalis.SecantSizeUniversal

open PrincipiaTractalis.SecantUniversal

/-! ### §1 — the integer bihomogeneous secant forms -/

/-- The secant denominator form: `((x₁−x₂)b₁b₂)² = (a₁b₂ − a₂b₁)²`. -/
def DDz (a₁ b₁ a₂ b₂ : ℤ) : ℤ := (a₁ * b₂ - a₂ * b₁) ^ 2

/-- The sum form: `(x(P+Q) + x(P−Q))·(x₁−x₂)²·b₁²b₂²`, bihomogeneous of
bidegree (2,2), in the b-invariant basis. -/
def Sfz (B₂ B₄ B₆ : ℤ) (a₁ b₁ a₂ b₂ : ℤ) : ℤ :=
  2 * a₁ * a₂ * (a₁ * b₂ + a₂ * b₁) + B₂ * (a₁ * a₂ * (b₁ * b₂))
    + B₄ * ((a₁ * b₂ + a₂ * b₁) * (b₁ * b₂)) + B₆ * (b₁ ^ 2 * b₂ ^ 2)

/-- The product form: `(x(P+Q)·x(P−Q))·(x₁−x₂)²·b₁²b₂²`, bihomogeneous of
bidegree (2,2). -/
def Prz (B₄ B₆ B₈ : ℤ) (a₁ b₁ a₂ b₂ : ℤ) : ℤ :=
  a₁ ^ 2 * a₂ ^ 2 - B₄ * (a₁ * a₂ * (b₁ * b₂))
    - B₆ * ((a₁ * b₂ + a₂ * b₁) * (b₁ * b₂)) - B₈ * (b₁ ^ 2 * b₂ ^ 2)

/-! ### §2 — specialization: the forms compute r181's field formulas -/

section Specialization

variable {W : WeierstrassCurve.Affine ℚ} {B₂ B₄ B₆ B₈ : ℤ}
variable {a₁ b₁ a₂ b₂ : ℤ}

/-- The denominator form is the bihomogenized `(x₁ − x₂)²`. -/
theorem DDz_spec (hb₁ : (b₁ : ℚ) ≠ 0) (hb₂ : (b₂ : ℚ) ≠ 0) :
    (((a₁ : ℚ) / b₁ - (a₂ : ℚ) / b₂) ^ 2) * ((b₁ : ℚ) ^ 2 * (b₂ : ℚ) ^ 2)
      = ((DDz a₁ b₁ a₂ b₂ : ℤ) : ℚ) := by
  rw [DDz]
  push_cast
  field_simp

/-- The sum form is the bihomogenized `sumNum` of r181. -/
theorem Sfz_spec (h₂ : W.b₂ = (B₂ : ℚ)) (h₄ : W.b₄ = (B₄ : ℚ))
    (h₆ : W.b₆ = (B₆ : ℚ)) (hb₁ : (b₁ : ℚ) ≠ 0) (hb₂ : (b₂ : ℚ) ≠ 0) :
    sumNum W ((a₁ : ℚ) / b₁) ((a₂ : ℚ) / b₂) * ((b₁ : ℚ) ^ 2 * (b₂ : ℚ) ^ 2)
      = ((Sfz B₂ B₄ B₆ a₁ b₁ a₂ b₂ : ℤ) : ℚ) := by
  rw [sumNum, Sfz, h₂, h₄, h₆]
  push_cast
  field_simp

/-- The product form is the bihomogenized `prdNum` of r181. -/
theorem Prz_spec (h₄ : W.b₄ = (B₄ : ℚ)) (h₆ : W.b₆ = (B₆ : ℚ))
    (h₈ : W.b₈ = (B₈ : ℚ)) (hb₁ : (b₁ : ℚ) ≠ 0) (hb₂ : (b₂ : ℚ) ≠ 0) :
    prdNum W ((a₁ : ℚ) / b₁) ((a₂ : ℚ) / b₂) * ((b₁ : ℚ) ^ 2 * (b₂ : ℚ) ^ 2)
      = ((Prz B₄ B₆ B₈ a₁ b₁ a₂ b₂ : ℤ) : ℚ) := by
  rw [prdNum, Prz, h₄, h₆, h₈]
  push_cast
  field_simp

end Specialization

/-! ### §3 — bidegree-(2,2) monomial bounds -/

section Size

variable (a₁ b₁ a₂ b₂ : ℤ)

/-- Any bidegree-(2,2) monomial is bounded by `H₁²·H₂²`. -/
private theorem abs_mono22 {u₁ v₁ u₂ v₂ : ℤ}
    (h₁ : |u₁| ≤ max |a₁| |b₁|) (h₂ : |v₁| ≤ max |a₁| |b₁|)
    (h₃ : |u₂| ≤ max |a₂| |b₂|) (h₄ : |v₂| ≤ max |a₂| |b₂|) :
    |u₁ * v₁ * (u₂ * v₂)| ≤ max |a₁| |b₁| ^ 2 * max |a₂| |b₂| ^ 2 := by
  have hM₁ : (0 : ℤ) ≤ max |a₁| |b₁| := le_trans (abs_nonneg a₁) (le_max_left _ _)
  have hM₂ : (0 : ℤ) ≤ max |a₂| |b₂| := le_trans (abs_nonneg a₂) (le_max_left _ _)
  calc |u₁ * v₁ * (u₂ * v₂)| = |u₁| * |v₁| * (|u₂| * |v₂|) := by
        simp [abs_mul]
    _ ≤ max |a₁| |b₁| * max |a₁| |b₁| * (max |a₂| |b₂| * max |a₂| |b₂|) := by
        gcongr <;> positivity
    _ = max |a₁| |b₁| ^ 2 * max |a₂| |b₂| ^ 2 := by ring

private theorem habs_a₁ : |a₁| ≤ max |a₁| |b₁| := le_max_left _ _
private theorem habs_b₁ : |b₁| ≤ max |a₁| |b₁| := le_max_right _ _
private theorem habs_a₂ : |a₂| ≤ max |a₂| |b₂| := le_max_left _ _
private theorem habs_b₂ : |b₂| ≤ max |a₂| |b₂| := le_max_right _ _

/-! ### §4 — the size upper bounds -/

/-- `|DDz| ≤ 4·H₁²·H₂²`. -/
theorem abs_DDz_le :
    |DDz a₁ b₁ a₂ b₂| ≤ 4 * (max |a₁| |b₁| ^ 2 * max |a₂| |b₂| ^ 2) := by
  have h1 : |a₁ * b₂ * (a₂ * b₁)|
      ≤ max |a₁| |b₁| ^ 2 * max |a₂| |b₂| ^ 2 := by
    have := abs_mono22 a₁ b₁ a₂ b₂ (u₁ := a₁) (v₁ := b₁) (u₂ := b₂) (v₂ := a₂)
      (habs_a₁ a₁ b₁) (habs_b₁ a₁ b₁) (habs_b₂ a₂ b₂) (habs_a₂ a₂ b₂)
    calc |a₁ * b₂ * (a₂ * b₁)| = |a₁ * b₁ * (b₂ * a₂)| := by ring_nf
      _ ≤ _ := this
  have h2 : |a₁ * b₂ * (a₁ * b₂)|
      ≤ max |a₁| |b₁| ^ 2 * max |a₂| |b₂| ^ 2 := by
    have := abs_mono22 a₁ b₁ a₂ b₂ (u₁ := a₁) (v₁ := a₁) (u₂ := b₂) (v₂ := b₂)
      (habs_a₁ a₁ b₁) (habs_a₁ a₁ b₁) (habs_b₂ a₂ b₂) (habs_b₂ a₂ b₂)
    calc |a₁ * b₂ * (a₁ * b₂)| = |a₁ * a₁ * (b₂ * b₂)| := by ring_nf
      _ ≤ _ := this
  have h3 : |a₂ * b₁ * (a₂ * b₁)|
      ≤ max |a₁| |b₁| ^ 2 * max |a₂| |b₂| ^ 2 := by
    have := abs_mono22 a₁ b₁ a₂ b₂ (u₁ := b₁) (v₁ := b₁) (u₂ := a₂) (v₂ := a₂)
      (habs_b₁ a₁ b₁) (habs_b₁ a₁ b₁) (habs_a₂ a₂ b₂) (habs_a₂ a₂ b₂)
    calc |a₂ * b₁ * (a₂ * b₁)| = |b₁ * b₁ * (a₂ * a₂)| := by ring_nf
      _ ≤ _ := this
  calc |DDz a₁ b₁ a₂ b₂|
      = |a₁ * b₂ * (a₁ * b₂) - a₁ * b₂ * (a₂ * b₁) - a₁ * b₂ * (a₂ * b₁)
          + a₂ * b₁ * (a₂ * b₁)| := by rw [DDz]; ring_nf
    _ ≤ |a₁ * b₂ * (a₁ * b₂)| + |a₁ * b₂ * (a₂ * b₁)| + |a₁ * b₂ * (a₂ * b₁)|
          + |a₂ * b₁ * (a₂ * b₁)| := by
        refine (abs_add _ _).trans (add_le_add_right ?_ _)
        refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
        exact abs_sub _ _
    _ ≤ 4 * (max |a₁| |b₁| ^ 2 * max |a₂| |b₂| ^ 2) := by linarith [h1, h2, h3]

/-- `|Sfz| ≤ (4 + |B₂| + 2|B₄| + |B₆|)·H₁²·H₂²`. -/
theorem abs_Sfz_le (B₂ B₄ B₆ : ℤ) :
    |Sfz B₂ B₄ B₆ a₁ b₁ a₂ b₂|
      ≤ (4 + |B₂| + 2 * |B₄| + |B₆|)
          * (max |a₁| |b₁| ^ 2 * max |a₂| |b₂| ^ 2) := by
  have hM : (0 : ℤ) ≤ max |a₁| |b₁| ^ 2 * max |a₂| |b₂| ^ 2 := by positivity
  -- the five monomial blocks
  have m1 : |a₁ * a₁ * (a₂ * b₂)| ≤ max |a₁| |b₁| ^ 2 * max |a₂| |b₂| ^ 2 :=
    abs_mono22 a₁ b₁ a₂ b₂ (habs_a₁ a₁ b₁) (habs_a₁ a₁ b₁)
      (habs_a₂ a₂ b₂) (habs_b₂ a₂ b₂)
  have m2 : |a₁ * b₁ * (a₂ * a₂)| ≤ max |a₁| |b₁| ^ 2 * max |a₂| |b₂| ^ 2 :=
    abs_mono22 a₁ b₁ a₂ b₂ (habs_a₁ a₁ b₁) (habs_b₁ a₁ b₁)
      (habs_a₂ a₂ b₂) (habs_a₂ a₂ b₂)
  have m3 : |a₁ * b₁ * (a₂ * b₂)| ≤ max |a₁| |b₁| ^ 2 * max |a₂| |b₂| ^ 2 :=
    abs_mono22 a₁ b₁ a₂ b₂ (habs_a₁ a₁ b₁) (habs_b₁ a₁ b₁)
      (habs_a₂ a₂ b₂) (habs_b₂ a₂ b₂)
  have m4 : |a₁ * b₁ * (b₂ * b₂)| ≤ max |a₁| |b₁| ^ 2 * max |a₂| |b₂| ^ 2 :=
    abs_mono22 a₁ b₁ a₂ b₂ (habs_a₁ a₁ b₁) (habs_b₁ a₁ b₁)
      (habs_b₂ a₂ b₂) (habs_b₂ a₂ b₂)
  have m5 : |b₁ * b₁ * (a₂ * b₂)| ≤ max |a₁| |b₁| ^ 2 * max |a₂| |b₂| ^ 2 :=
    abs_mono22 a₁ b₁ a₂ b₂ (habs_b₁ a₁ b₁) (habs_b₁ a₁ b₁)
      (habs_a₂ a₂ b₂) (habs_b₂ a₂ b₂)
  have m6 : |b₁ * b₁ * (b₂ * b₂)| ≤ max |a₁| |b₁| ^ 2 * max |a₂| |b₂| ^ 2 :=
    abs_mono22 a₁ b₁ a₂ b₂ (habs_b₁ a₁ b₁) (habs_b₁ a₁ b₁)
      (habs_b₂ a₂ b₂) (habs_b₂ a₂ b₂)
  calc |Sfz B₂ B₄ B₆ a₁ b₁ a₂ b₂|
      = |(2 * (a₁ * a₁ * (a₂ * b₂)) + 2 * (a₁ * b₁ * (a₂ * a₂)))
          + B₂ * (a₁ * b₁ * (a₂ * b₂))
          + (B₄ * (a₁ * b₁ * (b₂ * b₂)) + B₄ * (b₁ * b₁ * (a₂ * b₂)))
          + B₆ * (b₁ * b₁ * (b₂ * b₂))| := by rw [Sfz]; ring_nf
    _ ≤ |2 * (a₁ * a₁ * (a₂ * b₂)) + 2 * (a₁ * b₁ * (a₂ * a₂))|
          + |B₂ * (a₁ * b₁ * (a₂ * b₂))|
          + |B₄ * (a₁ * b₁ * (b₂ * b₂)) + B₄ * (b₁ * b₁ * (a₂ * b₂))|
          + |B₆ * (b₁ * b₁ * (b₂ * b₂))| := by
        refine (abs_add _ _).trans (add_le_add_right ?_ _)
        refine (abs_add _ _).trans (add_le_add_right ?_ _)
        exact abs_add _ _
    _ ≤ (2 * |a₁ * a₁ * (a₂ * b₂)| + 2 * |a₁ * b₁ * (a₂ * a₂)|)
          + |B₂| * |a₁ * b₁ * (a₂ * b₂)|
          + (|B₄| * |a₁ * b₁ * (b₂ * b₂)| + |B₄| * |b₁ * b₁ * (a₂ * b₂)|)
          + |B₆| * |b₁ * b₁ * (b₂ * b₂)| := by
        have t1 : |2 * (a₁ * a₁ * (a₂ * b₂)) + 2 * (a₁ * b₁ * (a₂ * a₂))|
            ≤ 2 * |a₁ * a₁ * (a₂ * b₂)| + 2 * |a₁ * b₁ * (a₂ * a₂)| := by
          refine (abs_add _ _).trans ?_
          simp only [abs_mul]
          norm_num
        have t2 : |B₄ * (a₁ * b₁ * (b₂ * b₂)) + B₄ * (b₁ * b₁ * (a₂ * b₂))|
            ≤ |B₄| * |a₁ * b₁ * (b₂ * b₂)| + |B₄| * |b₁ * b₁ * (a₂ * b₂)| := by
          refine (abs_add _ _).trans ?_
          simp only [abs_mul]
          exact le_refl _
        simp only [abs_mul] at *
        linarith [t1, t2]
    _ ≤ (4 + |B₂| + 2 * |B₄| + |B₆|)
          * (max |a₁| |b₁| ^ 2 * max |a₂| |b₂| ^ 2) := by
        have hB₂ : (0 : ℤ) ≤ |B₂| := abs_nonneg _
        have hB₄ : (0 : ℤ) ≤ |B₄| := abs_nonneg _
        have hB₆ : (0 : ℤ) ≤ |B₆| := abs_nonneg _
        nlinarith [m1, m2, m3, m4, m5, m6,
          mul_le_mul_of_nonneg_left m3 hB₂,
          mul_le_mul_of_nonneg_left m4 hB₄,
          mul_le_mul_of_nonneg_left m5 hB₄,
          mul_le_mul_of_nonneg_left m6 hB₆]

/-- `|Prz| ≤ (1 + |B₄| + 2|B₆| + |B₈|)·H₁²·H₂²`. -/
theorem abs_Prz_le (B₄ B₆ B₈ : ℤ) :
    |Prz B₄ B₆ B₈ a₁ b₁ a₂ b₂|
      ≤ (1 + |B₄| + 2 * |B₆| + |B₈|)
          * (max |a₁| |b₁| ^ 2 * max |a₂| |b₂| ^ 2) := by
  have m0 : |a₁ * a₁ * (a₂ * a₂)| ≤ max |a₁| |b₁| ^ 2 * max |a₂| |b₂| ^ 2 :=
    abs_mono22 a₁ b₁ a₂ b₂ (habs_a₁ a₁ b₁) (habs_a₁ a₁ b₁)
      (habs_a₂ a₂ b₂) (habs_a₂ a₂ b₂)
  have m3 : |a₁ * b₁ * (a₂ * b₂)| ≤ max |a₁| |b₁| ^ 2 * max |a₂| |b₂| ^ 2 :=
    abs_mono22 a₁ b₁ a₂ b₂ (habs_a₁ a₁ b₁) (habs_b₁ a₁ b₁)
      (habs_a₂ a₂ b₂) (habs_b₂ a₂ b₂)
  have m4 : |a₁ * b₁ * (b₂ * b₂)| ≤ max |a₁| |b₁| ^ 2 * max |a₂| |b₂| ^ 2 :=
    abs_mono22 a₁ b₁ a₂ b₂ (habs_a₁ a₁ b₁) (habs_b₁ a₁ b₁)
      (habs_b₂ a₂ b₂) (habs_b₂ a₂ b₂)
  have m5 : |b₁ * b₁ * (a₂ * b₂)| ≤ max |a₁| |b₁| ^ 2 * max |a₂| |b₂| ^ 2 :=
    abs_mono22 a₁ b₁ a₂ b₂ (habs_b₁ a₁ b₁) (habs_b₁ a₁ b₁)
      (habs_a₂ a₂ b₂) (habs_b₂ a₂ b₂)
  have m6 : |b₁ * b₁ * (b₂ * b₂)| ≤ max |a₁| |b₁| ^ 2 * max |a₂| |b₂| ^ 2 :=
    abs_mono22 a₁ b₁ a₂ b₂ (habs_b₁ a₁ b₁) (habs_b₁ a₁ b₁)
      (habs_b₂ a₂ b₂) (habs_b₂ a₂ b₂)
  calc |Prz B₄ B₆ B₈ a₁ b₁ a₂ b₂|
      = |a₁ * a₁ * (a₂ * a₂) - B₄ * (a₁ * b₁ * (a₂ * b₂))
          - (B₆ * (a₁ * b₁ * (b₂ * b₂)) + B₆ * (b₁ * b₁ * (a₂ * b₂)))
          - B₈ * (b₁ * b₁ * (b₂ * b₂))| := by rw [Prz]; ring_nf
    _ ≤ |a₁ * a₁ * (a₂ * a₂)| + |B₄| * |a₁ * b₁ * (a₂ * b₂)|
          + (|B₆| * |a₁ * b₁ * (b₂ * b₂)| + |B₆| * |b₁ * b₁ * (a₂ * b₂)|)
          + |B₈| * |b₁ * b₁ * (b₂ * b₂)| := by
        have s1 := abs_sub (a₁ * a₁ * (a₂ * a₂) - B₄ * (a₁ * b₁ * (a₂ * b₂))
          - (B₆ * (a₁ * b₁ * (b₂ * b₂)) + B₆ * (b₁ * b₁ * (a₂ * b₂))))
          (B₈ * (b₁ * b₁ * (b₂ * b₂)))
        have s2 := abs_sub (a₁ * a₁ * (a₂ * a₂) - B₄ * (a₁ * b₁ * (a₂ * b₂)))
          (B₆ * (a₁ * b₁ * (b₂ * b₂)) + B₆ * (b₁ * b₁ * (a₂ * b₂)))
        have s3 := abs_sub (a₁ * a₁ * (a₂ * a₂)) (B₄ * (a₁ * b₁ * (a₂ * b₂)))
        have s4 := abs_add (B₆ * (a₁ * b₁ * (b₂ * b₂)))
          (B₆ * (b₁ * b₁ * (a₂ * b₂)))
        simp only [abs_mul] at *
        linarith [s1, s2, s3, s4]
    _ ≤ (1 + |B₄| + 2 * |B₆| + |B₈|)
          * (max |a₁| |b₁| ^ 2 * max |a₂| |b₂| ^ 2) := by
        have hB₄ : (0 : ℤ) ≤ |B₄| := abs_nonneg _
        have hB₆ : (0 : ℤ) ≤ |B₆| := abs_nonneg _
        have hB₈ : (0 : ℤ) ≤ |B₈| := abs_nonneg _
        nlinarith [m0, m3, m4, m5, m6,
          mul_le_mul_of_nonneg_left m3 hB₄,
          mul_le_mul_of_nonneg_left m4 hB₆,
          mul_le_mul_of_nonneg_left m5 hB₆,
          mul_le_mul_of_nonneg_left m6 hB₈]

end Size

end PrincipiaTractalis.SecantSizeUniversal

#print axioms PrincipiaTractalis.SecantSizeUniversal.Sfz_spec
#print axioms PrincipiaTractalis.SecantSizeUniversal.Prz_spec
#print axioms PrincipiaTractalis.SecantSizeUniversal.abs_DDz_le
#print axioms PrincipiaTractalis.SecantSizeUniversal.abs_Sfz_le
#print axioms PrincipiaTractalis.SecantSizeUniversal.abs_Prz_le
