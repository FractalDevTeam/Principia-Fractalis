/-
# PF.QuasiParallelogramUpper389a1_r148f

★★★ 2026-07-28 — r148f: THE UPPER QUASI-PARALLELOGRAM BOUND ★★★

The assembly of W2 for 389a1.  Joining

  * r148d — `x(P₁+P₂) + x(P₁−P₂) = Sfnum/dd`, `x(P₁+P₂)·x(P₁−P₂) = Prnum/dd`
  * r148e — heights of the roots of an integer quadratic: `≤ 2·max(|A|,|B|,|C|)`
  * r148c — `|DD| ≤ 4H₁²H₂²`, `|Sf| ≤ 17H₁²H₂²`, `|Pf| ≤ 10H₁²H₂²`

gives, for any two on-curve rational points with distinct x-coordinates,

    `h(x(P₁+P₂)) · h(x(P₁−P₂)) ≤ 34 · h(x₁)² · h(x₂)²`

and in logarithmic form the upper half of the quasi-parallelogram law:

    `lognh(P₁+P₂) + lognh(P₁−P₂) ≤ 2·lognh(P₁) + 2·lognh(P₂) + log 34`.

The chain of identifications that makes this work: with `x₁ = a₁/b₁` and
`x₂ = a₂/b₂` reduced, the rational coefficients `Sfnum/dd`, `Prnum/dd` are
*exactly* `Sf/DD`, `Pf/DD` for the integer forms of r148a — so the integer
quadratic whose roots are `x(P₁±P₂)` has coefficients `(DD, Sf, Pf)`, whose
sizes r148c already bounds.

HONEST SCOPE.  The UPPER half only.  The lower half (needed for the exact
parallelogram in the limit) follows from this bound applied to the pair
`(P+Q, P−Q)` together with r143's duplication lower bound — that is the
next stone (r148g) and requires point-level group manipulation, not just
x-coordinate algebra.  No canonical-height or rank claim is made here.

Kernel axioms ⊆ `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-28.
-/
import PF.SecantBridge389a1_r148d
import PF.QuadraticRootHeights_r148e
import PF.QuasiParallelogramSize389a1_r148c

namespace PrincipiaTractalis.QuasiParallelogramUpper389a1

open PrincipiaTractalis.NaiveHeightQ
open PrincipiaTractalis.E389a1RankOne
open WeierstrassCurve WeierstrassCurve.Affine
open PrincipiaTractalis.SecantBridge389a1
open PrincipiaTractalis.QuadraticRootHeights
open PrincipiaTractalis.QuasiParallelogramCerts389a1
open PrincipiaTractalis.QuasiParallelogramSize389a1

/-! ## §1 — the denominator form is nonzero for distinct x -/

/-- For distinct rationals the cross-difference of the reduced coordinates is
nonzero, hence `DD ≠ 0`. -/
theorem DD_ne_zero {x₁ x₂ : ℚ} (hx : x₁ ≠ x₂) :
    DD x₁.num ((x₁.den : ℤ)) x₂.num ((x₂.den : ℤ)) ≠ 0 := by
  have hd₁ : ((x₁.den : ℚ)) ≠ 0 := by exact_mod_cast x₁.den_ne_zero
  have hd₂ : ((x₂.den : ℚ)) ≠ 0 := by exact_mod_cast x₂.den_ne_zero
  have hcross : x₁.num * ((x₂.den : ℤ)) - x₂.num * ((x₁.den : ℤ)) ≠ 0 := by
    intro h0
    apply hx
    have hQ : (x₁.num : ℚ) * ((x₂.den : ℚ)) = (x₂.num : ℚ) * ((x₁.den : ℚ)) := by
      have : ((x₁.num * ((x₂.den : ℤ)) - x₂.num * ((x₁.den : ℤ)) : ℤ) : ℚ) = 0 := by
        rw [h0]; norm_num
      push_cast at this
      linarith [this]
    calc x₁ = (x₁.num : ℚ) / ((x₁.den : ℚ)) := (Rat.num_div_den x₁).symm
      _ = (x₂.num : ℚ) / ((x₂.den : ℚ)) := by
          rw [div_eq_div_iff hd₁ hd₂]; exact hQ
      _ = x₂ := Rat.num_div_den x₂
  simp only [DD]
  exact pow_ne_zero 2 hcross

/-! ## §2 — the rational coefficients ARE the integer forms -/

section Coeffs

variable {x₁ x₂ : ℚ}

/-- `dd = (x₁−x₂)²` expressed through `DD`: `DD = dd · (b₁b₂)²`. -/
theorem DD_cast (x₁ x₂ : ℚ) :
    ((DD x₁.num ((x₁.den : ℤ)) x₂.num ((x₂.den : ℤ)) : ℤ) : ℚ)
      = (x₁ - x₂) ^ 2 * (((x₁.den : ℚ)) * ((x₂.den : ℚ))) ^ 2 := by
  have hd₁ : ((x₁.den : ℚ)) ≠ 0 := by exact_mod_cast x₁.den_ne_zero
  have hd₂ : ((x₂.den : ℚ)) ≠ 0 := by exact_mod_cast x₂.den_ne_zero
  have hn₁ : (x₁.num : ℚ) = x₁ * ((x₁.den : ℚ)) :=
    (div_eq_iff hd₁).mp (Rat.num_div_den x₁)
  have hn₂ : (x₂.num : ℚ) = x₂ * ((x₂.den : ℚ)) :=
    (div_eq_iff hd₂).mp (Rat.num_div_den x₂)
  simp only [DD]
  push_cast
  rw [hn₁, hn₂]
  ring

/-- `Sf` is `dd·(b₁b₂)²` times the rational sum coefficient. -/
theorem Sf_cast (x₁ x₂ : ℚ) :
    ((Sf x₁.num ((x₁.den : ℤ)) x₂.num ((x₂.den : ℤ)) : ℤ) : ℚ)
      = Sfnum x₁ x₂ * (((x₁.den : ℚ)) * ((x₂.den : ℚ))) ^ 2 := by
  have hd₁ : ((x₁.den : ℚ)) ≠ 0 := by exact_mod_cast x₁.den_ne_zero
  have hd₂ : ((x₂.den : ℚ)) ≠ 0 := by exact_mod_cast x₂.den_ne_zero
  have hn₁ : (x₁.num : ℚ) = x₁ * ((x₁.den : ℚ)) :=
    (div_eq_iff hd₁).mp (Rat.num_div_den x₁)
  have hn₂ : (x₂.num : ℚ) = x₂ * ((x₂.den : ℚ)) :=
    (div_eq_iff hd₂).mp (Rat.num_div_den x₂)
  simp only [Sf, Sfnum]
  push_cast
  rw [hn₁, hn₂]
  ring

/-- `Pf` is `dd·(b₁b₂)²` times the rational product coefficient. -/
theorem Pf_cast (x₁ x₂ : ℚ) :
    ((Pf x₁.num ((x₁.den : ℤ)) x₂.num ((x₂.den : ℤ)) : ℤ) : ℚ)
      = Prnum x₁ x₂ * (((x₁.den : ℚ)) * ((x₂.den : ℚ))) ^ 2 := by
  have hd₁ : ((x₁.den : ℚ)) ≠ 0 := by exact_mod_cast x₁.den_ne_zero
  have hd₂ : ((x₂.den : ℚ)) ≠ 0 := by exact_mod_cast x₂.den_ne_zero
  have hn₁ : (x₁.num : ℚ) = x₁ * ((x₁.den : ℚ)) :=
    (div_eq_iff hd₁).mp (Rat.num_div_den x₁)
  have hn₂ : (x₂.num : ℚ) = x₂ * ((x₂.den : ℚ)) :=
    (div_eq_iff hd₂).mp (Rat.num_div_den x₂)
  simp only [Pf, Prnum]
  push_cast
  rw [hn₁, hn₂]
  ring

end Coeffs

/-! ## §3 — the integer quadratic satisfied by `x(P₁±P₂)` -/

/-- **The addition quadratic has integer coefficients `(DD, Sf, Pf)`.**
Sum form: `DD·(x₃ + x₄) = Sf`. -/
theorem DD_mul_sum {x₁ x₂ y₁ y₂ : ℚ} (hx : x₁ ≠ x₂)
    (hE₁ : y₁ ^ 2 + y₁ = x₁ ^ 3 + x₁ ^ 2 - 2 * x₁)
    (hE₂ : y₂ ^ 2 + y₂ = x₂ ^ 3 + x₂ ^ 2 - 2 * x₂) :
    ((DD x₁.num ((x₁.den : ℤ)) x₂.num ((x₂.den : ℤ)) : ℤ) : ℚ)
        * (xAdd x₁ x₂ y₁ y₂ + xAdd x₁ x₂ y₁ (E389a1.toAffine.negY x₂ y₂))
      = ((Sf x₁.num ((x₁.den : ℤ)) x₂.num ((x₂.den : ℤ)) : ℤ) : ℚ) := by
  have hsub : (x₁ - x₂ : ℚ) ≠ 0 := sub_ne_zero.mpr hx
  have hdd : ((x₁ - x₂) ^ 2 : ℚ) ≠ 0 := pow_ne_zero 2 hsub
  rw [xAdd_sum hx hE₁ hE₂, DD_cast, Sf_cast]
  field_simp

/-- Product form: `DD·(x₃ · x₄) = Pf`. -/
theorem DD_mul_prod {x₁ x₂ y₁ y₂ : ℚ} (hx : x₁ ≠ x₂)
    (hE₁ : y₁ ^ 2 + y₁ = x₁ ^ 3 + x₁ ^ 2 - 2 * x₁)
    (hE₂ : y₂ ^ 2 + y₂ = x₂ ^ 3 + x₂ ^ 2 - 2 * x₂) :
    ((DD x₁.num ((x₁.den : ℤ)) x₂.num ((x₂.den : ℤ)) : ℤ) : ℚ)
        * (xAdd x₁ x₂ y₁ y₂ * xAdd x₁ x₂ y₁ (E389a1.toAffine.negY x₂ y₂))
      = ((Pf x₁.num ((x₁.den : ℤ)) x₂.num ((x₂.den : ℤ)) : ℤ) : ℚ) := by
  have hsub : (x₁ - x₂ : ℚ) ≠ 0 := sub_ne_zero.mpr hx
  have hdd : ((x₁ - x₂) ^ 2 : ℚ) ≠ 0 := pow_ne_zero 2 hsub
  rw [xAdd_prod hx hE₁ hE₂, DD_cast, Pf_cast]
  field_simp

/-! ## §4 — the size bound on the coefficient triple -/

/-- `max(|DD|, |Sf|, |Pf|) ≤ 17·h(x₁)²·h(x₂)²`. -/
theorem coeff_max_le (x₁ x₂ : ℚ) :
    max (max (DD x₁.num ((x₁.den : ℤ)) x₂.num ((x₂.den : ℤ))).natAbs
          (Sf x₁.num ((x₁.den : ℤ)) x₂.num ((x₂.den : ℤ))).natAbs)
        (Pf x₁.num ((x₁.den : ℤ)) x₂.num ((x₂.den : ℤ))).natAbs
      ≤ 17 * naiveHeight x₁ ^ 2 * naiveHeight x₂ ^ 2 := by
  have hH₁ : max x₁.num.natAbs ((x₁.den : ℤ)).natAbs = naiveHeight x₁ := by
    simp only [naiveHeight, Int.natAbs_natCast]
  have hH₂ : max x₂.num.natAbs ((x₂.den : ℤ)).natAbs = naiveHeight x₂ := by
    simp only [naiveHeight, Int.natAbs_natCast]
  have hD := DD_upper x₁.num ((x₁.den : ℤ)) x₂.num ((x₂.den : ℤ))
  have hS := Sf_upper x₁.num ((x₁.den : ℤ)) x₂.num ((x₂.den : ℤ))
  have hP := Pf_upper x₁.num ((x₁.den : ℤ)) x₂.num ((x₂.den : ℤ))
  rw [hH₁, hH₂] at hD hS hP
  refine max_le (max_le ?_ hS) ?_
  · exact le_trans hD (by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num)))
  · exact le_trans hP (by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num)))

/-! ## §5 — THE CAPSTONE: the upper quasi-parallelogram bound -/

/-- **★★★ r148f — THE UPPER QUASI-PARALLELOGRAM BOUND ★★★**

For two on-curve rational points of 389a1 with distinct x-coordinates:

  `h(x(P₁+P₂)) · h(x(P₁−P₂)) ≤ 34 · h(x₁)² · h(x₂)²`. -/
theorem height_prod_upper {x₁ x₂ y₁ y₂ : ℚ} (hx : x₁ ≠ x₂)
    (hE₁ : y₁ ^ 2 + y₁ = x₁ ^ 3 + x₁ ^ 2 - 2 * x₁)
    (hE₂ : y₂ ^ 2 + y₂ = x₂ ^ 3 + x₂ ^ 2 - 2 * x₂) :
    naiveHeight (xAdd x₁ x₂ y₁ y₂)
        * naiveHeight (xAdd x₁ x₂ y₁ (E389a1.toAffine.negY x₂ y₂))
      ≤ 34 * naiveHeight x₁ ^ 2 * naiveHeight x₂ ^ 2 := by
  have hDD := DD_ne_zero hx
  have hroots := naiveHeight_mul_le_of_quadratic (A := DD x₁.num ((x₁.den : ℤ))
      x₂.num ((x₂.den : ℤ))) (B := Sf x₁.num ((x₁.den : ℤ)) x₂.num ((x₂.den : ℤ)))
      (C := Pf x₁.num ((x₁.den : ℤ)) x₂.num ((x₂.den : ℤ)))
      hDD (DD_mul_sum hx hE₁ hE₂) (DD_mul_prod hx hE₁ hE₂)
  calc naiveHeight (xAdd x₁ x₂ y₁ y₂)
          * naiveHeight (xAdd x₁ x₂ y₁ (E389a1.toAffine.negY x₂ y₂))
      ≤ 2 * max (max (DD x₁.num ((x₁.den : ℤ)) x₂.num ((x₂.den : ℤ))).natAbs
            (Sf x₁.num ((x₁.den : ℤ)) x₂.num ((x₂.den : ℤ))).natAbs)
          (Pf x₁.num ((x₁.den : ℤ)) x₂.num ((x₂.den : ℤ))).natAbs := hroots
    _ ≤ 2 * (17 * naiveHeight x₁ ^ 2 * naiveHeight x₂ ^ 2) :=
        Nat.mul_le_mul_left 2 (coeff_max_le x₁ x₂)
    _ = 34 * naiveHeight x₁ ^ 2 * naiveHeight x₂ ^ 2 := by ring

/-- The same bound in logarithmic form — the upper half of the
quasi-parallelogram law, ready for the canonical-height limit. -/
theorem log_upper {x₁ x₂ y₁ y₂ : ℚ} (hx : x₁ ≠ x₂)
    (hE₁ : y₁ ^ 2 + y₁ = x₁ ^ 3 + x₁ ^ 2 - 2 * x₁)
    (hE₂ : y₂ ^ 2 + y₂ = x₂ ^ 3 + x₂ ^ 2 - 2 * x₂) :
    Real.log (naiveHeight (xAdd x₁ x₂ y₁ y₂))
        + Real.log (naiveHeight (xAdd x₁ x₂ y₁ (E389a1.toAffine.negY x₂ y₂)))
      ≤ 2 * Real.log (naiveHeight x₁) + 2 * Real.log (naiveHeight x₂)
        + Real.log 34 := by
  have h1 : (1 : ℕ) ≤ naiveHeight (xAdd x₁ x₂ y₁ y₂) := one_le_naiveHeight _
  have h2 : (1 : ℕ) ≤ naiveHeight (xAdd x₁ x₂ y₁ (E389a1.toAffine.negY x₂ y₂)) :=
    one_le_naiveHeight _
  have hx1 : (1 : ℕ) ≤ naiveHeight x₁ := one_le_naiveHeight _
  have hx2 : (1 : ℕ) ≤ naiveHeight x₂ := one_le_naiveHeight _
  have hprod := height_prod_upper hx hE₁ hE₂
  -- move to ℝ and take logs
  have hR : ((naiveHeight (xAdd x₁ x₂ y₁ y₂) : ℝ))
      * ((naiveHeight (xAdd x₁ x₂ y₁ (E389a1.toAffine.negY x₂ y₂)) : ℝ))
      ≤ 34 * (naiveHeight x₁ : ℝ) ^ 2 * (naiveHeight x₂ : ℝ) ^ 2 := by
    have := (Nat.cast_le (α := ℝ)).mpr hprod
    push_cast at this
    linarith [this]
  have hpos1 : (0 : ℝ) < (naiveHeight (xAdd x₁ x₂ y₁ y₂) : ℝ) := by
    exact_mod_cast naiveHeight_pos _
  have hpos2 : (0 : ℝ)
      < (naiveHeight (xAdd x₁ x₂ y₁ (E389a1.toAffine.negY x₂ y₂)) : ℝ) := by
    exact_mod_cast naiveHeight_pos _
  have hposx1 : (0 : ℝ) < (naiveHeight x₁ : ℝ) := by
    exact_mod_cast naiveHeight_pos _
  have hposx2 : (0 : ℝ) < (naiveHeight x₂ : ℝ) := by
    exact_mod_cast naiveHeight_pos _
  have hlog := Real.log_le_log (by positivity) hR
  rw [Real.log_mul (ne_of_gt hpos1) (ne_of_gt hpos2)] at hlog
  have hrhs : Real.log (34 * (naiveHeight x₁ : ℝ) ^ 2 * (naiveHeight x₂ : ℝ) ^ 2)
      = Real.log 34 + 2 * Real.log (naiveHeight x₁)
        + 2 * Real.log (naiveHeight x₂) := by
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity),
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  rw [hrhs] at hlog
  linarith [hlog]

end PrincipiaTractalis.QuasiParallelogramUpper389a1

#print axioms PrincipiaTractalis.QuasiParallelogramUpper389a1.DD_ne_zero
#print axioms PrincipiaTractalis.QuasiParallelogramUpper389a1.DD_mul_sum
#print axioms PrincipiaTractalis.QuasiParallelogramUpper389a1.DD_mul_prod
#print axioms PrincipiaTractalis.QuasiParallelogramUpper389a1.coeff_max_le
#print axioms PrincipiaTractalis.QuasiParallelogramUpper389a1.height_prod_upper
#print axioms PrincipiaTractalis.QuasiParallelogramUpper389a1.log_upper
