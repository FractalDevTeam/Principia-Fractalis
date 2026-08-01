/-
# PF.DuplicationHeightUniversal_r176

★★★ 2026-08-01 — THE DUPLICATION HEIGHT WINDOW, FOR EVERY CURVE ★★★

r174 gave the content bound (`gcd(Φ,Ψ) ∣ Δ²`) and r175 the size bounds, both
uniformly in the curve.  Both are stated on ℤ-homogeneous coordinates.  This
stone crosses to actual rational heights and closes the multiplicative window:

  `H(x)⁴ ≤ CL · H(x(2P))`   and   `H(x(2P)) ≤ CU · H(x)⁴`

for **every** rational Weierstrass curve, from its coefficients alone.

## The crossing

For `x = X/Y` in lowest terms the duplication map is `Φ(X,Y)/Ψ(X,Y)`, but that
fraction need not be reduced — its content is exactly what r174 bounds.  Writing
`g = gcd(Φ,Ψ)`, the bridge lemma is

  `g · H(Φ/Ψ) = max |Φ| |Ψ|`

so `g ≥ 1` gives the upper bound and `g ≤ Δ²` (r174) gives the lower one.  The
`Δ²` then cancels against the `Δ²` in r175's lower estimate, which is why the
final constants are just `CU` and `CL`.

## The formula was checked against the group law, not assumed

`dblQ` uses `Φ/Ψ` with `Φ = x⁴ − b₄x² − 2b₆x − b₈`, `Ψ = 4x³ + b₂x² + 2b₄x + b₆`
(Silverman AEC III.2.3(d)).  A sign slip there would silently invalidate
everything downstream, so it was tested against the affine group law at eight
on-curve points across both curves — 389a1 `(0,0) (1,0) (-1,1) (3,5)` and
5077a1 `(-3,0) (-2,3) (0,2) (1,0)`.  All eight agree exactly.

## What this reuses

`pair_eq_signed` — that a fraction's numerator and denominator, divided by their
gcd, agree with `Rat.num`/`Rat.den` up to one shared sign — was proved in r166b
for 5077a1 but stated fully generally.  It is imported rather than restated.

## Remaining to reach `HeightWindow`

r171's `HeightWindow` wants the *logarithmic* form, `|log H(2R) − 4 log H(R)| ≤
log κ`.  That is a direct consequence of the two bounds here with
`κ = max(CU, CL)`, and is pure ℝ-arithmetic — no arithmetic geometry left.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-08-01.
-/
import PF.DuplicationSizeUniversal_r175
import PF.TorsionTrivial5077a1_r166b

set_option maxHeartbeats 1000000

namespace PrincipiaTractalis.DuplicationHeight

open PrincipiaTractalis.DuplicationBezout PrincipiaTractalis.DuplicationSize

/-- The naive height of a rational: `max |num| den`. -/
def nh (x : ℚ) : ℤ := max |x.num| (x.den : ℤ)

theorem nh_pos (x : ℚ) : 0 < nh x :=
  lt_of_lt_of_le (by exact_mod_cast x.pos) (le_max_right _ _)

theorem nh_nonneg (x : ℚ) : 0 ≤ nh x := le_of_lt (nh_pos x)

/-- `nh` in the form r175's bounds produce: both entries under `|·|`. -/
theorem nh_eq_max_abs (x : ℚ) : nh x = max |x.num| |(x.den : ℤ)| := by
  rw [nh, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (x.den : ℤ))]

/-- **The bridge.**  For any fraction `p/q`, the content times the reduced
height is the unreduced max. -/
theorem gcd_mul_nh (p q : ℤ) (hq : q ≠ 0) :
    (Int.gcd p q : ℤ) * nh ((p : ℚ) / (q : ℚ)) = max |p| |q| := by
  set g : ℤ := (Int.gcd p q : ℤ) with hgdef
  have hgpos : 0 < g := by
    rw [hgdef]; exact_mod_cast Int.gcd_pos_of_ne_zero_right p hq
  obtain ⟨ε, hε, hp, hq'⟩ :=
    PrincipiaTractalis.TorsionTrivial5077a1.pair_eq_signed p q hq
  have habs_eps : |ε| = 1 := by rcases hε with h | h <;> simp [h]
  have hdp : g ∣ p := Int.gcd_dvd_left p q
  have hdq : g ∣ q := Int.gcd_dvd_right p q
  have hP : |p| = g * |((p : ℚ) / (q : ℚ)).num| := by
    have hrw : p = g * (ε * ((p : ℚ) / (q : ℚ)).num) := by
      rw [← hp, Int.mul_ediv_cancel' hdp]
    conv_lhs => rw [hrw]
    rw [abs_mul, abs_of_pos hgpos, abs_mul, habs_eps, one_mul]
  have hQ : |q| = g * ((((p : ℚ) / (q : ℚ)).den : ℤ)) := by
    have hrw : q = g * (ε * ((((p : ℚ) / (q : ℚ)).den : ℤ))) := by
      rw [← hq', Int.mul_ediv_cancel' hdq]
    conv_lhs => rw [hrw]
    rw [abs_mul, abs_of_pos hgpos, abs_mul, habs_eps, one_mul,
      abs_of_nonneg (by positivity : (0 : ℤ) ≤ ((((p : ℚ) / (q : ℚ)).den : ℤ)))]
  rw [hP, hQ, nh, ← mul_max_of_nonneg _ _ (le_of_lt hgpos)]

/-- The duplication map on `x`-coordinates, as a rational function of `x`. -/
def dblQ (b₂ b₄ b₆ b₈ : ℤ) (x : ℚ) : ℚ :=
  (Phi b₄ b₆ b₈ x.num (x.den : ℤ) : ℚ) / (Psi b₂ b₄ b₆ x.num (x.den : ℤ) : ℚ)

variable {b₂ b₄ b₆ b₈ : ℤ}

/-- `x.num` and `x.den` are coprime in the `IsCoprime` sense r174 wants. -/
theorem isCoprime_num_den (x : ℚ) : IsCoprime x.num (x.den : ℤ) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  simpa [Int.gcd] using x.reduced

section
variable (hrel : 4 * b₈ = b₂ * b₆ - b₄ ^ 2) (x : ℚ)
  (hΨ : Psi b₂ b₄ b₆ x.num (x.den : ℤ) ≠ 0)

/-- The content of the unreduced duplication fraction, named. -/
private noncomputable abbrev gg : ℤ :=
  (Int.gcd (Phi b₄ b₆ b₈ x.num (x.den : ℤ)) (Psi b₂ b₄ b₆ x.num (x.den : ℤ)) : ℤ)

include hΨ in
theorem gcd_mul_nh_dblQ :
    gg (b₂ := b₂) (b₄ := b₄) (b₆ := b₆) (b₈ := b₈) x * nh (dblQ b₂ b₄ b₆ b₈ x)
      = max |Phi b₄ b₆ b₈ x.num (x.den : ℤ)| |Psi b₂ b₄ b₆ x.num (x.den : ℤ)| :=
  gcd_mul_nh _ _ hΨ

include hΨ in
/-- **Upper bound**: `H(x(2P)) ≤ CU · H(x)⁴`, for every curve. -/
theorem nh_dblQ_le : nh (dblQ b₂ b₄ b₆ b₈ x) ≤ CU b₂ b₄ b₆ b₈ * nh x ^ 4 := by
  have hg1 : 1 ≤ gg (b₂ := b₂) (b₄ := b₄) (b₆ := b₆) (b₈ := b₈) x := by
    have : (0 : ℤ) < gg (b₂ := b₂) (b₄ := b₄) (b₆ := b₆) (b₈ := b₈) x := by
      exact_mod_cast Int.gcd_pos_of_ne_zero_right _ hΨ
    omega
  have hstep : nh (dblQ b₂ b₄ b₆ b₈ x)
      ≤ gg (b₂ := b₂) (b₄ := b₄) (b₆ := b₆) (b₈ := b₈) x * nh (dblQ b₂ b₄ b₆ b₈ x) :=
    le_mul_of_one_le_left (nh_nonneg _) hg1
  refine hstep.trans ?_
  rw [gcd_mul_nh_dblQ x hΨ]
  have := max_abs_le (b₂ := b₂) (b₄ := b₄) (b₆ := b₆) (b₈ := b₈) x.num (x.den : ℤ)
  rwa [← nh_eq_max_abs x] at this

include hrel hΨ in
/-- **Lower bound**: `H(x)⁴ ≤ CL · H(x(2P))`, for every curve.

The `Δ²` from r174's content bound cancels the `Δ²` in r175's size estimate, so
no discriminant survives into the constant. -/
theorem nh_pow_le_of_disc_ne_zero (hΔ : Disc b₂ b₄ b₆ b₈ ≠ 0) :
    nh x ^ 4 ≤ CL b₂ b₄ b₆ b₈ * nh (dblQ b₂ b₄ b₆ b₈ x) := by
  set g : ℤ := gg (b₂ := b₂) (b₄ := b₄) (b₆ := b₆) (b₈ := b₈) x with hgdef
  have hD2 : (0 : ℤ) < Disc b₂ b₄ b₆ b₈ ^ 2 := by positivity
  have hgpos : (0 : ℤ) < g := by
    rw [hgdef]; exact_mod_cast Int.gcd_pos_of_ne_zero_right _ hΨ
  -- r174: the content divides Δ², hence is at most Δ².
  have hgdvd : g ∣ Disc b₂ b₄ b₆ b₈ ^ 2 :=
    dvd_disc_sq_of_isCoprime b₂ b₄ b₆ b₈ hrel (isCoprime_num_den x)
      (Int.gcd_dvd_left _ _) (Int.gcd_dvd_right _ _)
  have hgle : g ≤ Disc b₂ b₄ b₆ b₈ ^ 2 := Int.le_of_dvd hD2 hgdvd
  -- r175: the size lower bound, with `max |Φ| |Ψ|` rewritten via the bridge.
  have hsize := disc_sq_mul_le (b₂ := b₂) (b₄ := b₄) (b₆ := b₆) (b₈ := b₈) hrel
    x.num (x.den : ℤ)
  rw [← nh_eq_max_abs x, ← gcd_mul_nh_dblQ x hΨ, ← hgdef] at hsize
  -- Replace `g` by `Δ²`, which is legitimate upward.
  have hCL : (0 : ℤ) ≤ CL b₂ b₄ b₆ b₈ := CL_nonneg b₂ b₄ b₆ b₈
  have hup : CL b₂ b₄ b₆ b₈ * (g * nh (dblQ b₂ b₄ b₆ b₈ x))
      ≤ Disc b₂ b₄ b₆ b₈ ^ 2 * (CL b₂ b₄ b₆ b₈ * nh (dblQ b₂ b₄ b₆ b₈ x)) := by
    have : CL b₂ b₄ b₆ b₈ * (g * nh (dblQ b₂ b₄ b₆ b₈ x))
        = g * (CL b₂ b₄ b₆ b₈ * nh (dblQ b₂ b₄ b₆ b₈ x)) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hgle
      (mul_nonneg hCL (nh_nonneg _))
  -- Cancel Δ².
  refine le_of_mul_le_mul_left ?_ hD2
  exact hsize.trans hup

end

/-! ### Validation: the two hand-built curves.

389a1 has `(b₂,b₄,b₆,b₈) = (4,-4,1,-3)`, `Δ = 389`;
5077a1 has `(0,-14,25,-49)`, `Δ = 5077`.  Both discriminants are nonzero and
both satisfy the b-relation, so the universal window applies to each with no
curve-specific input whatsoever. -/

theorem window_389a1 (x : ℚ) (hΨ : Psi 4 (-4) 1 x.num (x.den : ℤ) ≠ 0) :
    nh (dblQ 4 (-4) 1 (-3) x) ≤ CU 4 (-4) 1 (-3) * nh x ^ 4
      ∧ nh x ^ 4 ≤ CL 4 (-4) 1 (-3) * nh (dblQ 4 (-4) 1 (-3) x) :=
  ⟨nh_dblQ_le x hΨ,
   nh_pow_le_of_disc_ne_zero b_relation_389a1 x hΨ (by rw [disc_389a1]; decide)⟩

theorem window_5077a1 (x : ℚ) (hΨ : Psi 0 (-14) 25 x.num (x.den : ℤ) ≠ 0) :
    nh (dblQ 0 (-14) 25 (-49) x) ≤ CU 0 (-14) 25 (-49) * nh x ^ 4
      ∧ nh x ^ 4 ≤ CL 0 (-14) 25 (-49) * nh (dblQ 0 (-14) 25 (-49) x) :=
  ⟨nh_dblQ_le x hΨ,
   nh_pow_le_of_disc_ne_zero b_relation_5077a1 x hΨ (by rw [disc_5077a1]; decide)⟩

end PrincipiaTractalis.DuplicationHeight

#print axioms PrincipiaTractalis.DuplicationHeight.gcd_mul_nh
#print axioms PrincipiaTractalis.DuplicationHeight.nh_dblQ_le
#print axioms PrincipiaTractalis.DuplicationHeight.nh_pow_le_of_disc_ne_zero
#print axioms PrincipiaTractalis.DuplicationHeight.window_389a1
#print axioms PrincipiaTractalis.DuplicationHeight.window_5077a1
