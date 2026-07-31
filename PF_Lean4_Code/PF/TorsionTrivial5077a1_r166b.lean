/-
# PF.TorsionTrivial5077a1_r166b

★★★ 2026-07-31 — 5077a1 IS TORSION-FREE ★★★

Bridges r166a's integer finite check to `ℚ`, and concludes

    `IsOfFinAddOrder R → R = 0`   and   `R ≠ 0 → 0 < ĥ(R)`

for the Buhler–Gross–Zagier rank-3 curve.  This removes the non-torsion side
conditions from r164's parallelogram law and r165's multiple law.

## The bridge

r166a proves the check over `ℤ`, because over `ℚ` it does not fit in memory.
Connecting the two needs one fact r133 establishes internally but does not
export: for `Q ≠ 0`, the reduced pair of `(p:ℚ)/(Q:ℚ)` is `(p/d, Q/d)` with
`d = gcd(p,Q)` **up to a single common sign**.  `exists_common_factor` gives
`k ≠ 0` with `p = num·k`, `Q = den·k`, and `gcd(p,Q) = |k|`; dividing,
`(p/d, Q/d) = sign(k)·(num, den)`.  Since `F` has even degree and `D = b·G3`
with `G3` odd, both are invariant under `(a,b) ↦ (−a,−b)` (r166a's `Fp_neg`,
`Dp_neg`), so that common sign is irrelevant — which is what makes the
second duplication step expressible on `(F/d, D/d)` directly.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-31.
-/
import PF.TorsionCheck5077a1_r166a
import PF.CanheightMultiple5077a1_r165
import PF.DuplicationHeightBound37a1_r133

namespace PrincipiaTractalis.TorsionTrivial5077a1

open PrincipiaTractalis.NaiveHeightQ
open PrincipiaTractalis.E5077a1RankOne
open PrincipiaTractalis.CanonicalHeight5077a1
open PrincipiaTractalis.TorsionCheck5077a1
open PrincipiaTractalis.DuplicationHeightBound37a1 (exists_common_factor naiveHeight_div_int)
open WeierstrassCurve WeierstrassCurve.Affine

/-! ## §1 — r166a's forms are r144's forms -/

theorem Fp_eq (a b : ℤ) : Fp a b = F a b := by simp only [Fp, F]
theorem Dp_eq (a b : ℤ) : Dp a b = D a b := by simp only [Dp, G3p, D, G3]

/-! ## §2 — the reduced pair, up to one common sign -/

/-- For `Q ≠ 0` the pair `(p/d, Q/d)`, `d = gcd(p,Q)`, equals the reduced pair
of `(p:ℚ)/(Q:ℚ)` up to a single common sign. -/
theorem pair_eq_signed (p Q : ℤ) (hQ : Q ≠ 0) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      p / (Int.gcd p Q : ℤ) = ε * ((p : ℚ) / (Q : ℚ)).num ∧
      Q / (Int.gcd p Q : ℤ) = ε * ((((p : ℚ) / (Q : ℚ)).den : ℤ)) := by
  obtain ⟨k, hk0, hpk, hQk⟩ := exists_common_factor p Q hQ
  set r : ℚ := (p : ℚ) / (Q : ℚ) with hr
  have hd : Int.gcd p Q = k.natAbs := by
    rw [hpk, hQk]
    unfold Int.gcd
    rw [Int.natAbs_mul, Int.natAbs_mul, Nat.gcd_mul_right, Int.natAbs_natCast,
      r.reduced.gcd_eq_one, one_mul]
  have hkabs : ((Int.gcd p Q : ℤ)) = |k| := by
    rw [hd]; exact (Int.abs_eq_natAbs k).symm
  rcases abs_choice k with hk | hk
  · refine ⟨1, Or.inl rfl, ?_, ?_⟩
    · rw [hkabs, hk, hpk, one_mul, Int.mul_ediv_cancel _ hk0]
    · rw [hkabs, hk, hQk, one_mul, Int.mul_ediv_cancel _ hk0]
  · refine ⟨-1, Or.inr rfl, ?_, ?_⟩
    · have hkne : -k ≠ 0 := neg_ne_zero.mpr hk0
      rw [hkabs, hk, hpk]
      have : r.num * k = (-r.num) * (-k) := by ring
      rw [this, Int.mul_ediv_cancel _ hkne]; ring
    · have hkne : -k ≠ 0 := neg_ne_zero.mpr hk0
      rw [hkabs, hk, hQk]
      have : ((r.den : ℤ)) * k = (-(r.den : ℤ)) * (-k) := by ring
      rw [this, Int.mul_ediv_cancel _ hkne]; ring

/-- Consequence: `F` and `D` evaluated at `(p/d, Q/d)` agree with their values
at the reduced pair, because both forms are sign-invariant. -/
theorem Fp_Dp_at_reduced (p Q : ℤ) (hQ : Q ≠ 0) :
    Fp (p / (Int.gcd p Q : ℤ)) (Q / (Int.gcd p Q : ℤ))
        = Fp ((p : ℚ) / (Q : ℚ)).num ((((p : ℚ) / (Q : ℚ)).den : ℤ)) ∧
      Dp (p / (Int.gcd p Q : ℤ)) (Q / (Int.gcd p Q : ℤ))
        = Dp ((p : ℚ) / (Q : ℚ)).num ((((p : ℚ) / (Q : ℚ)).den : ℤ)) := by
  obtain ⟨ε, hε, hp, hq⟩ := pair_eq_signed p Q hQ
  rcases hε with h1 | h1
  · subst h1; rw [hp, hq]; constructor <;> ring_nf
  · subst h1
    rw [hp, hq]
    have e1 : (-1 : ℤ) * ((p : ℚ) / (Q : ℚ)).num = -((p : ℚ) / (Q : ℚ)).num := by ring
    have e2 : (-1 : ℤ) * ((((p : ℚ) / (Q : ℚ)).den : ℤ))
        = -((((p : ℚ) / (Q : ℚ)).den : ℤ)) := by ring
    rw [e1, e2]
    exact ⟨Fp_neg _ _, Dp_neg _ _⟩

/-! ## §3 — the height of one duplication step, in `ℤ` -/

/-- Generic cast, with `a b` FREE.  Specialising after the fact avoids rewriting
`x` inside its own `.num`/`.den`. -/
private theorem F_cast' (a b : ℤ) (hb : ((b : ℚ)) ≠ 0) :
    ((F a b : ℤ) : ℚ) = ((b : ℚ)) ^ 4 * f ((a : ℚ) / ((b : ℚ))) := by
  simp only [F, f]; push_cast; field_simp

private theorem D_cast' (a b : ℤ) (hb : ((b : ℚ)) ≠ 0) :
    ((D a b : ℤ) : ℚ) = ((b : ℚ)) ^ 4 * g ((a : ℚ) / ((b : ℚ))) := by
  simp only [D, G3, g]; push_cast; field_simp

/-- `D` is nonzero at the coordinates of any rational (`g` has no rational
zero, r144's `g_ne_zero`). -/
theorem D_ne_zero (x : ℚ) : D x.num ((x.den : ℤ)) ≠ 0 := by
  have hbQ : (((x.den : ℤ)) : ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have hx : x = (x.num : ℚ) / (((x.den : ℤ)) : ℚ) := by
    rw [Int.cast_natCast]; exact (Rat.num_div_den x).symm
  have hDc := D_cast' x.num ((x.den : ℤ)) hbQ
  rw [← hx] at hDc
  intro h0
  rw [h0] at hDc
  simp only [Int.cast_zero] at hDc
  rcases mul_eq_zero.mp hDc.symm with h | h
  · exact absurd h (by positivity)
  · exact g_ne_zero x h

/-- **The step bridge.**  `naiveHeight (f x / g x) = hgt (F …) (D …)`. -/
theorem naiveHeight_step (x : ℚ) :
    naiveHeight (f x / g x) = hgt (Fp x.num ((x.den : ℤ))) (Dp x.num ((x.den : ℤ))) := by
  have hbQ : (((x.den : ℤ)) : ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have hD := D_ne_zero x
  have hx : x = (x.num : ℚ) / (((x.den : ℤ)) : ℚ) := by
    rw [Int.cast_natCast]; exact (Rat.num_div_den x).symm
  have hF := F_cast' x.num ((x.den : ℤ)) hbQ
  have hDc := D_cast' x.num ((x.den : ℤ)) hbQ
  rw [← hx] at hF hDc
  have hgx : g x ≠ 0 := g_ne_zero x
  have hfg : f x / g x
      = ((F x.num ((x.den : ℤ)) : ℤ) : ℚ) / ((D x.num ((x.den : ℤ)) : ℤ) : ℚ) := by
    rw [hF, hDc]
    field_simp
  rw [hfg, naiveHeight_div_int _ _ hD, Fp_eq, Dp_eq]
  rfl


/-- The duplication step as an explicit integer fraction. -/
theorem step_eq (x : ℚ) :
    f x / g x
      = ((Fp x.num ((x.den : ℤ)) : ℤ) : ℚ) / ((Dp x.num ((x.den : ℤ)) : ℤ) : ℚ) := by
  have hbQ : (((x.den : ℤ)) : ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have hx : x = (x.num : ℚ) / (((x.den : ℤ)) : ℚ) := by
    rw [Int.cast_natCast]; exact (Rat.num_div_den x).symm
  have hF := F_cast' x.num ((x.den : ℤ)) hbQ
  have hDc := D_cast' x.num ((x.den : ℤ)) hbQ
  rw [← hx] at hF hDc
  have hgx : g x ≠ 0 := g_ne_zero x
  rw [Fp_eq, Dp_eq, hF, hDc]
  field_simp

/-! ## §4 — the second step, on `(F/d, D/d)` -/

/-- **The two-step bridge.**  The second duplication height is `hgt` at the
reduced pair `(sN, sD)` of the first — no sign normalisation needed, by
`Fp_Dp_at_reduced`. -/
theorem naiveHeight_step_two (x : ℚ) :
    naiveHeight (f (f x / g x) / g (f x / g x))
      = hgt (Fp (sN x.num ((x.den : ℤ))) (sD x.num ((x.den : ℤ))))
            (Dp (sN x.num ((x.den : ℤ))) (sD x.num ((x.den : ℤ)))) := by
  set a := x.num; set b := ((x.den : ℤ))
  have hD : Dp a b ≠ 0 := by rw [Dp_eq]; exact D_ne_zero x
  have hx' : f x / g x = ((Fp a b : ℤ) : ℚ) / ((Dp a b : ℤ) : ℚ) := step_eq x
  obtain ⟨hFe, hDe⟩ := Fp_Dp_at_reduced (Fp a b) (Dp a b) hD
  rw [naiveHeight_step (f x / g x), hx']
  simp only [sN, sD]
  rw [hFe, hDe]

/-! ## §5 — the candidate indices -/

/-- A rational of naïve height `≤ 47` is `((i:ℤ)-47)/((j:ℤ)+1)` for indices in
the ranges `all_escape` quantifies over. -/
theorem index_of_le {x : ℚ} (h : naiveHeight x ≤ 47) :
    ∃ i ∈ Finset.range 95, ∃ j ∈ Finset.range 47,
      ((i : ℤ) - 47) = x.num ∧ ((j : ℤ) + 1) = ((x.den : ℤ)) := by
  have hn : x.num.natAbs ≤ 47 := le_trans (le_max_left _ _) h
  have hd : x.den ≤ 47 := le_trans (le_max_right _ _) h
  have hd1 : 1 ≤ x.den := x.pos
  refine ⟨(x.num + 47).toNat, Finset.mem_range.mpr (by omega),
          x.den - 1, Finset.mem_range.mpr (by omega), ?_, ?_⟩
  · have ht : ((x.num + 47).toNat : ℤ) = x.num + 47 := Int.toNat_of_nonneg (by omega)
    rw [ht]; ring
  · have ht : ((x.den - 1 : ℕ) : ℤ) = (x.den : ℤ) - 1 := by
      have : (1 : ℕ) ≤ x.den := hd1
      push_cast [Nat.cast_sub this]; ring
    rw [ht]; ring

/-! ## §6 — two doublings in `X`-form -/

theorem two_zsmul_eq (R : E5077a1.toAffine.Point) : (2 : ℤ) • R = R + R := by
  rw [show (2 : ℤ) = 1 + 1 from rfl, add_smul, one_smul]

theorem X_two_smul {x₀ y₀ : ℚ} (h₀ : E5077a1.toAffine.Nonsingular x₀ y₀) :
    X ((2 : ℤ) • Point.some h₀) = f x₀ / g x₀ := by
  obtain ⟨x₁, y₁, h₁, e₁, hx₁⟩ := dbl_x h₀
  have s₁ : (2 : ℤ) • Point.some h₀ = Point.some h₁ := by
    rw [two_zsmul_eq]; exact e₁
  rw [s₁]; show x₁ = _; exact hx₁

theorem X_four_smul {x₀ y₀ : ℚ} (h₀ : E5077a1.toAffine.Nonsingular x₀ y₀) :
    X (((2 : ℤ) ^ 2) • Point.some h₀)
      = f (f x₀ / g x₀) / g (f x₀ / g x₀) := by
  obtain ⟨x₁, y₁, h₁, e₁, hx₁⟩ := dbl_x h₀
  obtain ⟨x₂, y₂, h₂, e₂, hx₂⟩ := dbl_x h₁
  have h4 : ((2 : ℤ) ^ 2) • Point.some h₀
      = (2 : ℤ) • ((2 : ℤ) • Point.some h₀) := by
    rw [smul_smul]; norm_num
  have s₁ : (2 : ℤ) • Point.some h₀ = Point.some h₁ := by
    rw [two_zsmul_eq]; exact e₁
  have s₂ : (2 : ℤ) • Point.some h₁ = Point.some h₂ := by
    rw [two_zsmul_eq]; exact e₂
  rw [h4, s₁, s₂]; show x₂ = _; rw [hx₂, hx₁]

/-! ## §7 — THE CAPSTONE -/

/-- **★ 5077a1 IS TORSION-FREE ★** -/
theorem torsion_eq_zero {R : E5077a1.toAffine.Point}
    (h : IsOfFinAddOrder R) : R = 0 := by
  by_contra hne
  have h0 : canheight R = 0 := canheight_of_torsion h
  cases R with
  | zero => exact hne rfl
  | @some x y hxy =>
      have b0 := naiveHeight_le_47_of_canheight_zero h0 0
      have b1 := naiveHeight_le_47_of_canheight_zero h0 1
      have b2 := naiveHeight_le_47_of_canheight_zero h0 2
      rw [pow_zero, one_zsmul] at b0
      rw [pow_one, X_two_smul hxy] at b1
      rw [X_four_smul hxy] at b2
      have hx : X (Point.some hxy) = x := rfl
      rw [hx] at b0
      rw [naiveHeight_step x] at b1
      rw [naiveHeight_step_two x] at b2
      obtain ⟨i, hi, j, hj, hnum, hden⟩ := index_of_le b0
      have hcontra := all_escape i hi j hj
      rw [hnum, hden] at hcontra
      exact hcontra ⟨b1, b2⟩

theorem nonTorsion_of_ne_zero {R : E5077a1.toAffine.Point} (h : R ≠ 0) :
    ¬ IsOfFinAddOrder R :=
  fun hfin => h (torsion_eq_zero hfin)

/-- **The payoff.**  r164's parallelogram law and r165's multiple law lose
their side conditions for 5077a1. -/
theorem canheight_pos_of_ne_zero {R : E5077a1.toAffine.Point} (h : R ≠ 0) :
    0 < canheight R := by
  rcases lt_or_eq_of_le (canheight_nonneg R) with hlt | heq
  · exact hlt
  · exact absurd (canheight_eq_zero_torsion heq.symm) (nonTorsion_of_ne_zero h)

end PrincipiaTractalis.TorsionTrivial5077a1

#print axioms PrincipiaTractalis.TorsionTrivial5077a1.pair_eq_signed
#print axioms PrincipiaTractalis.TorsionTrivial5077a1.Fp_Dp_at_reduced
#print axioms PrincipiaTractalis.TorsionTrivial5077a1.D_ne_zero
#print axioms PrincipiaTractalis.TorsionTrivial5077a1.naiveHeight_step
#print axioms PrincipiaTractalis.TorsionTrivial5077a1.naiveHeight_step_two
#print axioms PrincipiaTractalis.TorsionTrivial5077a1.torsion_eq_zero
#print axioms PrincipiaTractalis.TorsionTrivial5077a1.canheight_pos_of_ne_zero
