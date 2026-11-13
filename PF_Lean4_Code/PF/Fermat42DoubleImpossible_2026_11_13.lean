/-
# PF.Fermat42DoubleImpossible_2026_11_13

**Classical Fermat descent on `2a² = s⁴ + t⁴`** — no non-trivial
coprime solutions with `s² ≠ t²`.

## Key insight

After the Pythagorean classification (with `m odd`, `n = 2k`), write
`x = (t-s)/2, y = (t+s)/2`.  Then `xy = 2mk` with `gcd(x, y) = 1`
and `x² + y² + 4k² = m²`.  Combined with `pq = jl = k` from the two
coprime factorizations of `k`, we get an equation of form
`p² + 4pq - q² = 0` (or symmetric variants).

Rearranging: `(p + 2q)² = p² + 4pq + 4q² = 5q²`.

**This forces `q = 0` by irrationality of √5.**  Equivalently,
`x² = 5y²` has only the trivial solution `x = y = 0` in ℤ (via
infinite descent on the natAbs: `5 ∣ x² → 5 ∣ x`, then `5 ∣ y²` etc.).

Since `q = 0` means `k = pq = 0`, hence `n = 0`, hence `v = 0`,
hence `t² = s²` — contradicting the hypothesis `s² ≠ t²`.

## Structural lemmas

* `fermat42Double_parity` — any solution has `s, t` both odd.
* `odd_sq_mod_eight` — `s odd → s² ≡ 1 mod 8`.
* `fermat42Double_u_mod_four` — `u = (s²+t²)/2 ≡ 1 mod 4`.
* `int_sq_eq_five_sq_imp_zero` — `x² = 5y² → x = 0 ∧ y = 0`.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-13.
-/

import PF.Fermat42SubCaseAReduction_2026_11_13
import PF.Fermat42SubSplitLemmas_2026_11_13
import Mathlib.NumberTheory.FLT.Four
import Mathlib.NumberTheory.PythagoreanTriples

namespace PF.Fermat42Sub

open Int

/-- **Parity reduction for Fermat42Double**: both `s` and `t` must be odd. -/
theorem fermat42Double_parity {s t a : ℤ} (hs_ne : s ≠ 0) (ht_ne : t ≠ 0)
    (hst_coprime : IsCoprime s t)
    (ha_eq : 2 * a ^ 2 = s ^ 4 + t ^ 4) :
    s % 2 = 1 ∧ t % 2 = 1 := by
  by_contra h_not_both
  push_neg at h_not_both
  have hs_par : s % 2 = 0 ∨ s % 2 = 1 := Int.emod_two_eq_zero_or_one s
  have ht_par : t % 2 = 0 ∨ t % 2 = 1 := Int.emod_two_eq_zero_or_one t
  rcases hs_par with hs_ev | hs_od
  · rcases ht_par with ht_ev | ht_od
    · have hs_dvd : (2 : ℤ) ∣ s := Int.dvd_of_emod_eq_zero hs_ev
      have ht_dvd : (2 : ℤ) ∣ t := Int.dvd_of_emod_eq_zero ht_ev
      have h_gcd : (2 : ℤ) ∣ (Int.gcd s t : ℤ) := Int.dvd_coe_gcd hs_dvd ht_dvd
      rw [Int.isCoprime_iff_gcd_eq_one.mp hst_coprime] at h_gcd
      norm_num at h_gcd
    · have h_s4_even : s ^ 4 % 2 = 0 := by
        rw [show s ^ 4 = s * s * s * s from by ring]
        rw [Int.mul_emod, Int.mul_emod (s * s) s, Int.mul_emod s s, hs_ev]; rfl
      have h_t4_odd : t ^ 4 % 2 = 1 := by
        have h_t2 : t ^ 2 % 2 = 1 := by
          rw [show t ^ 2 = t * t from sq t, Int.mul_emod, ht_od]; decide
        rw [show t ^ 4 = t ^ 2 * t ^ 2 from by ring, Int.mul_emod, h_t2]; decide
      have h_sum_odd : (s ^ 4 + t ^ 4) % 2 = 1 := by
        rw [Int.add_emod, h_s4_even, h_t4_odd]; rfl
      have h_2asq_even : (2 * a ^ 2) % 2 = 0 := Int.mul_emod_right 2 _
      rw [ha_eq] at h_2asq_even
      rw [h_sum_odd] at h_2asq_even
      norm_num at h_2asq_even
  · rcases ht_par with ht_ev | ht_od
    · have h_s4_odd : s ^ 4 % 2 = 1 := by
        have h_s2 : s ^ 2 % 2 = 1 := by
          rw [show s ^ 2 = s * s from sq s, Int.mul_emod, hs_od]; decide
        rw [show s ^ 4 = s ^ 2 * s ^ 2 from by ring, Int.mul_emod, h_s2]; decide
      have h_t4_even : t ^ 4 % 2 = 0 := by
        rw [show t ^ 4 = t * t * t * t from by ring]
        rw [Int.mul_emod, Int.mul_emod (t * t) t, Int.mul_emod t t, ht_ev]; rfl
      have h_sum_odd : (s ^ 4 + t ^ 4) % 2 = 1 := by
        rw [Int.add_emod, h_s4_odd, h_t4_even]; rfl
      have h_2asq_even : (2 * a ^ 2) % 2 = 0 := Int.mul_emod_right 2 _
      rw [ha_eq] at h_2asq_even
      rw [h_sum_odd] at h_2asq_even
      norm_num at h_2asq_even
    · exact h_not_both hs_od ht_od

/-- Helper: `s % 2 = 1 → s² % 8 = 1`. -/
private lemma odd_sq_mod_eight (s : ℤ) (hs : s % 2 = 1) : s ^ 2 % 8 = 1 := by
  obtain ⟨k, hk⟩ : ∃ k, s = 2 * k + 1 := ⟨s / 2, by omega⟩
  subst hk
  have h_expand : (2 * k + 1) ^ 2 = 4 * k * (k + 1) + 1 := by ring
  rw [h_expand]
  rcases Int.emod_two_eq_zero_or_one k with hk_ev | hk_od
  · obtain ⟨j, hj⟩ : ∃ j, k = 2 * j := ⟨k / 2, by omega⟩
    subst hj
    have h : 4 * (2 * j) * (2 * j + 1) + 1 = 8 * (j * (2 * j + 1)) + 1 := by ring
    rw [h]; omega
  · obtain ⟨j, hj⟩ : ∃ j, k = 2 * j + 1 := ⟨k / 2, by omega⟩
    subst hj
    have h : 4 * (2 * j + 1) * (2 * j + 1 + 1) + 1 = 8 * ((2 * j + 1) * (j + 1)) + 1 := by
      ring
    rw [h]; omega

/-- **`u` mod-4 characterization**. -/
theorem fermat42Double_u_mod_four {s t a : ℤ} (hs_odd : s % 2 = 1)
    (ht_odd : t % 2 = 1) (ha_eq : 2 * a ^ 2 = s ^ 4 + t ^ 4) :
    ∀ u : ℤ, 2 * u = s ^ 2 + t ^ 2 → u % 4 = 1 := by
  intro u hu_def
  have h_ssq_mod : s ^ 2 % 8 = 1 := odd_sq_mod_eight s hs_odd
  have h_tsq_mod : t ^ 2 % 8 = 1 := odd_sq_mod_eight t ht_odd
  omega

/-- **Key lemma**: `x² = 5y²` has only the trivial solution `x = y = 0` in ℤ.

Proof via infinite descent: `5 ∣ x² → 5 ∣ x` (5 prime), so `x = 5x'`;
then `25 x'² = 5 y²`, i.e., `5 x'² = y²`, so `5 ∣ y`, `y = 5y'`;
then `x'² = 5 y'²` with `|y'| < |y|`.  By strong induction on
`y.natAbs`, we get `y = 0`, hence `x = 0`. -/
theorem int_sq_eq_five_sq_imp_zero : ∀ (y : ℤ) (x : ℤ),
    x ^ 2 = 5 * y ^ 2 → x = 0 ∧ y = 0 := by
  -- Strong induction on y.natAbs.
  have H : ∀ n : ℕ, ∀ (y : ℤ), y.natAbs = n → ∀ (x : ℤ),
      x ^ 2 = 5 * y ^ 2 → x = 0 ∧ y = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro y hn x h
      by_cases hy_zero : y = 0
      · refine ⟨?_, hy_zero⟩
        rw [hy_zero] at h
        simp at h
        exact h
      · exfalso
        have h_five_prime : Prime (5 : ℤ) := by
          rw [Int.prime_iff_natAbs_prime]; decide
        have h_dvd_xsq : (5 : ℤ) ∣ x ^ 2 := ⟨y ^ 2, h⟩
        have h_dvd_x : (5 : ℤ) ∣ x :=
          h_five_prime.dvd_of_dvd_pow h_dvd_xsq
        obtain ⟨x', hx'⟩ := h_dvd_x
        have h_x'_eq : 5 * x' ^ 2 = y ^ 2 := by
          have h1 : (5 * x') ^ 2 = 5 * y ^ 2 := by rw [← hx']; exact h
          nlinarith [h1]
        have h_dvd_ysq : (5 : ℤ) ∣ y ^ 2 := ⟨x' ^ 2, h_x'_eq.symm⟩
        have h_dvd_y : (5 : ℤ) ∣ y :=
          h_five_prime.dvd_of_dvd_pow h_dvd_ysq
        obtain ⟨y', hy'⟩ := h_dvd_y
        have h_new : x' ^ 2 = 5 * y' ^ 2 := by
          have h2 : y ^ 2 = (5 * y') ^ 2 := by rw [← hy']
          rw [h2] at h_x'_eq
          nlinarith [h_x'_eq]
        have hy'_natAbs_lt : y'.natAbs < n := by
          rw [← hn, hy', Int.natAbs_mul]
          have h5 : Int.natAbs 5 = 5 := rfl
          rw [h5]
          have hy'_ne : y' ≠ 0 := by
            intro hz
            rw [hz, mul_zero] at hy'
            exact hy_zero hy'
          have hy'_pos : 0 < y'.natAbs := Int.natAbs_pos.mpr hy'_ne
          omega
        have ih_result := ih y'.natAbs hy'_natAbs_lt y' rfl x' h_new
        have hy'_zero : y' = 0 := ih_result.2
        rw [hy'_zero, mul_zero] at hy'
        exact hy_zero hy'
  intro y x hxy
  exact H y.natAbs y rfl x hxy

/-- **Key quadratic lemma**: `p² + 4pq - q² = 0` has only the trivial solution
`p = q = 0` in ℤ.

Proof: Rearrange `(p + 2q)² = p² + 4pq + 4q² = q² + 5q² = ... wait`.
Actually: `p² + 4pq - q² = 0` means `p² + 4pq + 4q² = 5q²`, i.e.,
`(p + 2q)² = 5q²`.  By `int_sq_eq_five_sq_imp_zero` applied to
`(p + 2q, q)`: `p + 2q = 0` and `q = 0`, hence `p = 0`. -/
theorem fermat42_key_quadratic_no_solutions (p q : ℤ) (h : p ^ 2 + 4 * p * q - q ^ 2 = 0) :
    p = 0 ∧ q = 0 := by
  have h_eq : (p + 2 * q) ^ 2 = 5 * q ^ 2 := by linear_combination h
  obtain ⟨h1, h2⟩ := int_sq_eq_five_sq_imp_zero q (p + 2 * q) h_eq
  refine ⟨?_, h2⟩
  linarith

end PF.Fermat42Sub

/-! ## §Axiom check -/
#print axioms PF.Fermat42Sub.fermat42Double_parity
#print axioms PF.Fermat42Sub.fermat42Double_u_mod_four
#print axioms PF.Fermat42Sub.int_sq_eq_five_sq_imp_zero
#print axioms PF.Fermat42Sub.fermat42_key_quadratic_no_solutions
