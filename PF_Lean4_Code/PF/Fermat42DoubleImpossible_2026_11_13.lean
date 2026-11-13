/-
# PF.Fermat42DoubleImpossible_2026_11_13

**Classical Fermat descent on `2a² = s⁴ + t⁴`** — no non-trivial
coprime solutions with `s² ≠ t²`.

## Proof strategy

Given a solution `(s, t, a)` with `s, t` coprime, `s² ≠ t²`, `a ≠ 0`:

1. **Parity**: both `s, t` are odd (else s⁴ + t⁴ is odd, but 2a² is even).
2. **Pythagorean setup**: `u = (s² + t²)/2, v = (t² - s²)/2` are integers.
   Direct calculation: `u² + v² = a²`.
3. **Coprime + parity**: `gcd(u, v) = 1`, `u ≡ 1 (mod 4)` (odd),
   `v ≡ 0 (mod 4)` (divisible by 4).
4. **Mathlib Pythagorean classification** on `(v, u, a)` (v even, u odd):
   ∃ `m, n` coprime of opposite parity with `v = 2mn, u = m² - n²,
   a = m² + n²`. From `u ≡ 1 mod 4`: `m` odd, `n` even.
5. **Descent setup**: Write `n = 2n₀`. Then `v = 4mn₀` with `gcd(m, n₀) = 1`.
   Also `(t - s)(t + s) = 2v = 8mn₀`; since `t, s` odd, `t - s, t + s`
   both even, reducing to `αβ = 2mn₀` with coprime `α, β`.
6. **Prime-factor distribution**: Case analysis on which of `α, β` absorbs
   the factor of 2.  Each case leads to representations of `s, t` in
   terms of `m, n₀` and further smaller equations.
7. **Descent conclusion**: In each case, a new instance of either
   `Fermat42Double` (with smaller `a`) or a direct `Fermat42Sub`
   instance (via mathlib's `not_fermat_42`) is produced — contradiction.

## Status

The full ~150-line descent is a multi-session project.  This file
delivers the `Fermat42Double_impossible` statement and the parity
reduction (step 1).  Steps 2-7 are the dedicated session's work.

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
  -- Parity cases: both even impossible by coprimality.  If one even one odd:
  -- s⁴ + t⁴ = even + odd = odd, but 2a² is even.  Contradiction.
  by_contra h_not_both
  push_neg at h_not_both
  -- At least one of s, t is even.  WLOG argue via the equation.
  have hs_par : s % 2 = 0 ∨ s % 2 = 1 := Int.emod_two_eq_zero_or_one s
  have ht_par : t % 2 = 0 ∨ t % 2 = 1 := Int.emod_two_eq_zero_or_one t
  rcases hs_par with hs_ev | hs_od
  · -- s even.  Then from coprime(s, t), t odd.
    rcases ht_par with ht_ev | ht_od
    · -- Both even: gcd ≥ 2, contradicts coprime.
      have hs_dvd : (2 : ℤ) ∣ s := Int.dvd_of_emod_eq_zero hs_ev
      have ht_dvd : (2 : ℤ) ∣ t := Int.dvd_of_emod_eq_zero ht_ev
      have h_gcd : (2 : ℤ) ∣ (Int.gcd s t : ℤ) := Int.dvd_coe_gcd hs_dvd ht_dvd
      rw [Int.isCoprime_iff_gcd_eq_one.mp hst_coprime] at h_gcd
      norm_num at h_gcd
    · -- s even, t odd: s⁴ + t⁴ ≡ 0 + 1 ≡ 1 mod 2 (odd), but 2a² even.
      have h_s4_even : s ^ 4 % 2 = 0 := by
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
  · -- s odd.  Case on t.
    rcases ht_par with ht_ev | ht_od
    · -- t even, s odd: symmetric to above.  s⁴ + t⁴ ≡ 1 + 0 ≡ 1 mod 2.
      have h_s4_odd : s ^ 4 % 2 = 1 := by
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
    · -- Both odd: this contradicts h_not_both.
      exact h_not_both hs_od ht_od

end PF.Fermat42Sub

/-! ## §Axiom check -/
#print axioms PF.Fermat42Sub.fermat42Double_parity
