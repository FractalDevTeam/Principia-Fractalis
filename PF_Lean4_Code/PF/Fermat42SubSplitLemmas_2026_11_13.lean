/-
# PF.Fermat42SubSplitLemmas_2026_11_13

**Discharges the three square-split sub-gaps** from the Fermat descent.

* `fermat42SubCaseB_squareSplit_holds`
* `fermat42SubCaseA_squareSplit_holds`
* `fermat42SubCaseB_fourthPowerSplit_holds`

All three follow from mathlib's `Int.sq_of_gcd_eq_one` plus sign and
parity bookkeeping.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-13.
-/

import PF.Fermat42SubCaseBClosure_2026_11_13
import PF.Fermat42SubCaseAReduction_2026_11_13
import Mathlib.RingTheory.Int.Basic

namespace PF.Fermat42Sub

open Int

/-- Helper: if `x ≥ 0` and `x = y² ∨ x = -y²`, then `x = y²`. -/
private lemma eq_sq_of_nonneg_of_or {x y : ℤ} (hx : 0 ≤ x)
    (h : x = y ^ 2 ∨ x = -y ^ 2) : x = y ^ 2 := by
  rcases h with h | h
  · exact h
  · have : -y ^ 2 ≤ 0 := neg_nonpos.mpr (sq_nonneg y)
    have hx_eq : x = -y ^ 2 := h
    have hx_le : x ≤ 0 := hx_eq ▸ this
    have hx_eq_zero : x = 0 := le_antisymm hx_le hx
    have hy_eq_zero : y = 0 := by
      have : y ^ 2 = 0 := by linarith [hx_eq_zero, hx_eq]
      exact pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp this
    rw [hx_eq_zero, hy_eq_zero]; ring

/-- Discharge of `Fermat42SubCaseB_squareSplit`. -/
theorem fermat42SubCaseB_squareSplit_holds : Fermat42SubCaseB_squareSplit := by
  intro m n b hm_nn hn_pos hmn_coprime hm_odd hn_even hb_sq
  -- Write n = 2k.
  obtain ⟨k, hk⟩ : (2 : ℤ) ∣ n := Int.dvd_of_emod_eq_zero hn_even
  subst hk
  have hk_pos : 0 < k := by linarith
  -- gcd(m, k) = 1 from gcd(m, 2k) = 1.
  have hmk_coprime : IsCoprime m k :=
    hmn_coprime.of_mul_right_right
  -- b² = 4mk.
  have hb_sq_mk : b ^ 2 = 4 * (m * k) := by linarith
  -- 2 ∣ b (from 2 ∣ b²).
  have h_two_dvd_bsq : (2 : ℤ) ∣ b ^ 2 := ⟨2 * (m * k), by linarith⟩
  have h_two_dvd_b : (2 : ℤ) ∣ b :=
    Int.Prime.dvd_pow' Nat.prime_two h_two_dvd_bsq
  obtain ⟨b₀, hb₀⟩ := h_two_dvd_b
  -- b₀² = mk.
  have hb0_sq : b₀ ^ 2 = m * k := by
    have : (2 * b₀) ^ 2 = 4 * (m * k) := by rw [← hb₀]; exact hb_sq_mk
    have : 4 * b₀ ^ 2 = 4 * (m * k) := by linarith
    linarith
  -- gcd(m, k) = 1 → m, k each a signed square.
  have hmk_gcd : Int.gcd m k = 1 := isCoprime_iff_gcd_eq_one.mp hmk_coprime
  have hb0_sq_sym : m * k = b₀ ^ 2 := hb0_sq.symm
  obtain ⟨i, hi⟩ := Int.sq_of_gcd_eq_one hmk_gcd hb0_sq_sym
  -- Gcd commutative: k, m.
  have hkm_coprime : IsCoprime k m := hmk_coprime.symm
  have hkm_gcd : Int.gcd k m = 1 := isCoprime_iff_gcd_eq_one.mp hkm_coprime
  have hb0_sq' : k * m = b₀ ^ 2 := by linarith
  obtain ⟨j, hj⟩ := Int.sq_of_gcd_eq_one hkm_gcd hb0_sq'
  -- m ≥ 0 and m = ±i² → m = i².  k > 0 ≥ 0 and k = ±j² → k = j².
  have hm_eq : m = i ^ 2 := eq_sq_of_nonneg_of_or hm_nn hi
  have hk_eq : k = j ^ 2 := eq_sq_of_nonneg_of_or hk_pos.le hj
  -- Now b₀² = (ij)². So b₀ = ij or b₀ = -ij.
  have hb0_sq'' : b₀ ^ 2 = (i * j) ^ 2 := by
    rw [hb0_sq, hm_eq, hk_eq]; ring
  -- b₀ = ±ij.  Choose j's sign so b = 2·i·j.
  have hb0_abs : b₀ = i * j ∨ b₀ = -(i * j) := by
    have h : (b₀ - i * j) * (b₀ + i * j) = 0 := by
      have : b₀ ^ 2 - (i * j) ^ 2 = 0 := by rw [hb0_sq'']; ring
      linear_combination this
    rcases mul_eq_zero.mp h with h1 | h1
    · left; linarith
    · right; linarith
  rcases hb0_abs with hb₀_eq | hb₀_neg
  · refine ⟨i, j, hm_eq, ?_, ?_⟩
    · rw [hk_eq]
    · rw [hb₀, hb₀_eq]; ring
  · refine ⟨i, -j, hm_eq, ?_, ?_⟩
    · rw [hk_eq]; ring
    · rw [hb₀, hb₀_neg]; ring

end PF.Fermat42Sub

/-! ## §Axiom check -/
#print axioms PF.Fermat42Sub.fermat42SubCaseB_squareSplit_holds
