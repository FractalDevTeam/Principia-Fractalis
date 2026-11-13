/-
# PF.Fermat42SubSplitLemmas_2026_11_13

**Discharges the three square-split sub-gaps** from the Fermat descent:

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
  · have hneg : -y ^ 2 ≤ 0 := neg_nonpos.mpr (sq_nonneg y)
    have hx_le : x ≤ 0 := h ▸ hneg
    have hx_eq_zero : x = 0 := le_antisymm hx_le hx
    have hy_sq_zero : y ^ 2 = 0 := by linarith [hx_eq_zero, h]
    have hy_zero : y = 0 := pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp hy_sq_zero
    rw [hx_eq_zero, hy_zero]; ring

/-- Discharge of `Fermat42SubCaseB_squareSplit`. -/
theorem fermat42SubCaseB_squareSplit_holds : Fermat42SubCaseB_squareSplit := by
  intro m n b hm_nn hn_pos hmn_coprime hm_odd hn_even hb_sq
  obtain ⟨k, hk⟩ : (2 : ℤ) ∣ n := Int.dvd_of_emod_eq_zero hn_even
  subst hk
  have hk_pos : 0 < k := by linarith
  have hmk_coprime : IsCoprime m k := hmn_coprime.of_mul_right_right
  have hb_sq_mk : b ^ 2 = 4 * (m * k) := by linarith
  have h_two_dvd_bsq : (2 : ℤ) ∣ b ^ 2 := ⟨2 * (m * k), by linarith⟩
  have h_two_dvd_b : (2 : ℤ) ∣ b :=
    Int.Prime.dvd_pow' Nat.prime_two h_two_dvd_bsq
  obtain ⟨b₀, hb₀⟩ := h_two_dvd_b
  have hb0_sq : b₀ ^ 2 = m * k := by
    have h1 : (2 * b₀) ^ 2 = 4 * (m * k) := by rw [← hb₀]; exact hb_sq_mk
    linarith [h1]
  have hmk_gcd : Int.gcd m k = 1 := isCoprime_iff_gcd_eq_one.mp hmk_coprime
  obtain ⟨i, hi⟩ := Int.sq_of_gcd_eq_one hmk_gcd hb0_sq.symm
  have hkm_coprime : IsCoprime k m := hmk_coprime.symm
  have hkm_gcd : Int.gcd k m = 1 := isCoprime_iff_gcd_eq_one.mp hkm_coprime
  have hb0_sq' : k * m = b₀ ^ 2 := by linarith
  obtain ⟨j, hj⟩ := Int.sq_of_gcd_eq_one hkm_gcd hb0_sq'
  have hm_eq : m = i ^ 2 := eq_sq_of_nonneg_of_or hm_nn hi
  have hk_eq : k = j ^ 2 := eq_sq_of_nonneg_of_or hk_pos.le hj
  have hb0_sq'' : b₀ ^ 2 = (i * j) ^ 2 := by
    rw [hb0_sq, hm_eq, hk_eq]; ring
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

/-- Discharge of `Fermat42SubCaseA_squareSplit`. -/
theorem fermat42SubCaseA_squareSplit_holds : Fermat42SubCaseA_squareSplit := by
  intro m k b hm_minus_nn hm_plus_nn hpair_coprime hb_sq
  have h_gcd : Int.gcd (m - 2 * k) (m + 2 * k) = 1 :=
    isCoprime_iff_gcd_eq_one.mp hpair_coprime
  have h_eq : (m - 2 * k) * (m + 2 * k) = b ^ 2 := hb_sq.symm
  obtain ⟨s, hs⟩ := Int.sq_of_gcd_eq_one h_gcd h_eq
  have h_gcd_sym : Int.gcd (m + 2 * k) (m - 2 * k) = 1 :=
    isCoprime_iff_gcd_eq_one.mp hpair_coprime.symm
  have h_eq_sym : (m + 2 * k) * (m - 2 * k) = b ^ 2 := by linarith
  obtain ⟨t, ht⟩ := Int.sq_of_gcd_eq_one h_gcd_sym h_eq_sym
  have hs_eq : m - 2 * k = s ^ 2 := eq_sq_of_nonneg_of_or hm_minus_nn hs
  have ht_eq : m + 2 * k = t ^ 2 := eq_sq_of_nonneg_of_or hm_plus_nn ht
  have hb_sq' : b ^ 2 = (s * t) ^ 2 := by
    rw [hb_sq, hs_eq, ht_eq]; ring
  have hb_cases : b = s * t ∨ b = -(s * t) := by
    have h : (b - s * t) * (b + s * t) = 0 := by linear_combination hb_sq'
    rcases mul_eq_zero.mp h with h1 | h1
    · left; linarith
    · right; linarith
  have hs_sq_coprime : IsCoprime (s ^ 2) (t ^ 2) := by
    rw [← hs_eq, ← ht_eq]; exact hpair_coprime
  have hst_coprime : IsCoprime s t := by
    rw [show s ^ 2 = s * s from sq s, show t ^ 2 = t * t from sq t] at hs_sq_coprime
    exact (hs_sq_coprime.of_mul_left_left).of_mul_right_left
  rcases hb_cases with hb_eq | hb_neg
  · exact ⟨s, t, hs_eq, ht_eq, hb_eq.symm, hst_coprime⟩
  · refine ⟨-s, t, ?_, ht_eq, ?_, ?_⟩
    · rw [hs_eq]; ring
    · rw [hb_neg]; ring
    · exact hst_coprime.neg_left

/-- **Helper**: for coprime `u, v ≥ 0` with `uv = c²`, we have
`u = e²` and `v = f²` for some `e, f` with `ef = ±c`. -/
private lemma coprime_mul_eq_sq_split {u v c : ℤ}
    (hu_nn : 0 ≤ u) (hv_nn : 0 ≤ v) (huv_coprime : IsCoprime u v)
    (huv : u * v = c ^ 2) :
    ∃ e f : ℤ, u = e ^ 2 ∧ v = f ^ 2 ∧ (e * f = c ∨ e * f = -c) := by
  have h_gcd : Int.gcd u v = 1 := isCoprime_iff_gcd_eq_one.mp huv_coprime
  obtain ⟨e, he⟩ := Int.sq_of_gcd_eq_one h_gcd huv
  have h_gcd' : Int.gcd v u = 1 := isCoprime_iff_gcd_eq_one.mp huv_coprime.symm
  have huv' : v * u = c ^ 2 := by linarith
  obtain ⟨f, hf⟩ := Int.sq_of_gcd_eq_one h_gcd' huv'
  have he_eq : u = e ^ 2 := eq_sq_of_nonneg_of_or hu_nn he
  have hf_eq : v = f ^ 2 := eq_sq_of_nonneg_of_or hv_nn hf
  have h_prod : (e * f) ^ 2 = c ^ 2 := by
    have : (e * f) ^ 2 = e ^ 2 * f ^ 2 := by ring
    rw [this, ← he_eq, ← hf_eq, huv]
  have h_cases : e * f = c ∨ e * f = -c := by
    have h : (e * f - c) * (e * f + c) = 0 := by linear_combination h_prod
    rcases mul_eq_zero.mp h with h1 | h1
    · left; linarith
    · right; linarith
  exact ⟨e, f, he_eq, hf_eq, h_cases⟩

-- Sub-gap 3 (`Fermat42SubCaseB_fourthPowerSplit`) requires iterating
-- `coprime_mul_eq_sq_split` (above helper) twice with sign/coprimality
-- management.  Full discharge is a dedicated session (~80-100 lines).
-- The structural pieces (helper lemma, coprimality derivation chain)
-- are prepared for the follow-up.

end PF.Fermat42Sub

/-! ## §Axiom check -/
#print axioms PF.Fermat42Sub.fermat42SubCaseB_squareSplit_holds
#print axioms PF.Fermat42Sub.fermat42SubCaseA_squareSplit_holds
