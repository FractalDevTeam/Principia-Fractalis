/-
# PF.Fermat42SubSplitLemmas_2026_11_13

**Discharges the three square-split sub-gaps** from the Fermat descent:

* `fermat42SubCaseB_squareSplit_holds`
* `fermat42SubCaseA_squareSplit_holds`
* `fermat42SubCaseB_fourthPowerSplit_holds`

All follow from `Int.sq_of_gcd_eq_one` + sign/parity bookkeeping.

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
  have hb_sq' : b ^ 2 = (s * t) ^ 2 := by rw [hb_sq, hs_eq, ht_eq]; ring
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

/-- **Discharge of `Fermat42SubCaseB_fourthPowerSplit`**.
Iterates `coprime_mul_eq_sq_split` twice (on `uv = (i²)²` then on
the roots via `|e|·|f| = i²`), with sign adjustment. -/
theorem fermat42SubCaseB_fourthPowerSplit_holds :
    Fermat42SubCaseB_fourthPowerSplit := by
  intro a i j ha_pos hi_odd hj_ne haij_coprime ha_eq
  have hj_sq_pos : 0 < j ^ 2 := by positivity
  have hi_ne : i ≠ 0 := by
    intro h; rw [h] at hi_odd; norm_num at hi_odd
  have hi_sq_pos : 0 < i ^ 2 := by positivity
  have ha_sq_eq : a ^ 2 = i ^ 4 + 4 * j ^ 4 := by linarith
  have ha_ge : 2 * j ^ 2 < a := by
    have h1 : (2 * j ^ 2) ^ 2 < a ^ 2 := by
      rw [ha_sq_eq]
      have h2 : (2 * j ^ 2) ^ 2 = 4 * j ^ 4 := by ring
      have hi4_pos : 0 < i ^ 4 := by positivity
      linarith
    nlinarith [h1, sq_nonneg (2 * j ^ 2), ha_pos]
  have ha_minus_pos : 0 < a - 2 * j ^ 2 := by linarith
  have ha_plus_pos : 0 < a + 2 * j ^ 2 := by positivity
  have h_prod_sq : (a - 2 * j ^ 2) * (a + 2 * j ^ 2) = (i ^ 2) ^ 2 := by
    have h : (a - 2 * j ^ 2) * (a + 2 * j ^ 2) = a ^ 2 - 4 * j ^ 4 := by ring
    rw [h, show (i ^ 2 : ℤ) ^ 2 = i ^ 4 from by ring]; linarith
  -- a odd.
  have ha_odd : a % 2 = 1 := by
    have h_i2_odd : i ^ 2 % 2 = 1 := by
      rw [show i ^ 2 = i * i from sq i, Int.mul_emod, hi_odd]; decide
    have h_i4_odd : i ^ 4 % 2 = 1 := by
      rw [show i ^ 4 = i ^ 2 * i ^ 2 from by ring, Int.mul_emod, h_i2_odd]; decide
    have h_4j4_even : (4 * j ^ 4) % 2 = 0 := by
      rw [show (4 : ℤ) * j ^ 4 = 2 * (2 * j ^ 4) from by ring]
      exact Int.mul_emod_right 2 _
    have h_asq_odd : a ^ 2 % 2 = 1 := by
      rw [ha_sq_eq, Int.add_emod, h_i4_odd, h_4j4_even]; decide
    rcases Int.emod_two_eq_zero_or_one a with h | h
    · exfalso
      have : a ^ 2 % 2 = 0 := by
        rw [show a ^ 2 = a * a from sq a, Int.mul_emod, h]; decide
      rw [this] at h_asq_odd; norm_num at h_asq_odd
    · exact h
  -- Coprime pair (a - 2j², a + 2j²).
  have hpair : IsCoprime (a - 2 * j ^ 2) (a + 2 * j ^ 2) := by
    have hdiff_odd : (a - 2 * j ^ 2) % 2 = 1 := by
      have h_2jsq_even : (2 * j ^ 2) % 2 = 0 := Int.mul_emod_right 2 _
      rw [Int.sub_emod, ha_odd, h_2jsq_even]; rfl
    have hdiff_two : IsCoprime (a - 2 * j ^ 2) (2 : ℤ) := by
      refine (Int.isCoprime_iff_gcd_eq_one).mpr ?_
      rw [Int.gcd]
      have h2 : Int.natAbs 2 = 2 := rfl
      rw [h2]
      exact Nat.Coprime.symm
        (Nat.coprime_two_left.mpr (Int.natAbs_odd.mpr (Int.odd_iff.mpr hdiff_odd)))
    have ha_j : IsCoprime a j := haij_coprime.of_mul_right_right
    have ha_jsq : IsCoprime a (j ^ 2) := by
      rw [show (j : ℤ) ^ 2 = j * j from sq j]
      exact ha_j.mul_right ha_j
    have hdiff_jsq : IsCoprime (a - 2 * j ^ 2) (j ^ 2) := by
      have : a - 2 * j ^ 2 = a + (-2) * j ^ 2 := by ring
      rw [this]; exact ha_jsq.add_mul_right_left (-2)
    have hdiff_4jsq : IsCoprime (a - 2 * j ^ 2) (4 * j ^ 2) := by
      have h22 : IsCoprime (a - 2 * j ^ 2) ((2 : ℤ) * 2) :=
        hdiff_two.mul_right hdiff_two
      have h_rw : (4 : ℤ) * j ^ 2 = (2 * 2) * (j ^ 2) := by ring
      rw [h_rw]
      exact h22.mul_right hdiff_jsq
    have h_sum_rw : a + 2 * j ^ 2 = 4 * j ^ 2 + 1 * (a - 2 * j ^ 2) := by ring
    rw [h_sum_rw]
    exact hdiff_4jsq.add_mul_right_right 1
  -- First iteration: `(a-2j²)(a+2j²) = (i²)²`.
  obtain ⟨e, f, he_eq, hf_eq, _⟩ :=
    coprime_mul_eq_sq_split ha_minus_pos.le ha_plus_pos.le hpair h_prod_sq
  -- Define e' = |e|, f' = |f| (nonneg).
  set e' : ℤ := |e| with he'_def
  set f' : ℤ := |f| with hf'_def
  have he'_nn : 0 ≤ e' := abs_nonneg e
  have hf'_nn : 0 ≤ f' := abs_nonneg f
  have he'_sq : e' ^ 2 = e ^ 2 := sq_abs e
  have hf'_sq : f' ^ 2 = f ^ 2 := sq_abs f
  have hu_e' : a - 2 * j ^ 2 = e' ^ 2 := by rw [he'_sq]; exact he_eq
  have hv_f' : a + 2 * j ^ 2 = f' ^ 2 := by rw [hf'_sq]; exact hf_eq
  -- e' · f' = i² (nonneg since both nonneg).
  have hef'_prod : e' * f' = i ^ 2 := by
    have h1 : (e' * f') ^ 2 = (i ^ 2) ^ 2 := by
      have hef_sq : (e' * f') ^ 2 = e' ^ 2 * f' ^ 2 := by ring
      rw [hef_sq, ← hu_e', ← hv_f']
      exact h_prod_sq
    have h_ef_nn : 0 ≤ e' * f' := mul_nonneg he'_nn hf'_nn
    have h_isq_nn : 0 ≤ i ^ 2 := sq_nonneg i
    have h2 : (e' * f' - i ^ 2) * (e' * f' + i ^ 2) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h2 with h | h
    · linarith
    · -- e'f' + i² = 0 with both nonneg → both zero; contradiction with i ≠ 0.
      have h_sum : e' * f' + i ^ 2 = 0 := h
      have h_isq_zero : i ^ 2 = 0 := by linarith
      have : i = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h_isq_zero
      exact absurd this hi_ne
  -- Coprime e', f' (from coprime e, f via squares; and e', f' = |e|, |f|).
  have hef_coprime : IsCoprime e f := by
    have h_sq_coprime : IsCoprime (e ^ 2) (f ^ 2) := by
      rw [← he_eq, ← hf_eq]; exact hpair
    rw [show e ^ 2 = e * e from sq e, show f ^ 2 = f * f from sq f] at h_sq_coprime
    exact (h_sq_coprime.of_mul_left_left).of_mul_right_left
  have hef'_coprime : IsCoprime e' f' := by
    rw [he'_def, hf'_def]
    rcases abs_cases e with ⟨he_abs, _⟩ | ⟨he_abs, _⟩
    · rcases abs_cases f with ⟨hf_abs, _⟩ | ⟨hf_abs, _⟩
      · rw [he_abs, hf_abs]; exact hef_coprime
      · rw [he_abs, hf_abs]; exact hef_coprime.neg_right
    · rcases abs_cases f with ⟨hf_abs, _⟩ | ⟨hf_abs, _⟩
      · rw [he_abs, hf_abs]; exact hef_coprime.neg_left
      · rw [he_abs, hf_abs]; exact (hef_coprime.neg_left).neg_right
  -- Second iteration: e' · f' = i² = c² with c = i.
  obtain ⟨p, q, hp_eq, hq_eq, h_pq_cases⟩ :=
    coprime_mul_eq_sq_split he'_nn hf'_nn hef'_coprime hef'_prod
  -- Recover u = p⁴, v = q⁴.
  have hu_p4 : a - 2 * j ^ 2 = p ^ 4 := by
    rw [hu_e', hp_eq]; ring
  have hv_q4 : a + 2 * j ^ 2 = q ^ 4 := by
    rw [hv_f', hq_eq]; ring
  -- Sign adjustment for pq = i.
  rcases h_pq_cases with hpq_pos | hpq_neg
  · exact ⟨p, q, hpq_pos, hu_p4, hv_q4⟩
  · refine ⟨-p, q, ?_, ?_, hv_q4⟩
    · rw [neg_mul]; linarith
    · rw [hu_p4]; ring

end PF.Fermat42Sub

/-! ## §Axiom check -/
#print axioms PF.Fermat42Sub.fermat42SubCaseB_squareSplit_holds
#print axioms PF.Fermat42Sub.fermat42SubCaseA_squareSplit_holds
#print axioms PF.Fermat42Sub.fermat42SubCaseB_fourthPowerSplit_holds
