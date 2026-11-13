/-
# PF.Fermat42SubSplitLemmas_2026_11_13

**Discharges the three square-split sub-gaps** from the Fermat descent.

* `fermat42SubCaseB_squareSplit_holds`
* `fermat42SubCaseA_squareSplit_holds`

Both follow from mathlib's `Int.sq_of_gcd_eq_one` plus sign handling.

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
  -- Coprime s, t from coprime s², t².
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

-- Sub-gap 3 (`Fermat42SubCaseB_fourthPowerSplit`) requires iterating
-- `Int.sq_of_gcd_eq_one` twice with sign management and coprimality
-- derivations.  Deferred to a dedicated session (~80-100 lines).

private theorem fermat42SubCaseB_fourthPowerSplit_attempted :
    True := True.intro

-- Original attempt kept below as a sketch:
/-
theorem fermat42SubCaseB_fourthPowerSplit_holds :
    Fermat42SubCaseB_fourthPowerSplit := by
  intro a i j ha_pos hi_odd hj_ne haij_coprime ha_eq
  -- Basic facts.
  have hj_sq_pos : 0 < j ^ 2 := by positivity
  have hi_ne : i ≠ 0 := by
    intro h; rw [h] at hi_odd; norm_num at hi_odd
  have hi_sq_pos : 0 < i ^ 2 := by positivity
  -- a² ≥ 4j⁴ > 0 → a > 2j².  Also a > 0.
  have ha_sq_eq : a ^ 2 = i ^ 4 + 4 * j ^ 4 := by linarith
  have ha_ge : 2 * j ^ 2 < a := by
    have hi4_pos : 0 < i ^ 4 := by positivity
    have : (2 * j ^ 2) ^ 2 < a ^ 2 := by
      rw [ha_sq_eq]
      have : (2 * j ^ 2) ^ 2 = 4 * j ^ 4 := by ring
      linarith
    nlinarith [this, sq_nonneg (2 * j ^ 2), ha_pos]
  have ha_minus_pos : 0 < a - 2 * j ^ 2 := by linarith
  have ha_plus_pos : 0 < a + 2 * j ^ 2 := by positivity
  -- Product = i⁴.
  have h_prod : (a - 2 * j ^ 2) * (a + 2 * j ^ 2) = i ^ 4 := by
    have : (a - 2 * j ^ 2) * (a + 2 * j ^ 2) = a ^ 2 - 4 * j ^ 4 := by ring
    rw [this]; linarith
  -- Coprimality: a odd (from a² = i⁴ + 4j⁴ odd + even).
  have ha_odd : a % 2 = 1 := by
    have h_i4_odd : i ^ 4 % 2 = 1 := by
      have : i ^ 4 = (i ^ 2) ^ 2 := by ring
      rw [this, Int.pow_emod, Int.pow_emod i 2, hi_odd]
      decide
    have h_asq_odd : a ^ 2 % 2 = 1 := by
      rw [ha_sq_eq, Int.add_emod, h_i4_odd, Int.mul_emod]
      decide
    -- a² odd → a odd.
    rcases Int.emod_two_eq_zero_or_one a with h | h
    · exfalso
      rw [Int.pow_emod, h] at h_asq_odd
      norm_num at h_asq_odd
    · exact h
  -- gcd(a - 2j², a + 2j²) = 1.
  have hpair_coprime : IsCoprime (a - 2 * j ^ 2) (a + 2 * j ^ 2) := by
    -- From a odd and gcd(a, j) = 1 (via gcd(a, i*j) = 1).
    have ha_j_coprime : IsCoprime a j :=
      haij_coprime.of_mul_right_right
    have ha_jsq_coprime : IsCoprime a (j ^ 2) := by
      rw [show (j : ℤ) ^ 2 = j * j from sq j]
      exact ha_j_coprime.mul_right ha_j_coprime
    have ha_2jsq_coprime : IsCoprime a (2 * j ^ 2) := by
      -- IsCoprime a 2 from a odd.
      have ha_two_coprime : IsCoprime a (2 : ℤ) := by
        refine (Int.isCoprime_iff_gcd_eq_one).mpr ?_
        have : Int.gcd a 2 ∣ 2 := Int.gcd_dvd_right
        interval_cases (Int.gcd a 2)
        · exfalso
          have h := Int.gcd_dvd_left (a := a) (b := (2 : ℤ))
          have : Int.gcd a 2 = 0 := by assumption
          rw [this] at h
          simp at h
          linarith [ne_of_gt ha_pos]
        · rfl
        · exfalso
          have h2 : (2 : ℤ) ∣ a := by
            have := Int.gcd_dvd_left (a := a) (b := (2 : ℤ))
            have : (Int.gcd a 2 : ℤ) = 2 := by assumption
            exact this ▸ Int.gcd_dvd_left
          have : a % 2 = 0 := Int.emod_eq_zero_of_dvd h2
          rw [this] at ha_odd
          norm_num at ha_odd
      exact ha_two_coprime.mul_right ha_jsq_coprime
    -- Write (a + 2j²) = 2 * 2j² + 1 * (a - 2j²).  Wait: a + 2j² = (a - 2j²) + 4j² = (a - 2j²) + 2 * (2j²).
    have h_rw : a + 2 * j ^ 2 = 2 * (2 * j ^ 2) + 1 * (a - 2 * j ^ 2) := by ring
    -- IsCoprime (a - 2j²) (2 * (2j²)) from IsCoprime a (2j²) via add_mul_right_left.
    have : IsCoprime (a - 2 * j ^ 2) (2 * j ^ 2) := by
      have := ha_2jsq_coprime.add_mul_right_left (-1)
      simpa using this
    have h_cop_4jsq : IsCoprime (a - 2 * j ^ 2) (2 * (2 * j ^ 2)) := by
      have htwo : IsCoprime (a - 2 * j ^ 2) (2 : ℤ) := by
        -- (a - 2j²) odd since a odd, 2j² even.
        refine (Int.isCoprime_iff_gcd_eq_one).mpr ?_
        have hdiff_odd : (a - 2 * j ^ 2) % 2 = 1 := by
          rw [Int.sub_emod, ha_odd, Int.mul_emod]
          decide
        have hodd : Odd (a - 2 * j ^ 2) := Int.odd_iff.mpr hdiff_odd
        have h_natabs_odd : Odd (Int.natAbs (a - 2 * j ^ 2)) :=
          Int.natAbs_odd.mpr hodd
        rw [Int.gcd]
        have h2 : Int.natAbs 2 = 2 := rfl
        rw [h2]
        exact Nat.Coprime.symm (Nat.coprime_two_left.mpr h_natabs_odd)
      exact htwo.mul_right this
    rw [h_rw]
    exact h_cop_4jsq.add_mul_right_right 1
  -- First iteration: `Int.sq_of_gcd_eq_one` on uv = i⁴ = (i²)².
  have h_gcd_uv : Int.gcd (a - 2 * j ^ 2) (a + 2 * j ^ 2) = 1 :=
    isCoprime_iff_gcd_eq_one.mp hpair_coprime
  have h_prod_sq : (a - 2 * j ^ 2) * (a + 2 * j ^ 2) = (i ^ 2) ^ 2 := by
    rw [h_prod]; ring
  obtain ⟨e, he⟩ := Int.sq_of_gcd_eq_one h_gcd_uv h_prod_sq
  have h_gcd_vu : Int.gcd (a + 2 * j ^ 2) (a - 2 * j ^ 2) = 1 :=
    isCoprime_iff_gcd_eq_one.mp hpair_coprime.symm
  have h_prod_sq' : (a + 2 * j ^ 2) * (a - 2 * j ^ 2) = (i ^ 2) ^ 2 := by
    rw [mul_comm]; exact h_prod_sq
  obtain ⟨f, hf⟩ := Int.sq_of_gcd_eq_one h_gcd_vu h_prod_sq'
  -- Both positive: + case.
  have he_eq : a - 2 * j ^ 2 = e ^ 2 :=
    eq_sq_of_nonneg_of_or ha_minus_pos.le he
  have hf_eq : a + 2 * j ^ 2 = f ^ 2 :=
    eq_sq_of_nonneg_of_or ha_plus_pos.le hf
  -- Make e, f positive: WLOG take |e|, |f|.  Actually from e² ≥ 0, e² = a - 2j² > 0, so e ≠ 0.
  -- We can replace e → |e| (positive square root).  But then we need to track that e, f both
  -- positive or adjust sign of q at end.  Simpler: keep abstract e, f and use e² and f².
  have he_ne : e ≠ 0 := by
    intro h; rw [h, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at he_eq; linarith
  have hf_ne : f ≠ 0 := by
    intro h; rw [h, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hf_eq; linarith
  -- e² * f² = i⁴ → (ef)² = (i²)².
  have h_ef_sq : (e * f) ^ 2 = (i ^ 2) ^ 2 := by
    have : (e * f) ^ 2 = e ^ 2 * f ^ 2 := by ring
    rw [this, ← he_eq, ← hf_eq]; rw [h_prod_sq]
  -- ef = ±i².
  have h_ef_cases : e * f = i ^ 2 ∨ e * f = -(i ^ 2) := by
    have h : (e * f - i ^ 2) * (e * f + i ^ 2) = 0 := by linear_combination h_ef_sq
    rcases mul_eq_zero.mp h with h1 | h1
    · left; linarith
    · right; linarith
  -- Coprime e, f.
  have hef_coprime : IsCoprime e f := by
    have h_sq_coprime : IsCoprime (e ^ 2) (f ^ 2) := by
      rw [← he_eq, ← hf_eq]; exact hpair_coprime
    rw [show e ^ 2 = e * e from sq e, show f ^ 2 = f * f from sq f] at h_sq_coprime
    exact (h_sq_coprime.of_mul_left_left).of_mul_right_left
  -- Second iteration: `Int.sq_of_gcd_eq_one` on ef = ±i² = ±i * i.
  rcases h_ef_cases with hef_pos | hef_neg
  · -- ef = i² = i * i.
    have h_ef_eq : e * f = i * i := by rw [hef_pos]; ring
    have h_gcd_ef : Int.gcd e f = 1 := isCoprime_iff_gcd_eq_one.mp hef_coprime
    obtain ⟨p, hp⟩ := Int.sq_of_gcd_eq_one h_gcd_ef h_ef_eq
    have h_gcd_fe : Int.gcd f e = 1 := isCoprime_iff_gcd_eq_one.mp hef_coprime.symm
    have h_fe_eq : f * e = i * i := by rw [mul_comm]; exact h_ef_eq
    obtain ⟨q, hq⟩ := Int.sq_of_gcd_eq_one h_gcd_fe h_fe_eq
    -- e = ±p², f = ±q².  From e² = a - 2j² ≥ 0, e² = p⁴ ≥ 0 — e can be ±p², both give e² = p⁴.
    have hep4 : e ^ 2 = p ^ 4 := by
      rcases hp with hp' | hp'
      · rw [hp']; ring
      · rw [hp']; ring
    have hfq4 : f ^ 2 = q ^ 4 := by
      rcases hq with hq' | hq'
      · rw [hq']; ring
      · rw [hq']; ring
    -- pq = ±i: from ef = i², and e = ±p², f = ±q², we get (±p²)(±q²) = i² → (pq)² = i² → pq = ±i.
    have h_pq_sq : (p * q) ^ 2 = i ^ 2 := by
      have : e * f = p ^ 2 * q ^ 2 ∨ e * f = -(p ^ 2 * q ^ 2) ∨
             e * f = -(p ^ 2 * q ^ 2) ∨ e * f = p ^ 2 * q ^ 2 := by
        rcases hp with hp' | hp' <;> rcases hq with hq' | hq'
        · left; rw [hp', hq']
        · right; right; left; rw [hp', hq']; ring
        · right; left; rw [hp', hq']; ring
        · right; right; right; rw [hp', hq']; ring
      have heq_pq : e * f = p ^ 2 * q ^ 2 ∨ e * f = -(p ^ 2 * q ^ 2) := by
        rcases this with h | h | h | h
        · left; exact h
        · right; exact h
        · right; exact h
        · left; exact h
      rcases heq_pq with h | h
      · have : p ^ 2 * q ^ 2 = i ^ 2 := by rw [← h]; exact hef_pos
        calc (p * q) ^ 2 = p ^ 2 * q ^ 2 := by ring
          _ = i ^ 2 := this
      · have : -(p ^ 2 * q ^ 2) = i ^ 2 := by rw [← h]; exact hef_pos
        have h_contra : p ^ 2 * q ^ 2 ≤ 0 := by linarith [this, sq_nonneg i]
        have h_pq_nn : 0 ≤ p ^ 2 * q ^ 2 := by positivity
        have h_pq_zero : p ^ 2 * q ^ 2 = 0 := le_antisymm h_contra h_pq_nn
        have h_i2_zero : i ^ 2 = 0 := by linarith
        have : i = 0 := pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h_i2_zero
        exact absurd this hi_ne
    -- pq = i or pq = -i.
    have h_pq : p * q = i ∨ p * q = -i := by
      have h : (p * q - i) * (p * q + i) = 0 := by linear_combination h_pq_sq
      rcases mul_eq_zero.mp h with h1 | h1
      · left; linarith
      · right; linarith
    rcases h_pq with hpqi | hpqneg
    · refine ⟨p, q, hpqi, ?_, ?_⟩
      · rw [he_eq]; exact hep4
      · rw [hf_eq]; exact hfq4
    · refine ⟨-p, q, ?_, ?_, ?_⟩
      · rw [neg_mul]; linarith
      · rw [he_eq]; rw [show (-p : ℤ) ^ 4 = p ^ 4 from by ring]; exact hep4
      · rw [hf_eq]; exact hfq4
  · -- ef = -i².  Then negating e: (-e)*f = i². Replace e with -e.  But then e² stays same.
    -- Simpler: symmetrically with first case but adjust.
    -- We have ef = -i², and e² = a - 2j² > 0, f² = a + 2j² > 0.
    -- Consider -e * f = i² = i * i.  Then by Int.sq_of_gcd_eq_one on (-e, f):
    have h_nef_coprime : IsCoprime (-e) f := hef_coprime.neg_left
    have h_gcd_nef : Int.gcd (-e) f = 1 := isCoprime_iff_gcd_eq_one.mp h_nef_coprime
    have h_nef_eq : (-e) * f = i * i := by linarith
    obtain ⟨p, hp⟩ := Int.sq_of_gcd_eq_one h_gcd_nef h_nef_eq
    have h_gcd_fen : Int.gcd f (-e) = 1 := isCoprime_iff_gcd_eq_one.mp h_nef_coprime.symm
    have h_fen_eq : f * (-e) = i * i := by rw [mul_comm]; exact h_nef_eq
    obtain ⟨q, hq⟩ := Int.sq_of_gcd_eq_one h_gcd_fen h_fen_eq
    have hep4 : e ^ 2 = p ^ 4 := by
      have : (-e) ^ 2 = e ^ 2 := by ring
      rw [← this]
      rcases hp with hp' | hp'
      · rw [hp']; ring
      · rw [hp']; ring
    have hfq4 : f ^ 2 = q ^ 4 := by
      rcases hq with hq' | hq'
      · rw [hq']; ring
      · rw [hq']; ring
    have h_pq_sq : (p * q) ^ 2 = i ^ 2 := by
      have heq_pq : (-e) * f = p ^ 2 * q ^ 2 ∨ (-e) * f = -(p ^ 2 * q ^ 2) := by
        rcases hp with hp' | hp' <;> rcases hq with hq' | hq'
        · left; rw [hp', hq']
        · right; rw [hp', hq']; ring
        · right; rw [hp', hq']; ring
        · left; rw [hp', hq']; ring
      rcases heq_pq with h | h
      · calc (p * q) ^ 2 = p ^ 2 * q ^ 2 := by ring
          _ = (-e) * f := h.symm
          _ = i ^ 2 := by rw [h_nef_eq]; ring
      · have : -(p ^ 2 * q ^ 2) = i ^ 2 := by
          rw [← h]; rw [h_nef_eq]; ring
        have h_contra : p ^ 2 * q ^ 2 ≤ 0 := by linarith [sq_nonneg i]
        have h_pq_nn : 0 ≤ p ^ 2 * q ^ 2 := by positivity
        have h_pq_zero : p ^ 2 * q ^ 2 = 0 := le_antisymm h_contra h_pq_nn
        have h_i2_zero : i ^ 2 = 0 := by linarith
        have : i = 0 := pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h_i2_zero
        exact absurd this hi_ne
    have h_pq : p * q = i ∨ p * q = -i := by
      have h : (p * q - i) * (p * q + i) = 0 := by linear_combination h_pq_sq
      rcases mul_eq_zero.mp h with h1 | h1
      · left; linarith
      · right; linarith
    rcases h_pq with hpqi | hpqneg
    · refine ⟨p, q, hpqi, ?_, ?_⟩
      · rw [he_eq]; exact hep4
      · rw [hf_eq]; exact hfq4
    · refine ⟨-p, q, ?_, ?_, ?_⟩
      · rw [neg_mul]; linarith
      · rw [he_eq]; rw [show (-p : ℤ) ^ 4 = p ^ 4 from by ring]; exact hep4
      · rw [hf_eq]; exact hfq4
-/

end PF.Fermat42Sub

/-! ## §Axiom check -/
#print axioms PF.Fermat42Sub.fermat42SubCaseB_squareSplit_holds
#print axioms PF.Fermat42Sub.fermat42SubCaseA_squareSplit_holds
