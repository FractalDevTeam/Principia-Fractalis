/-
# PF.Fermat42SubAssembly_2026_11_14

**Full assembly of `not_fermat_42_sub`** — the "difference form" of
Fermat's n = 4 theorem: `∀ a b c : ℤ, a ≠ 0 → b ≠ 0 → c ≠ 0 →
a ^ 4 - b ^ 4 ≠ c ^ 2`.

Composes `fermat42Sub_caseA_reduces` + `fermat42Sub_caseB_descends`
(and its parity mirror) with the discharged split sub-gaps and the
now-unconditional `fermat42Double_impossible_unconditional`.

All theorems on three-axiom bar `[propext, Classical.choice, Quot.sound]`,
no sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-14.
-/

import PF.Fermat42SubSplitLemmas_2026_11_13
import PF.Fermat42DoubleImpossible_2026_11_13
import Mathlib.NumberTheory.PythagoreanTriples

namespace PF

namespace Fermat42Sub

/-- **Case B mirror** — same as `fermat42Sub_caseB_descends` but with
`(m even, n odd)` instead of `(m odd, n even)`.  Arises when the
Pythagorean classification of a primitive triple with odd leg
`c ≡ 3 mod 4` picks the other parity assignment.

Proof structure mirrors `fermat42Sub_caseB_descends` by calling
`hSplit1` with the (m, n) roles swapped. -/
theorem fermat42Sub_caseB_descends_mirror
    (hSplit1 : Fermat42SubCaseB_squareSplit)
    (hSplit2 : Fermat42SubCaseB_fourthPowerSplit)
    (a b c m n : ℤ)
    (h_min : Minimal a b c)
    (ha_pos : 0 < a) (hc_pos : 0 < c)
    (h_m_pos : 0 < m) (h_n_pos : 0 < n)
    (hmn_coprime : IsCoprime m n)
    (hm_even : m % 2 = 0) (hn_odd : n % 2 = 1)
    (hc_eq : c = m ^ 2 - n ^ 2)
    (hb_sq : b ^ 2 = 2 * m * n)
    (ha_sq : a ^ 2 = m ^ 2 + n ^ 2) : False := by
  -- Mirror square split: call hSplit1 with (n, m, b) so that n plays "m odd" and m plays "n even".
  have hb_sq' : b ^ 2 = 2 * n * m := by linarith [hb_sq]
  obtain ⟨i, j, hn_eq, hm_eq, hb_eq⟩ :=
    hSplit1 n m b h_n_pos.le h_m_pos hmn_coprime.symm hn_odd hm_even hb_sq'
  -- hn_eq : n = i², hm_eq : m = 2 j², hb_eq : b = 2 i j.
  -- a² = m² + n² = (2j²)² + (i²)² = 4j⁴ + i⁴, so a² - i⁴ = 4j⁴.
  have ha_sq' : a ^ 2 - i ^ 4 = 4 * j ^ 4 := by
    rw [hm_eq, hn_eq] at ha_sq
    linear_combination ha_sq
  have hj_ne : j ≠ 0 := by
    intro hj
    rw [hj] at hm_eq
    simp at hm_eq
    linarith
  have hi_odd : i % 2 = 1 := by
    rw [hn_eq] at hn_odd
    rw [show (i ^ 2 : ℤ) = i * i from sq i, Int.mul_emod] at hn_odd
    rcases Int.emod_two_eq_zero_or_one i with h | h
    · rw [h] at hn_odd; norm_num at hn_odd
    · exact h
  have hab_coprime : IsCoprime a b :=
    Fermat42Sub.coprime_of_minimal h_min
  have ha_ij_coprime : IsCoprime a (i * j) := by
    have hb_fact : b = 2 * (i * j) := by rw [hb_eq]; ring
    have h1 : IsCoprime a (2 * (i * j)) := hb_fact ▸ hab_coprime
    exact h1.of_mul_right_right
  obtain ⟨p, q, hpq, hp_eq, hq_eq⟩ := hSplit2 a i j ha_pos hi_odd hj_ne
    ha_ij_coprime ha_sq'
  have h_new_eq : q ^ 4 - p ^ 4 = (2 * j) ^ 2 := by
    have : q ^ 4 - p ^ 4 = (a + 2 * j ^ 2) - (a - 2 * j ^ 2) := by
      rw [hp_eq, hq_eq]
    rw [this]; ring
  have hi_ne : i ≠ 0 := by
    intro h; rw [h] at hi_odd; norm_num at hi_odd
  have hp_ne : p ≠ 0 := left_ne_zero_of_mul (by rw [hpq]; exact hi_ne)
  have hq_ne : q ≠ 0 := right_ne_zero_of_mul (by rw [hpq]; exact hi_ne)
  have h2j_ne : (2 * j : ℤ) ≠ 0 := mul_ne_zero two_ne_zero hj_ne
  have h_new : Fermat42Sub q p (2 * j) := ⟨hq_ne, hp_ne, h2j_ne, h_new_eq⟩
  have h_le : Int.natAbs c ≤ Int.natAbs (2 * j) := h_min.2 q p (2 * j) h_new
  -- Mirror bound: c = m² - n² = 4j⁴ - i⁴ = (2j² - i²)(2j² + i²).
  have hj_abs_pos : 0 < Int.natAbs j := Int.natAbs_pos.mpr hj_ne
  have hc_eq' : c = 4 * j ^ 4 - i ^ 4 := by
    rw [hc_eq, hm_eq, hn_eq]; ring
  have h_2j_sq_gt : 2 * j ^ 2 > i ^ 2 := by
    by_contra h_le_ij
    push_neg at h_le_ij
    have h_4j4_le : 4 * j ^ 4 ≤ i ^ 4 := by
      have h1 : (2 * j ^ 2) * (2 * j ^ 2) ≤ i ^ 2 * i ^ 2 := by
        exact mul_le_mul h_le_ij h_le_ij (by positivity) (sq_nonneg _)
      calc 4 * j ^ 4 = (2 * j ^ 2) * (2 * j ^ 2) := by ring
        _ ≤ i ^ 2 * i ^ 2 := h1
        _ = i ^ 4 := by ring
    linarith
  have hc_ge : 2 * j ^ 2 + 1 ≤ c := by
    -- c = (2j² - i²)(2j² + i²), 2j² - i² ≥ 1, 2j² + i² ≥ 2j² + 1.
    have h1 : 2 * j ^ 2 - i ^ 2 ≥ 1 := by linarith [h_2j_sq_gt]
    have h2 : 2 * j ^ 2 + i ^ 2 ≥ 2 * j ^ 2 + 1 := by
      have hi_sq_ge : i ^ 2 ≥ 1 := by
        have hi_sq_pos : 0 < i ^ 2 := by positivity
        omega
      linarith
    have h3 : c = (2 * j ^ 2 - i ^ 2) * (2 * j ^ 2 + i ^ 2) := by
      rw [hc_eq']; ring
    have h4 : (2 * j ^ 2 - i ^ 2) * (2 * j ^ 2 + i ^ 2) ≥ 1 * (2 * j ^ 2 + 1) := by
      have h5 : 0 ≤ 2 * j ^ 2 + i ^ 2 := by positivity
      nlinarith [h1, h2]
    linarith
  -- |2j|.natAbs = 2 · j.natAbs; c.natAbs = c.
  have h_abs_lt : Int.natAbs (2 * j) < Int.natAbs c := by
    have h2j_abs : Int.natAbs (2 * j) = 2 * Int.natAbs j := by
      rw [Int.natAbs_mul]; rfl
    have hc_cast : (Int.natAbs c : ℤ) = c := Int.natAbs_of_nonneg hc_pos.le
    have h_jsq_cast : (j : ℤ) ^ 2 = (Int.natAbs j : ℤ) ^ 2 := by
      rw [show ((Int.natAbs j : ℤ)) = |j| from (Int.abs_eq_natAbs j).symm, sq_abs]
    have hc_abs_ge : (2 * (Int.natAbs j : ℤ) ^ 2 + 1 : ℤ) ≤ (Int.natAbs c : ℤ) := by
      rw [hc_cast, ← h_jsq_cast]; exact hc_ge
    have hc_abs_nat : 2 * (Int.natAbs j) ^ 2 + 1 ≤ Int.natAbs c := by
      have h1 : ((2 * (Int.natAbs j) ^ 2 + 1 : ℕ) : ℤ)
            = 2 * (Int.natAbs j : ℤ) ^ 2 + 1 := by push_cast; ring
      have h2 : ((Int.natAbs c : ℕ) : ℤ) = (Int.natAbs c : ℤ) := by rfl
      have h3 : ((2 * (Int.natAbs j) ^ 2 + 1 : ℕ) : ℤ) ≤ ((Int.natAbs c : ℕ) : ℤ) := by
        rw [h1, h2]; exact hc_abs_ge
      exact_mod_cast h3
    rw [h2j_abs]
    calc 2 * Int.natAbs j
        < 2 * (Int.natAbs j) ^ 2 + 1 := by nlinarith [hj_abs_pos]
      _ ≤ Int.natAbs c := hc_abs_nat
  exact absurd h_le (not_le_of_gt h_abs_lt)

end Fermat42Sub

open Fermat42Sub

/-- **`not_fermat_42_sub`** — the difference form of Fermat's `n = 4`.

Full composition: `exists_minimal` + normalize-to-positive-via-abs +
primitive Pythagorean classification on `(b², c, a²)` (or `(c, b², a²)`)
based on parity of `b`, followed by `fermat42Sub_caseA_reduces` (Case A,
`b` odd) or `fermat42Sub_caseB_descends` / `_mirror` (Case B, `b` even,
mirror based on parity assignment of the Pyth classification). -/
theorem not_fermat_42_sub : ∀ a b c : ℤ,
    a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ 4 - b ^ 4 ≠ c ^ 2 := by
  intro a b c ha hb hc h_eq
  have h_sub : Fermat42Sub a b c := ⟨ha, hb, hc, h_eq⟩
  obtain ⟨a₀, b₀, c₀, h_min⟩ := Fermat42Sub.exists_minimal h_sub
  have ha₀_ne : a₀ ≠ 0 := h_min.1.1
  have hb₀_ne : b₀ ≠ 0 := h_min.1.2.1
  have hc₀_ne : c₀ ≠ 0 := h_min.1.2.2.1
  have h_abs_eq : |a₀| ^ 4 - |b₀| ^ 4 = |c₀| ^ 2 := by
    have h1 : |a₀| ^ 4 = a₀ ^ 4 := by
      have : (|a₀|) ^ 2 = a₀ ^ 2 := sq_abs a₀
      calc |a₀| ^ 4 = (|a₀| ^ 2) ^ 2 := by ring
        _ = (a₀ ^ 2) ^ 2 := by rw [this]
        _ = a₀ ^ 4 := by ring
    have h2 : |b₀| ^ 4 = b₀ ^ 4 := by
      have : (|b₀|) ^ 2 = b₀ ^ 2 := sq_abs b₀
      calc |b₀| ^ 4 = (|b₀| ^ 2) ^ 2 := by ring
        _ = (b₀ ^ 2) ^ 2 := by rw [this]
        _ = b₀ ^ 4 := by ring
    have h3 : |c₀| ^ 2 = c₀ ^ 2 := sq_abs c₀
    linarith [h_min.1.2.2.2]
  have h_abs_sub : Fermat42Sub |a₀| |b₀| |c₀| :=
    ⟨abs_ne_zero.mpr ha₀_ne, abs_ne_zero.mpr hb₀_ne, abs_ne_zero.mpr hc₀_ne, h_abs_eq⟩
  have h_abs_min : Fermat42Sub.Minimal |a₀| |b₀| |c₀| := by
    refine ⟨h_abs_sub, ?_⟩
    intro a1 b1 c1 hf1
    have : (|c₀|).natAbs = c₀.natAbs := Int.natAbs_abs c₀
    rw [this]; exact h_min.2 a1 b1 c1 hf1
  set A : ℤ := |a₀|
  set B : ℤ := |b₀|
  set C : ℤ := |c₀|
  have hA_pos : 0 < A := abs_pos.mpr ha₀_ne
  have hB_pos : 0 < B := abs_pos.mpr hb₀_ne
  have hC_pos : 0 < C := abs_pos.mpr hc₀_ne
  have hAB_cop : IsCoprime A B := Fermat42Sub.coprime_of_minimal h_abs_min
  have hpyth_eq : A ^ 4 - B ^ 4 = C ^ 2 := h_abs_sub.2.2.2
  have hpyth : PythagoreanTriple (B ^ 2) C (A ^ 2) := by
    show B ^ 2 * B ^ 2 + C * C = A ^ 2 * A ^ 2
    nlinarith [hpyth_eq]
  have hpyth' : PythagoreanTriple C (B ^ 2) (A ^ 2) :=
    pythagoreanTriple_comm.mp hpyth
  -- IsCoprime (B²) C via Bezout from IsCoprime (A⁴) (B⁴).
  have hB2_cop_C : IsCoprime (B ^ 2) C := by
    obtain ⟨u, v, huv⟩ : IsCoprime (A ^ 4) (B ^ 4) := hAB_cop.pow
    -- gcd divides B² so divides B⁴. gcd divides C so divides C² = A⁴ - B⁴, hence divides A⁴.
    rw [Int.isCoprime_iff_gcd_eq_one]
    set d := Int.gcd (B ^ 2) C
    have hd_dvd_B2 : (d : ℤ) ∣ B ^ 2 := Int.gcd_dvd_left _ _
    have hd_dvd_C : (d : ℤ) ∣ C := Int.gcd_dvd_right _ _
    have hd_dvd_B4 : (d : ℤ) ∣ B ^ 4 := by
      have h : B ^ 4 = B ^ 2 * B ^ 2 := by ring
      rw [h]; exact Dvd.dvd.mul_left hd_dvd_B2 _
    have hd_dvd_C2 : (d : ℤ) ∣ C ^ 2 := dvd_pow hd_dvd_C (by norm_num)
    have hd_dvd_A4 : (d : ℤ) ∣ A ^ 4 := by
      have h : A ^ 4 = C ^ 2 + B ^ 4 := by linarith [hpyth_eq]
      rw [h]; exact dvd_add hd_dvd_C2 hd_dvd_B4
    have hd_dvd_1 : (d : ℤ) ∣ 1 := by
      have h : (1 : ℤ) = u * A ^ 4 + v * B ^ 4 := huv.symm
      rw [h]
      exact dvd_add (dvd_mul_of_dvd_right hd_dvd_A4 _)
                    (dvd_mul_of_dvd_right hd_dvd_B4 _)
    have : d ∣ 1 := by exact_mod_cast hd_dvd_1
    exact Nat.dvd_one.mp this
  have hC_cop_B2 : IsCoprime C (B ^ 2) := hB2_cop_C.symm
  have hA2_pos : 0 < A ^ 2 := by positivity
  rcases Int.emod_two_eq_zero_or_one B with hB_ev | hB_od
  · -- Case B: B even, C odd.
    have hB2_ev : B ^ 2 % 2 = 0 := by
      rw [show B ^ 2 = B * B from sq B, Int.mul_emod, hB_ev]; decide
    have hA_odd : A % 2 = 1 := by
      by_contra hA_ev'
      push_neg at hA_ev'
      have : A % 2 = 0 := by omega
      have h2_dvd_A : (2 : ℤ) ∣ A := Int.dvd_of_emod_eq_zero this
      have h2_dvd_B : (2 : ℤ) ∣ B := Int.dvd_of_emod_eq_zero hB_ev
      have h2_dvd_gcd : (2 : ℤ) ∣ Int.gcd A B := Int.dvd_coe_gcd h2_dvd_A h2_dvd_B
      rw [Int.isCoprime_iff_gcd_eq_one.mp hAB_cop] at h2_dvd_gcd
      norm_num at h2_dvd_gcd
    have hA2_odd : A ^ 2 % 2 = 1 := by
      rw [show A ^ 2 = A * A from sq A, Int.mul_emod, hA_odd]; decide
    have hA4_odd : A ^ 4 % 2 = 1 := by
      rw [show A ^ 4 = A ^ 2 * A ^ 2 from by ring, Int.mul_emod, hA2_odd]; decide
    have hB4_ev : B ^ 4 % 2 = 0 := by
      rw [show B ^ 4 = B ^ 2 * B ^ 2 from by ring, Int.mul_emod, hB2_ev]; decide
    have hC2_odd : C ^ 2 % 2 = 1 := by
      rw [← hpyth_eq, Int.sub_emod, hA4_odd, hB4_ev]; decide
    have hC_odd : C % 2 = 1 := by
      rcases Int.emod_two_eq_zero_or_one C with h | h
      · exfalso
        have : C ^ 2 % 2 = 0 := by rw [sq, Int.mul_emod, h]; decide
        rw [this] at hC2_odd; norm_num at hC2_odd
      · exact h
    have hC_cop_nat : Int.gcd C (B ^ 2) = 1 :=
      Int.isCoprime_iff_gcd_eq_one.mp hC_cop_B2
    obtain ⟨m, n, hc_eq, hb2_eq, ha2_eq, hmn_gcd, hmn_par, hm_nn⟩ :=
      hpyth'.coprime_classification' hC_cop_nat hC_odd hA2_pos
    have hmn_cop : IsCoprime m n := Int.isCoprime_iff_gcd_eq_one.mpr hmn_gcd
    -- m > 0 and n > 0 since 2mn = B² > 0 and m ≥ 0.
    have hm_pos_strict : 0 < m := by
      rcases lt_or_eq_of_le hm_nn with h | h
      · exact h
      · exfalso
        rw [← h] at hb2_eq
        simp at hb2_eq
        have : 0 < B ^ 2 := by positivity
        linarith
    have hn_pos : 0 < n := by
      have hB2_pos : 0 < B ^ 2 := by positivity
      have : 0 < 2 * m * n := by rw [← hb2_eq]; exact hB2_pos
      nlinarith [hm_pos_strict]
    rcases hmn_par with ⟨hm_ev, hn_od⟩ | ⟨hm_od, hn_ev⟩
    · -- (m even, n odd) sub-case: use mirror.
      exact fermat42Sub_caseB_descends_mirror
        fermat42SubCaseB_squareSplit_holds
        fermat42SubCaseB_fourthPowerSplit_holds
        A B C m n h_abs_min hA_pos hC_pos hm_pos_strict hn_pos hmn_cop
        hm_ev hn_od hc_eq hb2_eq ha2_eq
    · -- (m odd, n even) sub-case: standard caseB_descends.
      exact fermat42Sub_caseB_descends
        fermat42SubCaseB_squareSplit_holds
        fermat42SubCaseB_fourthPowerSplit_holds
        A B C m n h_abs_min hA_pos hC_pos hm_nn hn_pos hmn_cop hm_od hn_ev
        hc_eq hb2_eq ha2_eq
  · -- Case A: B odd.
    have hB2_odd : B ^ 2 % 2 = 1 := by
      rw [show B ^ 2 = B * B from sq B, Int.mul_emod, hB_od]; decide
    have hB2_cop_nat : Int.gcd (B ^ 2) C = 1 :=
      Int.isCoprime_iff_gcd_eq_one.mp hB2_cop_C
    obtain ⟨m, n, hb2_eq, hc_eq, ha2_eq, hmn_gcd, hmn_par, hm_nn⟩ :=
      hpyth.coprime_classification' hB2_cop_nat hB2_odd hA2_pos
    have hmn_cop : IsCoprime m n := Int.isCoprime_iff_gcd_eq_one.mpr hmn_gcd
    -- In Case A: B² ≡ 1 mod 4 (B odd, B² ≡ 1 mod 8).  So m² - n² = B² ≡ 1 mod 4,
    -- which forces m odd, n even.
    have hm_odd : m % 2 = 1 ∧ n % 2 = 0 := by
      have hB2_mod : B ^ 2 % 4 = 1 := by
        obtain ⟨k, hk⟩ : ∃ k, B = 2 * k + 1 := ⟨(B - 1) / 2, by omega⟩
        have : B ^ 2 = 4 * (k * k + k) + 1 := by rw [hk]; ring
        rw [this]; omega
      rcases hmn_par with ⟨hm_ev, hn_od⟩ | ⟨hm_od, hn_ev⟩
      · exfalso
        -- m even, n odd: m² ≡ 0, n² ≡ 1 mod 4 ⟹ B² = m² - n² ≡ -1 ≡ 3 mod 4. Contradiction.
        obtain ⟨m₀, hm₀⟩ : (2 : ℤ) ∣ m := Int.dvd_of_emod_eq_zero hm_ev
        have hm2_mod : m ^ 2 % 4 = 0 := by
          rw [hm₀]
          have : (2 * m₀) ^ 2 = 4 * m₀ ^ 2 := by ring
          rw [this, Int.mul_emod_right]
        have hn2_mod : n ^ 2 % 4 = 1 := by
          obtain ⟨k, hk⟩ : ∃ k, n = 2 * k + 1 := ⟨(n - 1) / 2, by omega⟩
          subst hk
          have : (2 * k + 1) ^ 2 = 4 * (k * k + k) + 1 := by ring
          rw [this]; omega
        have : B ^ 2 % 4 = 3 := by
          rw [hb2_eq, Int.sub_emod, hm2_mod, hn2_mod]; decide
        rw [this] at hB2_mod; norm_num at hB2_mod
      · exact ⟨hm_od, hn_ev⟩
    have hn_pos : 0 < n := by
      rcases lt_or_eq_of_le hm_nn with hm_pos' | hm_zero
      · have : 0 < 2 * m * n := by rw [← hc_eq]; exact hC_pos
        nlinarith [hm_pos']
      · exfalso
        rw [← hm_zero] at hc_eq
        simp at hc_eq
        linarith
    exact fermat42Sub_caseA_reduces
      fermat42SubCaseA_squareSplit_holds
      fermat42Double_impossible_unconditional
      A B C m n h_abs_min hA_pos hC_pos hm_nn hn_pos hmn_cop hm_odd.1 hm_odd.2
      hb2_eq ha2_eq

end PF

/-! ## §Axiom check -/
#print axioms PF.Fermat42Sub.fermat42Sub_caseB_descends_mirror
#print axioms PF.not_fermat_42_sub
