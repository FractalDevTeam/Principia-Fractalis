/-
# PF.Fermat42SubCaseBClosure_2026_11_13

**Case B closure for `not_fermat_42_sub`**: if `Fermat42Sub a b c` with
`a odd, b even, c odd, a > 0`, then the Pythagorean decomposition
produces a strictly smaller `Fermat42Sub` instance — contradicting
minimality.

## Proof outline

Given `a⁴ - b⁴ = c²` with `(a, b)` coprime, `a odd, b even, c odd`:
1. Pythagorean classification of `(c, b², a²)` with `c odd leg`:
   ∃ m, n coprime of opposite parity, m ≥ 0, with
   * c = m² - n²
   * b² = 2mn
   * a² = m² + n²
2. WLOG n even (if m even, swap via commutativity of the triple).
   Write n = 2k, m odd. Then `b² = 4mk`, so `(b/2)² = mk` with
   `gcd(m, k) = 1`. Hence `m = i², k = j²`, `b = 2ij`.
3. Then `a² = m² + n² = i⁴ + 4j⁴`, so `a² - (2j²)² = i⁴`,
   i.e., `(a - 2j²)(a + 2j²) = i⁴`.
4. Both factors coprime (both odd, differ by `4j²`, `gcd(a, j) = 1`).
   Both positive (a ≥ 2j² since c > 0 ⟹ i⁴ > 4j⁴).
5. Each factor is a 4th power: `a - 2j² = p⁴`, `a + 2j² = q⁴`,
   `pq = i`.
6. Subtracting: `q⁴ - p⁴ = 4j² = (2j)²`.
7. `Fermat42Sub q p (2j)` — strictly smaller `|c|`.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-13.
-/

import PF.Fermat42SubFoundations_2026_11_13

namespace PF.Fermat42Sub

/-- **Sub-gap 1**: `b² = 2mn` with `gcd(m, n) = 1`, `m` odd, `n` even
implies `m` and `n/2` are each perfect squares.

Standard coprime-square-product lemma.  Stated as a named sub-gap. -/
def Fermat42SubCaseB_squareSplit : Prop :=
  ∀ m n b : ℤ, 0 ≤ m → 0 < n → IsCoprime m n →
    m % 2 = 1 → n % 2 = 0 → b ^ 2 = 2 * m * n →
    ∃ i j : ℤ, m = i ^ 2 ∧ n = 2 * j ^ 2 ∧ b = 2 * i * j

/-- **Sub-gap 2**: given `a² - i⁴ = 4j⁴`, `a > 0`, `i` odd, `j ≠ 0`,
with `gcd(a, i·j) = 1`, there exist `p, q` coprime with `pq = i` and
`a - 2j² = p⁴`, `a + 2j² = q⁴`.

Follows from coprimality of `(a - 2j²)` and `(a + 2j²)` plus the
coprime-product-is-4th-power argument.  Stated as a named sub-gap. -/
def Fermat42SubCaseB_fourthPowerSplit : Prop :=
  ∀ a i j : ℤ, 0 < a → i % 2 = 1 → j ≠ 0 → IsCoprime a (i * j) →
    a ^ 2 - i ^ 4 = 4 * j ^ 4 →
    ∃ p q : ℤ, p * q = i ∧ a - 2 * j ^ 2 = p ^ 4 ∧ a + 2 * j ^ 2 = q ^ 4

/-- **Case B closure**: conditional on the two square-split sub-gaps. -/
theorem fermat42Sub_caseB_descends
    (hSplit1 : Fermat42SubCaseB_squareSplit)
    (hSplit2 : Fermat42SubCaseB_fourthPowerSplit)
    (a b c m n : ℤ)
    (h_min : Minimal a b c)
    (ha_pos : 0 < a) (hc_pos : 0 < c)
    (h_m_nn : 0 ≤ m) (h_n_pos : 0 < n)
    (hmn_coprime : IsCoprime m n)
    (hm_odd : m % 2 = 1) (hn_even : n % 2 = 0)
    (hc_eq : c = m ^ 2 - n ^ 2)
    (hb_sq : b ^ 2 = 2 * m * n)
    (ha_sq : a ^ 2 = m ^ 2 + n ^ 2) : False := by
  -- Step 1: square split.
  obtain ⟨i, j, hm_eq, hn_eq, hb_eq⟩ := hSplit1 m n b h_m_nn h_n_pos
    hmn_coprime hm_odd hn_even hb_sq
  -- Step 2: `a² - i⁴ = 4j⁴` follows from `a² = m² + n²`, `m = i²`, `n = 2j²`.
  have ha_sq' : a ^ 2 - i ^ 4 = 4 * j ^ 4 := by
    rw [hm_eq, hn_eq] at ha_sq
    linear_combination ha_sq
  -- j ≠ 0: if j = 0, n = 0, contradicting h_n_pos.
  have hj_ne : j ≠ 0 := by
    intro hj
    rw [hj] at hn_eq
    simp at hn_eq
    linarith
  -- i odd: m = i² and m odd ⟹ i² odd ⟹ i odd.
  have hi_odd : i % 2 = 1 := by
    rw [hm_eq] at hm_odd
    rw [show (i ^ 2 : ℤ) = i * i from sq i, Int.mul_emod] at hm_odd
    rcases Int.emod_two_eq_zero_or_one i with h | h
    · rw [h] at hm_odd; norm_num at hm_odd
    · exact h
  -- gcd(a, i·j) = 1: follows from gcd(a, b) = 1 and b = 2ij.
  have hab_coprime : IsCoprime a b :=
    Fermat42Sub.coprime_of_minimal h_min
  have ha_ij_coprime : IsCoprime a (i * j) := by
    have hb_fact : b = 2 * (i * j) := by rw [hb_eq]; ring
    have h1 : IsCoprime a (2 * (i * j)) := hb_fact ▸ hab_coprime
    exact h1.of_mul_right_right
  -- Step 3: 4th power split.
  obtain ⟨p, q, hpq, hp_eq, hq_eq⟩ := hSplit2 a i j ha_pos hi_odd hj_ne
    ha_ij_coprime ha_sq'
  -- Step 4: construct new Fermat42Sub (q, p, 2j).
  have h_new_eq : q ^ 4 - p ^ 4 = (2 * j) ^ 2 := by
    have : q ^ 4 - p ^ 4 = (a + 2 * j ^ 2) - (a - 2 * j ^ 2) := by
      rw [hp_eq, hq_eq]
    rw [this]
    ring
  -- p, q nonzero (from pq = i ≠ 0 since i odd implies i ≠ 0).
  have hi_ne : i ≠ 0 := by
    intro h
    rw [h] at hi_odd
    norm_num at hi_odd
  have hp_ne : p ≠ 0 := left_ne_zero_of_mul (by rw [hpq]; exact hi_ne)
  have hq_ne : q ≠ 0 := right_ne_zero_of_mul (by rw [hpq]; exact hi_ne)
  have h2j_ne : (2 * j : ℤ) ≠ 0 := mul_ne_zero two_ne_zero hj_ne
  have h_new : Fermat42Sub q p (2 * j) := ⟨hq_ne, hp_ne, h2j_ne, h_new_eq⟩
  -- Step 5: |2j| < |c| contradicts minimality.
  have h_le : Int.natAbs c ≤ Int.natAbs (2 * j) := h_min.2 q p (2 * j) h_new
  -- c = m² - n² = i⁴ - 4j⁴. |c| ≥ 4j² + 1 ≥ 2|j| + 1 for |j| ≥ 1.
  -- Need |2j| < |c|.
  have hj_abs_pos : 0 < Int.natAbs j := Int.natAbs_pos.mpr hj_ne
  have hc_eq' : c = i ^ 4 - 4 * j ^ 4 := by
    rw [hc_eq, hm_eq, hn_eq]
    ring
  -- c > 0 and c = i⁴ - 4j⁴ > 0 → i⁴ > 4j⁴ → i² > 2j² (taking sqrt).
  have hi_sq_gt : i ^ 2 > 2 * j ^ 2 := by
    by_contra h_le_ij
    push_neg at h_le_ij
    have h_i4_le : i ^ 4 ≤ 4 * j ^ 4 := by
      have : i ^ 2 * i ^ 2 ≤ (2 * j ^ 2) * (2 * j ^ 2) := by
        exact mul_le_mul h_le_ij h_le_ij (sq_nonneg _) (by positivity)
      calc i ^ 4 = i ^ 2 * i ^ 2 := by ring
        _ ≤ (2 * j ^ 2) * (2 * j ^ 2) := this
        _ = 4 * j ^ 4 := by ring
    linarith
  -- From i² > 2j²: i² ≥ 2j² + 1 (since both integers). So i⁴ ≥ (2j² + 1)² = 4j⁴ + 4j² + 1.
  -- Hence c = i⁴ - 4j⁴ ≥ 4j² + 1.
  have hc_ge : 4 * j ^ 2 + 1 ≤ c := by
    have h1 : 2 * j ^ 2 + 1 ≤ i ^ 2 := hi_sq_gt
    have h2j_nn : 0 ≤ 2 * j ^ 2 + 1 := by positivity
    have h2 : (2 * j ^ 2 + 1) ^ 2 ≤ (i ^ 2) ^ 2 :=
      pow_le_pow_left₀ h2j_nn h1 2
    have h3 : (2 * j ^ 2 + 1) ^ 2 = 4 * j ^ 4 + 4 * j ^ 2 + 1 := by ring
    have h4 : (i ^ 2) ^ 2 = i ^ 4 := by ring
    rw [hc_eq']
    linarith [h2, h3, h4]
  -- Now |2j| ≤ 2|j|, and |c| ≥ 4j² + 1 ≥ 4|j|² + 1 > 2|j|.
  have h_abs_lt : Int.natAbs (2 * j) < Int.natAbs c := by
    have h2j_abs : Int.natAbs (2 * j) = 2 * Int.natAbs j := by
      rw [Int.natAbs_mul]; rfl
    have hc_cast : (Int.natAbs c : ℤ) = c := Int.natAbs_of_nonneg hc_pos.le
    have h_jsq_cast : (j : ℤ) ^ 2 = (Int.natAbs j : ℤ) ^ 2 := by
      rw [show ((Int.natAbs j : ℤ)) = |j| from (Int.abs_eq_natAbs j).symm,
          sq_abs]
    have hc_abs_ge : (4 * (Int.natAbs j : ℤ) ^ 2 + 1 : ℤ) ≤ (Int.natAbs c : ℤ) := by
      rw [hc_cast, ← h_jsq_cast]
      exact hc_ge
    have hc_abs_nat : 4 * (Int.natAbs j) ^ 2 + 1 ≤ Int.natAbs c := by
      have h1 : ((4 * (Int.natAbs j) ^ 2 + 1 : ℕ) : ℤ)
            = 4 * (Int.natAbs j : ℤ) ^ 2 + 1 := by push_cast; ring
      have h2 : ((Int.natAbs c : ℕ) : ℤ) = (Int.natAbs c : ℤ) := by rfl
      have h3 : ((4 * (Int.natAbs j) ^ 2 + 1 : ℕ) : ℤ) ≤ ((Int.natAbs c : ℕ) : ℤ) := by
        rw [h1, h2]; exact hc_abs_ge
      exact_mod_cast h3
    rw [h2j_abs]
    have := hj_abs_pos
    calc 2 * Int.natAbs j
        < 4 * (Int.natAbs j) ^ 2 + 1 := by nlinarith
      _ ≤ Int.natAbs c := hc_abs_nat
  exact absurd h_le (not_le_of_gt h_abs_lt)

end PF.Fermat42Sub

/-! ## §Axiom check -/
#print axioms PF.Fermat42Sub.fermat42Sub_caseB_descends
