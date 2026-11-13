/-
# PF.Fermat42SubCaseAReduction_2026_11_13

**Case A reduction for `not_fermat_42_sub`**: if `Fermat42Sub a b c`
with `b odd, c even`, then the Pythagorean decomposition reduces to
an instance of the auxiliary equation `2a'² = s⁴ + t⁴` with coprime
odd `s, t` and nonzero `a'`.

## Proof outline

Given `a⁴ − b⁴ = c²` with `(a, b)` coprime, `a odd, b odd, c even`:
1. Pythagorean classification of `(b², c, a²)`:
   ∃ m, n coprime of opposite parity, m ≥ 0, with
   * b² = m² − n²
   * c = 2mn
   * a² = m² + n²
2. WLOG m odd, n even (else swap via commutativity of the leg
   structure).  Write n = 2k.
3. b² = m² − n² = (m − 2k)(m + 2k).  Both factors odd and coprime
   (gcd argument from gcd(m, n) = 1 and m odd).
4. Each factor is a square: `m − 2k = s²`, `m + 2k = t²`, `st = b`.
5. Combining: `a² = (s⁴ + t⁴)/2`, i.e., `2a² = s⁴ + t⁴`.

The resulting equation `2a² = s⁴ + t⁴` has no nontrivial coprime
solutions (classical Fermat result).  Its non-solvability is stated
here as a named sub-gap `Fermat42Double_impossible`, since its
proof is a separate descent (~50-80 Lean lines).

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-13.
-/

import PF.Fermat42SubFoundations_2026_11_13

namespace PF.Fermat42Sub

/-- **Auxiliary Diophantine equation**: `2a² = s⁴ + t⁴` has no
nontrivial coprime solutions.

Classical Fermat result (same era as `not_fermat_42`, separate descent).
Proof structure: Pythagorean decomposition of the derived equation
`u² + v² = a²` with `u = (s²+t²)/2, v = (t²-s²)/2`, followed by
infinite descent.

Stated as a named Prop.  Discharging requires ~50-80 Lean lines. -/
def Fermat42Double_impossible : Prop :=
  ∀ s t a : ℤ, s ≠ 0 → t ≠ 0 → a ≠ 0 → IsCoprime s t →
    2 * a ^ 2 ≠ s ^ 4 + t ^ 4

/-- **Sub-gap 3**: `b² = (m − 2k)(m + 2k)` with coprime factors
(both odd), so each factor is a perfect square.

Standard coprime-square-product lemma.  Named for the descent. -/
def Fermat42SubCaseA_squareSplit : Prop :=
  ∀ m k b : ℤ, m % 2 = 1 → IsCoprime m (2 * k) →
    b ^ 2 = (m - 2 * k) * (m + 2 * k) →
    ∃ s t : ℤ, m - 2 * k = s ^ 2 ∧ m + 2 * k = t ^ 2 ∧
      s * t = b ∧ IsCoprime s t ∧ s % 2 = 1 ∧ t % 2 = 1

/-- **Case A reduction**: under the Case A hypothesis, we derive
an auxiliary `2a² = s⁴ + t⁴` instance that must be contradicted. -/
theorem fermat42Sub_caseA_reduces
    (hSplit3 : Fermat42SubCaseA_squareSplit)
    (hDouble : Fermat42Double_impossible)
    (a b c m n : ℤ)
    (_h_min : Minimal a b c)
    (_ha_pos : 0 < a) (_hc_pos : 0 < c)
    (_h_m_nn : 0 ≤ m) (_h_n_pos : 0 < n)
    (hmn_coprime : IsCoprime m n)
    (hm_odd : m % 2 = 1) (hn_even : n % 2 = 0)
    (hb_sq : b ^ 2 = m ^ 2 - n ^ 2)
    (ha_sq : a ^ 2 = m ^ 2 + n ^ 2) : False := by
  -- Write n = 2k where k = n / 2.
  obtain ⟨k, hk⟩ : (2 : ℤ) ∣ n := Int.dvd_of_emod_eq_zero hn_even
  -- hk : n = 2 * k.
  subst hk
  -- b² = m² - (2k)² = (m - 2k)(m + 2k).
  have hb_fact : b ^ 2 = (m - 2 * k) * (m + 2 * k) := by
    rw [hb_sq]; ring
  -- Apply sub-gap 3: square split.
  obtain ⟨s, t, hs_eq, ht_eq, hst_eq, hst_coprime, hs_odd, ht_odd⟩ :=
    hSplit3 m k b hm_odd hmn_coprime hb_fact
  -- From m - 2k = s² and m + 2k = t²: 2m = s² + t², 2(2k) = t² - s².
  -- Then a² = m² + (2k)² = ((s²+t²)/2)² + ((t²-s²)/2)² = (s⁴+t⁴)/2.
  have ha_dbl : 2 * a ^ 2 = s ^ 4 + t ^ 4 := by
    have h1 : 2 * m = s ^ 2 + t ^ 2 := by linear_combination hs_eq + ht_eq
    have h2 : 4 * k = t ^ 2 - s ^ 2 := by linear_combination ht_eq - hs_eq
    -- 4a² = 4(m² + (2k)²) = (2m)² + (4k)² = (s²+t²)² + (t²-s²)² = 2(s⁴+t⁴).
    have h3 : (2 * a) ^ 2 = (s ^ 2 + t ^ 2) ^ 2 + (t ^ 2 - s ^ 2) ^ 2 := by
      have : (2 * a) ^ 2 = 4 * a ^ 2 := by ring
      rw [this, ha_sq]
      have hfour_k : (4 * k) ^ 2 = 16 * k ^ 2 := by ring
      -- 4(m² + 4k²) = (2m)² + (4k)²
      calc 4 * (m ^ 2 + (2 * k) ^ 2)
          = (2 * m) ^ 2 + (4 * k) ^ 2 := by ring
        _ = (s ^ 2 + t ^ 2) ^ 2 + (t ^ 2 - s ^ 2) ^ 2 := by rw [h1, h2]
    -- (s²+t²)² + (t²-s²)² = 2(s⁴+t⁴).
    have h4 : (s ^ 2 + t ^ 2) ^ 2 + (t ^ 2 - s ^ 2) ^ 2 = 2 * (s ^ 4 + t ^ 4) := by
      ring
    have h5 : (2 * a) ^ 2 = 2 * (s ^ 4 + t ^ 4) := by rw [h3, h4]
    have h6 : (2 * a) ^ 2 = 4 * a ^ 2 := by ring
    linarith [h5, h6]
  -- s, t, a nonzero.
  have hb_ne : b ≠ 0 := _h_min.1.2.1
  have hst_ne : s * t ≠ 0 := by rw [hst_eq]; exact hb_ne
  have hs_ne : s ≠ 0 := left_ne_zero_of_mul hst_ne
  have ht_ne : t ≠ 0 := right_ne_zero_of_mul hst_ne
  have ha_ne : a ≠ 0 := ne_of_gt _ha_pos
  -- Apply sub-gap: 2a² = s⁴ + t⁴ is impossible.
  exact hDouble s t a hs_ne ht_ne ha_ne hst_coprime ha_dbl

end PF.Fermat42Sub

/-! ## §Axiom check -/
#print axioms PF.Fermat42Sub.fermat42Sub_caseA_reduces
