/-
# PF.Ch24DescentSub2TorsionCore_2026_11_14

**Descent core for `y² = x³ - x` — mirror of the
`y² = x³ + x` descent (`Ch24Descent2TorsionCore_2026_10_17`),
now using today's `not_fermat_42_sub` (landed 2026-11-14).**

## The curve and the strategy

`E : y² = x³ - x` (conductor 32, LMFDB 32.a2, rank 0).

Three rational 2-torsion points: `(0, 0), (1, 0), (-1, 0)`.  Claim: these
are the only rational points.

A rational point writes as `x = m/e²`, `y = n/e³` with `gcd(m, e) = 1`,
`e ≠ 0`.  Substituting and clearing denominators gives exactly

    `n² = m · (m² - e⁴)`.

The two factors are coprime (`m² - e⁴ ≡ -e⁴ mod m`), and their product
is a square.  Case analysis on signs of `m` and `m² - e⁴`:

* `m > 0 ∧ m² > e⁴`: both factors positive, each a perfect square;
  `m = d²`, `m² - e⁴ = t²`.  Combining: `d⁴ - e⁴ = t²`, contradicting
  `not_fermat_42_sub`.
* `m < 0 ∧ m² < e⁴`: both factors negative, each is minus-a-square;
  `m = -d²`, `m² - e⁴ = -t²`, i.e., `e⁴ - m² = t²`.  Combining:
  `e⁴ - d⁴ = t²`, contradicting `not_fermat_42_sub`.
* Mixed signs: `m(m² - e⁴) < 0`, but `n² ≥ 0`, forcing `n = 0`, hence
  `m(m² - e⁴) = 0`, hence `m = 0` or `m² = e⁴` — the 2-torsion cases,
  excluded by hypothesis.

## What is proved here

`descent_sub_core` — the displayed implication, over `ℤ`, with no
denominators:

    `e ≠ 0 → m ≠ 0 → m² ≠ e⁴ → IsCoprime m e →
     n² = m(m² - e⁴) → False`.

The hard infinite descent is **not** re-proved: it is
`PF.not_fermat_42_sub`.

Three-axiom bar: `[propext, Classical.choice, Quot.sound]`.  No `sorry`,
no project axioms, no `native_decide`.

Authors: Pablo Cohen. 2026-11-14.
-/

import PF.Fermat42SubAssembly_2026_11_14
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace PrincipiaTractalis.Ch24DescentSub20261114

/-! ## §1 — coprimality of the two descent factors -/

/-- `m` is coprime to `m² - e⁴` whenever it is coprime to `e`. -/
theorem isCoprime_descent_factors_sub {m e : ℤ} (hco : IsCoprime m e) :
    IsCoprime m (m ^ 2 - e ^ 4) := by
  have h4 : IsCoprime m (e ^ 4) := hco.pow_right
  -- m² - e⁴ = -e⁴ + m*m, which is -(e^4) + m*m.
  -- IsCoprime m (-(e^4)) = IsCoprime m (e^4) up to sign.
  have hneg : IsCoprime m (-(e ^ 4)) := h4.neg_right
  have := hneg.add_mul_left_right m
  -- now: IsCoprime m (-e^4 + m*m)
  have hEq : -(e ^ 4) + m * m = m ^ 2 - e ^ 4 := by ring
  rwa [hEq] at this

/-! ## §2 — descent sub-case on positive m, positive second factor -/

/-- **Positive-positive case.**  Assume `m > 0, m² > e⁴, e ≠ 0,
IsCoprime m e, n² = m(m² - e⁴)`.  Then `False`. -/
theorem descent_sub_case_pos_pos {m e n : ℤ} (he : e ≠ 0)
    (hm_pos : 0 < m) (hsq_gt : e ^ 4 < m ^ 2)
    (hco : IsCoprime m e)
    (h : n ^ 2 = m * (m ^ 2 - e ^ 4)) : False := by
  have hpos : 0 < m ^ 2 - e ^ 4 := by linarith
  have hcf : IsCoprime m (m ^ 2 - e ^ 4) :=
    isCoprime_descent_factors_sub hco
  have hmul : m * (m ^ 2 - e ^ 4) = n ^ 2 := h.symm
  obtain ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow' hcf hmul
  obtain ⟨t, ht⟩ :=
    exists_associated_pow_of_mul_eq_pow' hcf.symm
      (by linarith [hmul] : (m ^ 2 - e ^ 4) * m = n ^ 2)
  have hdm : m = d ^ 2 := by
    rcases Int.associated_iff.mp hd with hcase | hcase
    · exact hcase.symm
    · exfalso
      have : (0 : ℤ) ≤ d ^ 2 := sq_nonneg d
      omega
  have htm : m ^ 2 - e ^ 4 = t ^ 2 := by
    rcases Int.associated_iff.mp ht with hcase | hcase
    · exact hcase.symm
    · exfalso
      have : (0 : ℤ) ≤ t ^ 2 := sq_nonneg t
      omega
  have hd0 : d ≠ 0 := by
    intro hdz
    rw [hdz] at hdm
    simp at hdm
    linarith
  have ht0 : t ≠ 0 := by
    intro htz
    rw [htz] at htm
    simp at htm
    linarith
  have hfermat : d ^ 4 - e ^ 4 = t ^ 2 := by
    have : m ^ 2 = d ^ 4 := by rw [hdm]; ring
    linarith [htm, this]
  exact PF.not_fermat_42_sub d e t hd0 he ht0 hfermat

/-! ## §4 — descent sub-case on negative m, negative second factor -/

/-- **Negative-negative case.**  Assume `m < 0, m² < e⁴, e ≠ 0,
IsCoprime m e, n² = m(m² - e⁴)`.  Then `False`. -/
theorem descent_sub_case_neg_neg {m e n : ℤ} (he : e ≠ 0)
    (hm_neg : m < 0) (hsq_lt : m ^ 2 < e ^ 4)
    (hco : IsCoprime m e)
    (h : n ^ 2 = m * (m ^ 2 - e ^ 4)) : False := by
  have hneg : m ^ 2 - e ^ 4 < 0 := by linarith
  -- (-m) > 0, (e⁴ - m²) > 0, product (-m)(e⁴ - m²) = m(m² - e⁴) = n² ≥ 0.
  have hnm_pos : 0 < -m := by linarith
  have hemm_pos : 0 < e ^ 4 - m ^ 2 := by linarith
  have h_prod : (-m) * (e ^ 4 - m ^ 2) = n ^ 2 := by
    have := h.symm
    linarith [this]
  -- Coprimality of (-m) and (e⁴ - m²): IsCoprime m e ⟹ IsCoprime (-m) e ⟹ ...
  have hco_nm : IsCoprime (-m) e := hco.neg_left
  have hcf : IsCoprime (-m) (e ^ 4 - m ^ 2) := by
    have h1 : IsCoprime (-m) ((-m) ^ 2 - e ^ 4) := isCoprime_descent_factors_sub hco_nm
    have hEq : (-m) ^ 2 - e ^ 4 = -(e ^ 4 - m ^ 2) := by ring
    rw [hEq] at h1
    have : IsCoprime (-m) (- -(e ^ 4 - m ^ 2)) := h1.neg_right
    simpa using this
  obtain ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow' hcf h_prod
  obtain ⟨t, ht⟩ :=
    exists_associated_pow_of_mul_eq_pow' hcf.symm
      (by linarith [h_prod] : (e ^ 4 - m ^ 2) * (-m) = n ^ 2)
  have hnm_eq : -m = d ^ 2 := by
    rcases Int.associated_iff.mp hd with hcase | hcase
    · exact hcase.symm
    · exfalso
      have : (0 : ℤ) ≤ d ^ 2 := sq_nonneg d
      omega
  have hem_eq : e ^ 4 - m ^ 2 = t ^ 2 := by
    rcases Int.associated_iff.mp ht with hcase | hcase
    · exact hcase.symm
    · exfalso
      have : (0 : ℤ) ≤ t ^ 2 := sq_nonneg t
      omega
  have hd0 : d ≠ 0 := by
    intro hdz
    rw [hdz] at hnm_eq
    simp at hnm_eq
    linarith
  have ht0 : t ≠ 0 := by
    intro htz
    rw [htz] at hem_eq
    simp at hem_eq
    linarith
  -- From -m = d²: m = -d², m² = d⁴.
  -- From e⁴ - m² = t²: e⁴ - d⁴ = t².
  have hfermat : e ^ 4 - d ^ 4 = t ^ 2 := by
    have hmd : m = -(d ^ 2) := by linarith [hnm_eq]
    have hm2 : m ^ 2 = d ^ 4 := by rw [hmd]; ring
    linarith [hem_eq, hm2]
  exact PF.not_fermat_42_sub e d t he hd0 ht0 hfermat

/-! ## §5 — the full descent core -/

/-- **Full descent core for `y² = x³ - x`.**  With `e ≠ 0`, `m ≠ 0`,
`m² ≠ e⁴`, `m` coprime to `e`, the equation `n² = m(m² - e⁴)` is
impossible.  (The excluded cases `m = 0` and `m² = e⁴` correspond to the
three rational 2-torsion points `(0, 0), (1, 0), (-1, 0)`.) -/
theorem descent_sub_core {m e n : ℤ} (he : e ≠ 0) (hm : m ≠ 0)
    (hsq : m ^ 2 ≠ e ^ 4) (hco : IsCoprime m e)
    (h : n ^ 2 = m * (m ^ 2 - e ^ 4)) : False := by
  -- Split on sign of m(m² - e⁴).  n² ≥ 0 forces product ≥ 0.
  have h_prod_nn : 0 ≤ m * (m ^ 2 - e ^ 4) := by rw [← h]; exact sq_nonneg n
  -- Either both m and (m² - e⁴) positive, both negative, or at least one zero.
  rcases lt_trichotomy m 0 with hm_neg | hm_zero | hm_pos
  · -- m < 0: product ≥ 0 requires m² - e⁴ ≤ 0, i.e., m² ≤ e⁴.
    have hsq_le : m ^ 2 ≤ e ^ 4 := by nlinarith [h_prod_nn, hm_neg]
    have hsq_lt : m ^ 2 < e ^ 4 := lt_of_le_of_ne hsq_le hsq
    exact descent_sub_case_neg_neg he hm_neg hsq_lt hco h
  · exact hm hm_zero
  · -- m > 0: product ≥ 0 requires m² - e⁴ ≥ 0, i.e., m² ≥ e⁴.
    have hsq_ge : e ^ 4 ≤ m ^ 2 := by nlinarith [h_prod_nn, hm_pos]
    have hsq_gt : e ^ 4 < m ^ 2 := lt_of_le_of_ne hsq_ge (Ne.symm hsq)
    exact descent_sub_case_pos_pos he hm_pos hsq_gt hco h

end PrincipiaTractalis.Ch24DescentSub20261114

/-! ## §Axiom check -/
#print axioms PrincipiaTractalis.Ch24DescentSub20261114.isCoprime_descent_factors_sub
#print axioms PrincipiaTractalis.Ch24DescentSub20261114.descent_sub_case_pos_pos
#print axioms PrincipiaTractalis.Ch24DescentSub20261114.descent_sub_case_neg_neg
#print axioms PrincipiaTractalis.Ch24DescentSub20261114.descent_sub_core
