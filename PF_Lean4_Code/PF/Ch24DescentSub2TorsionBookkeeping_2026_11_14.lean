/-
# PF.Ch24DescentSub2TorsionBookkeeping_2026_11_14

**Two bookkeeping layers on top of `descent_sub_core` for the curve
`y² = x³ - x` — the mirror of Ch24Descent2TorsionBookkeeping_2026_10_17.**

## Layer 1 — lowest-terms form (§2)

`descent_sub_lowest_terms` : for integers `a, b, Y` with `b > 0`,
`a` coprime to `b`,

    `Y² = a·b·(a² - b²)  →  a = 0 ∨ a² = b²`.

This is the shape a rational point takes after clearing denominators:
writing `x = a/b` in lowest terms and multiplying `y² = x³ - x` through
by `b⁴` gives exactly `(b²y)² = ab(a² - b²)`.

The three excluded cases (`a = 0`, `a = b = 1`, `a = -1, b = 1`)
correspond to the three rational 2-torsion points `(0, 0), (1, 0),
(-1, 0)`.

## Layer 2 — rank zero from 2-torsion

Reused unchanged from the sum form: `rank_eq_zero_of_two_torsion` is
not specific to a curve.

## The remaining interface

Connecting §1 to `E(ℚ)` for `E : y² = x³ - x` still needs the
`Rat`-level step (`a = x.num`, `b = x.den`, `Y = b²y`).  That is
`Rat.num`/`Rat.den` bookkeeping, done in
`Ch24DescentSub2TorsionRatBridge_2026_11_14` (to follow).

Three-axiom bar: `[propext, Classical.choice, Quot.sound]`.  No `sorry`,
no project axioms, no `native_decide`.

Authors: Pablo Cohen. 2026-11-14.
-/

import PF.Ch24DescentSub2TorsionCore_2026_11_14
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.RingTheory.Int.Basic

namespace PrincipiaTractalis.Ch24DescentSubBookkeeping20261114

open PrincipiaTractalis.Ch24DescentSub20261114

/-! ## §1 — coprimality bookkeeping (mirror) -/

/-- From `IsCoprime a b`, the two descent factors `a*b` and `a² - b²`
are coprime. -/
theorem isCoprime_prod_diffSq {a b : ℤ} (hco : IsCoprime a b) :
    IsCoprime (a * b) (a ^ 2 - b ^ 2) := by
  have ha : IsCoprime a (a ^ 2 - b ^ 2) := by
    have h2 : IsCoprime a (b ^ 2) := hco.pow_right
    have h2neg : IsCoprime a (-(b ^ 2)) := h2.neg_right
    have := h2neg.add_mul_left_right a
    have hEq : -(b ^ 2) + a * a = a ^ 2 - b ^ 2 := by ring
    rwa [hEq] at this
  have hb : IsCoprime b (a ^ 2 - b ^ 2) := by
    -- (hco.symm).pow_right : IsCoprime b (a^2), i.e., ∃ p q, p*b + q*a^2 = 1.
    -- Then (p + q*b)*b + q*(a^2 - b^2) = p*b + q*b^2 + q*a^2 - q*b^2 = p*b + q*a^2 = 1.
    have h2 : IsCoprime b (a ^ 2) := (hco.symm).pow_right
    obtain ⟨p, q, hpq⟩ := h2
    exact ⟨p + q * b, q, by linear_combination hpq⟩
  exact ha.mul_left hb

/-- If `IsCoprime x (y ^ 2)` then `IsCoprime x y`. -/
theorem isCoprime_of_isCoprime_pow_right {x y : ℤ} (h : IsCoprime x (y ^ 2)) :
    IsCoprime x y := by
  obtain ⟨p, q, hpq⟩ := h
  exact ⟨p, q * y, by linear_combination hpq⟩

/-! ## §2 — Layer 1: the lowest-terms form (difference) -/

/-- **Layer 1.**  Lowest-terms shape of a rational point on
`y² = x³ - x`: with `x = a/b` reduced (`b > 0`, `gcd(a, b) = 1`) and
`Y = b²y`, the curve equation becomes `Y² = ab(a² - b²)`, and this
forces `a = 0` or `a² = b²`. -/
theorem descent_sub_lowest_terms {a b Y : ℤ} (hb : 0 < b) (hco : IsCoprime a b)
    (h : Y ^ 2 = a * b * (a ^ 2 - b ^ 2)) : a = 0 ∨ a ^ 2 = b ^ 2 := by
  by_contra hcontra
  push_neg at hcontra
  obtain ⟨ha, hab_sq⟩ := hcontra
  -- Y² = ab(a² - b²) ≥ 0, so sign(ab) = sign(a² - b²).
  have hY2_nn : 0 ≤ Y ^ 2 := sq_nonneg Y
  have h_prod_nn : 0 ≤ a * b * (a ^ 2 - b ^ 2) := by linarith [h]
  -- Split on sign of a.
  have hb_ne : b ≠ 0 := Int.ne_of_gt hb
  rcases lt_trichotomy a 0 with ha_neg | ha_zero | ha_pos
  · -- Case a < 0, b > 0: ab < 0, hence a² - b² ≤ 0. If a² = b² excluded.
    have hab_neg : a * b < 0 := mul_neg_of_neg_of_pos ha_neg hb
    have h_diff_le : a ^ 2 - b ^ 2 ≤ 0 := by nlinarith [h_prod_nn, hab_neg]
    have h_diff_lt : a ^ 2 - b ^ 2 < 0 := lt_of_le_of_ne h_diff_le
      (fun heq => hab_sq (by linarith [heq]))
    -- Transform to positives: (-a)(b)(b² - a²) = Y².
    have hna_pos : 0 < -a := by linarith
    have hbma_pos : 0 < b ^ 2 - a ^ 2 := by linarith
    have h_prod_rw : (-a) * b * (b ^ 2 - a ^ 2) = Y ^ 2 := by
      have := h; linarith [this]
    have hna_b_pos : 0 < (-a) * b := mul_pos hna_pos hb
    have h_outer : 0 < (-a) * b * (b ^ 2 - a ^ 2) := by
      exact mul_pos hna_b_pos hbma_pos
    -- Coprime: IsCoprime ((-a)·b) (b² - a²).
    have hco_neg : IsCoprime (-a) b := hco.neg_left
    have hcf : IsCoprime ((-a) * b) (b ^ 2 - a ^ 2) := by
      have h1 : IsCoprime (-a * b) ((-a) ^ 2 - b ^ 2) := isCoprime_prod_diffSq hco_neg
      -- (-a)² - b² = a² - b² = -(b² - a²).
      have hEq : (-a) ^ 2 - b ^ 2 = -(b ^ 2 - a ^ 2) := by ring
      rw [hEq] at h1
      have h2 : IsCoprime (-a * b) (- -(b ^ 2 - a ^ 2)) := h1.neg_right
      simpa using h2
    -- Each factor is a square.
    obtain ⟨s, hs⟩ := exists_associated_pow_of_mul_eq_pow' hcf h_prod_rw
    obtain ⟨t, ht⟩ := exists_associated_pow_of_mul_eq_pow' hcf.symm
      (by linarith [h_prod_rw] : (b ^ 2 - a ^ 2) * ((-a) * b) = Y ^ 2)
    have hssq : (-a) * b = s ^ 2 := by
      rcases Int.associated_iff.mp hs with hc | hc
      · exact hc.symm
      · exfalso; have := sq_nonneg s; omega
    have htsq : b ^ 2 - a ^ 2 = t ^ 2 := by
      rcases Int.associated_iff.mp ht with hc | hc
      · exact hc.symm
      · exfalso; have := sq_nonneg t; omega
    -- Split -a·b = s² with gcd(-a, b) = 1.
    obtain ⟨u, hu⟩ := exists_associated_pow_of_mul_eq_pow' hco_neg hssq
    obtain ⟨v, hv⟩ := exists_associated_pow_of_mul_eq_pow' hco_neg.symm
      (by linarith [hssq] : b * (-a) = s ^ 2)
    have hausq : -a = u ^ 2 := by
      rcases Int.associated_iff.mp hu with hc | hc
      · exact hc.symm
      · exfalso; have := sq_nonneg u; omega
    have hbsq : b = v ^ 2 := by
      rcases Int.associated_iff.mp hv with hc | hc
      · exact hc.symm
      · exfalso; have := sq_nonneg v; omega
    -- Now apply descent_sub_core with m = a, e = v, n = u·t.
    have hv0 : v ≠ 0 := by
      intro hvz; rw [hvz] at hbsq; simp at hbsq; omega
    have hco_a_v : IsCoprime a v := by
      refine isCoprime_of_isCoprime_pow_right ?_
      rw [← hbsq]; exact hco
    have hm_sq_e4 : a ^ 2 = v ^ 4 → False := by
      intro heq_sq
      have : v ^ 4 = b ^ 2 := by rw [hbsq]; ring
      exact hab_sq (by linarith [heq_sq, this])
    have hkey : (u * t) ^ 2 = a * (a ^ 2 - v ^ 4) := by
      have h_a_neg : a = -(u ^ 2) := by linarith [hausq]
      have h_a2 : a ^ 2 = u ^ 4 := by rw [h_a_neg]; ring
      have h_v4 : v ^ 4 = b ^ 2 := by rw [hbsq]; ring
      have h_t2_eq : t ^ 2 = b ^ 2 - a ^ 2 := htsq.symm
      have h_u4_v4 : u ^ 4 - v ^ 4 = a ^ 2 - b ^ 2 := by rw [h_a2, h_v4]
      have h_ut_sq : (u * t) ^ 2 = u ^ 2 * t ^ 2 := by ring
      rw [h_ut_sq, h_a_neg]
      -- Goal: u^2 * t^2 = (-(u^2)) * ((-(u^2))^2 - v^4)
      -- = -u^2 * (u^4 - v^4)
      -- = -u^2 * (a^2 - b^2)
      -- = u^2 * (b^2 - a^2)  -- and t^2 = b^2 - a^2
      have : u ^ 2 * t ^ 2 = u ^ 2 * (b ^ 2 - a ^ 2) := by rw [h_t2_eq]
      rw [this, h_a2, h_v4]; ring
    exact descent_sub_core hv0 ha (by
      intro heq
      have : v ^ 4 = b ^ 2 := by rw [hbsq]; ring
      exact hab_sq (by linarith [heq, this])) hco_a_v hkey
  · exact ha ha_zero
  · -- Case a > 0, b > 0: ab > 0, hence a² - b² ≥ 0. If a² = b² excluded.
    have hab_pos : 0 < a * b := mul_pos ha_pos hb
    have h_diff_ge : 0 ≤ a ^ 2 - b ^ 2 := by nlinarith [h_prod_nn, hab_pos]
    have h_diff_gt : 0 < a ^ 2 - b ^ 2 := lt_of_le_of_ne h_diff_ge
      (fun heq => hab_sq (by linarith [heq.symm]))
    have hcf : IsCoprime (a * b) (a ^ 2 - b ^ 2) := isCoprime_prod_diffSq hco
    have hmul : a * b * (a ^ 2 - b ^ 2) = Y ^ 2 := h.symm
    obtain ⟨s, hs⟩ := exists_associated_pow_of_mul_eq_pow' hcf hmul
    obtain ⟨t, ht⟩ := exists_associated_pow_of_mul_eq_pow' hcf.symm
      (by linarith [hmul] : (a ^ 2 - b ^ 2) * (a * b) = Y ^ 2)
    have hssq : a * b = s ^ 2 := by
      rcases Int.associated_iff.mp hs with hc | hc
      · exact hc.symm
      · exfalso; have := sq_nonneg s; omega
    have htsq : a ^ 2 - b ^ 2 = t ^ 2 := by
      rcases Int.associated_iff.mp ht with hc | hc
      · exact hc.symm
      · exfalso; have := sq_nonneg t; omega
    obtain ⟨u, hu⟩ := exists_associated_pow_of_mul_eq_pow' hco hssq
    obtain ⟨v, hv⟩ := exists_associated_pow_of_mul_eq_pow' hco.symm
      (by linarith [hssq] : b * a = s ^ 2)
    have hasq : a = u ^ 2 := by
      rcases Int.associated_iff.mp hu with hc | hc
      · exact hc.symm
      · exfalso; have := sq_nonneg u; omega
    have hbsq : b = v ^ 2 := by
      rcases Int.associated_iff.mp hv with hc | hc
      · exact hc.symm
      · exfalso; have := sq_nonneg v; omega
    have hv0 : v ≠ 0 := by
      intro hvz; rw [hvz] at hbsq; simp at hbsq; omega
    have hco_a_v : IsCoprime a v := by
      refine isCoprime_of_isCoprime_pow_right ?_
      rw [← hbsq]; exact hco
    have hkey : (u * t) ^ 2 = a * (a ^ 2 - v ^ 4) := by
      have h_u4_eq_a2 : u ^ 4 = a ^ 2 := by rw [hasq]; ring
      have h_v4_eq_b2 : v ^ 4 = b ^ 2 := by rw [hbsq]; ring
      have h_t2_eq : t ^ 2 = u ^ 4 - v ^ 4 := by
        rw [h_u4_eq_a2, h_v4_eq_b2]; linarith [htsq]
      have h_ut_sq : (u * t) ^ 2 = u ^ 2 * t ^ 2 := by ring
      rw [h_ut_sq, h_t2_eq, hasq]; ring
    exact descent_sub_core hv0 ha (by
      intro heq
      have : v ^ 4 = b ^ 2 := by rw [hbsq]; ring
      exact hab_sq (by linarith [heq, this])) hco_a_v hkey

/-! ## §3 — Layer 2: rank zero from 2-torsion (reused, generic) -/

/-- **Layer 2.**  A `ℤ`-module in which every element is killed by `2`
has rank `0`.  (Identical to the sum-form version; curve-independent.) -/
theorem rank_eq_zero_of_two_torsion {M : Type*} [AddCommGroup M] [Module ℤ M]
    (h : ∀ P : M, P + P = 0) : Module.rank ℤ M = 0 := by
  rw [rank_eq_zero_iff]
  intro P
  refine ⟨2, by norm_num, ?_⟩
  rw [two_smul]
  exact h P

end PrincipiaTractalis.Ch24DescentSubBookkeeping20261114

/-! ## §Axiom check -/
#print axioms PrincipiaTractalis.Ch24DescentSubBookkeeping20261114.isCoprime_prod_diffSq
#print axioms PrincipiaTractalis.Ch24DescentSubBookkeeping20261114.isCoprime_of_isCoprime_pow_right
#print axioms PrincipiaTractalis.Ch24DescentSubBookkeeping20261114.descent_sub_lowest_terms
#print axioms PrincipiaTractalis.Ch24DescentSubBookkeeping20261114.rank_eq_zero_of_two_torsion
