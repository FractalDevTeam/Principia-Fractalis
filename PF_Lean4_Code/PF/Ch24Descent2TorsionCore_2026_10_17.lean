/-
# PF.Ch24Descent2TorsionCore_2026_10_17

**The descent core for `y² = x³ + x` — the first RANK UPPER BOUND direction
in this repository.**

Every rank theorem in the tree is a lower bound (`n ≤ Module.rank`), obtained
by exhibiting points and proving them of infinite order. This file supplies the
opposite direction's engine: a 2-descent step that *forbids* points.

## The curve and the strategy

`E : y² = x³ + x` (conductor 64, rational 2-torsion `(0,0)`, rank 0).

A rational point writes as `x = m/e²`, `y = n/e³` with `gcd(m,e) = 1`, `e ≠ 0`.
Substituting and clearing denominators gives exactly

    `n² = m · (m² + e⁴)`.

The two factors are coprime (`m² + e⁴ ≡ e⁴ mod m`), and their product is a
square, so each is a square up to units. Positivity pins the signs, giving
`m = d²` and `m² + e⁴ = t²`, whence

    `t² = d⁴ + e⁴`,

contradicting Fermat's `a⁴ + b⁴ ≠ c²` unless `m = 0`.

## What is proved here

`descent_core` — the displayed implication, over `ℤ`, with no denominators:

    `e ≠ 0 → IsCoprime m e → n² = m(m² + e⁴) → m = 0`.

This is the whole arithmetic content of the descent. The hard infinite descent
is **not** re-proved: it is `Mathlib.NumberTheory.FLT.Four.not_fermat_42`.

## What is NOT proved here (deliberately, and named)

1. **The denominator normalisation** — that a rational point on `E` has the form
   `x = m/e²`, `y = n/e³` with `gcd(m,e) = 1`. Standard, fiddly, and separable.
2. **`Module.rank ℤ E(ℚ) = 0`** — needs 1 plus the step from finiteness of
   `E(ℚ)` to vanishing rank.
Neither is hard mathematics; both are bookkeeping on top of this file.

## The `e ≠ 0` hypothesis is necessary, not decorative

At `e = 0`, `IsCoprime m 0` forces `IsUnit m`, and `m = 1`, `n = 1` satisfies
`n² = m(m² + 0)`. So the conclusion genuinely fails without it
(`descent_core_needs_e_ne_zero` records this).

Three-axiom bar: `[propext, Classical.choice, Quot.sound]`. No `sorry`,
no `axiom`, no `native_decide`.

Author: Pablo Cohen + Claude Opus 5. 2026-10-17.
-/
import Mathlib.NumberTheory.FLT.Four
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace PrincipiaTractalis.Ch24Descent20261017

/-! ## §1 — coprimality of the two descent factors -/

/-- `m` is coprime to `m² + e⁴` whenever it is coprime to `e`. -/
theorem isCoprime_descent_factors {m e : ℤ} (hco : IsCoprime m e) :
    IsCoprime m (m ^ 2 + e ^ 4) := by
  have h4 : IsCoprime m (e ^ 4) := hco.pow_right
  have := h4.add_mul_left_right m
  -- `IsCoprime m (e ^ 4 + m * m)`
  have hEq : e ^ 4 + m * m = m ^ 2 + e ^ 4 := by ring
  rwa [hEq] at this

/-! ## §2 — the second factor is positive -/

theorem descent_second_factor_pos {m e : ℤ} (he : e ≠ 0) : 0 < m ^ 2 + e ^ 4 := by
  have h1 : 0 < e ^ 4 := by positivity
  have h2 : 0 ≤ m ^ 2 := sq_nonneg m
  linarith

/-! ## §3 — the descent core -/

/-- **The descent core for `y² = x³ + x`.** With `e ≠ 0` and `m` coprime to `e`,
the equation `n² = m(m² + e⁴)` forces `m = 0`.

The hard step is Fermat's `a⁴ + b⁴ ≠ c²`, imported from mathlib. -/
theorem descent_core {m e n : ℤ} (he : e ≠ 0) (hco : IsCoprime m e)
    (h : n ^ 2 = m * (m ^ 2 + e ^ 4)) : m = 0 := by
  by_contra hm
  -- the second factor is positive
  have hpos : 0 < m ^ 2 + e ^ 4 := descent_second_factor_pos he
  -- hence `m > 0`, since `m * (positive) = n² ≥ 0` and `m ≠ 0`
  have hmpos : 0 < m := by
    rcases lt_trichotomy m 0 with hlt | heq | hgt
    · exfalso
      have hneg : m * (m ^ 2 + e ^ 4) < 0 := mul_neg_of_neg_of_pos hlt hpos
      have : (0 : ℤ) ≤ n ^ 2 := sq_nonneg n
      linarith [h ▸ this]
    · exact absurd heq hm
    · exact hgt
  -- the two factors are coprime and multiply to a square
  have hcf : IsCoprime m (m ^ 2 + e ^ 4) := isCoprime_descent_factors hco
  have hmul : m * (m ^ 2 + e ^ 4) = n ^ 2 := h.symm
  -- `m` is a square up to a unit
  obtain ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow' hcf hmul
  -- `m² + e⁴` is a square up to a unit
  obtain ⟨t, ht⟩ :=
    exists_associated_pow_of_mul_eq_pow' hcf.symm (by linarith [hmul] : (m ^ 2 + e ^ 4) * m = n ^ 2)
  -- pin the signs using positivity
  have hdm : m = d ^ 2 := by
    rcases Int.associated_iff.mp hd with hcase | hcase
    · exact hcase.symm
    · exfalso
      have : d ^ 2 ≤ 0 := by omega
      have : (0 : ℤ) ≤ d ^ 2 := sq_nonneg d
      omega
  have htm : m ^ 2 + e ^ 4 = t ^ 2 := by
    rcases Int.associated_iff.mp ht with hcase | hcase
    · exact hcase.symm
    · exfalso
      have h1 : (0 : ℤ) ≤ t ^ 2 := sq_nonneg t
      omega
  -- now Fermat
  have hd0 : d ≠ 0 := by
    intro hdz
    rw [hdz] at hdm
    simp at hdm
    exact hm hdm
  have hfermat : d ^ 4 + e ^ 4 = t ^ 2 := by
    have : m ^ 2 = d ^ 4 := by rw [hdm]; ring
    linarith [htm, this]
  exact not_fermat_42 hd0 he hfermat

/-! ## §4 — the `e ≠ 0` hypothesis is necessary -/

/-- Without `e ≠ 0` the conclusion fails: `m = 1, e = 0, n = 1` is a
counterexample. Recorded so the hypothesis is not mistaken for decoration. -/
theorem descent_core_needs_e_ne_zero :
    IsCoprime (1 : ℤ) 0 ∧ (1 : ℤ) ^ 2 = 1 * (1 ^ 2 + 0 ^ 4) ∧ (1 : ℤ) ≠ 0 := by
  refine ⟨isCoprime_one_left, by norm_num, one_ne_zero⟩

end PrincipiaTractalis.Ch24Descent20261017

/-! ## §Axiom check -/
#print axioms PrincipiaTractalis.Ch24Descent20261017.isCoprime_descent_factors
#print axioms PrincipiaTractalis.Ch24Descent20261017.descent_second_factor_pos
#print axioms PrincipiaTractalis.Ch24Descent20261017.descent_core
#print axioms PrincipiaTractalis.Ch24Descent20261017.descent_core_needs_e_ne_zero
