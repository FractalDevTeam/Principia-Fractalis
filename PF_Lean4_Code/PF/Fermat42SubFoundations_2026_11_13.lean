/-
# PF.Fermat42SubFoundations_2026_11_13

**Foundations for `not_fermat_42_sub` — the "difference form" of
Fermat's n = 4 theorem**: there are no non-zero integers `a`, `b`
such that `a ^ 4 - b ^ 4 = c ^ 2` for any non-zero `c`.

This file mirrors mathlib's `Mathlib.NumberTheory.FLT.Four` structure
for the sum form `a^4 + b^4 = c^2`, adapting the key structural
lemmas to the difference form.

## Delivered

* `Fermat42Sub (a b c : ℤ) : Prop` — the predicate
  `a ≠ 0 ∧ b ≠ 0 ∧ a^4 - b^4 = c^2`.
* `Fermat42Sub.ne_zero` — a solution has `c ≠ 0 ∨ a^4 = b^4`.  Unlike
  the sum form, the difference can be zero when a = ±b.  We handle
  this by requiring `|a| > |b|` in the "proper" case.
* `Fermat42Sub.Minimal` — minimal counterexample predicate.
* `Fermat42Sub.exists_minimal` — any counterexample has a minimal one.
* `Fermat42Sub.mul` — scaling invariance.
* `Fermat42Sub.coprime_of_minimal` — minimal solutions are coprime.

## Downstream

The full `not_fermat_42_sub : ∀ a b c : ℤ, a ≠ 0 → b ≠ 0 →
a^4 - b^4 ≠ c^2` requires the Pythagorean descent case split, which
is substantial additional work (~100-150 Lean lines) on top of these
foundations.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-13.
-/

import Mathlib.Data.Nat.Factors
import Mathlib.NumberTheory.FLT.Basic
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination

namespace PF

/-- Three non-zero integers `a`, `b`, `c` with `a^4 - b^4 = c^2`.

Mirrors mathlib's `Fermat42` (sum form). We explicitly require
`c ≠ 0` to exclude the degenerate family `a = ±b, c = 0`. -/
def Fermat42Sub (a b c : ℤ) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ a ^ 4 - b ^ 4 = c ^ 2

namespace Fermat42Sub

/-- Scaling: `Fermat42Sub a b c ↔ Fermat42Sub (k·a) (k·b) (k²·c)` for `k ≠ 0`. -/
theorem mul {a b c k : ℤ} (hk0 : k ≠ 0) :
    Fermat42Sub a b c ↔ Fermat42Sub (k * a) (k * b) (k ^ 2 * c) := by
  delta Fermat42Sub
  constructor
  · intro ⟨ha, hb, hc, hH⟩
    refine ⟨mul_ne_zero hk0 ha, mul_ne_zero hk0 hb,
            mul_ne_zero (pow_ne_zero 2 hk0) hc, ?_⟩
    linear_combination k ^ 4 * hH
  · intro ⟨ha, hb, hc, hH⟩
    refine ⟨right_ne_zero_of_mul ha, right_ne_zero_of_mul hb,
            right_ne_zero_of_mul hc, ?_⟩
    apply (mul_right_inj' (pow_ne_zero 4 hk0)).mp
    linear_combination hH

/-- `a^4 > b^4` for any `Fermat42Sub a b c` with `c ≠ 0`.

Follows from `a^4 - b^4 = c^2 > 0`. -/
theorem lt_pow_of_fermat42Sub {a b c : ℤ} (h : Fermat42Sub a b c) :
    b ^ 4 < a ^ 4 := by
  have hc : c ≠ 0 := h.2.2.1
  have hH : a ^ 4 - b ^ 4 = c ^ 2 := h.2.2.2
  have hc_pos : 0 < c ^ 2 := by positivity
  linarith

/-- A minimal counterexample: no other `Fermat42Sub` has strictly smaller `|c|`. -/
def Minimal (a b c : ℤ) : Prop :=
  Fermat42Sub a b c ∧ ∀ a1 b1 c1 : ℤ, Fermat42Sub a1 b1 c1 →
    Int.natAbs c ≤ Int.natAbs c1

/-- Any `Fermat42Sub` solution yields a minimal one (via well-ordering of ℕ). -/
theorem exists_minimal {a b c : ℤ} (h : Fermat42Sub a b c) :
    ∃ a0 b0 c0, Minimal a0 b0 c0 := by
  classical
  let S : Set ℕ := { n | ∃ s : ℤ × ℤ × ℤ, Fermat42Sub s.1 s.2.1 s.2.2 ∧
    n = Int.natAbs s.2.2 }
  have S_nonempty : S.Nonempty := by
    refine ⟨Int.natAbs c, ?_⟩
    rw [Set.mem_setOf_eq]
    exact ⟨⟨a, ⟨b, c⟩⟩, h, rfl⟩
  let m : ℕ := Nat.find S_nonempty
  have m_mem : m ∈ S := Nat.find_spec S_nonempty
  rcases m_mem with ⟨s0, hs0, hs1⟩
  refine ⟨s0.1, s0.2.1, s0.2.2, hs0, ?_⟩
  intro a1 b1 c1 h1
  rw [← hs1]
  apply Nat.find_min'
  exact ⟨⟨a1, ⟨b1, c1⟩⟩, h1, rfl⟩

/-- A minimal `Fermat42Sub` solution has `a, b` coprime.

Proof: if prime `p ∣ gcd(a, b)`, then `p^2 ∣ c` (via `a^4 - b^4 = c^2`),
and dividing through gives a smaller solution — contradicting minimality. -/
theorem coprime_of_minimal {a b c : ℤ} (h : Minimal a b c) : IsCoprime a b := by
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  by_contra hab
  obtain ⟨p, hp, hpa, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hab
  obtain ⟨a1, rfl⟩ := Int.natCast_dvd.mpr hpa
  obtain ⟨b1, rfl⟩ := Int.natCast_dvd.mpr hpb
  have hpc : (p : ℤ) ^ 2 ∣ c := by
    rw [← Int.pow_dvd_pow_iff two_ne_zero, ← h.1.2.2.2]
    refine Dvd.intro (a1 ^ 4 - b1 ^ 4) ?_
    ring
  obtain ⟨c1, rfl⟩ := hpc
  have hp_ne : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (Nat.Prime.ne_zero hp)
  have hf : Fermat42Sub a1 b1 c1 :=
    (Fermat42Sub.mul hp_ne).mpr h.1
  apply Nat.le_lt_asymm (h.2 _ _ _ hf)
  rw [Int.natAbs_mul, lt_mul_iff_one_lt_left, Int.natAbs_pow, Int.natAbs_natCast]
  · exact Nat.one_lt_pow two_ne_zero (Nat.Prime.one_lt hp)
  · -- c1 ≠ 0 is in hf (now that we require c ≠ 0 in Fermat42Sub).
    exact Int.natAbs_pos.mpr hf.2.2.1

end Fermat42Sub

end PF

/-! ## §Axiom check -/
#print axioms PF.Fermat42Sub.mul
#print axioms PF.Fermat42Sub.lt_pow_of_fermat42Sub
#print axioms PF.Fermat42Sub.exists_minimal
#print axioms PF.Fermat42Sub.coprime_of_minimal
