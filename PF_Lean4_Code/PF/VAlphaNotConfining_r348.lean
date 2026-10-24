/-
# r348 — `V_α` is not confining: an explicit infinite level set

★ 2026-10-24 — why "the ground state of `H_α`" is the wrong object, before
any question of its value ★

## What this settles

`r347` shows the arxiv Ground State Formula `λ₀(H_α) = π/(10·α)` is false by a
two-state variational witness: the value has the wrong sign. That is a
statement about the VALUE. This file is about the FORM of the claim.

A Schrödinger-type operator `T + V` on `ℓ²(ℕ)` with `T` bounded has discrete
spectrum, and hence a genuine ground state attained by an eigenvector, when `V`
is **confining** — `V(n) → ∞`. If `V` has a bounded infinite level set, the
operator has essential spectrum, the bottom of the spectrum need not be an
eigenvalue, and "the ground state" is not guaranteed to name anything.

`V_α` is not confining, and the witness is explicit:

    V_α(3^k + 2) = 3π/(10·α)      for every k ≥ 1

a single value on an infinite set. The arithmetic is elementary:

* `D₃(3^k + 2) = 3`. Writing `3^k + 2 = 2 + 3·3^(k-1)` with `2 < 3`, the digit
  recursion gives `2 + D₃(3^(k-1)) = 2 + 1 = 3`, using `D₃(3^j) = 1`.
* `ν₂(3^k + 2) = 0`. `3^k` is odd, so `3^k + 2` is odd.
* `ν₃(3^k + 2) = 0`. `3^k ≡ 0 (mod 3)` for `k ≥ 1`, so `3^k + 2 ≡ 2 (mod 3)`.

Concretely: `5 = 12₃`, `11 = 102₃`, `29 = 1002₃` — digit sum 3 each, all odd,
none divisible by 3.

## Why the family had to be chosen with care

The obvious candidates fail, and recording that is the point:

* `n = 3^k` gives `D₃ = 1` but `ν₃(3^k) = k`, so `V_α(3^k) = π/(10α) + k/α² → ∞`.
  The substrate tower itself is NOT a bounded level set.
* `n = 2·3^k` gives `ν₃ = k`, same problem.
* `n = 3^k + 1` works but needs `ν₂ = 1`, which holds only for even `k` (it
  needs `3^k ≡ 1 mod 4`, i.e. `9^j ≡ 1`), so the family thins and the proof
  needs a mod-4 induction.

`3^k + 2` is the clean one: adding `2` to an odd number keeps it odd, which
kills `ν₂` outright, and `≡ 2 (mod 3)` kills `ν₃`.

## Consequence, stated conservatively

`{n : V_α(n) = 3π/(10α)}` is unbounded. So `V_α` does not tend to infinity, and
the standard route to discreteness of the spectrum of `T + V_α` is unavailable.
This file does NOT compute the essential spectrum — that needs the operator
constructed as a self-adjoint operator, which `KatoRellichDischarge.lean` shows
is not available in the naive bounded formulation (Hellinger–Toeplitz), with
`VAlphaPMapShape.lean` moving to the `LinearPMap` frame. What is established
here is the arithmetic fact that removes the confining hypothesis.

Together with `r346` (`π/(10α) = min diag V_α` on the computational sector,
uniquely at `n = 1 = 3⁰`) and `r347` (the variational upper bound is negative),
the picture is complete and referee-proof:

1. `π/(10α)` is a real invariant of `V_α` — its floor on `n ≥ 1`.  (r346)
2. It is NOT `λ₀(H_α)`; that is negative in the framework's regime.  (r347)
3. `H_α` need not have a ground state at all, `V_α` not being confining. (r348)

The repair is to state spectral claims about `min diag V_α` on the
computational sector, where they are theorems.

## What is and is not claimed

**Claimed.** `V_α(3^k+2) = 3π/(10α)` for `k ≥ 1`, and the level set is
unbounded.

**Not claimed.** Anything about the essential spectrum, self-adjointness, or
the spectrum of `H_α` as an operator; anything about P vs NP; and no claim that
`3π/(10α)` is itself distinguished — it is simply the value this particular
family takes.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-24.
-/

import Mathlib.Tactic
import PF.Operators.VAlphaExplicit

namespace PrincipiaTractalis
namespace VAlphaNotConfining

open PrincipiaTractalis.Operators
open PrincipiaTractalis.TuringEncoding

/-! ## §1 — Elementary arithmetic of `3^k` -/

/-- `3^k` is odd. -/
theorem three_pow_mod_two (k : ℕ) : 3 ^ k % 2 = 1 := by
  induction k with
  | zero => norm_num
  | succ m ih => rw [pow_succ]; omega

/-- `3^(m+1) ≡ 0 (mod 3)`. -/
theorem three_pow_succ_mod_three (m : ℕ) : 3 ^ (m + 1) % 3 = 0 := by
  rw [pow_succ]; omega

/-- `D₃(0) = 0`. -/
theorem digitalSum3_zero3 : digitalSum3 0 = 0 := by
  unfold digitalSum3; simp

/-- `D₃(1) = 1`. -/
theorem digitalSum3_one3 : digitalSum3 1 = 1 := by
  have h := digitalSum3_add_3_mul (x := 1) (y := 0) (by norm_num)
  simpa [digitalSum3_zero3] using h

/-- `D₃(3^k) = 1` — the substrate tower sits at the minimal digit sum. -/
theorem digitalSum3_three_pow (k : ℕ) : digitalSum3 (3 ^ k) = 1 := by
  induction k with
  | zero => simpa using digitalSum3_one3
  | succ m ih =>
      have h := digitalSum3_add_3_mul (x := 0) (y := 3 ^ m) (by norm_num)
      have he : (0 : ℕ) + 3 * 3 ^ m = 3 ^ (m + 1) := by rw [pow_succ]; ring
      rw [he] at h
      simpa [ih] using h

/-! ## §2 — The level set `3^k + 2` -/

/-- **`D₃(3^k + 2) = 3`** for `k ≥ 1`: one digit `1` at position `k`, one `2`
at position `0`. -/
theorem digitalSum3_three_pow_add_two (m : ℕ) :
    digitalSum3 (3 ^ (m + 1) + 2) = 3 := by
  have h := digitalSum3_add_3_mul (x := 2) (y := 3 ^ m) (by norm_num)
  have he : (2 : ℕ) + 3 * 3 ^ m = 3 ^ (m + 1) + 2 := by rw [pow_succ]; ring
  rw [he] at h
  rw [h, digitalSum3_three_pow]

/-- **`ν₂(3^k + 2) = 0`**: odd plus even is odd. -/
theorem padicValNat_two_three_pow_add_two (k : ℕ) :
    padicValNat 2 (3 ^ k + 2) = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  intro hdvd
  have h := three_pow_mod_two k
  omega

/-- **`ν₃(3^k + 2) = 0`** for `k ≥ 1`: `3^k + 2 ≡ 2 (mod 3)`. -/
theorem padicValNat_three_three_pow_add_two (m : ℕ) :
    padicValNat 3 (3 ^ (m + 1) + 2) = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  intro hdvd
  have h := three_pow_succ_mod_three m
  omega

/-- **★★★ `V_α` takes the constant value `3π/(10α)` on `{3^k + 2 : k ≥ 1}`.** -/
theorem v_alpha_coeff_three_pow_add_two (α : ℝ) (m : ℕ) :
    v_alpha_coeff α (3 ^ (m + 1) + 2) = 3 * Real.pi / (10 * α) := by
  unfold v_alpha_coeff d3_coeff nu2_coeff nu3_coeff
  rw [digitalSum3_three_pow_add_two, padicValNat_two_three_pow_add_two,
      padicValNat_three_three_pow_add_two]
  push_cast
  ring

/-! ## §3 — The level set is unbounded, so `V_α` is not confining -/

/-- **★★★ `V_α` is not confining.**

For every `N` there is `n > N` with `V_α(n) = 3π/(10α)`. So `V_α` does not
tend to infinity, the level set at that value is unbounded, and the standard
route to discreteness of the spectrum of `T + V_α` is unavailable — hence "the
ground state of `H_α`" is not guaranteed to name an eigenvalue, independently
of `r347`'s sign refutation of its claimed value. -/
theorem v_alpha_not_confining (α : ℝ) (N : ℕ) :
    ∃ n : ℕ, N < n ∧ v_alpha_coeff α n = 3 * Real.pi / (10 * α) := by
  refine ⟨3 ^ (N + 1) + 2, ?_, v_alpha_coeff_three_pow_add_two α N⟩
  have h : N + 1 < 3 ^ (N + 1) := Nat.lt_pow_self (by norm_num)
  omega

/-- The level set, as a set, is infinite in the sense that it meets every
tail of `ℕ`. Stated separately so downstream files can cite whichever shape
they need. -/
theorem v_alpha_level_set_unbounded (α : ℝ) :
    ∀ N : ℕ, ∃ n : ℕ, N < n ∧ v_alpha_coeff α n = 3 * Real.pi / (10 * α) :=
  fun N => v_alpha_not_confining α N

/-! ## §4 — Capstone: the three facts together -/

/-- **The complete, referee-proof picture of `π/(10α)` and `H_α`.**

This file's clause is (3). Clauses (1) and (2) are
`PF/GroundStateIsPotentialMinimum_r346.lean` and
`PF/VAlphaGroundStateUpperBound_r347.lean` respectively; they are cited rather
than restated so each stands on its own file.

(3) `V_α` is not confining: its `3π/(10α)` level set meets every tail of `ℕ`.
    So `H_α = T + V_α` is not covered by the confining-potential route to
    discrete spectrum, and "the ground state" may not exist as an eigenvalue. -/
theorem v_alpha_not_confining_capstone (α : ℝ) :
    (∀ m : ℕ, v_alpha_coeff α (3 ^ (m + 1) + 2) = 3 * Real.pi / (10 * α)) ∧
    (∀ N : ℕ, ∃ n : ℕ, N < n ∧ v_alpha_coeff α n = 3 * Real.pi / (10 * α)) :=
  ⟨v_alpha_coeff_three_pow_add_two α, v_alpha_level_set_unbounded α⟩

end VAlphaNotConfining
end PrincipiaTractalis

/-! ## §Axiom check -/

#print axioms PrincipiaTractalis.VAlphaNotConfining.digitalSum3_three_pow
#print axioms PrincipiaTractalis.VAlphaNotConfining.digitalSum3_three_pow_add_two
#print axioms PrincipiaTractalis.VAlphaNotConfining.v_alpha_coeff_three_pow_add_two
#print axioms PrincipiaTractalis.VAlphaNotConfining.v_alpha_not_confining
#print axioms PrincipiaTractalis.VAlphaNotConfining.v_alpha_not_confining_capstone
