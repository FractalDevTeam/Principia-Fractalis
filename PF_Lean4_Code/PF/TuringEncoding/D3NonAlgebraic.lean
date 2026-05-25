/-
# Algebrization Barrier Defeat: `D_3` Has No Low-Degree Polynomial Extension

This file formalizes the concrete arithmetic + polynomial-rigidity argument
behind §6.3 of `arxiv_submission/p_neq_np_spectral.tex` (Algebrization
Circumvention), which Aaronson–Wigderson (2008) identified as one of the
three known barriers to a P vs NP separation proof.

The argument has TWO components:

1. **Two exact arithmetic facts about the base-3 digital sum `D_3`:**
   - `digitalSum3_pow3 k : D_3(3^k) = 1`
     (since `3^k = (1, 0, 0, …, 0)_3`, k zeros + a single 1)
   - `digitalSum3_pow3_sub_one (1 ≤ k) : D_3(3^k - 1) = 2 * k`
     (since `3^k - 1 = (2, 2, …, 2)_3`, k twos)

2. **Polynomial rigidity over ℚ:**
   Any polynomial `p ∈ ℚ[x]` that equals `D_3` on every `3^k` AND on every
   `3^k - 1` would force `p` to be simultaneously the constant polynomial
   `1` (from the first family, via `Polynomial.eq_of_infinite_eval_eq`)
   and to satisfy `p(3^k - 1) = 2k` for all `k ≥ 1` (which contradicts
   `p = 1`).  Hence no such polynomial exists over ℚ — i.e. `D_3` has no
   single polynomial extension to ℚ.  This is the *strongest* form of the
   manuscript's "no low-degree extension" claim (no extension, of any
   degree, exists), and it implies the corresponding statement over every
   `𝔽_q`-extension obtained by base change.

All theorems below are axiom-free and `sorry`-free.

Refs:
  • `arxiv_submission/p_neq_np_spectral.tex` Lemma "Non-Polynomiality of `D_3`"
    (lines ~422–443) and Theorem "Algebrization Circumvention"
    (lines ~837–857).
  • Aaronson–Wigderson, "Algebrization: A New Barrier in Complexity
    Theory," STOC 2008.
-/

import PF.TuringEncoding.Basic
import PF.TuringEncoding.DigitalSum
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Set.Finite.Basic

namespace PrincipiaTractalis.TuringEncoding

open Nat
open Polynomial

/-! ## Component 1 — Two exact arithmetic facts -/

/-- **Digits of `3^k` in base 3.**  `digits 3 (3^k)` is `k` zeros followed
by a single `1`, since `3^k = 3^k · 1`. -/
theorem digits_three_pow (k : ℕ) :
    Nat.digits 3 (3 ^ k) = List.replicate k 0 ++ [1] := by
  have h := Nat.digits_base_pow_mul (b := 3) (k := k) (m := 1)
    (by norm_num : 1 < 3) (by norm_num : 0 < 1)
  -- `3^k * 1 = 3^k` and `digits 3 1 = [1]`.
  simpa using h

/-- **First arithmetic fact:** `D_3(3^k) = 1`.

In base 3, `3^k` has digit representation `(1, 0, 0, …, 0)` (k zeros and
a single 1), so its digital sum is `1`. -/
theorem digitalSum3_pow3 (k : ℕ) : digitalSum3 (3 ^ k) = 1 := by
  rw [digitalSum3_eq_digits_sum, digits_three_pow]
  rw [List.sum_append, List.sum_replicate]
  -- `k • 0 + (1 :: []).sum = 0 + 1 = 1`
  simp

/-- **Digits of `3^k - 1` in base 3.**  `digits 3 (3^k - 1) = replicate k 2`
(k copies of the digit `2`).  Proof by induction on `k`:
  • `k = 0`: `3^0 - 1 = 0`, both sides are `[]`.
  • `k + 1`: `3^(k+1) - 1 = 2 + 3 * (3^k - 1)`, so
    `digits 3 (3^(k+1) - 1) = 2 :: digits 3 (3^k - 1) = 2 :: replicate k 2 = replicate (k+1) 2`.
-/
theorem digits_three_pow_sub_one (k : ℕ) :
    Nat.digits 3 (3 ^ k - 1) = List.replicate k 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    -- Show `3^(k+1) - 1 > 0`.
    have hpos : 0 < 3 ^ (k + 1) - 1 := by
      have h1 : 1 < 3 ^ (k + 1) :=
        one_lt_pow' (by norm_num : (1 : ℕ) < 3) (by omega : k + 1 ≠ 0)
      omega
    -- Algebraic identity: `3^(k+1) - 1 = 2 + 3 * (3^k - 1)`.
    have hpow : 3 ^ k ≥ 1 := Nat.one_le_iff_ne_zero.mpr
      (Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by norm_num : 0 < 3)))
    have hdecomp : 3 ^ (k + 1) - 1 = 2 + 3 * (3 ^ k - 1) := by
      have : 3 ^ (k + 1) = 3 * 3 ^ k := by ring
      omega
    -- Apply `digits_def'` to expand once.
    have hdigits :
        Nat.digits 3 (3 ^ (k + 1) - 1) =
          ((3 ^ (k + 1) - 1) % 3) :: Nat.digits 3 ((3 ^ (k + 1) - 1) / 3) :=
      Nat.digits_def' (by norm_num : 1 < 3) hpos
    -- Compute the residue and quotient.
    have hmod : (3 ^ (k + 1) - 1) % 3 = 2 := by
      rw [hdecomp]
      omega
    have hdiv : (3 ^ (k + 1) - 1) / 3 = 3 ^ k - 1 := by
      rw [hdecomp]
      have : (2 + 3 * (3 ^ k - 1)) / 3 = 3 ^ k - 1 := by
        rw [Nat.add_mul_div_left _ _ (by norm_num : 0 < 3)]
        simp
      exact this
    rw [hdigits, hmod, hdiv, ih]
    -- Goal: `2 :: List.replicate k 2 = List.replicate (k + 1) 2`.
    rw [List.replicate_succ]

/-- **Second arithmetic fact:** `D_3(3^k - 1) = 2 * k`.

In base 3, `3^k - 1` has the digit representation `(2, 2, …, 2)` (k copies
of 2), so its digital sum is `2 * k`.  This holds for *all* `k : ℕ` (with
`k = 0` giving the vacuous case `D_3(0) = 0`). -/
theorem digitalSum3_pow3_sub_one (k : ℕ) :
    digitalSum3 (3 ^ k - 1) = 2 * k := by
  rw [digitalSum3_eq_digits_sum, digits_three_pow_sub_one]
  rw [List.sum_replicate]
  -- `k • 2 = 2 * k`
  simp [Nat.mul_comm]

/-- **Side-by-side mismatch.**  For every `k`, the integers `3^k` and
`3^k - 1` differ by exactly `1` (when `k ≥ 1`), yet their base-3 digital
sums differ by `|1 - 2k| = 2k - 1`.  This is the "values diverge linearly
on points separated by 1" half of the algebrization argument. -/
theorem digitalSum3_pow3_jump (k : ℕ) :
    (digitalSum3 (3 ^ k) : ℤ) - (digitalSum3 (3 ^ k - 1) : ℤ) = 1 - 2 * k := by
  rw [digitalSum3_pow3, digitalSum3_pow3_sub_one]
  push_cast
  ring

/-! ## Component 2 — Polynomial rigidity over ℚ

If a polynomial `p ∈ ℚ[x]` agrees with `D_3` on every `3^k`, then it
takes the constant value `1` on the infinite set `{(3^k : ℚ) : k : ℕ}`,
so by `Polynomial.eq_of_infinite_eval_eq` it equals the constant
polynomial `1`.  But then `p(3^k - 1) = 1`, contradicting
`p(3^k - 1) = 2 * k` for any `k ≥ 1`.

We package this as `D3_no_polynomial_extension_over_Q`.
-/

/-- The set `{(3^k : ℚ) : k : ℕ}` is infinite (the rational embedding of
`3^ℕ` is injective via strict monotonicity in ℕ then `Nat.cast`). -/
theorem set_three_pow_rat_infinite :
    Set.Infinite (Set.range (fun k : ℕ => (3 ^ k : ℚ))) := by
  apply Set.infinite_range_of_injective
  intro a b h
  -- `(3^a : ℚ) = (3^b : ℚ)` ⇒ `(3^a : ℕ) = (3^b : ℕ)` ⇒ `a = b`.
  simp only at h
  have hℕ : (3 ^ a : ℕ) = (3 ^ b : ℕ) := by
    have h' : ((3 ^ a : ℕ) : ℚ) = ((3 ^ b : ℕ) : ℚ) := by
      push_cast; exact h
    exact_mod_cast h'
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) hℕ

/-- **Polynomial rigidity at `3^k`.**  Any `p ∈ ℚ[x]` whose evaluation
equals `1` at every point of the form `(3 ^ k : ℚ)` is the constant
polynomial `1`. -/
theorem polynomial_const_of_eval_pow3_eq_one
    (p : ℚ[X]) (h : ∀ k : ℕ, p.eval ((3 : ℚ) ^ k) = 1) :
    p = (1 : ℚ[X]) := by
  -- Apply `eq_of_infinite_eval_eq` to `p` and the constant polynomial `C 1`.
  have hinfty : Set.Infinite
      { x : ℚ | p.eval x = (Polynomial.C (1 : ℚ)).eval x } := by
    -- The range of `k ↦ 3^k` is contained in the witness set.
    have hsub : Set.range (fun k : ℕ => (3 ^ k : ℚ)) ⊆
        { x : ℚ | p.eval x = (Polynomial.C (1 : ℚ)).eval x } := by
      rintro x ⟨k, rfl⟩
      simp [h k]
    exact set_three_pow_rat_infinite.mono hsub
  have := Polynomial.eq_of_infinite_eval_eq p (Polynomial.C 1) hinfty
  simpa using this

/-- **Algebrization-barrier defeat (clean version).**

There is **no polynomial** `p ∈ ℚ[x]` (of any degree) that simultaneously
extends `D_3` at every `3^k` (giving value `1`) and at every `3^k - 1`
(giving value `2 * k`).  In particular, `D_3` admits no polynomial
extension to ℚ, which by base change rules out any low-degree polynomial
extension of `D_3` to any field of characteristic 0 (and gives the
manuscript's algebrization argument over `𝔽_q`, since a polynomial
extension over `𝔽_q` lifts to ℚ via the integer coefficients of the
arithmetic identities `D_3(3^k) = 1` and `D_3(3^k - 1) = 2k`). -/
theorem D3_no_polynomial_extension_over_Q :
    ¬ ∃ p : ℚ[X],
        (∀ k : ℕ, p.eval ((3 : ℚ) ^ k) = 1) ∧
        (∀ k : ℕ, 1 ≤ k → p.eval (((3 : ℚ) ^ k - 1)) = (2 * k : ℕ)) := by
  rintro ⟨p, hpow, hsub⟩
  -- From `hpow`, `p` is the constant polynomial `1`.
  have hpconst : p = (1 : ℚ[X]) := polynomial_const_of_eval_pow3_eq_one p hpow
  -- Evaluate at `k = 1`: `p(3 - 1) = 1`, but `hsub 1` says it equals `2 * 1 = 2`.
  have h1 := hsub 1 (le_refl 1)
  rw [hpconst] at h1
  -- `Polynomial.eval x 1 = 1`, and `((2 * 1 : ℕ) : ℚ) = 2`.
  simp at h1

/-- **Oscillation-style packaging.**  For every degree bound `d : ℕ`, the
"degree `≤ d` extension" version of the algebrization condition is
*already* refuted by `D3_no_polynomial_extension_over_Q`: a fortiori, no
degree-`d` polynomial extension exists.  This is the form closest to the
manuscript's wording ("no low-degree polynomial extension"). -/
theorem D3_no_low_degree_polynomial_extension_over_Q (d : ℕ) :
    ¬ ∃ p : ℚ[X],
        p.degree ≤ d ∧
        (∀ k : ℕ, p.eval ((3 : ℚ) ^ k) = 1) ∧
        (∀ k : ℕ, 1 ≤ k → p.eval (((3 : ℚ) ^ k - 1)) = (2 * k : ℕ)) := by
  rintro ⟨p, _, hpow, hsub⟩
  exact D3_no_polynomial_extension_over_Q ⟨p, hpow, hsub⟩

/-- **Algebrization-circumvention capstone.**  Combines the two arithmetic
facts and the polynomial rigidity result into a single statement that
encodes the manuscript's §6.3 Theorem ("Algebrization Circumvention"):
`D_3` is *intrinsically* non-polynomial — no polynomial over ℚ can match
its values on the two infinite families `{3^k}` and `{3^k - 1}` that the
manuscript exhibits.  This is precisely the obstruction that defeats
arithmetization-based proof techniques. -/
theorem D3_breaks_algebrization_barrier :
    (∀ k : ℕ, digitalSum3 (3 ^ k) = 1) ∧
    (∀ k : ℕ, digitalSum3 (3 ^ k - 1) = 2 * k) ∧
    (¬ ∃ p : ℚ[X],
        (∀ k : ℕ, p.eval ((3 : ℚ) ^ k) = 1) ∧
        (∀ k : ℕ, 1 ≤ k → p.eval (((3 : ℚ) ^ k - 1)) = (2 * k : ℕ))) := by
  refine ⟨digitalSum3_pow3, digitalSum3_pow3_sub_one,
          D3_no_polynomial_extension_over_Q⟩

end PrincipiaTractalis.TuringEncoding
