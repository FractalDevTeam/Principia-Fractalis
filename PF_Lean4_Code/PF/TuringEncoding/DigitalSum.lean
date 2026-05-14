/-
# Digital Sum (Base 3) — Lemmas and Generating Function

The digital sum `D(n) = digitalSum3 n` is defined in `TuringEncoding/Basic.lean`
as the recursive sum of base-3 digits. This file builds:

1. **Bridge to mathlib**: `digitalSum3_eq_digits_sum n : digitalSum3 n = (Nat.digits 3 n).sum`.
2. **Composition with `+ 3 * y`**: `digitalSum3 (x + 3 * y) = x + digitalSum3 y` for `x < 3`.
3. **Multiplicative form of the recursive identity** (the substantive
   building block for the truncated generating function):
   `z ^ (digitalSum3 n) = z ^ (n % 3) * z ^ (digitalSum3 (n / 3))`
   over any commutative semiring `R`.

The book's claimed infinite generating function `Σ N_m^(3) z^m = Π (1+z+z²·3^k)`
is informal: `N_m^(3) = |{n ∈ ℕ : D(n) = m}|` is generally infinite, so the
infinite sum doesn't converge in the usual sense. The finite truncated
identity `Σ_{n < 3^N} z^{D(n)} = (1 + z + z²)^N` is the substantive
combinatorial content; this file provides the building blocks (the
multiplicative recursive identity plus its base case), with the final
Finset reindex left to a follow-up.

Stage L3 — digital-sum and generating-function infrastructure.
-/

import PF.TuringEncoding.Basic
import Mathlib.Data.Nat.Digits.Defs

namespace PrincipiaTractalis.TuringEncoding

/-! ## Bridge to `Nat.digits 3` -/

/-- The recursive `digitalSum3` agrees with the sum of base-3 digits. -/
theorem digitalSum3_eq_digits_sum (n : ℕ) :
    digitalSum3 n = (Nat.digits 3 n).sum := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n = 0
    · subst hn; simp [digitalSum3]
    · -- n > 0, so digits 3 n = (n % 3) :: digits 3 (n / 3)
      have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
      have hdiv_lt : n / 3 < n := Nat.div_lt_self hn_pos (by norm_num)
      have h_digits : Nat.digits 3 n = (n % 3) :: Nat.digits 3 (n / 3) :=
        Nat.digits_def' (by norm_num : 1 < 3) hn_pos
      unfold digitalSum3
      rw [if_neg hn, h_digits, List.sum_cons]
      rw [ih (n / 3) hdiv_lt]

/-! ## Composition lemma: digital sum of `x + 3 * y` -/

/-- For `x < 3` and `0 < x + 3 * y` (i.e. not both zero):
    `digitalSum3 (x + 3 * y) = x + digitalSum3 y`. -/
theorem digitalSum3_lo_plus_3_mul_hi {x y : ℕ} (hx : x < 3)
    (hxy : x ≠ 0 ∨ y ≠ 0) :
    digitalSum3 (x + 3 * y) = x + digitalSum3 y := by
  rw [digitalSum3_eq_digits_sum, digitalSum3_eq_digits_sum]
  rw [Nat.digits_add 3 (by norm_num) x y hx hxy]
  rw [List.sum_cons]

/-- The zero case: `digitalSum3 (0 + 3 * 0) = 0 + digitalSum3 0 = 0`. -/
theorem digitalSum3_zero_plus_3_mul_zero :
    digitalSum3 (0 + 3 * 0) = 0 + digitalSum3 0 := by
  simp [digitalSum3]

/-- General form covering all cases: for `x < 3`,
    `digitalSum3 (x + 3 * y) = x + digitalSum3 y`. -/
theorem digitalSum3_add_3_mul {x y : ℕ} (hx : x < 3) :
    digitalSum3 (x + 3 * y) = x + digitalSum3 y := by
  by_cases h : x = 0 ∧ y = 0
  · obtain ⟨hx0, hy0⟩ := h
    subst hx0; subst hy0
    simp [digitalSum3]
  · push_neg at h
    apply digitalSum3_lo_plus_3_mul_hi hx
    by_cases hx0 : x = 0
    · subst hx0
      exact Or.inr (h rfl)
    · exact Or.inl hx0

/-! ## Multiplicative form of the recursive identity

The substantive building block: `z^(digitalSum3 n)` factors as a product
matching the recursive decomposition `n = (n % 3) + 3 * (n / 3)`. -/

/-- **Multiplicative recursive form of the digital-sum power.** Combined
    with a Finset reindex on `range (3 ^ (N+1))` into `range 3 × range (3^N)`
    (left to a follow-up), this yields the truncated generating function
    identity `Σ_{n < 3^N} z^(digitalSum3 n) = (1 + z + z²)^N`. -/
theorem pow_digitalSum3_eq_low_mul
    {R : Type*} [CommSemiring R] (z : R) (n : ℕ) :
    z ^ (digitalSum3 n) = z ^ (n % 3) * z ^ (digitalSum3 (n / 3)) := by
  have hn_decomp : n = (n % 3) + 3 * (n / 3) := (Nat.mod_add_div n 3).symm
  conv_lhs => rw [hn_decomp]
  rw [digitalSum3_add_3_mul (Nat.mod_lt n (by norm_num : (0 : ℕ) < 3))]
  rw [pow_add]

/-! ## Truncated generating function (finite Finset identity) -/

/-- The `range (3 * M)` sum reindexes via `n ↔ (n / 3, n % 3)`. This is
    the low-digit factorization at the `Finset` level, separating the
    sum into a product of two independent sums (over the high-`M` block
    and over the low 3-residues). -/
theorem sum_range_three_mul_eq
    {R : Type*} [CommSemiring R] (g : ℕ → R) (M : ℕ) :
    ∑ n ∈ Finset.range (3 * M), g n =
      ∑ p ∈ Finset.range M ×ˢ Finset.range 3, g (p.2 + 3 * p.1) := by
  apply Finset.sum_nbij' (fun n => (n / 3, n % 3)) (fun p => p.2 + 3 * p.1)
  · -- forward in: n ∈ range(3M) → (n/3, n%3) ∈ range M × range 3
    intro n hn
    simp only [Finset.mem_range, Finset.mem_product] at hn ⊢
    refine ⟨?_, Nat.mod_lt n (by norm_num : (0 : ℕ) < 3)⟩
    exact Nat.div_lt_iff_lt_mul (by norm_num : (0 : ℕ) < 3) |>.mpr
      (by rw [mul_comm]; exact hn)
  · -- backward in: (d, q) ∈ range M × range 3 → q + 3*d ∈ range(3M)
    intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp ⊢
    obtain ⟨hd, hq⟩ := hp
    omega
  · -- left inverse: (n / 3, n % 3) → n % 3 + 3 * (n / 3) = n
    intro n _
    exact (Nat.mod_add_div n 3).symm |>.symm
  · -- right inverse: (d, q) → ((q + 3*d) / 3, (q + 3*d) % 3) = (d, q)
    intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    obtain ⟨_, hq⟩ := hp
    ext
    · show (p.2 + 3 * p.1) / 3 = p.1
      rw [Nat.add_mul_div_left _ _ (by norm_num : (0 : ℕ) < 3)]
      rw [Nat.div_eq_of_lt hq]
      omega
    · show (p.2 + 3 * p.1) % 3 = p.2
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hq
  · -- pointwise: g n = g (n % 3 + 3 * (n / 3))
    intro n _
    congr 1
    exact (Nat.mod_add_div n 3).symm

/-- **Truncated digital-sum generating function** (the substantive content
    of Ch 21 line 286, in its finite, well-defined form). For any
    commutative semiring `R` and `z : R`:

    `Σ_{n ∈ range (3^N)} z^(digitalSum3 n) = (1 + z + z²)^N`.

    Proof by induction on `N`. The step uses `sum_range_three_mul_eq` to
    factorize the sum over `range (3 * 3^N)` into a product of sums over
    `range (3^N)` and `range 3`, then `pow_digitalSum3_eq_low_mul` to
    split the integrand. -/
theorem digitalSum3_generating_truncated
    {R : Type*} [CommSemiring R] (z : R) :
    ∀ N : ℕ, ∑ n ∈ Finset.range (3 ^ N), z ^ (digitalSum3 n) =
              (1 + z + z ^ 2) ^ N := by
  intro N
  induction N with
  | zero =>
    -- 3^0 = 1; range 1 = {0}; (1+z+z²)^0 = 1
    have h_d0 : digitalSum3 0 = 0 := by unfold digitalSum3; simp
    simp [h_d0]
  | succ N ih =>
    have h_three :
        (∑ q ∈ Finset.range 3, z ^ q) = 1 + z + z ^ 2 := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
          Finset.sum_range_zero]
      ring
    calc ∑ n ∈ Finset.range (3 ^ (N + 1)), z ^ digitalSum3 n
        = ∑ n ∈ Finset.range (3 * 3 ^ N), z ^ digitalSum3 n := by
          rw [show (3 ^ (N + 1) : ℕ) = 3 * 3 ^ N from by ring]
      _ = ∑ p ∈ Finset.range (3 ^ N) ×ˢ Finset.range 3,
            z ^ (digitalSum3 (p.2 + 3 * p.1)) :=
          sum_range_three_mul_eq (fun n => z ^ (digitalSum3 n)) (3 ^ N)
      _ = ∑ p ∈ Finset.range (3 ^ N) ×ˢ Finset.range 3,
            z ^ p.2 * z ^ (digitalSum3 p.1) := by
          apply Finset.sum_congr rfl
          intro p hp
          simp only [Finset.mem_product, Finset.mem_range] at hp
          rw [digitalSum3_add_3_mul hp.2, pow_add]
      _ = (∑ d ∈ Finset.range (3 ^ N), z ^ digitalSum3 d) *
          (∑ q ∈ Finset.range 3, z ^ q) := by
          rw [Finset.sum_product]
          -- Goal: ∑ d, ∑ y, z^y * z^(D d) = (∑ d z^(D d)) * (∑ q z^q)
          rw [show (∑ d ∈ Finset.range (3 ^ N),
                ∑ y ∈ Finset.range 3,
                  z ^ ((d, y) : ℕ × ℕ).2 * z ^ digitalSum3 ((d, y) : ℕ × ℕ).1) =
              ∑ d ∈ Finset.range (3 ^ N),
                z ^ digitalSum3 d * ∑ y ∈ Finset.range 3, z ^ y from ?_]
          · rw [← Finset.sum_mul]
          · apply Finset.sum_congr rfl
            intro d _
            simp only
            rw [← Finset.sum_mul, mul_comm]
      _ = (1 + z + z ^ 2) ^ N * (1 + z + z ^ 2) := by
          rw [ih, h_three]
      _ = (1 + z + z ^ 2) ^ (N + 1) := (pow_succ _ _).symm

end PrincipiaTractalis.TuringEncoding
