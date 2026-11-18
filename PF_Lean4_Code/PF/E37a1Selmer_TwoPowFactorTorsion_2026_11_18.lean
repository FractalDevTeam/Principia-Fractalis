import PF.E37a1Selmer_TwoFactorTorsion_2026_11_18

/-!
# E_37a1 Selmer rank-1, brick 8 — stripping any 2-power factor from torsion

Generalises brick 7 (stripping a single factor of 2) to every 2-power
for **E_37a1** : `y² + y = x³ - x`:

```
E37a1_two_pow_mul_torsion_iff (n k : ℕ) (P : E37a1.toAffine.Point) :
    (2^n * k : ℕ) • P = 0 ↔ (k : ℕ) • P = 0
```

on three-axiom bar `[propext, Classical.choice, Quot.sound]`.

## Proof

Induction on `n`:
- `n = 0`: `(2^0 * k) • P = (1 * k) • P = k • P` by `one_mul`; `simp` closes.
- `n + 1`: rewrite `2^(n+1) * k = 2 * (2^n * k)`, apply brick 7 to
  collapse the outer factor of 2, then IH.

## Corollaries

As practical specialisations:

```
E37a1_12_torsion_iff_three_torsion :
    (12 : ℕ) • P = 0 ↔ (3 : ℕ) • P = 0

E37a1_10_torsion_iff_five_torsion :
    (10 : ℕ) • P = 0 ↔ (5 : ℕ) • P = 0
```

## Selmer significance

For the Mordell–Weil torsion computation, this pins the exact structure
of odd-cofactor torsion queries on E_37a1(ℚ):

  `N • P = 0`  ⟺  `(odd part of N) • P = 0`.

Combined with Mazur-theorem-classified odd-order possibilities
({1, 3, 5, 7, 9} for E_37a1 given trivial 2-torsion), this is exactly
the infrastructure for the "trivial torsion subgroup" conclusion.
-/

namespace PrincipiaTractalis.E37a1Selmer_TwoPowFactorTorsion_2026_11_18

open PrincipiaTractalis.DuplicationFormula37a1 (E37a1)
open PrincipiaTractalis.E37a1Selmer_TwoFactorTorsion_2026_11_18
  (E37a1_two_mul_torsion_iff)

/-- **Brick 8.** Stripping any 2-power factor from the torsion exponent
    is a no-op on E_37a1. -/
theorem E37a1_two_pow_mul_torsion_iff (n k : ℕ) (P : E37a1.toAffine.Point) :
    (2^n * k : ℕ) • P = 0 ↔ (k : ℕ) • P = 0 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hrewrite : (2^(n + 1) * k : ℕ) = 2 * (2^n * k) := by ring
      rw [hrewrite, E37a1_two_mul_torsion_iff]
      exact ih

/-- 12-torsion ↔ 3-torsion on E_37a1. -/
theorem E37a1_12_torsion_iff_three_torsion (P : E37a1.toAffine.Point) :
    (12 : ℕ) • P = 0 ↔ (3 : ℕ) • P = 0 := by
  have h : (12 : ℕ) = 2^2 * 3 := by norm_num
  rw [h]
  exact E37a1_two_pow_mul_torsion_iff 2 3 P

/-- 10-torsion ↔ 5-torsion on E_37a1. -/
theorem E37a1_10_torsion_iff_five_torsion (P : E37a1.toAffine.Point) :
    (10 : ℕ) • P = 0 ↔ (5 : ℕ) • P = 0 := by
  have h : (10 : ℕ) = 2^1 * 5 := by norm_num
  rw [h]
  exact E37a1_two_pow_mul_torsion_iff 1 5 P

#print axioms E37a1_two_pow_mul_torsion_iff
#print axioms E37a1_12_torsion_iff_three_torsion
#print axioms E37a1_10_torsion_iff_five_torsion

end PrincipiaTractalis.E37a1Selmer_TwoPowFactorTorsion_2026_11_18
