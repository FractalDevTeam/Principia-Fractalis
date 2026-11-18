import PF.E37a1Selmer_TrivialTwoTorsion_2026_11_18

/-!
# E_37a1 Selmer rank-1, brick 7 — stripping 2-factors from torsion

For **E_37a1** : `y² + y = x³ - x`, the trivial rational 2-torsion
(brick 2) means that multiplying the torsion exponent by `2` adds no
new torsion points: `(2k) • P = 0 ↔ k • P = 0`.

Two forms shipped:

```
E37a1_two_mul_torsion_iff (k : ℕ) (P : E37a1.toAffine.Point) :
    (2 * k : ℕ) • P = 0 ↔ (k : ℕ) • P = 0

E37a1_six_torsion_iff_three_torsion (P : E37a1.toAffine.Point) :
    (6 : ℕ) • P = 0 ↔ (3 : ℕ) • P = 0
```

Both on three-axiom bar `[propext, Classical.choice, Quot.sound]`.

## Proof

Forward: `(2k) • P = 2 • (k • P) = 0 ⟹ k • P = 0` by brick 2
(trivial 2-torsion applied to `k • P`).

Backward: `k • P = 0 ⟹ (2k) • P = 2 • (k • P) = 2 • 0 = 0`.

## Selmer significance

This means the Mordell–Weil torsion computation on E_37a1(ℚ) reduces
to **odd-order** torsion only — the 2-part is trivially killed by
brick 2 and this reduction lemma. Combined with brick 5 (eventual
trivial 3-torsion), this would eliminate 6-torsion directly.

The general factor-of-2-strip pattern underlies the "pro-2 Tate module
is trivial" statement that brick 4 pins at the `(2^n)`-level; this
brick is its multiplicative analog.
-/

namespace PrincipiaTractalis.E37a1Selmer_TwoFactorTorsion_2026_11_18

open PrincipiaTractalis.DuplicationFormula37a1 (E37a1)
open PrincipiaTractalis.E37a1Selmer_TrivialTwoTorsion_2026_11_18
  (E37a1_two_torsion_trivial)

/-- **Brick 7.** Stripping a factor of `2` from a torsion exponent is
    a no-op on E_37a1. -/
theorem E37a1_two_mul_torsion_iff (k : ℕ) (P : E37a1.toAffine.Point) :
    (2 * k : ℕ) • P = 0 ↔ (k : ℕ) • P = 0 := by
  constructor
  · intro h
    have hrewrite : (2 * k : ℕ) • P = 2 • ((k : ℕ) • P) := by
      rw [mul_nsmul']
    rw [hrewrite] at h
    exact E37a1_two_torsion_trivial _ h
  · intro h
    have hrewrite : (2 * k : ℕ) • P = 2 • ((k : ℕ) • P) := by
      rw [mul_nsmul']
    rw [hrewrite, h, nsmul_zero]

/-- **Immediate corollary.** `6 • P = 0 ↔ 3 • P = 0`. -/
theorem E37a1_six_torsion_iff_three_torsion (P : E37a1.toAffine.Point) :
    (6 : ℕ) • P = 0 ↔ (3 : ℕ) • P = 0 := by
  have h : (6 : ℕ) = 2 * 3 := by norm_num
  rw [h]
  exact E37a1_two_mul_torsion_iff 3 P

#print axioms E37a1_two_mul_torsion_iff
#print axioms E37a1_six_torsion_iff_three_torsion

end PrincipiaTractalis.E37a1Selmer_TwoFactorTorsion_2026_11_18
