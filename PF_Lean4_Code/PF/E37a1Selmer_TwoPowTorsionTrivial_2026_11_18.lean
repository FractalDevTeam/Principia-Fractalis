import PF.E37a1Selmer_TrivialTwoTorsion_2026_11_18

/-!
# E_37a1 Selmer rank-1, brick 4 — trivial `2^n`-torsion for all `n`

Generalises brick 2 (`E37a1_two_torsion_trivial`) to every power of 2:

```
E37a1_two_pow_torsion_trivial :
    ∀ (n : ℕ) (P : E37a1.toAffine.Point), (2^n : ℕ) • P = 0 → P = 0
```

on three-axiom bar `[propext, Classical.choice, Quot.sound]`.

Induction on `n`. The base `n = 0` is `1 • P = 0 → P = 0` (trivial);
the step uses brick 2 applied to `2^n • P` (killed by `2 •` under
hypothesis), yielding `2^n • P = 0`, then the IH.

## Selmer significance

For the 2-descent on `E_37a1`, this says the pro-2 Tate module
`T_2(E_37a1 / ℚ) = lim E_37a1(ℚ)[2^n]` is trivial. Combined with the
Mordell–Weil theorem (when available in mathlib), this would pin the
2-adic structure of `E_37a1(ℚ)` exactly, yielding
    `E_37a1(ℚ) ⊗ ℤ_2 ≅ ℤ_2^rank`.

As an immediate corollary we also ship:
  `E37a1_four_torsion_trivial` : trivial rational 4-torsion.
  `E37a1_eight_torsion_trivial` : trivial rational 8-torsion.
-/

namespace PrincipiaTractalis.E37a1Selmer_TwoPowTorsionTrivial_2026_11_18

open PrincipiaTractalis.DuplicationFormula37a1 (E37a1)
open PrincipiaTractalis.E37a1Selmer_TrivialTwoTorsion_2026_11_18
  (E37a1_two_torsion_trivial)

/-- **Brick 4.** Every `2^n`-torsion point of E_37a1 is zero. -/
theorem E37a1_two_pow_torsion_trivial :
    ∀ (n : ℕ) (P : E37a1.toAffine.Point), (2^n : ℕ) • P = 0 → P = 0 := by
  intro n
  induction n with
  | zero =>
      intro P hP
      simpa using hP
  | succ n ih =>
      intro P hP
      -- `(2^(n+1)) • P = 2 • ((2^n) • P)`
      have hre : (2 ^ (n + 1) : ℕ) • P = 2 • ((2 ^ n : ℕ) • P) := by
        rw [show (2 ^ (n + 1) : ℕ) = 2 * 2 ^ n from by ring, mul_nsmul']
      rw [hre] at hP
      -- hP : 2 • (2^n • P) = 0
      -- Apply brick 2: 2^n • P = 0.
      have h2n : (2 ^ n : ℕ) • P = 0 := E37a1_two_torsion_trivial _ hP
      -- Apply induction hypothesis.
      exact ih P h2n

/-- Immediate corollary: trivial rational 4-torsion. -/
theorem E37a1_four_torsion_trivial :
    ∀ P : E37a1.toAffine.Point, (4 : ℕ) • P = 0 → P = 0 := by
  intro P hP
  have h : (2 ^ 2 : ℕ) • P = 0 := by
    have : (2 ^ 2 : ℕ) = 4 := by norm_num
    rw [this]; exact hP
  exact E37a1_two_pow_torsion_trivial 2 P h

/-- Immediate corollary: trivial rational 8-torsion. -/
theorem E37a1_eight_torsion_trivial :
    ∀ P : E37a1.toAffine.Point, (8 : ℕ) • P = 0 → P = 0 := by
  intro P hP
  have h : (2 ^ 3 : ℕ) • P = 0 := by
    have : (2 ^ 3 : ℕ) = 8 := by norm_num
    rw [this]; exact hP
  exact E37a1_two_pow_torsion_trivial 3 P h

#print axioms E37a1_two_pow_torsion_trivial
#print axioms E37a1_four_torsion_trivial
#print axioms E37a1_eight_torsion_trivial

end PrincipiaTractalis.E37a1Selmer_TwoPowTorsionTrivial_2026_11_18
