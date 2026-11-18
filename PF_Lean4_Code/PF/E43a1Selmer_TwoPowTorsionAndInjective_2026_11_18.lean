import PF.E43a1Selmer_TrivialTwoTorsion_2026_11_18

/-!
# E_43a1 Selmer rank-1, bricks 11 + 12

**Headline.** For E_43a1 : `y² + y = x³ + x²`:

```
E43a1_two_pow_torsion_trivial (brick 11) :
    ∀ (n : ℕ) (P : E43a1.toAffine.Point), (2^n : ℕ) • P = 0 → P = 0

E43a1_two_smul_injective (brick 12) :
    ∀ P Q : E43a1.toAffine.Point, (2 : ℕ) • P = (2 : ℕ) • Q → P = Q
```

Both on three-axiom bar `[propext, Classical.choice, Quot.sound]`.

## Chain

Templated directly from the E_37a1 analogues (bricks 4 and 3):

- Brick 11 = E_37a1 brick 4: induction on `n` using brick 10
  (E_43a1 trivial 2-torsion) as the base step.
- Brick 12 = E_37a1 brick 3: corollary of brick 10 via group arithmetic.

## Selmer significance

For E_43a1, the pro-2 Tate module `T_2(E_43a1 / ℚ) = lim E_43a1(ℚ)[2^n]`
is trivial, and the 2-divisible structure is as expected. Mirrors the
E_37a1 Selmer picture — two rank-1 curves now carry the full 2-adic
torsion content.
-/

namespace PrincipiaTractalis.E43a1Selmer_TwoPowTorsionAndInjective_2026_11_18

open PrincipiaTractalis.E43a1RankOne (E43a1)
open PrincipiaTractalis.E43a1Selmer_TrivialTwoTorsion_2026_11_18
  (E43a1_two_torsion_trivial)

/-- **Brick 11.** Every `2^n`-torsion point of E_43a1 is zero. -/
theorem E43a1_two_pow_torsion_trivial :
    ∀ (n : ℕ) (P : E43a1.toAffine.Point), (2^n : ℕ) • P = 0 → P = 0 := by
  intro n
  induction n with
  | zero =>
      intro P hP
      simpa using hP
  | succ n ih =>
      intro P hP
      have hre : (2 ^ (n + 1) : ℕ) • P = 2 • ((2 ^ n : ℕ) • P) := by
        rw [show (2 ^ (n + 1) : ℕ) = 2 * 2 ^ n from by ring, mul_nsmul']
      rw [hre] at hP
      have h2n : (2 ^ n : ℕ) • P = 0 := E43a1_two_torsion_trivial _ hP
      exact ih P h2n

/-- **Brick 12.** Multiplication-by-2 on E_43a1(ℚ) is injective. -/
theorem E43a1_two_smul_injective :
    ∀ P Q : E43a1.toAffine.Point, (2 : ℕ) • P = (2 : ℕ) • Q → P = Q := by
  intro P Q hPQ
  have h1 : (2 : ℕ) • (P - Q) = 0 := by
    have hexpand : (2 : ℕ) • (P - Q) = (2 : ℕ) • P - (2 : ℕ) • Q := by
      rw [two_nsmul, two_nsmul, two_nsmul]; abel
    rw [hexpand, hPQ, sub_self]
  have h2 : P - Q = 0 := E43a1_two_torsion_trivial _ h1
  exact sub_eq_zero.mp h2

#print axioms E43a1_two_pow_torsion_trivial
#print axioms E43a1_two_smul_injective

end PrincipiaTractalis.E43a1Selmer_TwoPowTorsionAndInjective_2026_11_18
