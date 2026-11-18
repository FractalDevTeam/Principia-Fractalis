import PF.E43a1Selmer_TwoPowTorsionAndInjective_2026_11_18
import PF.WeierstrassSelmer_TwoSmulInjectiveOfTrivialTorsion_2026_11_18
import PF.WeierstrassSelmer_FactorStripOfTrivialTorsion_2026_11_18

/-!
# E_43a1 Selmer rank-1, bricks 14-16 via generic lemmas

Specialises the generic Weierstrass Selmer lemmas (commits `425c0010`,
`90c32258`) to **E_43a1 : y² + y = x³ + x²**, yielding three previously
missing bricks as one-liners:

```
E43a1_two_pow_smul_injective (brick 14 = E_43a1 brick 6) :
    ∀ (n : ℕ) (P Q : E43a1.toAffine.Point),
      (2^n : ℕ) • P = (2^n : ℕ) • Q → P = Q

E43a1_two_mul_torsion_iff (brick 15 = E_43a1 brick 7) :
    ∀ (k : ℕ) (P : E43a1.toAffine.Point),
      (2 * k : ℕ) • P = 0 ↔ (k : ℕ) • P = 0

E43a1_two_pow_mul_torsion_iff (brick 16 = E_43a1 brick 8) :
    ∀ (n k : ℕ) (P : E43a1.toAffine.Point),
      (2^n * k : ℕ) • P = 0 ↔ (k : ℕ) • P = 0
```

All three on three-axiom bar `[propext, Classical.choice, Quot.sound]`,
each a one-line application of the generic lemma.

## Demonstration

The curve-specific arithmetic (E_43a1 brick 9's no-rational-root of
`4x³ + 4x² + 1`, commit `dc565ff3`) was the real work. Everything
group-theoretic — `2•` injective, factor-strip, 2^n variants —
now lands for free from the generic lemmas.

The E_43a1 Selmer chain now mirrors E_37a1's chain state exactly at
the 2-adic torsion level (bricks 1-8 of each curve's structure).
Future rank-1 curves added to the roster need only the curve-specific
no-rational-root brick; the group-theoretic chain is reusable.
-/

namespace PrincipiaTractalis.E43a1Selmer_GenericConsequences_2026_11_18

open PrincipiaTractalis.E43a1RankOne (E43a1)
open PrincipiaTractalis.E43a1Selmer_TwoPowTorsionAndInjective_2026_11_18
  (E43a1_two_pow_torsion_trivial)
open PrincipiaTractalis.WeierstrassSelmer_TwoSmulInjectiveOfTrivialTorsion_2026_11_18
  (two_pow_smul_injective_of_two_pow_torsion_trivial)
open PrincipiaTractalis.WeierstrassSelmer_FactorStripOfTrivialTorsion_2026_11_18
  (two_mul_torsion_iff_of_two_torsion_trivial
   two_pow_mul_torsion_iff_of_two_pow_torsion_trivial)

/-- **Brick 14 (E_43a1 brick 6).** Multiplication-by-`2^n` on
    `E_43a1(ℚ)` is injective for every `n`. -/
theorem E43a1_two_pow_smul_injective (n : ℕ)
    (P Q : E43a1.toAffine.Point)
    (hPQ : (2 ^ n : ℕ) • P = (2 ^ n : ℕ) • Q) :
    P = Q :=
  two_pow_smul_injective_of_two_pow_torsion_trivial
    E43a1_two_pow_torsion_trivial n P Q hPQ

/-- **Brick 15 (E_43a1 brick 7).** Stripping a factor of 2 from the
    torsion exponent is a no-op on E_43a1. -/
theorem E43a1_two_mul_torsion_iff (k : ℕ) (P : E43a1.toAffine.Point) :
    (2 * k : ℕ) • P = 0 ↔ (k : ℕ) • P = 0 :=
  two_mul_torsion_iff_of_two_torsion_trivial
    (E43a1_two_pow_torsion_trivial 1) k P

/-- **Brick 16 (E_43a1 brick 8).** Stripping any 2-power factor from
    the torsion exponent is a no-op on E_43a1. -/
theorem E43a1_two_pow_mul_torsion_iff (n k : ℕ) (P : E43a1.toAffine.Point) :
    (2 ^ n * k : ℕ) • P = 0 ↔ (k : ℕ) • P = 0 :=
  two_pow_mul_torsion_iff_of_two_pow_torsion_trivial
    E43a1_two_pow_torsion_trivial n k P

#print axioms E43a1_two_pow_smul_injective
#print axioms E43a1_two_mul_torsion_iff
#print axioms E43a1_two_pow_mul_torsion_iff

end PrincipiaTractalis.E43a1Selmer_GenericConsequences_2026_11_18
