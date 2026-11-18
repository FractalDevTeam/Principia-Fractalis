import PF.E37a1Selmer_TwoPowTorsionTrivial_2026_11_18

/-!
# E_37a1 Selmer rank-1, brick 6 — multiplication by `2^n` is injective

Generalises brick 3 (injectivity of `2 •`) to every power of `2` for
**E_37a1** : `y² + y = x³ - x`.

```
E37a1_two_pow_smul_injective (n : ℕ) :
    Function.Injective ((2^n : ℕ) • · : E37a1.toAffine.Point → _)
```

on three-axiom bar `[propext, Classical.choice, Quot.sound]`.

## Proof

Direct corollary of brick 4 (`E37a1_two_pow_torsion_trivial`) via
group arithmetic:
```
(2^n) • P = (2^n) • Q
  ⟹ (2^n) • (P - Q) = 0
  ⟹ P - Q = 0
  ⟹ P = Q
```

## Selmer significance

For the 2-adic structure, this says the Frobenius-free part of
`E_37a1(ℚ) ⊗ ℤ_2` is torsion-free as a `ℤ_2`-module — equivalently,
`E_37a1(ℚ)` has no divisible 2-power elements. This is the input
required to pin `|E_37a1(ℚ) / 2^n · E_37a1(ℚ)| = 2^(n·rank)` in a
future Mordell–Weil-aware brick.
-/

namespace PrincipiaTractalis.E37a1Selmer_TwoPowSmulInjective_2026_11_18

open PrincipiaTractalis.DuplicationFormula37a1 (E37a1)
open PrincipiaTractalis.E37a1Selmer_TwoPowTorsionTrivial_2026_11_18
  (E37a1_two_pow_torsion_trivial)

/-- **Brick 6.** For every `n : ℕ`, multiplication-by-`2^n` on
    `E_37a1(ℚ)` is injective. -/
theorem E37a1_two_pow_smul_injective (n : ℕ) :
    Function.Injective (((2 ^ n : ℕ) • ·) : E37a1.toAffine.Point → E37a1.toAffine.Point) := by
  intro P Q hPQ
  have hPQ' : (2 ^ n : ℕ) • P = (2 ^ n : ℕ) • Q := hPQ
  have h_diff : (2 ^ n : ℕ) • (P - Q) = 0 := by
    have hexpand :
        (2 ^ n : ℕ) • (P - Q) = (2 ^ n : ℕ) • P - (2 ^ n : ℕ) • Q := by
      induction (2 ^ n : ℕ) with
      | zero => simp
      | succ k ih =>
          rw [succ_nsmul, succ_nsmul, succ_nsmul, ih]; abel
    rw [hexpand, hPQ', sub_self]
  have : P - Q = 0 := E37a1_two_pow_torsion_trivial n _ h_diff
  exact sub_eq_zero.mp this

#print axioms E37a1_two_pow_smul_injective

end PrincipiaTractalis.E37a1Selmer_TwoPowSmulInjective_2026_11_18
