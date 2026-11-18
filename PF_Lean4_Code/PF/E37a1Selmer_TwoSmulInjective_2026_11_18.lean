import PF.E37a1Selmer_TrivialTwoTorsion_2026_11_18

/-!
# E_37a1 Selmer rank-1, brick 3 — multiplication-by-2 is injective

**Headline.** For E_37a1 : `y² + y = x³ - x`,

```
E37a1_two_smul_injective :
    ∀ P Q : E37a1.toAffine.Point, 2 • P = 2 • Q → P = Q
```

on three-axiom bar `[propext, Classical.choice, Quot.sound]`.

## The chain

Brick 2 (`PF.E37a1Selmer_TrivialTwoTorsion_2026_11_18`) proved
`∀ R, 2 • R = 0 → R = 0`. Injectivity of `2 •` on the full group is the
immediate corollary via group arithmetic:

```
2 • P = 2 • Q  ⟹  2 • (P - Q) = 0  ⟹  P - Q = 0  ⟹  P = Q
```

In the Selmer attack this packages the "trivial 2-torsion" fact in the
form actually needed for the descent exact sequence
`0 → E(ℚ)/2E(ℚ) → Sel_2(E/ℚ) → Ш(E/ℚ)[2] → 0`:
the left term `E(ℚ)/2E(ℚ)` has order equal to the index of the image
of `2 •`, which this result pins at `2^rank` (brick 3+ assumes
finite generation).
-/

namespace PrincipiaTractalis.E37a1Selmer_TwoSmulInjective_2026_11_18

open PrincipiaTractalis.DuplicationFormula37a1 (E37a1)
open PrincipiaTractalis.E37a1Selmer_TrivialTwoTorsion_2026_11_18
  (E37a1_two_torsion_trivial)

/-- **Brick 3 of the E_37a1 Selmer rank-1 attack.**
    Multiplication-by-2 on `E_37a1(ℚ)` is injective. Direct corollary
    of brick 2 (trivial rational 2-torsion) via group arithmetic. -/
theorem E37a1_two_smul_injective :
    ∀ P Q : E37a1.toAffine.Point, (2 : ℕ) • P = (2 : ℕ) • Q → P = Q := by
  intro P Q hPQ
  have h1 : (2 : ℕ) • (P - Q) = 0 := by
    have hexpand : (2 : ℕ) • (P - Q) = (2 : ℕ) • P - (2 : ℕ) • Q := by
      rw [two_nsmul, two_nsmul, two_nsmul]; abel
    rw [hexpand, hPQ, sub_self]
  have h2 : P - Q = 0 := E37a1_two_torsion_trivial _ h1
  exact sub_eq_zero.mp h2

#print axioms E37a1_two_smul_injective

end PrincipiaTractalis.E37a1Selmer_TwoSmulInjective_2026_11_18
