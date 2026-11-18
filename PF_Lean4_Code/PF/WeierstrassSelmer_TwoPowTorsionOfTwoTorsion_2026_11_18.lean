import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Generic Selmer-attack lemma: `2^n`-torsion trivial from `2`-torsion trivial

For any Weierstrass curve `W` over `ℚ` with trivial rational 2-torsion,
every `2^n`-torsion point is zero.

```
two_pow_torsion_trivial_of_two_torsion_trivial :
    (∀ P : W.toAffine.Point, (2 : ℕ) • P = 0 → P = 0) →
    ∀ (n : ℕ) (P : W.toAffine.Point), (2^n : ℕ) • P = 0 → P = 0
```

on three-axiom bar `[propext, Classical.choice, Quot.sound]`.

## Proof

Induction on `n`:
- `n = 0`: `(2^0) • P = 1 • P = P`, so hypothesis gives `P = 0`.
- `n + 1`: rewrite `(2^(n+1)) • P = 2 • ((2^n) • P)` via `mul_nsmul'`;
  apply `h` to `(2^n) • P` under the hypothesis; then IH.

## Reusability

Together with the earlier generic Weierstrass Selmer lemmas

  - `two_smul_injective_of_two_torsion_trivial` (commit 425c0010)
  - `two_mul_torsion_iff_of_two_torsion_trivial` (commit 90c32258)
  - `two_pow_smul_injective_of_two_pow_torsion_trivial` (commit 425c0010)
  - `two_pow_mul_torsion_iff_of_two_pow_torsion_trivial` (commit 90c32258)

this completes the "trivial 2-torsion → full 2-adic torsion content"
generic chain. Any Weierstrass curve `W / ℚ` satisfying the single
hypothesis `∀ P, 2•P = 0 → P = 0` automatically gets:

  - trivial `2^n`-torsion for all `n`,
  - `2•` injective, `2^n•` injective,
  - `(2k)•P = 0 ↔ k•P = 0`, `(2^n·k)•P = 0 ↔ k•P = 0`.

The curve-specific work is confined to: (1) proving rank ≥ 1 and
(2) proving trivial rational 2-torsion. Every 2-adic chain-brick above
those is reusable.
-/

namespace PrincipiaTractalis.WeierstrassSelmer_TwoPowTorsionOfTwoTorsion_2026_11_18

/-- **Generic Selmer brick.** `2^n`-torsion trivial follows from
    `2`-torsion trivial, for any Weierstrass curve. -/
theorem two_pow_torsion_trivial_of_two_torsion_trivial
    {W : WeierstrassCurve ℚ}
    (h : ∀ P : W.toAffine.Point, (2 : ℕ) • P = 0 → P = 0) :
    ∀ (n : ℕ) (P : W.toAffine.Point), (2^n : ℕ) • P = 0 → P = 0 := by
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
      have h2n : (2 ^ n : ℕ) • P = 0 := h _ hP
      exact ih P h2n

#print axioms two_pow_torsion_trivial_of_two_torsion_trivial

end PrincipiaTractalis.WeierstrassSelmer_TwoPowTorsionOfTwoTorsion_2026_11_18
