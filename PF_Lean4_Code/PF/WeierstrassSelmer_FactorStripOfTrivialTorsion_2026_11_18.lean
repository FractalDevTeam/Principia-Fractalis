import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Generic Selmer-attack lemma: stripping 2-factors from torsion exponents

For any Weierstrass curve `W` over `ℚ` with trivial rational 2-torsion,
multiplying the torsion exponent by `2` adds no new torsion points.

```
two_mul_torsion_iff_of_two_torsion_trivial :
    (∀ P : W.toAffine.Point, (2 : ℕ) • P = 0 → P = 0) →
    ∀ (k : ℕ) (P : W.toAffine.Point), (2 * k : ℕ) • P = 0 ↔ (k : ℕ) • P = 0

two_pow_mul_torsion_iff_of_two_pow_torsion_trivial :
    (∀ (n : ℕ) (P : W.toAffine.Point), (2^n : ℕ) • P = 0 → P = 0) →
    ∀ (n k : ℕ) (P : W.toAffine.Point), (2^n * k : ℕ) • P = 0 ↔ (k : ℕ) • P = 0
```

Both on three-axiom bar `[propext, Classical.choice, Quot.sound]`.

## Reusability

Specialising to `W = E_37a1` reproduces the E_37a1 bricks 7 and 8
(session commits 059a0585 and 4e48f1f0) as one-line corollaries.
The matching `W = E_43a1` version lands for free once the curve-specific
trivial-torsion bricks are in place.

The curve-specific arithmetic (polynomial no-rational-root proofs for
2-torsion and 3-torsion, bricks 1/9 and 5/13) is where the real work
lies; the group-theoretic layer is now factored into these generic
lemmas.
-/

namespace PrincipiaTractalis.WeierstrassSelmer_FactorStripOfTrivialTorsion_2026_11_18

/-- **Generic Selmer brick.** Stripping a factor of 2 from the torsion
    exponent is a no-op for any Weierstrass curve with trivial rational
    2-torsion. -/
theorem two_mul_torsion_iff_of_two_torsion_trivial
    {W : WeierstrassCurve ℚ}
    (h : ∀ P : W.toAffine.Point, (2 : ℕ) • P = 0 → P = 0)
    (k : ℕ) (P : W.toAffine.Point) :
    (2 * k : ℕ) • P = 0 ↔ (k : ℕ) • P = 0 := by
  constructor
  · intro hP
    have hrewrite : (2 * k : ℕ) • P = 2 • ((k : ℕ) • P) := by
      rw [mul_nsmul']
    rw [hrewrite] at hP
    exact h _ hP
  · intro hP
    have hrewrite : (2 * k : ℕ) • P = 2 • ((k : ℕ) • P) := by
      rw [mul_nsmul']
    rw [hrewrite, hP, nsmul_zero]

/-- **Generic Selmer brick.** Stripping any 2-power factor from the
    torsion exponent is a no-op for any Weierstrass curve with trivial
    rational `2^n`-torsion for all n. -/
theorem two_pow_mul_torsion_iff_of_two_pow_torsion_trivial
    {W : WeierstrassCurve ℚ}
    (h : ∀ (n : ℕ) (P : W.toAffine.Point), (2^n : ℕ) • P = 0 → P = 0) :
    ∀ (n k : ℕ) (P : W.toAffine.Point), (2^n * k : ℕ) • P = 0 ↔ (k : ℕ) • P = 0 := by
  intro n k P
  induction n with
  | zero => simp
  | succ n ih =>
      have hrewrite : (2^(n + 1) * k : ℕ) = 2 * (2^n * k) := by ring
      rw [hrewrite,
          two_mul_torsion_iff_of_two_torsion_trivial (h 1) (2^n * k) P]
      exact ih

#print axioms two_mul_torsion_iff_of_two_torsion_trivial
#print axioms two_pow_mul_torsion_iff_of_two_pow_torsion_trivial

end PrincipiaTractalis.WeierstrassSelmer_FactorStripOfTrivialTorsion_2026_11_18
