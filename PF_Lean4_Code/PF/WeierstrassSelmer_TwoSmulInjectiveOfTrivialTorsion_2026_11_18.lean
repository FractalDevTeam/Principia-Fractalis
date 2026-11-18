import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Generic Selmer-attack lemma: `2 •` injective from trivial rational 2-torsion

**Headline.** For any Weierstrass curve `W` over `ℚ`,

```
two_smul_injective_of_two_torsion_trivial :
    (∀ P : W.toAffine.Point, 2 • P = 0 → P = 0) →
    ∀ P Q : W.toAffine.Point, (2 : ℕ) • P = (2 : ℕ) • Q → P = Q
```

on three-axiom bar `[propext, Classical.choice, Quot.sound]`.

Pure group theory over the `AddCommGroup` structure of
`WeierstrassCurve.Affine.Point`:
    `2 • P = 2 • Q  ⟹  2 • (P - Q) = 0  ⟹  P - Q = 0  ⟹  P = Q`.

## Selmer significance

Specialising to `W = E_37a1` + `W = E_43a1` reproduces the E_37a1
brick 3 and E_43a1 brick 4 bricks as one-line corollaries. Any future
rank-1 curve `W` that lands trivial rational 2-torsion gets the
matching `2•`-injectivity brick for free.

Also admits an analogous `2^n`-version (future generic brick):
    `(∀ n P, (2^n) • P = 0 → P = 0) → ∀ n P Q, (2^n) • P = (2^n) • Q → P = Q`.
-/

namespace PrincipiaTractalis.WeierstrassSelmer_TwoSmulInjectiveOfTrivialTorsion_2026_11_18

/-- **Generic Selmer brick.** Injectivity of `2 •` on rational points
    follows from trivial rational 2-torsion. -/
theorem two_smul_injective_of_two_torsion_trivial
    {W : WeierstrassCurve ℚ}
    (h : ∀ P : W.toAffine.Point, (2 : ℕ) • P = 0 → P = 0) :
    ∀ P Q : W.toAffine.Point, (2 : ℕ) • P = (2 : ℕ) • Q → P = Q := by
  intro P Q hPQ
  have h1 : (2 : ℕ) • (P - Q) = 0 := by
    have hexpand : (2 : ℕ) • (P - Q) = (2 : ℕ) • P - (2 : ℕ) • Q := by
      rw [two_nsmul, two_nsmul, two_nsmul]; abel
    rw [hexpand, hPQ, sub_self]
  have h2 : P - Q = 0 := h _ h1
  exact sub_eq_zero.mp h2

/-- **Generic `2^n`-version.** Injectivity of `2^n •` follows from
    trivial rational `2^n`-torsion. -/
theorem two_pow_smul_injective_of_two_pow_torsion_trivial
    {W : WeierstrassCurve ℚ}
    (h : ∀ (n : ℕ) (P : W.toAffine.Point), (2^n : ℕ) • P = 0 → P = 0) :
    ∀ (n : ℕ) (P Q : W.toAffine.Point), (2^n : ℕ) • P = (2^n : ℕ) • Q → P = Q := by
  intro n P Q hPQ
  have hPQ' : (2 ^ n : ℕ) • P = (2 ^ n : ℕ) • Q := hPQ
  have h_diff : (2 ^ n : ℕ) • (P - Q) = 0 := by
    have hexpand :
        (2 ^ n : ℕ) • (P - Q) = (2 ^ n : ℕ) • P - (2 ^ n : ℕ) • Q := by
      induction (2 ^ n : ℕ) with
      | zero => simp
      | succ k ih =>
          rw [succ_nsmul, succ_nsmul, succ_nsmul, ih]; abel
    rw [hexpand, hPQ', sub_self]
  have : P - Q = 0 := h n _ h_diff
  exact sub_eq_zero.mp this

#print axioms two_smul_injective_of_two_torsion_trivial
#print axioms two_pow_smul_injective_of_two_pow_torsion_trivial

end PrincipiaTractalis.WeierstrassSelmer_TwoSmulInjectiveOfTrivialTorsion_2026_11_18
