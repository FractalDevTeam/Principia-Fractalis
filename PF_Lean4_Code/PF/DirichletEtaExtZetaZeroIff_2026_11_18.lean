import PF.DirichletEtaExtension_r269

/-!
# Zeros of `dirichletEtaExt` off the extra-zero family coincide with zeros of `riemannZeta`

The identity `η_ext(s) = (1 - 2^(1-s)) · ζ(s)` factors the eta
extension into two parts. Away from the "extra family" of zeros of
`(1 - 2^(1-s))` (which includes `s = 1`), the zeros of `η_ext` are
exactly the zeros of `ζ`.

This file ships the `iff` at the pointwise level, hypothesised on
`2^(1-s) ≠ 1`:

```
dirichletEtaExt_eq_zero_iff_riemannZeta_eq_zero :
    (2 : ℂ) ^ (1 - s) ≠ 1 →
      (dirichletEtaExt s = 0 ↔ riemannZeta s = 0)
```

The hypothesis `2^(1-s) ≠ 1` automatically excludes `s = 1` (where
`2^0 = 1`), so this is the "off the extra zeros" correspondence. The
converse direction (zeros of `η_ext` on the extra family) is the
companion file `DirichletEtaExtExtraZeros_2026_11_18`.

Combined: for any `s : ℂ`,
  - `s` on the extra family (`2^(1-s) = 1`) ⟹ `η_ext s = 0`
    (direct, no ζ involvement).
  - `s` off the extra family ⟹ `η_ext s = 0 ↔ ζ s = 0`.

So the zeros of `η_ext` split cleanly into the extra family plus the
pullback of the zeros of `ζ`.

Three-axiom bar `[propext, Classical.choice, Quot.sound]`.
-/

namespace PrincipiaTractalis.DirichletEtaExtZetaZeroIff_2026_11_18

open PrincipiaTractalis.DirichletEtaExtension (dirichletEtaExt)

/-- **Zero correspondence off the extra family.**
    Where the factor `(1 - 2^(1-s))` is nonzero, the zeros of
    `dirichletEtaExt` coincide with those of `riemannZeta`. -/
theorem dirichletEtaExt_eq_zero_iff_riemannZeta_eq_zero
    {s : ℂ} (h2 : (2 : ℂ) ^ (1 - s) ≠ 1) :
    dirichletEtaExt s = 0 ↔ riemannZeta s = 0 := by
  have hfact : (1 : ℂ) - (2 : ℂ) ^ (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm h2)
  unfold PrincipiaTractalis.DirichletEtaExtension.dirichletEtaExt
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2'
    · exact absurd h1 hfact
    · exact h2'
  · intro h
    rw [h, mul_zero]

#print axioms dirichletEtaExt_eq_zero_iff_riemannZeta_eq_zero

end PrincipiaTractalis.DirichletEtaExtZetaZeroIff_2026_11_18
