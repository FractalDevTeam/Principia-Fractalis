import PF.DirichletEtaExtraFamilyOnCriticalLine_2026_11_18
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# The extra-zero family is disjoint from ζ-zeros

```
extraFamily_not_riemannZeta_zero (k : ℤ) :
    riemannZeta (extraFamily k) ≠ 0

extraFamily_disjoint_from_zeta_zeros (k : ℤ) (s : ℂ) :
    s = extraFamily k → riemannZeta s ≠ 0
```

Both on three-axiom bar `[propext, Classical.choice, Quot.sound]`.

Direct composition: `Re(extraFamily k) = 1 ≥ 1`
(`extraFamily_re`, commit 32b066cb) + mathlib's
`riemannZeta_ne_zero_of_one_le_re` (Nonvanishing).

## Structural picture

The zero sources of `dirichletEtaExt` — the extra family (where the
factor `(1 - 2^(1-s))` vanishes) and the ζ-zeros — are **disjoint**:
the extra family lives on `Re s = 1`, and `ζ` has no zeros on
`Re s ≥ 1`. So the full zero characterisation

```
dirichletEtaExt s = 0 ↔ (∃ k, s = extraFamily k) ∨ riemannZeta s = 0
```

is a **disjoint union** — each zero of `dirichletEtaExt` comes from
exactly one of the two sources, never both.
-/

namespace PrincipiaTractalis.DirichletEtaExtExtraFamilyDisjointFromZetaZeros_2026_11_18

open PrincipiaTractalis.DirichletEtaExtraFamilyStructure_2026_11_18
  (extraFamily)
open PrincipiaTractalis.DirichletEtaExtraFamilyOnCriticalLine_2026_11_18
  (extraFamily_re)

/-- Every extra-family point has `Re = 1`, hence is not a ζ-zero. -/
theorem extraFamily_not_riemannZeta_zero (k : ℤ) :
    riemannZeta (extraFamily k) ≠ 0 := by
  have h_re : (extraFamily k).re = 1 := extraFamily_re k
  have h_one_le : 1 ≤ (extraFamily k).re := by rw [h_re]
  exact riemannZeta_ne_zero_of_one_le_re h_one_le

/-- Alternative framing: if `s` equals an extra-family point, then
    `s` is not a ζ-zero. -/
theorem extraFamily_disjoint_from_zeta_zeros (k : ℤ) (s : ℂ) :
    s = extraFamily k → riemannZeta s ≠ 0 := by
  rintro rfl
  exact extraFamily_not_riemannZeta_zero k

#print axioms extraFamily_not_riemannZeta_zero
#print axioms extraFamily_disjoint_from_zeta_zeros

end PrincipiaTractalis.DirichletEtaExtExtraFamilyDisjointFromZetaZeros_2026_11_18
