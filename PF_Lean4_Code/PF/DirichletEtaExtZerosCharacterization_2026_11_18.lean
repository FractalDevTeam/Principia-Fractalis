import PF.DirichletEtaExtExtraZeros_2026_11_18
import PF.DirichletEtaExtZetaZeroIff_2026_11_18

/-!
# Full characterization of zeros of `dirichletEtaExt`

Combines the two companion theorems
(`dirichletEtaExt_eq_zero_of_two_cpow_eq_one`, `dirichletEtaExt_eq_zero_iff_riemannZeta_eq_zero`)
into a single pointwise `iff`:

```
dirichletEtaExt_eq_zero_iff :
    dirichletEtaExt s = 0 ↔ (2 : ℂ)^(1-s) = 1 ∨ riemannZeta s = 0
```

This is the final packaging of the zero structure: a point `s : ℂ` is
a zero of the eta extension if and only if it is either in the extra
family (where the factor vanishes) or a zero of the Riemann zeta
function. The two sources are the only sources.

Three-axiom bar `[propext, Classical.choice, Quot.sound]`.
-/

namespace PrincipiaTractalis.DirichletEtaExtZerosCharacterization_2026_11_18

open PrincipiaTractalis.DirichletEtaExtension (dirichletEtaExt)

/-- **Full zero characterization.** `s` is a zero of `dirichletEtaExt`
    iff either the factor `(1 - 2^(1-s))` vanishes at `s` (extra zero)
    or `s` is a zero of `riemannZeta`. -/
theorem dirichletEtaExt_eq_zero_iff (s : ℂ) :
    dirichletEtaExt s = 0 ↔ (2 : ℂ) ^ (1 - s) = 1 ∨ riemannZeta s = 0 := by
  unfold PrincipiaTractalis.DirichletEtaExtension.dirichletEtaExt
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hfact | hzeta
    · -- 1 - 2^(1-s) = 0 ⟺ 2^(1-s) = 1
      left
      have : (2 : ℂ) ^ (1 - s) = 1 := by linear_combination -hfact
      exact this
    · right; exact hzeta
  · intro h
    rcases h with h2 | hz
    · -- 2^(1-s) = 1 ⟹ factor is zero
      rw [h2, sub_self, zero_mul]
    · rw [hz, mul_zero]

#print axioms dirichletEtaExt_eq_zero_iff

end PrincipiaTractalis.DirichletEtaExtZerosCharacterization_2026_11_18
