import PF.DirichletEtaExtension_r269
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# The closed-form value `η(2) = π² / 12`

```
dirichletEtaExt_at_two : dirichletEtaExt 2 = (Real.pi : ℂ) ^ 2 / 12
```

Direct computation from the identity

    `dirichletEtaExt s = (1 - 2^(1-s)) · ζ(s)`

at `s = 2`:

    `η(2) = (1 - 2⁻¹) · ζ(2) = (1/2) · (π²/6) = π² / 12`

using mathlib's `riemannZeta_two : ζ(2) = π² / 6` (Euler 1735).

Three-axiom bar `[propext, Classical.choice, Quot.sound]`.

This is the first concrete closed-form value of `dirichletEtaExt`
in the corpus; the family `η(2k) = (-1)^(k+1) · (2^(2k-1) - 1)·B_{2k}·π^(2k)/(2k)!`
for `k ≥ 1` admits analogous computations at each even positive integer.
-/

namespace PrincipiaTractalis.DirichletEtaExtAtTwo_2026_11_18

open PrincipiaTractalis.DirichletEtaExtension (dirichletEtaExt)

/-- **Euler closed form.** `dirichletEtaExt 2 = π² / 12`. -/
theorem dirichletEtaExt_at_two :
    dirichletEtaExt 2 = (Real.pi : ℂ) ^ 2 / 12 := by
  unfold PrincipiaTractalis.DirichletEtaExtension.dirichletEtaExt
  rw [riemannZeta_two]
  -- Goal: (1 - 2^(1 - 2)) * ((π : ℂ)^2 / 6) = (π : ℂ)^2 / 12
  have h_cpow : (2 : ℂ) ^ ((1 : ℂ) - 2) = 1 / 2 := by
    have : ((1 : ℂ) - 2) = (-1 : ℤ) := by push_cast; ring
    rw [this, Complex.cpow_intCast, zpow_neg, zpow_one]
    norm_num
  rw [h_cpow]
  ring

#print axioms dirichletEtaExt_at_two

end PrincipiaTractalis.DirichletEtaExtAtTwo_2026_11_18
