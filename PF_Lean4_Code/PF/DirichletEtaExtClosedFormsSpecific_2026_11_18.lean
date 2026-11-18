import PF.DirichletEtaExtAtTwo_2026_11_18
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Further closed-form values of `dirichletEtaExt` at specific points

Extends the Euler-value table for the Dirichlet eta extension:

```
dirichletEtaExt_at_zero : dirichletEtaExt 0 = 1 / 2
dirichletEtaExt_at_four : dirichletEtaExt 4 = 7 * (Real.pi : ℂ)^4 / 720
```

Both on three-axiom bar `[propext, Classical.choice, Quot.sound]`.

### Formulas

- At `s = 0`: `η(0) = (1 - 2¹) · ζ(0) = (-1) · (-1/2) = 1/2`, using
  mathlib's `riemannZeta_zero`.
- At `s = 4`: `η(4) = (1 - 2⁻³) · ζ(4) = (7/8) · (π⁴/90) = 7π⁴/720`,
  using mathlib's `riemannZeta_four`.

These are concrete numeric landings for the Euler closed-form family
`η(2k) = (-1)^(k+1) · (2^(2k-1) - 1) · B_{2k} · π^(2k) / (2k)!`.
-/

namespace PrincipiaTractalis.DirichletEtaExtClosedFormsSpecific_2026_11_18

open PrincipiaTractalis.DirichletEtaExtension (dirichletEtaExt)

/-- **`η(0) = 1/2`**. -/
theorem dirichletEtaExt_at_zero : dirichletEtaExt 0 = 1 / 2 := by
  unfold PrincipiaTractalis.DirichletEtaExtension.dirichletEtaExt
  rw [riemannZeta_zero]
  -- Goal: (1 - 2^(1 - 0)) * (-1/2) = 1/2
  have h_cpow : (2 : ℂ) ^ ((1 : ℂ) - 0) = 2 := by
    have : ((1 : ℂ) - 0) = (1 : ℂ) := by ring
    rw [this, Complex.cpow_one]
  rw [h_cpow]
  ring

/-- **`η(4) = 7π⁴ / 720`**. -/
theorem dirichletEtaExt_at_four :
    dirichletEtaExt 4 = 7 * (Real.pi : ℂ) ^ 4 / 720 := by
  unfold PrincipiaTractalis.DirichletEtaExtension.dirichletEtaExt
  rw [riemannZeta_four]
  -- Goal: (1 - 2^(1 - 4)) * (π⁴/90) = 7π⁴/720
  have h_cpow : (2 : ℂ) ^ ((1 : ℂ) - 4) = 1 / 8 := by
    have h : ((1 : ℂ) - 4) = (-3 : ℤ) := by push_cast; ring
    rw [h, Complex.cpow_intCast, zpow_neg]
    norm_num
  rw [h_cpow]
  ring

#print axioms dirichletEtaExt_at_zero
#print axioms dirichletEtaExt_at_four

end PrincipiaTractalis.DirichletEtaExtClosedFormsSpecific_2026_11_18
