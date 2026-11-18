import PF.DirichletEtaExtension_r269
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# The Dirichlet eta value `η(-1) = 1/4`

The regularised "divergent sum" `1 - 2 + 3 - 4 + …` summed by analytic
continuation of the Dirichlet eta function:

```
dirichletEtaExt_at_neg_one : dirichletEtaExt (-1) = 1 / 4
```

on three-axiom bar `[propext, Classical.choice, Quot.sound]`.

Computation: `η(-1) = (1 - 2²) · ζ(-1) = (-3) · (-1/12) = 1/4`,
using mathlib's `riemannZeta_neg_nat_eq_bernoulli` at `k = 1`
(which gives `ζ(-1) = -1/12` via `bernoulli 2 = 1/6`).

Classical appearances: this value sits at the boundary of the critical
strip's reflected half-plane; it also provides the famous Abel-summed
value of the alternating divergent series.
-/

namespace PrincipiaTractalis.DirichletEtaExtAtNegOne_2026_11_18

open PrincipiaTractalis.DirichletEtaExtension (dirichletEtaExt)

/-- `riemannZeta (-1) = -1/12`. Direct from the Bernoulli-number
    formula `riemannZeta_neg_nat_eq_bernoulli` at `k = 1`. -/
theorem riemannZeta_neg_one : riemannZeta (-1) = -1 / 12 := by
  have h := riemannZeta_neg_nat_eq_bernoulli 1
  simp at h
  -- h : riemannZeta (-1) = -↑(bernoulli 2) / (1 + 1)
  rw [h]
  rw [show (bernoulli 2 : ℚ) = (1/6 : ℚ) from by norm_num [bernoulli]]
  push_cast
  ring

/-- **Euler closed form.** `dirichletEtaExt (-1) = 1 / 4`. -/
theorem dirichletEtaExt_at_neg_one :
    dirichletEtaExt (-1) = 1 / 4 := by
  unfold PrincipiaTractalis.DirichletEtaExtension.dirichletEtaExt
  rw [riemannZeta_neg_one]
  -- Goal: (1 - 2^(1 - (-1))) * (-1/12) = 1/4
  have h_cpow : (2 : ℂ) ^ ((1 : ℂ) - (-1)) = 4 := by
    have : ((1 : ℂ) - (-1)) = (2 : ℤ) := by push_cast; ring
    rw [this, Complex.cpow_intCast]
    norm_num
  rw [h_cpow]
  ring

#print axioms riemannZeta_neg_one
#print axioms dirichletEtaExt_at_neg_one

end PrincipiaTractalis.DirichletEtaExtAtNegOne_2026_11_18
