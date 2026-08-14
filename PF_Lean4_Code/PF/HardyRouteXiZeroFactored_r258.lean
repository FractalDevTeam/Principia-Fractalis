/-
# r258: HARDY ROUTE — Xi(0) FACTORED VIA `Gammaℝ · ζ`.

★ 2026-08-13 r258 — the next concrete substrate advance on the Xi-Route B
path started by r115 and continued by r257. Factors `Xi 0` through
mathlib's `riemannZeta_def_of_ne_zero` identity so downstream numerics
on `ζ(1/2)` (classically negative, ≈ -1.4603545088...) can discharge
`Xi 0 < 0` cleanly.

## What r258 adds

r257 gave `Xi 0 = (completedRiemannZeta (1/2 : ℂ)).re`.
r258 factors the completed zeta as `Λ = Gammaℝ · ζ`:

- `completedRiemannZeta_half_eq`:
  `completedRiemannZeta (1/2 : ℂ) = Gammaℝ (1/2 : ℂ) * riemannZeta (1/2 : ℂ)`
  Direct from mathlib's `riemannZeta_def_of_ne_zero`, using that `1/2 ≠ 0`
  and `Gammaℝ (1/2 : ℂ) ≠ 0` (since `re (1/2) = 1/2 > 0`).

- `xi_zero_factored`:
  `Xi 0 = (Gammaℝ (1/2 : ℂ) * riemannZeta (1/2 : ℂ)).re`
  Immediate composition of r257's `xi_symm_at_zero` with the above.

- `gammaR_half_ne_zero`:
  `Gammaℝ (1/2 : ℂ) ≠ 0` — needed downstream for factoring numerics.

## Route B substrate advance value

The `xi_zero_factored` factorization sets up the standard reduction
"sign of `Xi 0` = sign of `ζ(1/2)`", which combined with the classically
established `ζ(1/2) < 0` and any `Xi b > 0` at a `b > 14.135` (past the
first Riemann zero) discharges `Xi 0 * Xi b < 0`, feeding r257's
`xi_sign_change_via_zero` to inhabit `PositiveOnLineZetaZeroOrdinatesNonempty`
— the Wave 58/59 atomic residual.

r258 is one further brick on that path. The next bricks:
r259 — realness of `Gammaℝ (1/2 : ℂ)` (image lies on `im = 0`).
r260 — positivity of the real part of `Gammaℝ (1/2 : ℂ)`.
r261 — sign of `Xi 0` reduces to sign of `(riemannZeta (1/2 : ℂ)).re`.

## Scope

* NOT novel — the completed-zeta factorization is mathlib's own definition.
* NOT a Millennium discharge.
* IS a concrete substrate advance on r257's Xi machine, threading
  mathlib's `Λ = Gammaℝ · ζ` into the Route B path.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.HardyRouteXiEvenness_r257

open scoped Real ComplexConjugate

namespace PrincipiaTractalis.HardyRouteXiZeroFactored

open PrincipiaTractalis.XiRealWitness
open PrincipiaTractalis.HardyRouteXiEvenness
open Complex

/-! ## §1 `Gammaℝ (1/2 : ℂ)` is nonzero. -/

/-- **`gammaR_half_ne_zero`** — the Deligne archimedean Γ factor
`Gammaℝ` is nonzero at `s = 1/2`, since `Re(1/2) = 1/2 > 0`. Direct
from mathlib's `Gammaℝ_ne_zero_of_re_pos`. -/
theorem gammaR_half_ne_zero : Gammaℝ (1/2 : ℂ) ≠ 0 := by
  apply Gammaℝ_ne_zero_of_re_pos
  show (0 : ℝ) < (1/2 : ℂ).re
  norm_num

/-! ## §2 Completed zeta at `1/2` factored as `Gammaℝ · ζ`. -/

/-- **`completedRiemannZeta_half_eq`** — the identity
`Λ(1/2) = Gammaℝ(1/2) · ζ(1/2)` obtained by rearranging mathlib's
`riemannZeta_def_of_ne_zero: ζ s = Λ s / Gammaℝ s`. -/
theorem completedRiemannZeta_half_eq :
    completedRiemannZeta (1/2 : ℂ)
      = Gammaℝ (1/2 : ℂ) * riemannZeta (1/2 : ℂ) := by
  have hne : (1/2 : ℂ) ≠ 0 := by norm_num
  rw [riemannZeta_def_of_ne_zero hne, mul_div_cancel₀ _ gammaR_half_ne_zero]

/-! ## §3 `Xi 0` in factored form. -/

/-- **`xi_zero_factored`** — `Xi 0` expressed as the real part of
`Gammaℝ(1/2) · ζ(1/2)`. Composes r257's `xi_symm_at_zero` with the
mathlib-native `Λ = Gammaℝ · ζ` factorization at `s = 1/2`. -/
theorem xi_zero_factored :
    Xi 0 = (Gammaℝ (1/2 : ℂ) * riemannZeta (1/2 : ℂ)).re := by
  rw [xi_symm_at_zero, completedRiemannZeta_half_eq]

/-! ## §4 Axiom check. -/

#print axioms PrincipiaTractalis.HardyRouteXiZeroFactored.gammaR_half_ne_zero
#print axioms PrincipiaTractalis.HardyRouteXiZeroFactored.completedRiemannZeta_half_eq
#print axioms PrincipiaTractalis.HardyRouteXiZeroFactored.xi_zero_factored

end PrincipiaTractalis.HardyRouteXiZeroFactored
