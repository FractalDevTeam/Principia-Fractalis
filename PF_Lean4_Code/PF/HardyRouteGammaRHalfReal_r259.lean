/-
# r259: HARDY ROUTE — `Gammaℝ (1/2 : ℂ)` IS A POSITIVE REAL.

★ 2026-08-13 r259 — the next concrete substrate advance on the Xi-Route B
path. After r257's `Xi 0 = (Λ(1/2)).re` and r258's factorization
`Λ(1/2) = Gammaℝ(1/2) · ζ(1/2)`, r259 nails down that the archimedean
Γ-factor `Gammaℝ(1/2 : ℂ)` is a positive real (in the sense that its
imaginary part vanishes and its real part is strictly positive), so the
downstream reduction `sign(Xi 0) = sign((ζ(1/2)).re)` becomes routine.

## What r259 adds

- `Complex.ofReal_pi`: (∗) actually a mathlib fact reused —
  `((Real.pi : ℝ) : ℂ) = Complex.ofReal Real.pi = (Complex.pi ?)`.
  We use it as coerced casts.

- `gammaR_half_eq_ofReal`:
  `Gammaℝ (1/2 : ℂ) = ((Real.pi ^ (-(1/4 : ℝ)) * Real.Gamma (1/4) : ℝ) : ℂ)`
  Direct from `Gammaℝ_def` + `Complex.ofReal_cpow` (with π ≥ 0) +
  `Complex.Gamma_ofReal` (Complex.Gamma on a real coercion equals
  Real.Gamma).

- `gammaR_half_im_zero`:
  `(Gammaℝ (1/2 : ℂ)).im = 0` — immediate corollary.

- `gammaR_half_re_pos`:
  `0 < (Gammaℝ (1/2 : ℂ)).re` — from
  `Real.rpow_pos_of_pos Real.pi_pos _ > 0` × `Gamma_pos_of_pos` on `1/4 > 0`.

## Route B advance value

Combined with r258's `xi_zero_factored`, r259 lets us extract:
  `Xi 0 = (Gammaℝ (1/2)).re * (ζ(1/2)).re`
i.e. the real product on the critical line, so the sign of `Xi 0`
reduces to the sign of `(ζ(1/2)).re`. That is the last algebraic layer
before numerical content on `ζ(1/2)` (classically negative) plus a
`b > 14.135` sign witness for `Xi b > 0` inhabit
`PositiveOnLineZetaZeroOrdinatesNonempty` via r257's
`xi_sign_change_via_zero`.

## Scope

* NOT novel — realness+positivity of the archimedean Γ-factor at
  positive real arguments is a mathlib-native corollary.
* NOT a Millennium discharge.
* IS a concrete substrate advance nailing down the algebraic layer
  of Route B.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.HardyRouteXiZeroFactored_r258
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

open scoped Real ComplexConjugate

namespace PrincipiaTractalis.HardyRouteGammaRHalfReal

open PrincipiaTractalis.XiRealWitness
open PrincipiaTractalis.HardyRouteXiEvenness
open PrincipiaTractalis.HardyRouteXiZeroFactored
open Complex

/-! ## §1 `Gammaℝ (1/2 : ℂ)` as a real coercion. -/

/-- **`gammaR_half_eq_ofReal`** — the archimedean Γ-factor at `s = 1/2`
is the coercion of the real number `π^{-1/4} · Γ(1/4)` into ℂ. Follows
from `Gammaℝ_def`, `Complex.ofReal_cpow` (π ≥ 0), and
`Complex.Gamma_ofReal`. -/
theorem gammaR_half_eq_ofReal :
    Gammaℝ (1/2 : ℂ)
      = ((Real.pi ^ (-(1/4 : ℝ)) * Real.Gamma (1/4) : ℝ) : ℂ) := by
  rw [Gammaℝ_def]
  have hpi : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have hexp : (-(1/2 : ℂ) / 2) = ((-(1/4 : ℝ) : ℝ) : ℂ) := by
    push_cast; ring
  have harg : ((1/2 : ℂ) / 2) = (((1/4 : ℝ) : ℝ) : ℂ) := by
    push_cast; ring
  rw [hexp, harg]
  rw [← Complex.ofReal_cpow hpi (-(1/4 : ℝ))]
  rw [Complex.Gamma_ofReal (1/4 : ℝ)]
  push_cast
  ring

/-! ## §2 Realness — the imaginary part vanishes. -/

/-- **`gammaR_half_im_zero`** — the imaginary part of `Gammaℝ(1/2 : ℂ)`
is zero. Immediate from `gammaR_half_eq_ofReal`. -/
theorem gammaR_half_im_zero : (Gammaℝ (1/2 : ℂ)).im = 0 := by
  rw [gammaR_half_eq_ofReal]
  exact Complex.ofReal_im _

/-! ## §3 Positivity of the real part. -/

/-- **`gammaR_half_re_pos`** — the real part of `Gammaℝ(1/2 : ℂ)` is
strictly positive: it equals `π^{-1/4} · Γ(1/4)`, and both factors are
positive (`π > 0` gives `π^{-1/4} > 0` by `Real.rpow_pos_of_pos`, and
`Γ(1/4) > 0` by `Real.Gamma_pos_of_pos`). -/
theorem gammaR_half_re_pos : 0 < (Gammaℝ (1/2 : ℂ)).re := by
  rw [gammaR_half_eq_ofReal]
  rw [Complex.ofReal_re]
  exact mul_pos (Real.rpow_pos_of_pos Real.pi_pos _)
    (Real.Gamma_pos_of_pos (by norm_num))

/-! ## §4 Axiom check. -/

#print axioms PrincipiaTractalis.HardyRouteGammaRHalfReal.gammaR_half_eq_ofReal
#print axioms PrincipiaTractalis.HardyRouteGammaRHalfReal.gammaR_half_im_zero
#print axioms PrincipiaTractalis.HardyRouteGammaRHalfReal.gammaR_half_re_pos

end PrincipiaTractalis.HardyRouteGammaRHalfReal
