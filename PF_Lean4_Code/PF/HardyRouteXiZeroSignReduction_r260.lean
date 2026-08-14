/-
# r260: HARDY ROUTE — SIGN OF `Xi 0` REDUCES TO SIGN OF `(ζ(1/2)).re`.

★ 2026-08-13 r260 — closes the algebraic reduction stage of the Xi
Route B path. After r257 (Xi = real part of Λ at critical line), r258
(Λ(1/2) = Gammaℝ(1/2) · ζ(1/2)), r259 (Gammaℝ(1/2) is a positive real),
r260 assembles the final algebraic layer:

  `sign(Xi 0) = sign((riemannZeta (1/2 : ℂ)).re)`

  and its concrete Route B corollary: if the real part of `ζ(1/2)` is
  strictly negative and `Xi b` is strictly positive at some `b > 0`,
  then `PositiveOnLineZetaZeroOrdinatesNonempty` holds — the last RH
  atomic residual.

## What r260 adds

- `xi_zero_eq_gammaR_re_mul_zeta_re`:
  `Xi 0 = (Gammaℝ (1/2 : ℂ)).re * (riemannZeta (1/2 : ℂ)).re`
  Follows from r258's `xi_zero_factored`, expanding `(a*b).re` with
  r259's `gammaR_half_im_zero`.

- `xi_zero_neg_iff_zeta_half_re_neg`:
  `Xi 0 < 0 ↔ (riemannZeta (1/2 : ℂ)).re < 0`
  Direct from r259's `gammaR_half_re_pos > 0`, the positive factor
  distributes across the strict inequality.

- `xi_zero_pos_iff_zeta_half_re_pos`:
  the symmetric statement.

- `xi_sign_change_via_zeta_half_neg`:
  if `(riemannZeta (1/2 : ℂ)).re < 0` AND `∃ b > 0, Xi b > 0`, then
  `PositiveOnLineZetaZeroOrdinatesNonempty`.
  Composes the above with r257's `xi_sign_change_via_zero`.

## Route B substrate value

r260 is the final algebraic-layer brick. What remains for full Route B
discharge of the RH atomic residual is now purely NUMERICAL:

  (a) a certified sign fact `(riemannZeta (1/2 : ℂ)).re < 0` — the
      classical value ≈ -1.4603545088... < 0;

  (b) a certified sign fact `∃ b > 0, Xi b > 0` — e.g. any evaluation
      past the first Riemann zero at `b > 14.135`.

Either interval-arithmetic package inside Lean or an ambient certified
witness discharges (a) and (b) after r260, kernel-clean.

## Scope

* NOT novel — the sign reduction is standard algebra once realness of
  the archimedean Γ-factor is known.
* NOT a Millennium discharge.
* IS the closure of the algebraic reduction stage of Route B, one
  brick above r259.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.HardyRouteGammaRHalfReal_r259

open scoped Real ComplexConjugate

namespace PrincipiaTractalis.HardyRouteXiZeroSignReduction

open PrincipiaTractalis.XiRealWitness
open PrincipiaTractalis.HardyRouteXiEvenness
open PrincipiaTractalis.HardyRouteXiZeroFactored
open PrincipiaTractalis.HardyRouteGammaRHalfReal
open PrincipiaTractalis.HilbertPolyaPositiveReductionToCountability
open Complex

/-! ## §1 `Xi 0` as a real product of real parts. -/

/-- **`xi_zero_eq_gammaR_re_mul_zeta_re`** — the real value `Xi 0`
equals the product of `(Gammaℝ (1/2 : ℂ)).re` and
`(riemannZeta (1/2 : ℂ)).re`, since the archimedean Γ-factor is real
at `s = 1/2` (r259). -/
theorem xi_zero_eq_gammaR_re_mul_zeta_re :
    Xi 0 = (Gammaℝ (1/2 : ℂ)).re * (riemannZeta (1/2 : ℂ)).re := by
  rw [xi_zero_factored]
  rw [Complex.mul_re, gammaR_half_im_zero, zero_mul, sub_zero]

/-! ## §2 Sign of `Xi 0` = sign of `(ζ(1/2)).re`. -/

/-- **`xi_zero_neg_iff_zeta_half_re_neg`** — `Xi 0 < 0` iff
`(riemannZeta (1/2 : ℂ)).re < 0`. The positive real factor
`(Gammaℝ (1/2 : ℂ)).re > 0` (r259) distributes across the strict
inequality. -/
theorem xi_zero_neg_iff_zeta_half_re_neg :
    Xi 0 < 0 ↔ (riemannZeta (1/2 : ℂ)).re < 0 := by
  rw [xi_zero_eq_gammaR_re_mul_zeta_re]
  constructor
  · intro h
    exact (mul_neg_iff.mp h).elim (fun ⟨_, h2⟩ => h2)
      (fun ⟨h1, _⟩ => absurd h1 (not_lt.mpr gammaR_half_re_pos.le))
  · intro h
    exact mul_neg_of_pos_of_neg gammaR_half_re_pos h

/-- **`xi_zero_pos_iff_zeta_half_re_pos`** — `Xi 0 > 0` iff
`(riemannZeta (1/2 : ℂ)).re > 0`. Symmetric to
`xi_zero_neg_iff_zeta_half_re_neg`. -/
theorem xi_zero_pos_iff_zeta_half_re_pos :
    0 < Xi 0 ↔ 0 < (riemannZeta (1/2 : ℂ)).re := by
  rw [xi_zero_eq_gammaR_re_mul_zeta_re]
  constructor
  · intro h
    exact (mul_pos_iff.mp h).elim (fun ⟨_, h2⟩ => h2)
      (fun ⟨h1, _⟩ => absurd h1 (not_lt.mpr gammaR_half_re_pos.le))
  · intro h
    exact mul_pos gammaR_half_re_pos h

/-! ## §3 Route B sign-change composition. -/

/-- **`xi_sign_change_via_zeta_half_neg`** — if `(riemannZeta (1/2 : ℂ)).re`
is strictly negative AND `Xi b > 0` for some `b > 0`, then the Wave 58/59
atomic residual `PositiveOnLineZetaZeroOrdinatesNonempty` is inhabited.

Route B algebraic-layer capstone: composes the sign reduction with r257's
`xi_sign_change_via_zero`. Numerical content on `(ζ(1/2)).re < 0` and
`Xi b > 0` at some `b > 14.135` closes the last RH atomic residual. -/
theorem xi_sign_change_via_zeta_half_neg
    (hζ : (riemannZeta (1/2 : ℂ)).re < 0)
    {b : ℝ} (hb : 0 < b) (hXi_b : 0 < Xi b) :
    PositiveOnLineZetaZeroOrdinatesNonempty := by
  have hXi_0_neg : Xi 0 < 0 := xi_zero_neg_iff_zeta_half_re_neg.mpr hζ
  have hsign : Xi 0 * Xi b < 0 := mul_neg_of_neg_of_pos hXi_0_neg hXi_b
  exact xi_sign_change_via_zero hb hsign

/-! ## §4 Axiom check. -/

#print axioms PrincipiaTractalis.HardyRouteXiZeroSignReduction.xi_zero_eq_gammaR_re_mul_zeta_re
#print axioms PrincipiaTractalis.HardyRouteXiZeroSignReduction.xi_zero_neg_iff_zeta_half_re_neg
#print axioms PrincipiaTractalis.HardyRouteXiZeroSignReduction.xi_zero_pos_iff_zeta_half_re_pos
#print axioms PrincipiaTractalis.HardyRouteXiZeroSignReduction.xi_sign_change_via_zeta_half_neg

end PrincipiaTractalis.HardyRouteXiZeroSignReduction
