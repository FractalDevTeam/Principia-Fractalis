/-
# r261: HARDY ROUTE — `ζ(1/2)` IS REAL, PLUS TWO-SIDED SIGN CHANGE.

★ 2026-08-13 r261 — two further concrete substrate advances on the Xi
Route B path.

## What r261 adds

- `zeta_half_im_zero`:
  `(riemannZeta (1/2 : ℂ)).im = 0` — the Riemann zeta function at the
  critical point `s = 1/2` takes a REAL value. Derived from
  r258's `completedRiemannZeta_half_eq` combined with r257's
  `xi_symm_at_zero`, r115's `Xi_im_eq_zero`, r259's
  `gammaR_half_im_zero`, and `gammaR_half_re_pos`.

- `xi_sign_change_via_zero_symmetric`:
  `Xi 0 * Xi b < 0` for ANY `b ≠ 0` implies
  `PositiveOnLineZetaZeroOrdinatesNonempty`. Uses r257's `xi_even` to
  reduce the case `b < 0` to the case `|b| > 0`, then applies r257's
  `xi_sign_change_via_zero`.

## Route B substrate value

r261 provides two orthogonal strengthenings:

  (i) `zeta_half_im_zero` makes explicit that any downstream statement
      about `(riemannZeta (1/2)).re` is a statement about the full
      complex value: `ζ(1/2) = ((ζ(1/2)).re : ℂ)`.

 (ii) `xi_sign_change_via_zero_symmetric` removes the `b > 0` side
      constraint on the sign-change witness: any nonzero `b` — positive
      or negative — with `Xi 0 * Xi b < 0` discharges the RH atomic
      residual.

## Scope

* NOT novel — realness of `ζ(1/2)` is classical, and the two-sided
  sign-change extension is a direct evenness argument.
* NOT a Millennium discharge.
* IS two further substrate advances on the r257-r260 chain.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.HardyRouteXiZeroSignReduction_r260

open scoped Real ComplexConjugate

namespace PrincipiaTractalis.HardyRouteZetaHalfReal

open PrincipiaTractalis.XiRealWitness
open PrincipiaTractalis.HardyRouteXiEvenness
open PrincipiaTractalis.HardyRouteXiZeroFactored
open PrincipiaTractalis.HardyRouteGammaRHalfReal
open PrincipiaTractalis.HardyRouteXiZeroSignReduction
open PrincipiaTractalis.HilbertPolyaPositiveReductionToCountability
open Complex

/-! ## §1 `ζ(1/2)` is real. -/

/-- **`zeta_half_im_zero`** — `(riemannZeta (1/2 : ℂ)).im = 0`.

Derivation: from `Λ(1/2) = Gammaℝ(1/2) · ζ(1/2)` (r258) and the fact
that `Λ(1/2)` is real (r115's `Xi_im_eq_zero` at `t = 0`, transported
by r257's `xi_symm_at_zero`), plus `Gammaℝ(1/2)` real (r259), the ratio
`ζ(1/2) = Λ(1/2) / Gammaℝ(1/2)` is real too. -/
theorem zeta_half_im_zero : (riemannZeta (1/2 : ℂ)).im = 0 := by
  have hne : (1/2 : ℂ) ≠ 0 := by norm_num
  have hΛ_im : (completedRiemannZeta (1/2 : ℂ)).im = 0 := by
    have h1 : (⟨1/2, (0 : ℝ)⟩ : ℂ) = (1/2 : ℂ) := by
      apply Complex.ext
      · show (1/2 : ℝ) = (1/2 : ℂ).re; norm_num
      · show (0 : ℝ) = (1/2 : ℂ).im; norm_num
    have := Xi_im_eq_zero 0
    rw [h1] at this
    exact this
  -- ζ(1/2) = Λ(1/2) / Gammaℝ(1/2)
  rw [riemannZeta_def_of_ne_zero hne]
  -- The im part of (a + bi)/(c + 0i) where c ≠ 0, c real: (b·c - a·0)/(c^2 + 0^2) = b/c.
  -- Since b = Λ.im = 0, get 0.
  rw [Complex.div_im]
  rw [hΛ_im, gammaR_half_im_zero]
  simp

/-! ## §2 Two-sided sign-change via evenness. -/

/-- **`xi_sign_change_via_zero_symmetric`** — the sign-change witness
`Xi 0 * Xi b < 0` at ANY nonzero `b` (positive or negative) discharges
the Wave 58/59 atomic residual. `xi_even` reduces the `b < 0` branch to
the `|b| > 0` branch. -/
theorem xi_sign_change_via_zero_symmetric {b : ℝ} (hb : b ≠ 0)
    (hsign : Xi 0 * Xi b < 0) : PositiveOnLineZetaZeroOrdinatesNonempty := by
  rcases lt_or_gt_of_ne hb with hlt | hgt
  · -- b < 0. Use xi_even to reduce to -b > 0.
    have hposb : 0 < -b := neg_pos.mpr hlt
    have hxi : Xi (-b) = Xi b := xi_even b
    have hsign' : Xi 0 * Xi (-b) < 0 := by rw [hxi]; exact hsign
    exact xi_sign_change_via_zero hposb hsign'
  · -- b > 0. Direct.
    exact xi_sign_change_via_zero hgt hsign

/-! ## §3 Axiom check. -/

#print axioms PrincipiaTractalis.HardyRouteZetaHalfReal.zeta_half_im_zero
#print axioms PrincipiaTractalis.HardyRouteZetaHalfReal.xi_sign_change_via_zero_symmetric

end PrincipiaTractalis.HardyRouteZetaHalfReal
