/-
# PF.Analytic.ThetaBoundaryConstant_2026_10_19

**`ω(1)/2 + 2ω′(1) = −1/4`, from mathlib's Jacobi theta transformation law** —
and with it the sharp form of the Tier-3 identity,

  `Λ₀(1+it) = 1/t² − (4/t²)(I₊ + I₋)`,

**leading coefficient pinned at exactly 1** rather than `O(t⁻²)`.

### Route

The gate passed: `jacobiTheta_S_smul` is on the pin. The bridge is immediate
because `jacobiTheta_eq_tsum_nat` is *already* the tree's `ω` after one
substitution — at `τ = i·x` the summand
`exp(π i (n+1)² (i x)) = exp(−π(n+1)²x)`:

1. `jacobiTheta (i·x) = 1 + 2ω(x)` for `x > 0`  (§1, termwise)
2. `1 + 2ω(1/x) = √x·(1 + 2ω(x))` for `x > 0`   (§2, from `jacobiTheta_S_smul`)
3. differentiate (2) at `x = 1`                 (§3) ⟹ `ω′(1) = −(1 + 2ω(1))/8`
4. hence `ω(1)/2 + 2ω′(1) = −1/4`               (§4)

**Note the route never differentiates `jacobiTheta`.** Step 2 is extracted as a
*real* identity and then differentiated using the tree's own
`omega_hasDerivAt` (built 2026-10-18) plus `Real.hasDerivAt_sqrt`. So no
holomorphy of `jacobiTheta` is needed — `differentiable_jacobiTheta` does not
exist on this pin, and this route does not want it.

### Naming

`jacobiTheta` here is the **modular** theta function. It is unrelated to the
Yang–Mills reflection `θ` (`timeReflectionGaugeField`,
`PF.YangMills.*`), which lives in a different namespace; nothing is shared.

Three-axiom bar: every top-level declaration prints
`[propext, Classical.choice, Quot.sound]`. No sorry, no native_decide,
no `interval` tactic, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-19.
-/
import PF.Analytic.Lambda0IBP2Combined_2026_10_18
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable

set_option autoImplicit false

namespace PrincipiaTractalis
namespace ThetaBoundaryConstant20261019

open Real MeasureTheory Set
open PrincipiaTractalis.XiThetaIntegral
open PrincipiaTractalis.OmegaDerivative20261014
open PrincipiaTractalis.OmegaSecondDerivative20261018
open PrincipiaTractalis.FPlusSecondDerivative20261018
open PrincipiaTractalis.FMinusSecondIBP20261018
open PrincipiaTractalis.Lambda0IBP2Combined20261018

noncomputable section

/-! ## §1 — The bridge: `jacobiTheta (i·x) = 1 + 2·ω(x)`. -/

/-- `(Complex.I * x).im = x`. -/
lemma im_I_mul (x : ℝ) : (Complex.I * (x : ℂ)).im = x := by simp

/-- Termwise: `exp(π i (n+1)² (i x)) = exp(−π(n+1)²x)`. -/
lemma theta_summand_eq (n : ℕ) (x : ℝ) :
    Complex.exp ((Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1) ^ 2 * (Complex.I * (x : ℂ)))
      = ((Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x) : ℝ) : ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  rw [show (Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1) ^ 2 * (Complex.I * (x : ℂ))
      = (Complex.I * Complex.I) * ((Real.pi : ℂ) * ((n : ℂ) + 1) ^ 2 * (x : ℂ)) from by ring,
    Complex.I_mul_I]
  push_cast
  ring

/-- **★ The bridge ★** `jacobiTheta (i·x) = 1 + 2·ω(x)` for `x > 0`. -/
theorem jacobiTheta_I_mul_eq {x : ℝ} (hx : 0 < x) :
    jacobiTheta (Complex.I * (x : ℂ)) = 1 + 2 * ((omega x : ℝ) : ℂ) := by
  have him : 0 < (Complex.I * (x : ℂ)).im := by rw [im_I_mul]; exact hx
  rw [jacobiTheta_eq_tsum_nat him]
  congr 1
  rw [show (fun n : ℕ =>
      Complex.exp ((Real.pi : ℂ) * Complex.I * ((n : ℂ) + 1) ^ 2 * (Complex.I * (x : ℂ))))
      = (fun n : ℕ => ((Real.exp (-π * ((n : ℝ) + 1) ^ 2 * x) : ℝ) : ℂ)) from
    funext fun n => theta_summand_eq n x]
  rw [← Complex.ofReal_tsum]
  rfl

/-! ## §2 — The functional equation, as a real identity. -/

/-- `(-(i·x))⁻¹ = i·(1/x)`. -/
lemma neg_inv_I_mul {x : ℝ} (hx : 0 < x) :
    (-(Complex.I * (x : ℂ)))⁻¹ = Complex.I * ((1 / x : ℝ) : ℂ) := by
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  push_cast
  field_simp
  rw [Complex.I_sq]

/-- `(-i·(i·x))^(1/2) = √x` as a complex number, for `x > 0`. -/
lemma cpow_half_eq_sqrt {x : ℝ} (hx : 0 < x) :
    (-Complex.I * (Complex.I * (x : ℂ))) ^ (1 / 2 : ℂ) = ((Real.sqrt x : ℝ) : ℂ) := by
  have hrw : -Complex.I * (Complex.I * (x : ℂ)) = ((x : ℝ) : ℂ) := by
    rw [show -Complex.I * (Complex.I * (x : ℂ))
        = -(Complex.I * Complex.I) * (x : ℂ) from by ring, Complex.I_mul_I]
    ring
  rw [hrw, Real.sqrt_eq_rpow, Complex.ofReal_cpow hx.le]
  norm_num

/-- `jacobiTheta_S_smul` with the `UpperHalfPlane` wrapper discharged, so the
statement is about a bare `z : ℂ` and later rewrites can match it. -/
lemma theta_S_at {z : ℂ} (hz : 0 < z.im) :
    jacobiTheta (-z)⁻¹ = (-Complex.I * z) ^ (1 / 2 : ℂ) * jacobiTheta z := by
  have hS := jacobiTheta_S_smul (⟨z, hz⟩ : UpperHalfPlane)
  rw [UpperHalfPlane.modular_S_smul] at hS
  exact hS

/-- **★ The functional equation, real form ★**
`1 + 2ω(1/x) = √x·(1 + 2ω(x))` for `x > 0`. -/
theorem omega_functional_equation {x : ℝ} (hx : 0 < x) :
    1 + 2 * omega (1 / x) = Real.sqrt x * (1 + 2 * omega x) := by
  have hinv : 0 < 1 / x := by positivity
  have him : 0 < (Complex.I * (x : ℂ)).im := by rw [im_I_mul]; exact hx
  have hS := theta_S_at him
  rw [neg_inv_I_mul hx, jacobiTheta_I_mul_eq hinv, jacobiTheta_I_mul_eq hx,
    cpow_half_eq_sqrt hx] at hS
  exact_mod_cast hS

/-! ## §3 — Differentiate at `x = 1`. -/

/-- **★ `ω′(1) = −(1 + 2ω(1))/8` ★** -/
theorem omega'_one_eq : omega' 1 = -(1 + 2 * omega 1) / 8 := by
  -- the two sides of the functional equation, as functions
  set L : ℝ → ℝ := fun x => 1 + 2 * omega (1 / x) with hL
  set R : ℝ → ℝ := fun x => Real.sqrt x * (1 + 2 * omega x) with hR
  -- they agree on a neighbourhood of 1
  have hEq : L =ᶠ[nhds (1 : ℝ)] R := by
    filter_upwards [eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)] with y hy
    exact omega_functional_equation hy
  -- derivative of L at 1
  have hinvd : HasDerivAt (fun x : ℝ => 1 / x) (-1) 1 := by
    have h := hasDerivAt_inv (by norm_num : (1 : ℝ) ≠ 0)
    simpa using h
  have homega1 : HasDerivAt omega (omega' 1) (1 / 1 : ℝ) := by
    norm_num
    exact omega_hasDerivAt (by norm_num)
  have hLd : HasDerivAt L (2 * (omega' 1 * (-1))) 1 := by
    have hcomp : HasDerivAt (fun x : ℝ => omega (1 / x)) (omega' 1 * (-1)) 1 :=
      homega1.comp 1 hinvd
    have := (hcomp.const_mul (2 : ℝ)).const_add (1 : ℝ)
    simpa [hL] using this
  -- derivative of R at 1
  have hsq : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt 1)) 1 :=
    Real.hasDerivAt_sqrt (by norm_num)
  have hg : HasDerivAt (fun x : ℝ => 1 + 2 * omega x) (2 * omega' 1) 1 := by
    have := ((omega_hasDerivAt (by norm_num : (0:ℝ) < 1)).const_mul (2 : ℝ)).const_add (1 : ℝ)
    simpa using this
  have hRd : HasDerivAt R
      (1 / (2 * Real.sqrt 1) * (1 + 2 * omega 1) + Real.sqrt 1 * (2 * omega' 1)) 1 :=
    hsq.mul hg
  -- transport and equate
  have hLd' : HasDerivAt R (2 * (omega' 1 * (-1))) 1 := hLd.congr_of_eventuallyEq hEq.symm
  have hkey := hLd'.unique hRd
  rw [Real.sqrt_one] at hkey
  linarith [hkey]

/-! ## §4 — The boundary constant. -/

/-- **★ THE CONSTANT: `ω(1)/2 + 2ω′(1) = −1/4` ★**

Previously measured at `−0.2500000000000001`; now a theorem. -/
theorem boundary_const_eq_neg_quarter : omega 1 / 2 + 2 * omega' 1 = -1 / 4 := by
  rw [omega'_one_eq]
  ring

/-! ## §5 — The sharp Tier-3 identity. -/

/-- `1/(i·t/2)² = −4/t²` as complex numbers, for `t ≠ 0`. -/
theorem inv_phase_sq_eq {t : ℝ} (ht : t ≠ 0) :
    (1 : ℂ) / (Complex.I * ((t : ℂ) / 2)) ^ 2 = -(4 / (t : ℂ) ^ 2) := by
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [phase_sq_eq]
  field_simp

/-- **★ THE SHARP TIER-3 IDENTITY ★**

`Λ₀(1+it) = 1/t² − (4/t²)·(I₊ + I₋)`.

The boundary constant is now `−1/4` exactly (§4), so the leading coefficient of
`Λ₀` on the edge is **exactly 1**, not merely `O(t⁻²)`. -/
theorem lambda0_edge_ibp2_identity_sharp {t : ℝ} (ht : t ≠ 0) :
    completedRiemannZeta₀ (⟨1, t⟩ : ℂ)
      = 1 / (t : ℂ) ^ 2
        - (4 / (t : ℂ) ^ 2)
            * ((∫ u in Ioi (0 : ℝ),
                  ((F_plus'' u : ℝ) : ℂ)
                    * Complex.exp (Complex.I * ((t : ℂ) / 2) * (u : ℂ)))
               + (∫ u in Ioi (0 : ℝ),
                  ((F_minus'' u : ℝ) : ℂ)
                    * Complex.exp (-(Complex.I * ((t : ℂ) / 2)) * (u : ℂ)))) := by
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [lambda0_edge_ibp2_identity ht]
  have hconst : ((omega 1 / 2 + 2 * omega' 1 : ℝ) : ℂ) = (-1 / 4 : ℂ) := by
    rw [boundary_const_eq_neg_quarter]
    norm_num
  rw [hconst, inv_phase_sq_eq ht]
  field_simp
  ring

end

end ThetaBoundaryConstant20261019
end PrincipiaTractalis

/-! ## §Axiom check -/
#print axioms PrincipiaTractalis.ThetaBoundaryConstant20261019.theta_summand_eq
#print axioms PrincipiaTractalis.ThetaBoundaryConstant20261019.jacobiTheta_I_mul_eq
#print axioms PrincipiaTractalis.ThetaBoundaryConstant20261019.cpow_half_eq_sqrt
#print axioms PrincipiaTractalis.ThetaBoundaryConstant20261019.theta_S_at
#print axioms PrincipiaTractalis.ThetaBoundaryConstant20261019.omega_functional_equation
#print axioms PrincipiaTractalis.ThetaBoundaryConstant20261019.omega'_one_eq
#print axioms PrincipiaTractalis.ThetaBoundaryConstant20261019.boundary_const_eq_neg_quarter
#print axioms PrincipiaTractalis.ThetaBoundaryConstant20261019.lambda0_edge_ibp2_identity_sharp
