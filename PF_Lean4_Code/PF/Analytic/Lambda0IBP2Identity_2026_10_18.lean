/-
# PF.Analytic.Lambda0IBP2Identity_2026_10_18

**The second integration by parts, and the `1/c²` decay.**

`ibp_phase` (`Lambda0IBPIdentity_2026_10_15:306`) applied a **second** time, at
`F := deriv F_plus`, `F′ := deriv (deriv F_plus)`. All six of its hypotheses
were assembled in `FPlusSecondIBPRows_2026_10_18` and `…SecondDerivative…`:

| hypothesis | source |
|---|---|
| `hc`, `hcre` | `phase_plus_ne_zero`, `re_phase_plus` |
| `hFderiv` | `hasDerivAt_deriv_F_plus` |
| `hFcont0` | `continuousWithinAt_deriv_F_plus_zero` |
| `hFtop` | `tendsto_deriv_F_plus_atTop_zero` |
| `hFint` | `integrableOn_deriv_F_plus` (2026-10-15) |
| `hF'int` | `integrableOn_deriv_deriv_F_plus` (stage 3) |

### What the decay claim is, precisely

The first IBP leaves a remainder carrying `1/c`; the second leaves one carrying
`1/c²`. With `c = i·t/2` that is `‖1/c²‖ = 4/t²`, against `‖1/c‖ = 2/t` —
**one extra power of `t`**, which is the entire purpose of iterating.

`norm_ibp2_remainder_le` states it: the remainder is bounded by
`(4/t²) · ∫_{Ioi 0} |F₊″|`, where the integral is a finite constant
**independent of `t`** (finite by stage 3's `F_plus''_integrable_Ioi`).

**Measured confirmation** (`codex/ibp2_decay_verify.py`), with
`R₁ = ‖(1/c)∫F₊′e^{cu}‖` and `R₂ = ‖(1/c²)∫F₊″e^{cu}‖`:

| t | `R₁` | `R₂` | `t·R₂/R₁` |
|---|---|---|---|
| 10 | 4.960e−3 | 2.008e−3 | 4.05 |
| 20 | 1.171e−3 | 1.776e−4 | 3.03 |
| 40 | 2.872e−4 | 2.111e−5 | 2.94 |
| 80 | 7.147e−5 | 2.608e−6 | 2.92 |

`t·R₂/R₁` settles to a constant, i.e. `R₂/R₁ ~ 2.92/t`. `R₁ ~ t⁻²` and
`R₂ ~ t⁻³`. **The decay materialises.**

### One thing deliberately not claimed

Numerically `∫_{Ioi 0}|F₊″| = 0.1141956486`, which is exactly
`−(deriv F_plus 0) = −(ω(1)/2 + ω′(1))`. That is not a coincidence: it would
follow from `F₊″ ≥ 0` — the convexity of `F₊` — via the fundamental theorem on
`Ioi 0`. **But `F₊″ ≥ 0` is measured, not proved**, and Route 2 was chosen
precisely to avoid needing it (the pre-flight priced the sign lemma at
200–400 L). So the bound here keeps `∫|F₊″|` abstract. Sharpening it to the
exact constant is exactly as expensive as Route 1 would have been.

Three-axiom bar: every top-level declaration prints
`[propext, Classical.choice, Quot.sound]`. No sorry, no native_decide,
no `interval` tactic, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-18.
-/
import PF.Analytic.FPlusSecondIBPRows_2026_10_18
import PF.Analytic.Lambda0IBPIdentity_2026_10_15

set_option autoImplicit false

namespace PrincipiaTractalis
namespace Lambda0IBP2Identity20261018

open Real MeasureTheory Set Topology Filter
open PrincipiaTractalis.XiThetaIntegral
open PrincipiaTractalis.OmegaDerivative20261014
open PrincipiaTractalis.OmegaSecondDerivative20261018
open PrincipiaTractalis.FPlusSecondDerivative20261018
open PrincipiaTractalis.FPlusSecondIBPRows20261018
open PrincipiaTractalis.Lambda0IBPIdentity20261015

noncomputable section

/-! ## §1 — The second integration by parts on the `+` branch. -/

/-- **★ Second IBP, plus branch ★**

`∫ (deriv F₊)·e^{cu} = −(ω(1)/2 + ω′(1))/c − (1/c)∫ F₊″·e^{cu}`,
with `c = i·t/2`.

Substituted into `ibp_F_plus_branch`, the `F₊″` remainder acquires `1/c²`. -/
theorem ibp2_F_plus_branch {t : ℝ} (ht : t ≠ 0) :
    (∫ u in Ioi (0 : ℝ),
        ((deriv F_plus u : ℝ) : ℂ) * Complex.exp (Complex.I * ((t : ℂ) / 2) * (u : ℂ)))
      = -(((omega 1 / 2 + omega' 1 : ℝ) : ℂ) / (Complex.I * ((t : ℂ) / 2)))
        - (1 / (Complex.I * ((t : ℂ) / 2)))
            * ∫ u in Ioi (0 : ℝ),
                ((F_plus'' u : ℝ) : ℂ)
                  * Complex.exp (Complex.I * ((t : ℂ) / 2) * (u : ℂ)) := by
  have h := ibp_phase (F := deriv F_plus) (F' := deriv (deriv F_plus))
    (phase_plus_ne_zero ht) (re_phase_plus t)
    (fun x hx => hasDerivAt_deriv_F_plus x hx)
    continuousWithinAt_deriv_F_plus_zero
    tendsto_deriv_F_plus_atTop_zero
    (integrableOn_phase_of_integrableOn (re_phase_plus t) integrableOn_deriv_F_plus)
    (integrableOn_phase_of_integrableOn (re_phase_plus t)
      integrableOn_deriv_deriv_F_plus)
  rw [deriv_deriv_F_plus_eq] at h
  rw [deriv_F_plus_zero] at h
  exact h

/-! ## §2 — The decay: the remainder carries `1/c²`, i.e. `4/t²`. -/

/-- `‖1/(i·t/2)²‖ = 4/t²`. -/
theorem norm_inv_phase_sq {t : ℝ} (_ht : t ≠ 0) :
    ‖(1 : ℂ) / (Complex.I * ((t : ℂ) / 2)) ^ 2‖ = 4 / t ^ 2 := by
  have hphase : ‖Complex.I * ((t : ℂ) / 2)‖ = |t| / 2 := by
    rw [norm_mul, Complex.norm_I, one_mul, norm_div, Complex.norm_real,
      Real.norm_eq_abs]
    simp
  rw [norm_div, norm_one, norm_pow, hphase]
  rw [div_pow, sq_abs]
  rw [one_div_div]
  norm_num

/-- **★ The decay materialises ★**

The second-IBP remainder is bounded by `(4/t²) · ∫_{Ioi 0}|F₊″|`, where the
integral is finite (stage 3) and **independent of `t`**. Against the first
IBP's `‖1/c‖ = 2/t`, that is one extra power of `t`. -/
theorem norm_ibp2_remainder_le {t : ℝ} (ht : t ≠ 0) :
    ‖(1 / (Complex.I * ((t : ℂ) / 2)) ^ 2)
        * ∫ u in Ioi (0 : ℝ),
            ((F_plus'' u : ℝ) : ℂ)
              * Complex.exp (Complex.I * ((t : ℂ) / 2) * (u : ℂ))‖
      ≤ (4 / t ^ 2) * ∫ u in Ioi (0 : ℝ), |F_plus'' u| := by
  have hcre := re_phase_plus t
  -- the integrand's norm is |F₊″| pointwise, the phase having modulus 1
  have hptwise : ∀ u : ℝ,
      ‖((F_plus'' u : ℝ) : ℂ) * Complex.exp (Complex.I * ((t : ℂ) / 2) * (u : ℂ))‖
        = |F_plus'' u| := by
    intro u
    rw [norm_mul, norm_exp_mul_ofReal hcre, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
  -- ‖∫ ...‖ ≤ ∫ ‖...‖ = ∫ |F₊″|
  have hle : ‖∫ u in Ioi (0 : ℝ),
        ((F_plus'' u : ℝ) : ℂ) * Complex.exp (Complex.I * ((t : ℂ) / 2) * (u : ℂ))‖
      ≤ ∫ u in Ioi (0 : ℝ), |F_plus'' u| := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    exact le_of_eq (integral_congr_ae (Filter.Eventually.of_forall hptwise))
  have hInn : (0 : ℝ) ≤ ∫ u in Ioi (0 : ℝ), |F_plus'' u| :=
    integral_nonneg fun u => abs_nonneg _
  rw [norm_mul, norm_inv_phase_sq ht]
  have hfacnn : (0 : ℝ) ≤ 4 / t ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_left hle hfacnn

/-- For contrast, the first-IBP prefactor: `‖1/(i·t/2)‖ = 2/|t|`. -/
theorem norm_inv_phase {t : ℝ} (_ht : t ≠ 0) :
    ‖(1 : ℂ) / (Complex.I * ((t : ℂ) / 2))‖ = 2 / |t| := by
  have hphase : ‖Complex.I * ((t : ℂ) / 2)‖ = |t| / 2 := by
    rw [norm_mul, Complex.norm_I, one_mul, norm_div, Complex.norm_real,
      Real.norm_eq_abs]
    simp
  rw [norm_div, norm_one, hphase, one_div_div]

end

end Lambda0IBP2Identity20261018
end PrincipiaTractalis

/-! ## §Axiom check -/
#print axioms PrincipiaTractalis.Lambda0IBP2Identity20261018.ibp2_F_plus_branch
#print axioms PrincipiaTractalis.Lambda0IBP2Identity20261018.norm_inv_phase_sq
#print axioms PrincipiaTractalis.Lambda0IBP2Identity20261018.norm_ibp2_remainder_le
#print axioms PrincipiaTractalis.Lambda0IBP2Identity20261018.norm_inv_phase
