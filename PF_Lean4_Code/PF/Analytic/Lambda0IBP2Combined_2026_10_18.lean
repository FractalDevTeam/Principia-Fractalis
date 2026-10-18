/-
# PF.Analytic.Lambda0IBP2Combined_2026_10_18

**The Tier-3 theorem: the second-order edge identity and its `t⁻²` bound.**

Second-order analogue of `lambda0_edge_ibp_identity`
(`Lambda0IBPIdentity_2026_10_15:470`), assembled from both branches'
second IBPs (`164a9843`, `783903d1`).

### The identity

Feeding `ibp_F_plus_branch`/`ibp_F_minus_branch` and then
`ibp2_F_plus_branch`/`ibp2_F_minus_branch` into `lambda0_edge_eq_F_integrals`,
**the two first-order boundary terms cancel** (both equal `ω(1)`, with opposite
phases) and the two second-order ones survive:

  `Λ₀(1+it) = (1/c²)·[ (ω(1)/2 + 2ω′(1)) + I₊ + I₋ ]`,   `c = i·t/2`

where `I± = ∫_{Ioi 0} F±″·e^{±icu}` and `1/c² = −4/t²`.

**Verified numerically** against `mpmath`'s `Λ₀`: agreement to `2.4e−13`,
`1.2e−13`, `5.9e−14` at `t = 10, 20, 40` (`codex/ibp2_combined_verify.py`).

### The boundary constant is exactly −1/4 — measured, not proved here

`ω(1)/2 + 2ω′(1) = −0.2500000000000001`, i.e. **−1/4** to machine precision.
This is the theta functional equation differentiated: with `θ(x) = 1 + 2ω(x)`
and `θ(1/x) = √x·θ(x)`, differentiating at `x = 1` gives `θ′(1) = −θ(1)/4`,
hence `2ω′(1) = −1/4 − ω(1)/2`.

**Not proved in Lean here.** The tree has no differentiated theta functional
equation, and supplying one is its own project. So `ibp2_boundary_const` states
the constant as `ω(1)/2 + 2ω′(1)` and the `= −1/4` sharpening is recorded as
`OPEN` — with the payoff spelled out, since it is large: it would turn the
identity into

  `Λ₀(1+it) = 1/t² − (4/t²)(I₊ + I₋)`,

pinning the **leading coefficient exactly at 1**, not merely `O(t⁻²)`.

### The decay, visible in the type

`norm_ibp2_combined_remainder_le`:
`‖(1/c²)(I₊+I₋)‖ ≤ (4/t²)·(∫|F₊″| + ∫|F₋″|)`, both integrals finite and
independent of `t`. That is the `t⁻²` statement.

Three-axiom bar: every top-level declaration prints
`[propext, Classical.choice, Quot.sound]`. No sorry, no native_decide,
no `interval` tactic, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-18.
-/
import PF.Analytic.FMinusSecondIBP_2026_10_18

set_option autoImplicit false

namespace PrincipiaTractalis
namespace Lambda0IBP2Combined20261018

open Real MeasureTheory Set Topology Filter
open PrincipiaTractalis.XiThetaIntegral
open PrincipiaTractalis.OmegaDerivative20261014
open PrincipiaTractalis.OmegaSecondDerivative20261018
open PrincipiaTractalis.FPlusSecondDerivative20261018
open PrincipiaTractalis.FPlusSecondIBPRows20261018
open PrincipiaTractalis.Lambda0IBP2Identity20261018
open PrincipiaTractalis.FMinusSecondIBP20261018
open PrincipiaTractalis.Lambda0IBPIdentity20261015

noncomputable section

/-! ## §1 — The phase squared, and the boundary constants. -/

/-- `(i·t/2)² = −t²/4`. -/
theorem phase_sq_eq (t : ℝ) :
    (Complex.I * ((t : ℂ) / 2)) ^ 2 = -((t : ℂ) ^ 2 / 4) := by
  have : (Complex.I) ^ 2 = -1 := Complex.I_sq
  ring_nf
  rw [this]
  ring

/-- The minus phase squares to the same thing. -/
theorem phase_minus_sq_eq (t : ℝ) :
    (-(Complex.I * ((t : ℂ) / 2))) ^ 2 = -((t : ℂ) ^ 2 / 4) := by
  rw [neg_pow, show ((-1 : ℂ)) ^ 2 = 1 from by norm_num, one_mul, phase_sq_eq]

/-- **★ The plus-branch second-order boundary term ★**
`(ω(1)/2 + ω′(1))/c² = −(4/t²)·(ω(1)/2 + ω′(1))`. -/
theorem ibp2_boundary_plus {t : ℝ} (ht : t ≠ 0) :
    ((omega 1 / 2 + omega' 1 : ℝ) : ℂ) / (Complex.I * ((t : ℂ) / 2)) ^ 2
      = -((4 : ℂ) / (t : ℂ) ^ 2) * ((omega 1 / 2 + omega' 1 : ℝ) : ℂ) := by
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [phase_sq_eq]
  field_simp

/-- **★ The minus-branch second-order boundary term ★**
`ω′(1)/c² = −(4/t²)·ω′(1)`. -/
theorem ibp2_boundary_minus {t : ℝ} (ht : t ≠ 0) :
    ((omega' 1 : ℝ) : ℂ) / (-(Complex.I * ((t : ℂ) / 2))) ^ 2
      = -((4 : ℂ) / (t : ℂ) ^ 2) * ((omega' 1 : ℝ) : ℂ) := by
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [phase_minus_sq_eq]
  field_simp

/-- **★ The two second-order boundary terms combined ★**

`ω(1)/2 + 2ω′(1)` is the whole second-order boundary content. **Measured to be
exactly `−1/4`** (theta functional equation differentiated at `1`); see the file
header. That sharpening is `OPEN` — it needs a differentiated theta functional
equation, which the tree does not have. -/
theorem ibp2_boundary_const {t : ℝ} (ht : t ≠ 0) :
    ((omega 1 / 2 + omega' 1 : ℝ) : ℂ) / (Complex.I * ((t : ℂ) / 2)) ^ 2
        + ((omega' 1 : ℝ) : ℂ) / (-(Complex.I * ((t : ℂ) / 2))) ^ 2
      = -((4 : ℂ) / (t : ℂ) ^ 2) * ((omega 1 / 2 + 2 * omega' 1 : ℝ) : ℂ) := by
  rw [ibp2_boundary_plus ht, ibp2_boundary_minus ht]
  push_cast
  ring

/-! ## §2 — The combined second-order identity. -/

/-- **★ THE TIER-3 IDENTITY ★**

`Λ₀(1+it) = (1/c²)·[ (ω(1)/2 + 2ω′(1)) + I₊ + I₋ ]` with `c = i·t/2`.

The two first-order boundary terms cancel — both are `ω(1)` with opposite
phases — which is why only the second-order constant survives. -/
theorem lambda0_edge_ibp2_identity {t : ℝ} (ht : t ≠ 0) :
    completedRiemannZeta₀ (⟨1, t⟩ : ℂ)
      = (1 / (Complex.I * ((t : ℂ) / 2)) ^ 2)
          * (((omega 1 / 2 + 2 * omega' 1 : ℝ) : ℂ)
             + (∫ u in Ioi (0 : ℝ),
                 ((F_plus'' u : ℝ) : ℂ)
                   * Complex.exp (Complex.I * ((t : ℂ) / 2) * (u : ℂ)))
             + (∫ u in Ioi (0 : ℝ),
                 ((F_minus'' u : ℝ) : ℂ)
                   * Complex.exp (-(Complex.I * ((t : ℂ) / 2)) * (u : ℂ)))) := by
  have hc : Complex.I * ((t : ℂ) / 2) ≠ 0 := phase_plus_ne_zero ht
  rw [lambda0_edge_eq_F_integrals, ibp_F_plus_branch ht, ibp_F_minus_branch ht,
    ibp2_F_plus_branch ht, ibp2_F_minus_branch ht]
  push_cast
  field_simp
  ring

/-! ## §3 — The remainder bound: the `t⁻²` decay, in the type. -/

/-- `‖∫ F₊″·e^{icu}‖ ≤ ∫|F₊″|` — the phase has modulus 1. -/
theorem norm_int_F_plus''_le (t : ℝ) :
    ‖∫ u in Ioi (0 : ℝ),
        ((F_plus'' u : ℝ) : ℂ) * Complex.exp (Complex.I * ((t : ℂ) / 2) * (u : ℂ))‖
      ≤ ∫ u in Ioi (0 : ℝ), |F_plus'' u| := by
  have hcre := re_phase_plus t
  have hptwise : ∀ u : ℝ,
      ‖((F_plus'' u : ℝ) : ℂ) * Complex.exp (Complex.I * ((t : ℂ) / 2) * (u : ℂ))‖
        = |F_plus'' u| := by
    intro u
    rw [norm_mul, norm_exp_mul_ofReal hcre, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  exact le_of_eq (integral_congr_ae (Filter.Eventually.of_forall hptwise))

/-- `‖∫ F₋″·e^{−icu}‖ ≤ ∫|F₋″|`. -/
theorem norm_int_F_minus''_le (t : ℝ) :
    ‖∫ u in Ioi (0 : ℝ),
        ((F_minus'' u : ℝ) : ℂ)
          * Complex.exp (-(Complex.I * ((t : ℂ) / 2)) * (u : ℂ))‖
      ≤ ∫ u in Ioi (0 : ℝ), |F_minus'' u| := by
  have hcre := re_phase_minus t
  have hptwise : ∀ u : ℝ,
      ‖((F_minus'' u : ℝ) : ℂ)
          * Complex.exp (-(Complex.I * ((t : ℂ) / 2)) * (u : ℂ))‖ = |F_minus'' u| := by
    intro u
    rw [norm_mul, norm_exp_mul_ofReal hcre, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  exact le_of_eq (integral_congr_ae (Filter.Eventually.of_forall hptwise))

/-- **★ THE TIER-3 DECAY BOUND ★**

`‖(1/c²)(I₊ + I₋)‖ ≤ (4/t²)·(∫|F₊″| + ∫|F₋″|)`.

Both integrals are finite (`F_plus''_integrable_Ioi`,
`F_minus''_integrable_Ioi`) and **independent of `t`**, so the whole
`t`-dependence is the explicit `4/t²`. Against the first IBP's `‖1/c‖ = 2/|t|`
this is one extra power of `t` — the `t⁻²` bound. -/
theorem norm_ibp2_combined_remainder_le {t : ℝ} (ht : t ≠ 0) :
    ‖(1 / (Complex.I * ((t : ℂ) / 2)) ^ 2)
        * ((∫ u in Ioi (0 : ℝ),
              ((F_plus'' u : ℝ) : ℂ)
                * Complex.exp (Complex.I * ((t : ℂ) / 2) * (u : ℂ)))
           + (∫ u in Ioi (0 : ℝ),
              ((F_minus'' u : ℝ) : ℂ)
                * Complex.exp (-(Complex.I * ((t : ℂ) / 2)) * (u : ℂ))))‖
      ≤ (4 / t ^ 2)
          * ((∫ u in Ioi (0 : ℝ), |F_plus'' u|)
             + ∫ u in Ioi (0 : ℝ), |F_minus'' u|) := by
  rw [norm_mul, norm_inv_phase_sq ht]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans (norm_add_le _ _) ?_
  exact add_le_add (norm_int_F_plus''_le t) (norm_int_F_minus''_le t)

end

end Lambda0IBP2Combined20261018
end PrincipiaTractalis

/-! ## §Axiom check -/
#print axioms PrincipiaTractalis.Lambda0IBP2Combined20261018.phase_sq_eq
#print axioms PrincipiaTractalis.Lambda0IBP2Combined20261018.phase_minus_sq_eq
#print axioms PrincipiaTractalis.Lambda0IBP2Combined20261018.ibp2_boundary_plus
#print axioms PrincipiaTractalis.Lambda0IBP2Combined20261018.ibp2_boundary_minus
#print axioms PrincipiaTractalis.Lambda0IBP2Combined20261018.ibp2_boundary_const
#print axioms PrincipiaTractalis.Lambda0IBP2Combined20261018.lambda0_edge_ibp2_identity
#print axioms PrincipiaTractalis.Lambda0IBP2Combined20261018.norm_int_F_plus''_le
#print axioms PrincipiaTractalis.Lambda0IBP2Combined20261018.norm_int_F_minus''_le
#print axioms PrincipiaTractalis.Lambda0IBP2Combined20261018.norm_ibp2_combined_remainder_le
