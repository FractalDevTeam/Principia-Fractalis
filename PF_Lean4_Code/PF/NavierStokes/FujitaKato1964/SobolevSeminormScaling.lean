/-
# Fujita-Kato 1964 — Sobolev Seminorm Scaling Identity

★ 2026-06-10 — Second brick of real Fujita-Kato infrastructure.

Adds the small-data scaling identity to the homogeneous `Ḣ^{1/2}`
seminorm squared:

  ‖c • f‖²_{Ḣ^{1/2}} = ‖c‖² · ‖f‖²_{Ḣ^{1/2}}

The Fujita-Kato 1964 contraction argument requires precisely this:
shrinking the initial data shrinks the Sobolev seminorm
quadratically, which is what makes the small-data ball contract
under the Picard iteration.

Builds on `PF/NavierStokes/FujitaKato1964/SobolevSeminormFourier.lean`.

Scope: scalar (`ℂ`-valued) Schwartz on `EuclideanSpace ℝ (Fin 3)`.

Axiom-free: depends on `[propext, Classical.choice, Quot.sound]` only.

Author: Pablo Cohen (2026-06-10)
-/

import PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier

set_option autoImplicit false

namespace PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier

open MeasureTheory SchwartzMap

/-! ## §1 — Pointwise scaling of the integrand -/

/-- **Pointwise scaling of the Sobolev integrand**: at every frequency ξ,

  `|ξ| · |F(c • f)(ξ)|² = ‖c‖² · |ξ| · |F(f)(ξ)|²`

This is the algebraic core of the small-data scaling. Uses Fourier
linearity and the norm-of-scalar-multiplication identity. -/
theorem h12IntegrandSq_smul (c : ℂ) (f : ScalarSchwartz3C) (ξ : R3) :
    h12IntegrandSq (c • f) ξ = ‖c‖ ^ 2 * h12IntegrandSq f ξ := by
  unfold h12IntegrandSq
  -- Fourier transform (as a continuous linear map) commutes with scalar
  -- multiplication: F(c • f) = c • F(f).
  rw [map_smul]
  -- Evaluating the scaled Schwartz function at ξ: (c • g) ξ = c • g ξ.
  rw [SchwartzMap.smul_apply]
  -- The norm of a scalar multiple: ‖c • x‖ = ‖c‖ * ‖x‖.
  rw [norm_smul]
  -- Algebraic rearrangement: ‖ξ‖ · (‖c‖ · ‖_‖)² = ‖c‖² · (‖ξ‖ · ‖_‖²).
  ring

/-! ## §2 — Scaling identity for the seminorm squared -/

/-- **Scaling identity for the homogeneous Ḣ^{1/2} seminorm squared.**

  `‖c • f‖²_{Ḣ^{1/2}} = ‖c‖² · ‖f‖²_{Ḣ^{1/2}}`

This is the small-data property required by the Fujita-Kato 1964
contraction proof: scaling the initial data by `c` scales the Sobolev
norm squared by `‖c‖²`, so for small `c` the contraction shrinks the
ball at the rate the bilinear estimate needs. -/
theorem homogeneousH12SeminormSq_smul (c : ℂ) (f : ScalarSchwartz3C) :
    homogeneousH12SeminormSq (c • f) = ‖c‖ ^ 2 * homogeneousH12SeminormSq f := by
  unfold homogeneousH12SeminormSq
  calc ∫ ξ : R3, h12IntegrandSq (c • f) ξ
      = ∫ ξ : R3, ‖c‖ ^ 2 * h12IntegrandSq f ξ := by
        congr 1
        ext ξ
        exact h12IntegrandSq_smul c f ξ
    _ = ‖c‖ ^ 2 * ∫ ξ : R3, h12IntegrandSq f ξ :=
        MeasureTheory.integral_const_mul _ _

/-! ## §3 — Scaling capstone -/

/-- **★ Sobolev seminorm scaling brick capstone ★**

Bundles:

  (a) Pointwise scaling: `h12IntegrandSq (c • f) ξ = ‖c‖² · h12IntegrandSq f ξ`
  (b) Integrated-seminorm scaling:
      `homogeneousH12SeminormSq (c • f) = ‖c‖² · homogeneousH12SeminormSq f`

Together with the non-negativity and zero-on-zero results from
`SobolevSeminormFourier.lean`, this gives the algebraic shell of a
homogeneous seminorm needed by Fujita-Kato 1964. -/
theorem fujitaKato_sobolev_seminorm_scaling_capstone :
    (∀ (c : ℂ) (f : ScalarSchwartz3C) (ξ : R3),
       h12IntegrandSq (c • f) ξ = ‖c‖ ^ 2 * h12IntegrandSq f ξ) ∧
    (∀ (c : ℂ) (f : ScalarSchwartz3C),
       homogeneousH12SeminormSq (c • f) = ‖c‖ ^ 2 * homogeneousH12SeminormSq f) :=
  ⟨h12IntegrandSq_smul, homogeneousH12SeminormSq_smul⟩

/-! ## §4 — Axiom audit -/

#print axioms h12IntegrandSq_smul
#print axioms homogeneousH12SeminormSq_smul
#print axioms fujitaKato_sobolev_seminorm_scaling_capstone

end PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier
