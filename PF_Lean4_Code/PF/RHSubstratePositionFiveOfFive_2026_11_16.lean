import PF.RHSubstratePositionFourthIngredientDischarge_2026_11_16
import PF.DirichletEtaConditionalConvergenceComplex_r277

/-!
# RH substrate attack — 5 of 5 Dirichlet-1858 sub-ingredients bundled

Closes open-item 3 of `PF/DirichletChainStatus_2026_11_16.lean`.

Extends `rh_substrate_attack_HEAD_bundle_EXTENDED2_2026_11_16` by one
conjunct: ingredient (2), the abscissa of conditional convergence for
`η` on `0 < re s`. That ingredient was discharged kernel-clean in r276
+ r277 but was not yet composed into the substrate-attack bundle.

Adding it bumps the sub-ingredient count from 4/5 to 5/5.

Three-axiom bar `[propext, Classical.choice, Quot.sound]`.
-/

namespace PF.RHSubstratePositionFiveOfFive

open PF.RHSubstratePositionFourthIngredientDischarge
  (rh_substrate_attack_HEAD_bundle_EXTENDED2_2026_11_16)
open PF.RHSubstratePositionStrengthening
  (RH_FrontierExtensionViaSigmaResidual_SubstantiveCore
   substantive_core_strictly_stronger_than_structural_tag
   rh_frontier_extension_residual_trivial_discharge)
open PF.RHSubstratePositionPartialDischarge
  (RH_SubstantiveCore_AbelBridgeIngredient_Closed
   rh_substantive_partial_discharge_abel_bridge)
open PF.RHSubstratePositionExtendedPartialDischarge
  (RH_SubstantiveCore_AnalyticContinuationIngredient_Closed
   RH_SubstantiveCore_IdentityTheoremTemplate_Closed
   rh_substantive_partial_discharge_analytic_continuation
   rh_substantive_partial_discharge_identity_theorem_template)
open PF.RHSubstratePositionFourthIngredientDischarge
  (RH_SubstantiveCore_FourthIngredientAtHalf_Closed
   rh_substantive_partial_discharge_fourth_ingredient_at_half)
open PF.RHSubstratePositionViaSigma (RH_FrontierExtensionViaSigmaResidual)
open PrincipiaTractalis.DirichletEtaConditionalConvergenceComplex
  (dirichletEta_lseries_partial_cauchy
   dirichletEta_conditionalConvergence_complexOffReal_discharged)

/-! ## §1 — The abscissa sub-ingredient as a substrate-attack Prop. -/

/-- The (2) sub-ingredient of the Dirichlet-1858 chain: the Cauchy
    criterion for the LSeries partial sums of `dirichletEta` on
    `0 < re s`, i.e. the abscissa of conditional convergence is `0`. -/
def RH_SubstantiveCore_AbscissaIngredient_Closed : Prop :=
  ∀ {s : ℂ}, 0 < s.re →
    CauchySeq (fun N : ℕ =>
      ∑ n ∈ Finset.range N,
        LSeries.term PrincipiaTractalis.DirichletEtaComplex.dirichletEtaCoeff s n)

/-- Kernel-clean discharge via r277. -/
theorem rh_substantive_partial_discharge_abscissa :
    RH_SubstantiveCore_AbscissaIngredient_Closed :=
  @dirichletEta_lseries_partial_cauchy

/-! ## §2 — The 5-of-5 bundle. -/

/-- **`rh_substrate_attack_HEAD_bundle_5_of_5_2026_11_16`** —
    seven-conjunct bundle extending the EXTENDED2 bundle with the
    abscissa sub-ingredient:

      (1) Structural tag discharged.
      (2) Abel bridge CLOSED (r275).
      (3) Analytic continuation CLOSED (r279).
      (4-template) Identity-theorem template CLOSED (r279).
      (4-construction-at-half) Point closure at s = 1/2 CLOSED (r270).
      (5) **Abscissa of conditional convergence CLOSED (r277).**
      (6) Substantive-core → structural tag (logical ordering).

    The abscissa sub-ingredient was discharged kernel-clean in r276 +
    r277 but had not been composed into the substrate-attack bundle.
    This file composes it in.

    All 5 of 5 classical Dirichlet-1858 sub-ingredients are now
    kernel-clean at the substrate-attack layer. -/
theorem rh_substrate_attack_HEAD_bundle_5_of_5_2026_11_16 :
    RH_FrontierExtensionViaSigmaResidual ∧
    RH_SubstantiveCore_AbelBridgeIngredient_Closed ∧
    RH_SubstantiveCore_AnalyticContinuationIngredient_Closed ∧
    RH_SubstantiveCore_IdentityTheoremTemplate_Closed ∧
    RH_SubstantiveCore_FourthIngredientAtHalf_Closed ∧
    RH_SubstantiveCore_AbscissaIngredient_Closed ∧
    (RH_FrontierExtensionViaSigmaResidual_SubstantiveCore
      → RH_FrontierExtensionViaSigmaResidual) :=
  ⟨rh_frontier_extension_residual_trivial_discharge,
   rh_substantive_partial_discharge_abel_bridge,
   rh_substantive_partial_discharge_analytic_continuation,
   rh_substantive_partial_discharge_identity_theorem_template,
   rh_substantive_partial_discharge_fourth_ingredient_at_half,
   rh_substantive_partial_discharge_abscissa,
   substantive_core_strictly_stronger_than_structural_tag⟩

/-! ## §3 — Axiom audit. -/

#print axioms RH_SubstantiveCore_AbscissaIngredient_Closed
#print axioms rh_substantive_partial_discharge_abscissa
#print axioms rh_substrate_attack_HEAD_bundle_5_of_5_2026_11_16

end PF.RHSubstratePositionFiveOfFive
