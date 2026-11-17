import PF.Dirichlet1858AbelBridge_r275
import PF.DirichletEtaConditionalConvergenceReal_r276
import PF.DirichletEtaConditionalConvergenceComplex_r277
import PF.DirichletEtaExtDifferentiable_r278
import PF.DirichletEtaIdentityTheorem_r279
import PF.DirichletEtaExtHalf_r270
import PF.DirichletEtaZetaIdentity_r268

/-!
# Dirichlet-1858 chain status checklist (2026-11-16)

Status of the six Dirichlet-1858 sub-ingredients that support the
RH substrate route. Each entry: file, discharging theorem (if any),
remaining open obligation (if any).

The `#check` statements below are compile-time verifiers: if any cited
theorem is renamed or removed, this file will fail to build.

## The six sub-ingredients

### (1) Abel bridge — s = 1/2 power-series limit matches product form.
- **File:** `PF/Dirichlet1858AbelBridge_r275.lean`
- **Theorem:** `abel_bridge_dirichletEtaHalf` [PROVED]
- **Named residual:** `Dirichlet1858_PowerSeriesLimit_EqualsProductForm` (hypothesis for chains)
- **Status:** [X] theorem discharged at s = 1/2. Named-residual composition routed through it.

### (2) Abscissa of conditional convergence for η on 0 < re s.
- **Files:** `PF/DirichletEtaConditionalConvergenceReal_r276.lean`,
            `PF/DirichletEtaConditionalConvergenceComplex_r277.lean`
- **Real-σ theorem:** `dirichletEta_lseries_partial_cauchy_real` [PROVED]
- **Complex theorem:** `dirichletEta_lseries_partial_cauchy` [PROVED]
- **Named discharge:** `dirichletEta_conditionalConvergence_complexOffReal_discharged` [PROVED]
- **Status:** [X] closed kernel-clean. Substrate-attack bundle
    `rh_substrate_attack_HEAD_bundle_EXTENDED2_2026_11_16` does not yet
    cite this discharge; see open-item 3 below.

### (3) Analytic continuation of η to ℂ \ {1}.
- **File:** `PF/DirichletEtaExtDifferentiable_r278.lean`
- **Theorem:** `dirichletEtaExt_differentiableOn_ne_one` [PROVED on ℂ \ {1}]
- **Theorem:** `dirichletEtaExt_differentiableOn_pos_re_ne_one` [PROVED]
- **Named residual (open):** `DirichletEtaExt_DifferentiableAtOne` — discharges the s = 1 case
- **Status:** [X] for s ≠ 1. Named residual at s = 1 remains for the full discharge.

### (4-template) Identity-theorem template.
- **File:** `PF/DirichletEtaIdentityTheorem_r279.lean`
- **Theorem:** `eqOn_dirichletEtaExt_of_analyticOnNhd_eventuallyEq` [PROVED]
- **Theorem:** `eqOn_dirichletEtaExt_of_analyticOnNhd_agrees_on_one_lt_re` [PROVED]
- **Named residual (open):** `DirichletEta_HasAnalyticExtension` — composes with (3) and r268
- **Status:** [X] template proved. Named residual open; see (4-construction-universal).

### (4-construction-at-half) Point closure at s = 1/2.
- **File:** `PF/DirichletEtaExtHalf_r270.lean`
- **Theorem:** `dirichletEtaExt_half_eq`:
    `dirichletEtaExt (1/2 : ℂ) = (1 - √2) · riemannZeta (1/2 : ℂ)` [PROVED]
- **Status:** [X] closed kernel-clean. Already in
    `rh_substrate_attack_HEAD_bundle_EXTENDED2_2026_11_16`.

### (4-construction-universal) Universal-s identity.
- **Theorem:**
    `dirichletEtaExt_eq_one_sub_two_cpow_mul_riemannZeta_universal`
    `: ∀ {s : ℂ}, s ≠ 1 → dirichletEtaExt s = (1 - 2^(1-s)) · riemannZeta s`
- **File:** `PF/DirichletEtaExtUniversalIdentity_2026_11_16.lean`
- **Commit:** `bb7ceaca`
- **Status:** [X] closed kernel-clean (2026-11-16). Composition of r268
    (identity on `1 < re s`) + r269 (`dirichletEtaExt = dirichletEta`
    on `1 < re s`) + r278 (analyticity on `ℂ \ {1}`) + r279 (identity
    theorem template).

## Open items at HEAD 2026-11-16 EOD

1. ~~**(4-construction-universal)** Compose r268 + r278 + r279 into
   the universal-s identity theorem.~~ [closed at `bb7ceaca` in
   `PF/DirichletEtaExtUniversalIdentity_2026_11_16.lean`]
2. **Discharge of `DirichletEtaExt_DifferentiableAtOne`**: show that
   `dirichletEtaExt` is differentiable at s = 1. Limit value is `ln 2`;
   differentiability follows from the Abel summation structure. Needed
   to complete (3) at s = 1.
3. **Cite (2) in the substrate-attack bundle.** Currently the meta-capstone
   reports "4 of 5 Dirichlet-1858 sub-ingredients" — (2) is closed but
   not yet composed into the bundle. Adding this bumps the count to 5 of 5
   under the sub-ingredient enumeration here.
4. **Bridge R_f(1, s) to the universal-s identity.** Per the 2026-11-16
   Rio academia co-scientist audit (`rio.pdf §5.1`):
   `R_f(1, s) = Σ_{n≥1} (-1)^n · n^(-s) = -dirichletEta s` on `1 < re s`,
   because `D_3(n) ≡ n (mod 2)` at `α = 1`. Combined with the now-closed
   universal-s identity, this gives
   `R_f(1, s) = -(1 - 2^(1-s)) · riemannZeta s` for all `s ≠ 1`.
   Compose in a new file once the Lean definition of `R_f` is located.

## Downstream users

Substrate-attack bundles that cite this chain:
- `PF/RHSubstratePositionPartialDischarge_2026_11_15.lean`  (Abel bridge)
- `PF/RHSubstratePositionExtendedPartialDischarge_2026_11_15.lean`  ((3) + (4-template))
- `PF/RHSubstratePositionFourthIngredientDischarge_2026_11_16.lean`  ((4-construction-at-half))
- `PF/PrincipiaFractalisToEMetaCapstone_2026_11_16.lean`  (meta-capstone conjunct 2)

-/

namespace PF.DirichletChainStatus

/-! ## Compile-time checker: every cited theorem must still exist. -/

-- (1) Abel bridge.
#check @PrincipiaTractalis.Dirichlet1858AbelBridge.abel_bridge_dirichletEtaHalf
#check @PrincipiaTractalis.Dirichlet1858AbelBridge.Dirichlet1858_PowerSeriesLimit_EqualsProductForm

-- (2) Abscissa of conditional convergence.
#check @PrincipiaTractalis.DirichletEtaConditionalConvergenceReal.dirichletEta_lseries_partial_cauchy_real
#check @PrincipiaTractalis.DirichletEtaConditionalConvergenceComplex.dirichletEta_lseries_partial_cauchy
#check @PrincipiaTractalis.DirichletEtaConditionalConvergenceComplex.dirichletEta_conditionalConvergence_complexOffReal_discharged

-- (3) Analytic continuation on ℂ \ {1}.
#check @PrincipiaTractalis.DirichletEtaExtDifferentiable.dirichletEtaExt_differentiableOn_ne_one
#check @PrincipiaTractalis.DirichletEtaExtDifferentiable.dirichletEtaExt_differentiableOn_pos_re_ne_one
#check @PrincipiaTractalis.DirichletEtaExtDifferentiable.DirichletEtaExt_DifferentiableAtOne

-- (4-template) Identity theorem.
#check @PrincipiaTractalis.DirichletEtaIdentityTheorem.eqOn_dirichletEtaExt_of_analyticOnNhd_eventuallyEq
#check @PrincipiaTractalis.DirichletEtaIdentityTheorem.eqOn_dirichletEtaExt_of_analyticOnNhd_agrees_on_one_lt_re
#check @PrincipiaTractalis.DirichletEtaIdentityTheorem.DirichletEta_HasAnalyticExtension

-- (4-construction-at-half) Point closure.
#check @PrincipiaTractalis.DirichletEtaExtHalf.dirichletEtaExt_half_eq

-- (ingredient for 4-construction-universal) Identity on 1 < re s.
#check @PrincipiaTractalis.DirichletEtaZetaIdentity.dirichletEta_eq_one_sub_two_cpow_mul_riemannZeta

end PF.DirichletChainStatus
