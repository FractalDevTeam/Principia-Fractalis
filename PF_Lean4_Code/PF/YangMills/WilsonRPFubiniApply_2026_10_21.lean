/-
# Yang-Mills — Wilson RP with the explicit `Φ` pinned (step 6, specialisation)

**Rio's §2 ACER directive, 2026-10-21.** Specialisation of
`wilson_reflection_positivity` to the explicit `Φ := wilsonReducedPhi`.

### What this file provides

* **`wilson_reflection_positivity_withReducedPhi`** — the headline
  `wilson_reflection_positivity` with `Φ i := wilsonReducedPhi β (F i)`
  substituted into the hypothesis list. Reduces the two remaining
  hypotheses (`hΦ_integrable`, `hFubini`) to statements about the
  explicit `wilsonReducedPhi`.

### Why this is a step forward

The remaining Fubini identity, in this specialised form, has a concrete
target to prove: both sides are explicit base-measure integrals over
`GaugeField L`. The proof chain is:

1. `wilsonGibbs_integral_bochner_factorize` — Gibbs → base with
   `exp(-β S_+) · exp(-β S_-)` factored (`f852724c`).
2. Three-way Fubini on `Λ_- ⊕ (Λ_0 ∪ Λ_+)` via
   `wilsonBaseMeasure_integral_split` (`13b7c9e3`).
3. The `W`-integrand `F_j · exp(-β S_+)` factors through the glue
   as an `X`-independent function (`c5080d4b`, `4e5bbb10`).
4. The `X`-integrand `star F_i(θU) · exp(-β S_-)` becomes `star Φ_i(W)`
   under change of variable `X ↦ θ_Λ⁻ V` using Λ_- Pi inv-invariance
   (`5ad9b21a`) + sector action reflection `S_-(θV, W) = S_+(V, W)`.

Step 4 is the remaining structural payload — the sector action
reflection identity is not yet landed. This file reduces the headline
to that single remaining identity + integrability, and provides the
plug-in form.

### Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-21.
-/
import PF.YangMills.WilsonFubiniPhi_2026_10_21
import PF.YangMills.WilsonReflectionPositivity_2026_10_20

set_option autoImplicit false

namespace PF.YangMills

open MeasureTheory
open scoped ComplexOrder

noncomputable section

variable {L : ℕ} [NeZero L]

/-! ## §1 — `wilson_reflection_positivity` with `Φ := wilsonReducedPhi` pinned. -/

/-- **★ Specialised Wilson RP ★**

The headline `wilson_reflection_positivity` applied to the explicit
`Φ i := wilsonReducedPhi β (F i)`. Takes two remaining hypotheses:

* **integrability** of the Gram integrand against the explicit Φ,
* **Fubini identity** connecting the Gibbs cross-θ integral to the base
  integral of the explicit Φ.

Discharging those two hypotheses (step 6 proper) is the remaining
structural payload. The specialisation here is a pure plug-in. -/
theorem wilson_reflection_positivity_withReducedPhi {K : ℕ} (β : ℝ)
    (F : Fin K → GaugeField L → ℂ)
    (hF_support : ∀ i : Fin K, supportedOnPlusZero (F i))
    (hΦ_integrable : ∀ i j : Fin K,
      Integrable (fun U =>
        star (wilsonReducedPhi β (F i) U) * wilsonReducedPhi β (F j) U)
        (wilsonBaseMeasure L))
    (hFubini : ∀ i j : Fin K,
      ∫ U, star (F i (timeReflectionGaugeField U)) * F j U
        ∂(wilsonGibbsMeasure L β)
      = ∫ U, star (wilsonReducedPhi β (F i) U) * wilsonReducedPhi β (F j) U
        ∂(wilsonBaseMeasure L)) :
    (Matrix.of (fun i j : Fin K =>
      ∫ U, star (F i (timeReflectionGaugeField U)) * F j U
        ∂(wilsonGibbsMeasure L β))).PosSemidef :=
  wilson_reflection_positivity β F hF_support
    (fun i => wilsonReducedPhi β (F i)) hΦ_integrable hFubini

/-- Companion: specialised Hermiticity. -/
theorem wilson_reflection_gram_hermitian_withReducedPhi {K : ℕ} (β : ℝ)
    (F : Fin K → GaugeField L → ℂ)
    (hF_support : ∀ i : Fin K, supportedOnPlusZero (F i))
    (hΦ_integrable : ∀ i j : Fin K,
      Integrable (fun U =>
        star (wilsonReducedPhi β (F i) U) * wilsonReducedPhi β (F j) U)
        (wilsonBaseMeasure L))
    (hFubini : ∀ i j : Fin K,
      ∫ U, star (F i (timeReflectionGaugeField U)) * F j U
        ∂(wilsonGibbsMeasure L β)
      = ∫ U, star (wilsonReducedPhi β (F i) U) * wilsonReducedPhi β (F j) U
        ∂(wilsonBaseMeasure L)) :
    (Matrix.of (fun i j : Fin K =>
      ∫ U, star (F i (timeReflectionGaugeField U)) * F j U
        ∂(wilsonGibbsMeasure L β))).IsHermitian :=
  (wilson_reflection_positivity_withReducedPhi β F hF_support
    hΦ_integrable hFubini).1

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.wilson_reflection_positivity_withReducedPhi
#print axioms PF.YangMills.wilson_reflection_gram_hermitian_withReducedPhi
