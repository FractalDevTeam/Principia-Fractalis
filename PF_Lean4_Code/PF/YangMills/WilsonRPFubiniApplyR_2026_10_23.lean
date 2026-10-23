/-
# Yang-Mills — Wilson RP with refined `Φ` (step 6)

**Rio's §P3 ACER directive, 2026-10-23.** Specialisation of
`wilson_reflection_positivity` to the REFINED Φ (`wilsonReducedPhiR`,
`8f8e160f`), using `wilsonActionPlusR` instead of binary
`wilsonActionPlus`.

### Why the refined specialisation

The binary specialisation (`wilson_reflection_positivity_withReducedPhi`,
`52a1cd3e`) was blocked at the Fubini identity by the asymmetric
lumping of boundary FF plaquettes. The refined 3-way sector resolves
this: the pointwise reflection `S_-R(θU) = S_+R(U)` holds sum-level
(landed at `24a2a90c`), so the refined Fubini identity is proveable
from the sector-action payload + the Λ_- measure-preserving restriction
(`74414ed1`).

### What this file provides

* **`wilson_reflection_positivity_withReducedPhiR`** — the headline
  specialised to `Φ i := wilsonReducedPhiR β (F i)`. Takes the two
  remaining hypotheses (`hΦ_integrable`, `hFubini`); still conditional,
  but structurally positioned for the final internal discharge.

### Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-23.
-/
import PF.YangMills.WilsonReducedPhiR_2026_10_23
import PF.YangMills.WilsonReflectionPositivity_2026_10_20

set_option autoImplicit false

namespace PF.YangMills

open MeasureTheory
open scoped ComplexOrder

noncomputable section

variable {L : ℕ} [NeZero L]

/-- **★ Wilson RP with refined `Φ` ★**

The headline `wilson_reflection_positivity` with
`Φ i := wilsonReducedPhiR β (F i)`. -/
theorem wilson_reflection_positivity_withReducedPhiR {K : ℕ} (β : ℝ)
    (F : Fin K → GaugeField L → ℂ)
    (hF_support : ∀ i : Fin K, supportedOnPlusZero (F i))
    (hΦ_integrable : ∀ i j : Fin K,
      Integrable (fun U =>
        star (wilsonReducedPhiR β (F i) U) * wilsonReducedPhiR β (F j) U)
        (wilsonBaseMeasure L))
    (hFubini : ∀ i j : Fin K,
      ∫ U, star (F i (timeReflectionGaugeField U)) * F j U
        ∂(wilsonGibbsMeasure L β)
      = ∫ U, star (wilsonReducedPhiR β (F i) U) * wilsonReducedPhiR β (F j) U
        ∂(wilsonBaseMeasure L)) :
    (Matrix.of (fun i j : Fin K =>
      ∫ U, star (F i (timeReflectionGaugeField U)) * F j U
        ∂(wilsonGibbsMeasure L β))).PosSemidef :=
  wilson_reflection_positivity β F hF_support
    (fun i => wilsonReducedPhiR β (F i)) hΦ_integrable hFubini

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.wilson_reflection_positivity_withReducedPhiR
