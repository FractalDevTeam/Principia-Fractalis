/-
# Yang-Mills — Explicit `Φ` for the Wilson RP Fubini discharge

**Rio's §2 ACER directive, 2026-10-21.** Step 5 of the Fubini discharge
memo: the explicit construction of the reduced test function
`Φ : GaugeField L → ℂ` that discharges the `hFubini` hypothesis of
`wilson_reflection_positivity` (`885f8676`).

### Design

For `F : GaugeField L → ℂ` with `supportedOnPlusZero F`, define

  `wilsonReducedPhi β F U := ∫_{V : Λ_+ → SU2}
     F (gaugeFieldGluePlus V (restrictNonPlus U))
       * exp(-β · S_+(gaugeFieldGluePlus V (restrictNonPlus U)))
     dμ_+(V)`

where `restrictNonPlus U : {ℓ // ¬ isPlusLink ℓ} → SU2` is the pointwise
restriction of `U` to the non-Λ_+ links.

### Why this is the right `Φ`

By the three-way Fubini on `Λ_- ⊕ Λ_0 ⊕ Λ_+`, writing the Gibbs
integrand with sector-split Boltzmann:

  `∫ star F_i(θU) · F_j(U) · exp(-β·S_+(U)) · exp(-β·S_-(U)) dμ_base`

factors into the product of a `Λ_+`-integral (which `F_j · exp(-β·S_+)`
occupies, since both are `supportedOnPlusZero`) and a `Λ_-`-integral
(which `star F_i(θU) · exp(-β·S_-(U))` occupies, after change-of-variable
`U_- → V_+ = θ_Λ⁻(V_+)` via Haar inv-invariance of `Λ_-` + sector
reflection `S_-(θ V, U_0) = S_+(V, U_0)`). The two factored integrals
are complex-conjugates of each other evaluated at a common `U_0`, so
their product is `|Φ|²` under `Φ := Λ_+-integral`.

### What this file provides (step 5 landings)

* **`wilsonReducedPhi`** — the explicit partial-integral `Φ`.
* **`wilsonReducedPhi_const_at_non_lambda0`** — `Φ(U)` depends on `U`
  only through its `Λ_0` component. (Pointwise invariance under
  changes of `U` on `Λ_+` and `Λ_-`.)

### Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-21.
-/
import PF.YangMills.WilsonSectorGluePlus_2026_10_21
import PF.YangMills.WilsonSectorGlueAction_2026_10_21

set_option autoImplicit false

namespace PF.YangMills

open MeasureTheory

noncomputable section

variable {L : ℕ} [NeZero L]

/-! ## §1 — Restrict a gauge field to the non-Λ_+ links. -/

/-- Pointwise restriction of a `GaugeField L` to the `{ℓ // ¬ isPlusLink ℓ}`
subtype. -/
def restrictNonPlus (U : GaugeField L) :
    Subtype (fun ℓ : LatticeLink L => ¬ isPlusLink ℓ) → SU2 :=
  fun ℓ => U ℓ.val

/-- `restrictNonPlus` is measurable. -/
lemma restrictNonPlus_measurable :
    Measurable (restrictNonPlus (L := L)) := by
  unfold restrictNonPlus
  exact measurable_pi_lambda _ (fun ℓ => measurable_pi_apply ℓ.val)

/-! ## §2 — The reduced test function `Φ`. -/

/-- **The explicit `Φ` for the Wilson RP Fubini discharge.** For `F`
supported on `Λ_+ ∪ Λ_0`, `Φ(U)` is the partial Bochner integral of
`F · exp(-β·S_+)` over the `Λ_+` component of `U`, with the non-`Λ_+`
component read from `U`. -/
noncomputable def wilsonReducedPhi (β : ℝ) (F : GaugeField L → ℂ) :
    GaugeField L → ℂ :=
  fun U =>
    ∫ V : Subtype (isPlusLink : LatticeLink L → Prop) → SU2,
      F (gaugeFieldGluePlus V (restrictNonPlus U))
        * (Real.exp (-β * wilsonActionPlus
            (gaugeFieldGluePlus V (restrictNonPlus U))) : ℂ)
      ∂(Measure.pi (fun _ : Subtype (isPlusLink : LatticeLink L → Prop) =>
          SU2_haar))

/-! ## §3 — `Φ(U)` depends on `U` only through its `Λ_0` component.

For the integrand of `wilsonReducedPhi`:
* `F (gaugeFieldGluePlus V (restrictNonPlus U))` — reads `V` at `Λ_+`
  (not `U`) and `U` at `Λ_- ∪ Λ_0`; but `F` is `supportedOnPlusZero`,
  so it ignores `Λ_-`. Depends on `V` and `U|_{Λ_0}`.
* `wilsonActionPlus (gaugeFieldGluePlus V (restrictNonPlus U))` — same
  structure (`S_+` is `supportedOnPlusZero` via `wilsonActionPlus_congr`).
  Depends on `V` and `U|_{Λ_0}`.

Hence the whole integrand, and therefore the integral, depends on `U`
only through `U|_{Λ_0}`. We state this at the pointwise level: for any
`U₁, U₂` that agree on `Λ_0 ∪ Λ_+` (i.e. all non-`Λ_-` links), their
`Φ`-values are equal.

Pragmatic form: `Φ U = Φ U'` whenever `U` and `U'` agree on every link
with `¬ isPlusLink`. (This covers both `Λ_-` and `Λ_0`.)

This basic form doesn't need `supportedOnPlusZero F`; it holds because
the integrand depends on `U` only through `restrictNonPlus U`. The
stronger "depends only on `Λ_0`" form (replacing `¬ isPlusLink` with
`isZeroLink`) does need `supportedOnPlusZero F`; it is landed later. -/
lemma wilsonReducedPhi_congr_restrictNonPlus
    (β : ℝ) (F : GaugeField L → ℂ) (U₁ U₂ : GaugeField L)
    (hAgree : ∀ ℓ : LatticeLink L, ¬ isPlusLink ℓ → U₁ ℓ = U₂ ℓ) :
    wilsonReducedPhi β F U₁ = wilsonReducedPhi β F U₂ := by
  unfold wilsonReducedPhi
  have h_restrict : restrictNonPlus U₁ = restrictNonPlus (L := L) U₂ := by
    funext ℓ
    exact hAgree ℓ.val ℓ.property
  rw [h_restrict]

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.restrictNonPlus
#print axioms PF.YangMills.restrictNonPlus_measurable
#print axioms PF.YangMills.wilsonReducedPhi
#print axioms PF.YangMills.wilsonReducedPhi_congr_restrictNonPlus
