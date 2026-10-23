/-
# Yang-Mills — Refined explicit `Φ` for the Wilson RP Fubini discharge

**Rio's §P3 ACER directive, 2026-10-23.** Refined counterpart to
`wilsonReducedPhi` (`cc1fe60c`, using binary `wilsonActionPlus`),
using `wilsonActionPlusR` (3-way refined — no boundary residuals).

### Why the refined version

The Fubini identity needs the pointwise reflection
`S_-R(θU) = S_+R(U)` (sum-level) and `exp(-β S_W) = exp(-β S_+R)
exp(-β S_0) exp(-β S_-R)` (3-way factorization). Both hold for the
refined sector but not for the binary one, which lumps boundary FF
plaquettes asymmetrically.

### What this file provides

* `wilsonReducedPhiR` — the explicit Φ using `wilsonActionPlusR`.
* `wilsonReducedPhiR_congr_restrictNonPlus` — Φ invariant under
  changes of U on Λ_+ links (parallel to `wilsonReducedPhi_congr_restrictNonPlus`).

### Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-23.
-/
import PF.YangMills.WilsonSectorGluePlus_2026_10_21
import PF.YangMills.WilsonSectorPlaquetteZero_2026_10_21
import PF.YangMills.WilsonFubiniPhi_2026_10_21

set_option autoImplicit false

namespace PF.YangMills

open MeasureTheory

noncomputable section

variable {L : ℕ} [NeZero L]

/-- **The refined explicit `Φ` for the Wilson RP Fubini discharge.**

For `F` supported on `Λ_+ ∪ Λ_0`, `Φ(U)` is the partial Bochner
integral of `F · exp(-β · S_+R)` over the `Λ_+` component of `U`, with
the non-`Λ_+` component read from `U`.

Compared to `wilsonReducedPhi`, this uses `wilsonActionPlusR` (refined
3-way) instead of `wilsonActionPlus` (binary) — the refined form is
what the Fubini identity's sum-level reflection consumes. -/
noncomputable def wilsonReducedPhiR (β : ℝ) (F : GaugeField L → ℂ) :
    GaugeField L → ℂ :=
  fun U =>
    ∫ V : Subtype (isPlusLink : LatticeLink L → Prop) → SU2,
      F (gaugeFieldGluePlus V (restrictNonPlus U))
        * (Real.exp (-β * wilsonActionPlusR
            (gaugeFieldGluePlus V (restrictNonPlus U))) : ℂ)
      ∂(Measure.pi (fun _ : Subtype (isPlusLink : LatticeLink L → Prop) =>
          SU2_haar))

/-- `Φ(U)` depends on `U` only through its non-Λ_+ (= Λ_- ∪ Λ_0) component. -/
lemma wilsonReducedPhiR_congr_restrictNonPlus
    (β : ℝ) (F : GaugeField L → ℂ) (U₁ U₂ : GaugeField L)
    (hAgree : ∀ ℓ : LatticeLink L, ¬ isPlusLink ℓ → U₁ ℓ = U₂ ℓ) :
    wilsonReducedPhiR β F U₁ = wilsonReducedPhiR β F U₂ := by
  unfold wilsonReducedPhiR
  have h_restrict : restrictNonPlus U₁ = restrictNonPlus (L := L) U₂ := by
    funext ℓ
    exact hAgree ℓ.val ℓ.property
  rw [h_restrict]

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.wilsonReducedPhiR
#print axioms PF.YangMills.wilsonReducedPhiR_congr_restrictNonPlus
