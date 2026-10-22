/-
# Yang-Mills — Refined (3-way) Boltzmann factorization

**Rio's §2 ACER directive, 2026-10-22.** The 3-way Boltzmann
factorization uses the refined sector decomposition
(`wilsonActionTotal_sector_decomposition_refined`, `09b95c1c`):

  `exp(-β · S_W(U)) = exp(-β · S_+R(U)) · exp(-β · S_0(U)) · exp(-β · S_-R(U))`.

This is the pointwise identity the Fubini apply consumes to split the
Gibbs integrand across three sector factors.

### Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-22.
-/
import PF.YangMills.WilsonActionSectorDecomp3Way_2026_10_22

set_option autoImplicit false

namespace PF.YangMills

noncomputable section

variable {L : ℕ} [NeZero L]

/-- **★ 3-WAY BOLTZMANN FACTORIZATION (ℝ-valued) ★**

`exp(-β · S_W(U)) = exp(-β · S_+R(U)) · exp(-β · S_0(U)) · exp(-β · S_-R(U))`. -/
theorem wilsonBoltzmann_factorize_3way_real (β : ℝ) (U : GaugeField L) :
    Real.exp (-β * wilsonActionTotal U)
      = Real.exp (-β * wilsonActionPlusR U)
        * Real.exp (-β * wilsonActionZero U)
        * Real.exp (-β * wilsonActionMinusR U) := by
  rw [wilsonActionTotal_sector_decomposition_refined]
  rw [mul_add, Real.exp_add, mul_add, Real.exp_add]

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.wilsonBoltzmann_factorize_3way_real
