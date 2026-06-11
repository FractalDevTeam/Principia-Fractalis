/-
# Fujita-Kato 1964 — Linearity of the Leray Fourier Symbol

★ 2026-06-11 — Adds ℂ-linearity properties of the Leray symbol
`lerayFourierSymbolC` in its vector argument.

The Leray symbol at the complex Fourier-side is

  `lerayFourierSymbolC ξ v := v - (⟨complexifyVec ξ, v⟩_ℂ / ‖ξ‖²) • complexifyVec ξ`

for `ξ ≠ 0`, and the identity for `ξ = 0`. In the vector argument
`v ∈ ℂ³`, this is ℂ-linear because the Hermitian inner product
`⟨_, v⟩_ℂ` is ℂ-linear in `v` (the second argument by mathlib's
convention).

Combined with the already-landed ℂ-linearity of
`vectorHeatEvolveFreq` (`HeatEvolveLinear.lean`), this gives
ℂ-linearity of the composite `heatLerayCompose` in the Schwartz
input — which is what the Fujita-Kato Picard contraction needs.

This file:
  §1 — `lerayFourierSymbolC_add` (additivity in `v`)
  §2 — `lerayFourierSymbolC_smul` (ℂ-scalar action in `v`)
  §3 — Capstone

Axiom-free; kernel-only `[propext, Classical.choice, Quot.sound]`.

Author: Pablo Cohen (2026-06-11)
-/

import PF.NavierStokes.FujitaKato1964.LerayProjectorOperator

set_option autoImplicit false

namespace PF.NavierStokes.FujitaKato1964.LerayLinear

open PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier (R3 C3)
open PF.NavierStokes.FujitaKato1964.LerayProjectorOperator
  (complexifyVec lerayFourierSymbolC)

/-! ## §1 — Additivity in the vector argument -/

/-- **The Leray symbol is additive in its vector argument.**

For any frequency `ξ ∈ ℝ³` and any pair `v, w ∈ ℂ³`:

  `lerayFourierSymbolC ξ (v + w) = lerayFourierSymbolC ξ v + lerayFourierSymbolC ξ w`. -/
theorem lerayFourierSymbolC_add (ξ : R3) (v w : C3) :
    lerayFourierSymbolC ξ (v + w)
      = lerayFourierSymbolC ξ v + lerayFourierSymbolC ξ w := by
  unfold lerayFourierSymbolC
  by_cases hξ : ξ = 0
  · simp [hξ]
  · simp only [if_neg hξ]
    rw [inner_add_right]
    rw [add_div]
    rw [add_smul]
    abel

/-! ## §2 — ℂ-scalar action in the vector argument -/

/-- **The Leray symbol commutes with ℂ-scalar action on its vector
argument.**

For any frequency `ξ ∈ ℝ³`, scalar `c ∈ ℂ`, and vector `v ∈ ℂ³`:

  `lerayFourierSymbolC ξ (c • v) = c • lerayFourierSymbolC ξ v`. -/
theorem lerayFourierSymbolC_smul (ξ : R3) (c : ℂ) (v : C3) :
    lerayFourierSymbolC ξ (c • v) = c • lerayFourierSymbolC ξ v := by
  unfold lerayFourierSymbolC
  by_cases hξ : ξ = 0
  · simp [hξ]
  · simp only [if_neg hξ]
    rw [inner_smul_right]
    rw [smul_sub]
    rw [mul_div_assoc, mul_smul]

/-! ## §3 — Capstone -/

/-- **★ Leray symbol linearity brick capstone ★**

Bundles the ℂ-linearity of `lerayFourierSymbolC` in the vector argument:

  (a) Additivity in `v`
  (b) ℂ-scalar action in `v`

Together: `lerayFourierSymbolC ξ` is a ℂ-linear endomorphism of `C3`
at every frequency `ξ`. Combined with the already-landed
ℂ-linearity of `vectorHeatEvolveFreq` (HeatEvolveLinear), this
gives ℂ-linearity of the composite `heatLerayCompose` in the
Schwartz input — the linearity the Fujita-Kato Picard contraction
needs to identify the mild solution as a fixed point of a ℂ-affine
map.

Axiom-free; kernel-only `[propext, Classical.choice, Quot.sound]`. -/
theorem fujitaKato_leray_linear_brick_capstone :
    (∀ (ξ : R3) (v w : C3),
       lerayFourierSymbolC ξ (v + w)
         = lerayFourierSymbolC ξ v + lerayFourierSymbolC ξ w) ∧
    (∀ (ξ : R3) (c : ℂ) (v : C3),
       lerayFourierSymbolC ξ (c • v) = c • lerayFourierSymbolC ξ v) :=
  ⟨lerayFourierSymbolC_add, lerayFourierSymbolC_smul⟩

/-! ## §4 — Axiom audit -/

#print axioms lerayFourierSymbolC_add
#print axioms lerayFourierSymbolC_smul
#print axioms fujitaKato_leray_linear_brick_capstone

end PF.NavierStokes.FujitaKato1964.LerayLinear
