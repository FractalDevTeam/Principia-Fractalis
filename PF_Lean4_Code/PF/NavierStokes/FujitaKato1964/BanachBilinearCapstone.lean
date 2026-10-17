/-
# Fujita-Kato 1964 — Banach Bilinear Capstone (steps 1 + 2 + 2b composed)

**Rio's NS carrier migration.** Instantiates the step-2 bilinear
(`BanachBilinear.mildBilinear`) with the step-2b concrete operator
realizations (`BanachOperatorShell`), producing the Banach-side
replacement of `BilinearScaffold.trivialBilinear`.

### What this file provides

* `banachMildBilinear u v : TimeFieldR3C_Banach` — the Banach-side mild
  bilinear with the concrete (step-2b trivial) heat / Leray / convective
  inputs supplied.
* `banachPicardMap u₀ u : TimeFieldR3C_Banach` — the Picard map
  `Φ(u)(t) = e^{tΔ} u₀ + B(u, u)(t)` on the Banach carrier.
* Zero-input identities `B(0, v) = 0`, `B(u, 0) = 0`, and the Picard
  initial-datum match `Φ(0)(0) = u₀`.

With the trivial step-2b realizations, `banachMildBilinear u v`
collapses to `0` identically (just like the old `trivialBilinear`),
but every type signature now matches the real Fujita-Kato operator
shape. Step 2c (density-extension of the Schwartz operators to Lp)
will supply the non-trivial realizations, at which point this
capstone's conclusions upgrade to the real bilinear content without
any API change at the call site.

Three-axiom bar: every declaration kernel-clean
`[propext, Classical.choice, Quot.sound]`. No sorry.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-17.
-/
import PF.NavierStokes.FujitaKato1964.BanachBilinear
import PF.NavierStokes.FujitaKato1964.BanachOperatorShell

set_option autoImplicit false

namespace PF.NavierStokes.FujitaKato1964

noncomputable section

/-! ## §1 — The composed bilinear + Picard map. -/

/-- **Banach-side mild bilinear with concrete (step-2b trivial) inputs**.
`banachMildBilinear u v (t) = ∫₀ᵗ e^{(t−s)Δ} ℙ[(u·∇)v(s)] ds` with the
step-2b heat / Leray / convective operators. With the trivial
realizations currently in `BanachOperatorShell`, this is identically
zero; step-2c replaces the realizations, upgrading this definition
without API change. -/
def banachMildBilinear (u v : TimeFieldR3C_Banach) : TimeFieldR3C_Banach :=
  mildBilinear banachHeatSemigroup banachLerayProjection
    banachConvectiveDerivative u v

/-- **Banach-side Picard map** `Φ(u)(t) = e^{tΔ} u₀ + B(u, u)(t)`. -/
def banachPicardMap (u₀ : VectorBanach3C) (u : TimeFieldR3C_Banach) :
    TimeFieldR3C_Banach :=
  picardMap banachHeatSemigroup banachLerayProjection
    banachConvectiveDerivative u₀ u

/-! ## §2 — Zero-input identities. -/

/-- `banachMildBilinear 0 v = 0`. -/
theorem banachMildBilinear_zero_left (v : TimeFieldR3C_Banach) :
    banachMildBilinear zeroTimeFieldBanach v = zeroTimeFieldBanach :=
  mildBilinear_zero_left banachConvectiveDerivative_zero_left v

/-- `banachMildBilinear u 0 = 0`. -/
theorem banachMildBilinear_zero_right (u : TimeFieldR3C_Banach) :
    banachMildBilinear u zeroTimeFieldBanach = zeroTimeFieldBanach :=
  mildBilinear_zero_right banachConvectiveDerivative_zero_right u

/-- `banachPicardMap u₀ 0 (0) = u₀` — the initial-datum match. -/
theorem banachPicardMap_zero_at_zero (u₀ : VectorBanach3C) :
    banachPicardMap u₀ zeroTimeFieldBanach 0 = u₀ :=
  picardMap_zero_at_zero banachHeatSemigroup_zero
    banachConvectiveDerivative_zero_left u₀

end

end PF.NavierStokes.FujitaKato1964

/-! ## §Axiom check -/
#print axioms PF.NavierStokes.FujitaKato1964.banachMildBilinear_zero_left
#print axioms PF.NavierStokes.FujitaKato1964.banachMildBilinear_zero_right
#print axioms PF.NavierStokes.FujitaKato1964.banachPicardMap_zero_at_zero
