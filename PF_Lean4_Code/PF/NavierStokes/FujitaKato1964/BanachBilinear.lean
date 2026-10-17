/-
# Fujita-Kato 1964 — Banach Bilinear Operator `B(u,v)` (step 2 of 4)

**Rio's NS carrier migration, 2026-10-17.** The actual Fujita-Kato mild
bilinear

    `B(u, v)(t) = ∫₀ᵗ e^{(t−s)Δ} ℙ[(u·∇) v(s)] ds`

defined on the Banach-valued time curve `TimeFieldR3C_Banach :=
ℝ → VectorBanach3C` (step 1, `BanachCarrier.lean`). This is the operator
`BilinearScaffold.lean` could not build: `intervalIntegral` requires
`[NormedAddCommGroup E]` on its codomain, which `SchwartzMap` lacks and
`Lp C3 2 volume` has for free.

### Shape

The construction factors through three abstract operators (supplied by
the caller — the concrete heat / Leray / convective lifts from the
Schwartz side are step 2b, separate files):

* `heatSemigroup : ℝ → VectorBanach3C →L[ℂ] VectorBanach3C` — the
  evolution `e^{tΔ}` as a continuous linear map, parameterized by `t`.
* `lerayProjection : VectorBanach3C →L[ℂ] VectorBanach3C` — the Leray
  projector `ℙ` as a continuous linear map.
* `convectiveDerivative : VectorBanach3C → VectorBanach3C → VectorBanach3C`
  — `(u·∇) v` as a (non-linear) map between Banach spaces.

Given these, `mildBilinear` is the composition

    `B(u, v)(t) = ∫₀ᵗ heatSemigroup (t−s)
                      (lerayProjection (convectiveDerivative (u s) (v s)))
                   ds`

a Bochner integral in `VectorBanach3C`. The integrand is
`VectorBanach3C`-valued, which has `NormedAddCommGroup` (from `Lp`), so
`intervalIntegral` type-checks.

### What this file proves

* `mildBilinear` is a well-typed `TimeFieldR3C_Banach →
  TimeFieldR3C_Banach → TimeFieldR3C_Banach`.
* The two zero-input identities `B(0, v) = 0` and `B(u, 0) = 0`, under
  the natural hypotheses `convectiveDerivative 0 v = 0` and
  `convectiveDerivative u 0 = 0` on the convective derivative (which the
  concrete lift will satisfy).
* The mild formulation `Φ(u)(t) = e^{tΔ} u₀ + B(u, u)(t)` as a `def`.

### What this file does NOT prove (deferred to steps 3-4)

* The `Ḣ^{1/2}` product estimate for `(u·∇) v` (step 3; one analytic
  lemma, the load-bearing piece).
* Picard contraction ⇒ local existence (step 4; needs step 3).
* Measurability / integrability of the integrand (will be supplied by
  step 2b once the concrete operators are constructed; the shell here
  is unconditional on those hypotheses — `intervalIntegral` returns `0`
  if the integrand is not integrable, so the definition type-checks
  regardless, and the content theorems add the integrability side).

Three-axiom bar: every declaration kernel-clean
`[propext, Classical.choice, Quot.sound]`. No sorry.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-17.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import PF.NavierStokes.FujitaKato1964.BanachCarrier

set_option autoImplicit false

namespace PF.NavierStokes.FujitaKato1964

open MeasureTheory

noncomputable section

/-! ## §1 — The abstract bilinear shell. -/

/-- **The Banach mild bilinear operator `B(u, v)(t)`**, factored through
three abstract operators the concrete lifts (step 2b) will supply:

* `heatSG` — heat semigroup `e^{sΔ}` as a CLM, `s`-parameterized.
* `leray` — Leray projection `ℙ`.
* `conv`  — convective derivative `(u·∇) v`.

The integrand `s ↦ heatSG (t − s) (leray (conv (u s) (v s)))` is
`VectorBanach3C`-valued; `intervalIntegral` applies because
`VectorBanach3C` has `NormedAddCommGroup`. -/
def mildBilinear
    (heatSG : ℝ → VectorBanach3C →L[ℂ] VectorBanach3C)
    (leray : VectorBanach3C →L[ℂ] VectorBanach3C)
    (conv : VectorBanach3C → VectorBanach3C → VectorBanach3C)
    (u v : TimeFieldR3C_Banach) : TimeFieldR3C_Banach :=
  fun t => ∫ s in (0 : ℝ)..t, heatSG (t - s) (leray (conv (u s) (v s)))

/-! ## §2 — Zero-input identities. -/

/-- **`B(0, v) = 0`** under the natural hypothesis that the convective
derivative vanishes on the zero first argument (satisfied by any
operator of the form `(u·∇)v` since `0·∇v = 0`).

The proof: `conv (0) (v s) = 0`, so `leray 0 = 0` (CLM), so
`heatSG (t−s) 0 = 0` (CLM). The constant-zero integrand integrates to
zero. -/
theorem mildBilinear_zero_left
    {heatSG : ℝ → VectorBanach3C →L[ℂ] VectorBanach3C}
    {leray : VectorBanach3C →L[ℂ] VectorBanach3C}
    {conv : VectorBanach3C → VectorBanach3C → VectorBanach3C}
    (hconv0 : ∀ w : VectorBanach3C, conv (0 : VectorBanach3C) w = 0)
    (v : TimeFieldR3C_Banach) :
    mildBilinear heatSG leray conv zeroTimeFieldBanach v = zeroTimeFieldBanach := by
  funext t
  show (∫ s in (0 : ℝ)..t,
          heatSG (t - s) (leray (conv (zeroTimeFieldBanach s) (v s))))
        = zeroTimeFieldBanach t
  simp only [zeroTimeFieldBanach_apply, hconv0, map_zero,
             intervalIntegral.integral_zero]

/-- **`B(u, 0) = 0`** under the dual hypothesis on the second argument. -/
theorem mildBilinear_zero_right
    {heatSG : ℝ → VectorBanach3C →L[ℂ] VectorBanach3C}
    {leray : VectorBanach3C →L[ℂ] VectorBanach3C}
    {conv : VectorBanach3C → VectorBanach3C → VectorBanach3C}
    (hconv0 : ∀ w : VectorBanach3C, conv w (0 : VectorBanach3C) = 0)
    (u : TimeFieldR3C_Banach) :
    mildBilinear heatSG leray conv u zeroTimeFieldBanach = zeroTimeFieldBanach := by
  funext t
  show (∫ s in (0 : ℝ)..t,
          heatSG (t - s) (leray (conv (u s) (zeroTimeFieldBanach s))))
        = zeroTimeFieldBanach t
  simp only [zeroTimeFieldBanach_apply, hconv0, map_zero,
             intervalIntegral.integral_zero]

/-! ## §3 — The mild formulation `Φ(u)(t) = e^{tΔ} u₀ + B(u, u)(t)`. -/

/-- **Picard map for the Fujita-Kato mild formulation.** Given initial data
`u₀ : VectorBanach3C`, abstract heat/Leray/convective operators, and a
candidate time curve `u`, the Picard map

    `Φ(u)(t) = e^{tΔ} u₀ + B(u, u)(t)`

returns a new time curve whose fixed points (if any) are mild solutions
to the Navier-Stokes Cauchy problem. -/
def picardMap
    (heatSG : ℝ → VectorBanach3C →L[ℂ] VectorBanach3C)
    (leray : VectorBanach3C →L[ℂ] VectorBanach3C)
    (conv : VectorBanach3C → VectorBanach3C → VectorBanach3C)
    (u₀ : VectorBanach3C) (u : TimeFieldR3C_Banach) : TimeFieldR3C_Banach :=
  fun t => heatSG t u₀ + mildBilinear heatSG leray conv u u t

/-- **`Φ(0)(0) = u₀`** when the heat semigroup satisfies `e^{0·Δ} = 𝟙`
(satisfied by any proper semigroup lift from the Schwartz side) — the
initial-datum match for the Picard map at the fixed point `u = 0`. -/
theorem picardMap_zero_at_zero
    {heatSG : ℝ → VectorBanach3C →L[ℂ] VectorBanach3C}
    {leray : VectorBanach3C →L[ℂ] VectorBanach3C}
    {conv : VectorBanach3C → VectorBanach3C → VectorBanach3C}
    (hheat0 : heatSG 0 = ContinuousLinearMap.id ℂ VectorBanach3C)
    (hconv0 : ∀ w : VectorBanach3C, conv (0 : VectorBanach3C) w = 0)
    (u₀ : VectorBanach3C) :
    picardMap heatSG leray conv u₀ zeroTimeFieldBanach 0 = u₀ := by
  show heatSG 0 u₀ + mildBilinear heatSG leray conv
          zeroTimeFieldBanach zeroTimeFieldBanach 0 = u₀
  have h_bilin_zero :
      mildBilinear heatSG leray conv zeroTimeFieldBanach zeroTimeFieldBanach
        = zeroTimeFieldBanach :=
    mildBilinear_zero_left hconv0 zeroTimeFieldBanach
  rw [h_bilin_zero, zeroTimeFieldBanach_apply, add_zero, hheat0]
  rfl

end

end PF.NavierStokes.FujitaKato1964

/-! ## §Axiom check -/
#print axioms PF.NavierStokes.FujitaKato1964.mildBilinear_zero_left
#print axioms PF.NavierStokes.FujitaKato1964.mildBilinear_zero_right
#print axioms PF.NavierStokes.FujitaKato1964.picardMap_zero_at_zero
