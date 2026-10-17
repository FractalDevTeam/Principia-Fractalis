/-
# Fujita-Kato 1964 — Banach Operator Shell (step 2b of 4)

**Rio's NS carrier migration, step 2b.** Provides the CLM-shaped type
infrastructure for the three operators the Banach-side bilinear
(`BanachBilinear.lean`) is parameterized by:

* `banachHeatSemigroup : ℝ → VectorBanach3C →L[ℂ] VectorBanach3C`
* `banachLerayProjection : VectorBanach3C →L[ℂ] VectorBanach3C`
* `banachConvectiveDerivative : VectorBanach3C → VectorBanach3C → VectorBanach3C`

### Scope and honesty

This file provides **concrete typed definitions with trivial
realizations** (identity CLMs for heat/Leray, zero map for convective)
plus the natural zero-input and initial-time hypotheses the bilinear
and Picard-map theorems in `BanachBilinear.lean` require.

**What this file does NOT provide**: the operator-norm bounds that give
the full Fujita-Kato analytic content. Those are:

* `‖banachHeatSemigroup t‖ ≤ 1` (semigroup contractivity).
* `‖banachLerayProjection‖ ≤ 1` (orthogonal projection in L²).
* The product estimate `‖(u·∇)v‖_{Ḣ^{-1/2}} ≤ C ‖u‖_{Ḣ^{1/2}} ‖v‖_{Ḣ^{1/2}}`
  (step 3; the load-bearing analytic lemma).

The trivial realizations here let `BanachBilinear.mildBilinear` and
`BanachBilinear.picardMap` be instantiated with concrete inputs that
type-check. With these choices `mildBilinear = 0` identically, exactly
like the previous `trivialBilinear` on the Schwartz side — but now with
the correct type signatures, so a drop-in replacement by the real
operators (step 2c, separate commit — the actual density-extension of
`vectorHeatEvolveFreq` / `lerayProjectFreq` / `convectiveComponent`
from `VectorSchwartz3C` to `VectorBanach3C`) is a 1-line change at the
call site.

### The deferred mathematical content

Each real operator exists on the Schwartz side (`HeatSemigroupVector`,
`LerayProjectorOperator`, `ConvectiveDerivative` — ~820 L combined).
Lifting each to `VectorBanach3C` uses the standard pattern:

1. Prove the Schwartz operator is bounded in the `L²` norm (Plancherel
   on the Fourier side; the symbols `e^{-t|ξ|²}` and `I - ξ⊗ξ/|ξ|²` are
   bounded by 1).
2. Extend by density: `SchwartzMap R3 C3` is dense in `Lp C3 2 volume`
   via mathlib's `SchwartzMap.denseRange_toLp` (or equivalent).
3. Package as `ContinuousLinearMap` via
   `UniformContinuousOn.continuousExtend` on the dense subspace, or
   mathlib's `DenseInducing` machinery.

For the convective derivative the situation is different: `(u·∇)v`
genuinely takes `H^{1/2}` out of `H^{1/2}` (into `H^{-1/2}`), so the
lift's target space is weaker than its source. This is why the full
Fujita-Kato argument composes convective with heat + Leray to recover
the `H^{1/2}` space, and why the product estimate (step 3) is the
load-bearing step — not a mechanical lift.

Three-axiom bar: every declaration kernel-clean
`[propext, Classical.choice, Quot.sound]`. No sorry.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-17.
-/
import PF.NavierStokes.FujitaKato1964.BanachCarrier

set_option autoImplicit false

namespace PF.NavierStokes.FujitaKato1964

open MeasureTheory

noncomputable section

/-! ## §1 — The heat semigroup CLM. -/

/-- **Banach-side heat semigroup `e^{tΔ}` as a CLM**. **Trivial realization**
(`CLM.id`) at the type level pending the real Fourier-multiplier lift;
step 2c. This choice satisfies `banachHeatSemigroup 0 = 𝟙` — the
Picard initial-datum hypothesis — and `‖banachHeatSemigroup t‖ ≤ 1` for
all `t` (trivially, as `CLM.id` has operator norm 1).

The real `e^{tΔ}` on `L²(ℝ³, ℂ³)` acts in Fourier space by multiplication
by `e^{-t|ξ|²}` (a Schwartz multiplier bounded by 1 on `t ≥ 0`), lifted
by Plancherel density. -/
def banachHeatSemigroup (_t : ℝ) : VectorBanach3C →L[ℂ] VectorBanach3C :=
  ContinuousLinearMap.id ℂ VectorBanach3C

/-- `banachHeatSemigroup 0 = 𝟙` — the Picard initial-datum hypothesis. -/
theorem banachHeatSemigroup_zero :
    banachHeatSemigroup 0 = ContinuousLinearMap.id ℂ VectorBanach3C := rfl

/-! ## §2 — The Leray projection CLM. -/

/-- **Banach-side Leray projection `ℙ` as a CLM**. **Trivial realization**
(`CLM.id`) pending the Fourier-multiplier lift; step 2c. The real
operator is `(ℙf)^(ξ) = f̂(ξ) − (ξ·f̂(ξ)/|ξ|²) ξ`, bounded by 1 on
`L²(ℝ³, ℂ³)` (orthogonal projection). -/
def banachLerayProjection : VectorBanach3C →L[ℂ] VectorBanach3C :=
  ContinuousLinearMap.id ℂ VectorBanach3C

/-! ## §3 — The convective derivative. -/

/-- **Banach-side convective derivative `(u·∇) v`**. **Trivial realization**
(zero map) pending the full product-estimate lift; step 3.

The real convective derivative, `((u·∇) v)_j = Σᵢ uᵢ ∂ᵢ vⱼ`, takes
`H^{1/2}` out of `H^{1/2}` (into `H^{-1/2}` — one Sobolev order
weaker). The step-3 product estimate restores the balance after
composition with heat + Leray.

In the trivial realization used here, `conv u v = 0`, so the bilinear
`mildBilinear` instantiated with these operators yields `B(u,v) = 0`,
matching the previous `trivialBilinear` on the Schwartz side — but with
correct Banach types throughout. -/
def banachConvectiveDerivative (_u _v : VectorBanach3C) : VectorBanach3C :=
  (0 : VectorBanach3C)

/-- `conv 0 v = 0` for the Picard initial-datum hypothesis. (Satisfied
trivially by the trivial realization.) -/
theorem banachConvectiveDerivative_zero_left (v : VectorBanach3C) :
    banachConvectiveDerivative (0 : VectorBanach3C) v = 0 := rfl

/-- `conv u 0 = 0` dual hypothesis. -/
theorem banachConvectiveDerivative_zero_right (u : VectorBanach3C) :
    banachConvectiveDerivative u (0 : VectorBanach3C) = 0 := rfl

end

end PF.NavierStokes.FujitaKato1964

/-! ## §Axiom check -/
#print axioms PF.NavierStokes.FujitaKato1964.banachHeatSemigroup_zero
#print axioms PF.NavierStokes.FujitaKato1964.banachConvectiveDerivative_zero_left
#print axioms PF.NavierStokes.FujitaKato1964.banachConvectiveDerivative_zero_right
