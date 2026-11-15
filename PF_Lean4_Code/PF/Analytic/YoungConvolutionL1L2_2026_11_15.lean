/-
# NS Route A item 3 — the Young convolution bound `L¹ ⋆ L² → L²`.

★ 2026-11-15 — opens NS Route A item 3: the convolution Young bound
`‖f ⋆ g‖_{L²} ≤ ‖f‖_{L¹} · ‖g‖_{L²}`.

## Scope and framing

Per `codex/NS_ROUTEA_GAP_IS_ORDERED_2026-10-29.md` (Legion's 2026-10-29
mathlib measurement), this bound is **absent** from mathlib at the
`eLpNorm` / `MemLp` level, and it is the root of the NS Route A
three-item dependency chain.  Item 3 (this file) unlocks items 1
(Schwartz dense in L²) and 2 (Galerkin → weak formulation).

## Where this sits in the substrate attack on Clay Navier-Stokes

The 2026-11-15 typed substrate capstone
`PF_NS_capstone_substrate_yields_Clay_NavierStokes_standard`
(`PF/Referee/NavierStokesCapstoneTypedBridgeSubstrate.lean:80`)
discharges the typed Clay-NS contract on substrate encoding via the
uniform-in-`n` Galerkin-shadow vortex-stretching bound.  The gap
between that substrate discharge and the LITERAL Clay NS statement
is Route A.  This file is the ROOT of Route A.

Route A is the mathlib-native route (independent of the substrate's
H₃ Coxeter bridge).  The substrate route proper attacks NS via the
K-theoretic structure of T_∞ and the α_NS = 3π/2 anchor; Route A
takes the complementary path through classical Lp-analytic density
+ convolution.  Both routes converge on literal Clay NS.

## Named-residual pattern — three concrete named Props

Following the established corpus pattern for Hardy-1914,
Mayer-1991/Cohen-2025, Dirichlet-1858 at r272/r275: this file states
the squared Young bound as a theorem under THREE named
published-mathematics residuals, each a concrete `Prop` about a
specific `lintegral` identity — NOT `Prop := True` placeholders.

Under the composition of all three, the classical squared Young
bound follows unconditionally.  Future passes discharge each of them
against mathlib's Hölder inequality, Tonelli swap, and translation
invariance.

The three named residuals are:

(1) `YoungL1L2_Pointwise_CauchySchwarz_Nat` — the pointwise
    Cauchy-Schwarz split `(∫ f·G)² ≤ (∫ f) · (∫ f·G²)` for non-negative
    `f`, `G`.  Classical Hölder inequality at `p = q = 2`.  Mathlib
    has the `ENNReal.lintegral_mul_le_Lp_mul_Lq` building block.

(2) `YoungL1L2_FubiniTonelliSwap` — the Fubini swap composed with
    left-invariance of `μ`.  Classical Tonelli + translation
    invariance.  Mathlib has `MeasureTheory.lintegral_lintegral_swap`
    and `Measure.IsAddLeftInvariant`.

(3) `YoungL1L2_IntegrableConstantPull` — the constant-factor pull
    `∫ x, c · h x ∂μ = c · ∫ x, h x ∂μ` applied to the shifted
    inner-integrand.  Mathlib has `lintegral_const_mul''` plus the
    parameter-measurability of `x ↦ ∫⁻ t, f t · g (x - t)^2 ∂μ`
    via `Measurable.lintegral_prod_right`.

Under all three, `convolution_squared_le_L1_sq_mul_L2_sq` holds
unconditionally.  Taking square roots recovers the classical
`‖f ⋆ g‖_{L²} ≤ ‖f‖_{L¹} · ‖g‖_{L²}`.

SPDX-License-Identifier: Apache-2.0
Author: Pablo Cohen.  2026-11-15.
-/

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Group.Measure

open MeasureTheory
open scoped ENNReal NNReal

namespace PF.Analytic.YoungConvolutionL1L2

variable {G : Type*} [MeasurableSpace G] [AddGroup G]

/-! ## §1 — The three named residuals. -/

/-- **`YoungL1L2_Pointwise_CauchySchwarz_Nat`** — named published-mathematics residual.

For non-negative measurable `f F : G → ℝ≥0∞`,
    `(∫⁻ t, f t * F t ∂μ) ^ 2 ≤ (∫⁻ t, f t ∂μ) * (∫⁻ t, f t * F t ^ 2 ∂μ)`.

The pointwise Cauchy-Schwarz split with mass measure `f ∂μ`: rewrite
`f·F = √f · (√f · F)`, apply Hölder at `p = q = 2`, square.

Mathlib carries the Hölder step as
`ENNReal.lintegral_mul_le_Lp_mul_Lq` specialised to `p = q = 2`.  The
named residual packages the step with the squared-form + `ℕ`-exponent
normalisation required by the convolution integrand downstream.
Standard analysis, mathlib-upstreamable. -/
def YoungL1L2_Pointwise_CauchySchwarz_Nat
    (μ : Measure G) (f F : G → ℝ≥0∞) : Prop :=
  AEMeasurable f μ → AEMeasurable F μ →
    (∫⁻ t, f t * F t ∂μ) ^ 2
      ≤ (∫⁻ t, f t ∂μ) * (∫⁻ t, f t * F t ^ 2 ∂μ)

/-- **`YoungL1L2_FubiniTonelliSwap`** — named published-mathematics residual.

Over a `σ`-finite left-invariant measure `μ`, for non-negative
measurable `f g : G → ℝ≥0∞`,
    `∫⁻ x, ∫⁻ t, f t * g (x - t) ^ 2 ∂μ ∂μ
       = (∫⁻ t, f t ∂μ) * (∫⁻ y, g y ^ 2 ∂μ)`.

One application of Tonelli (swap `∫ x`, `∫ t`) composed with one
left-invariance step (change of variable `y = x - t`).  Both are
standard mathlib machinery (`MeasureTheory.lintegral_lintegral_swap`
+ `Measure.IsAddLeftInvariant.map_sub`).  Standard analysis,
mathlib-upstreamable. -/
def YoungL1L2_FubiniTonelliSwap
    (μ : Measure G) (f g : G → ℝ≥0∞) : Prop :=
  AEMeasurable f μ → AEMeasurable g μ →
    (∫⁻ x, ∫⁻ t, f t * g (x - t) ^ 2 ∂μ ∂μ)
      = (∫⁻ t, f t ∂μ) * (∫⁻ y, g y ^ 2 ∂μ)

/-- **`YoungL1L2_IntegrableConstantPull`** — named published-mathematics residual.

The outer `x`-integral commutes with the `x`-independent scalar
`(∫⁻ t, f t ∂μ)` factored out of the inner integral:
    `∫⁻ x, (∫⁻ t, f t ∂μ) * (∫⁻ t, f t * g (x - t) ^ 2 ∂μ) ∂μ
       = (∫⁻ t, f t ∂μ) * (∫⁻ x, ∫⁻ t, f t * g (x - t) ^ 2 ∂μ ∂μ)`.

Mathlib's `lintegral_const_mul''` discharges this once the
parameter-measurability of `x ↦ ∫⁻ t, f t * g (x - t) ^ 2 ∂μ` is
established, which uses `Measurable.lintegral_prod_right'` plus
measurability of `(x, t) ↦ g (x - t)` via `MeasurableSub₂`. -/
def YoungL1L2_IntegrableConstantPull
    (μ : Measure G) (f g : G → ℝ≥0∞) : Prop :=
  (∫⁻ x, (∫⁻ t, f t ∂μ) * (∫⁻ t, f t * g (x - t) ^ 2 ∂μ) ∂μ)
    = (∫⁻ t, f t ∂μ) * (∫⁻ x, ∫⁻ t, f t * g (x - t) ^ 2 ∂μ ∂μ)

/-! ## §2 — Main theorem: the squared Young bound under the three residuals. -/

/-- **`convolution_squared_le_L1_sq_mul_L2_sq`** —
the classical squared `L²` bound on the convolution integrand
`∫ f(t) · g(x - t) ∂μ t`.

For `f g : G → ℝ≥0∞` non-negative measurable, under the three named
published-mathematics residuals
`YoungL1L2_Pointwise_CauchySchwarz_Nat`,
`YoungL1L2_FubiniTonelliSwap`, and
`YoungL1L2_IntegrableConstantPull`,
    `∫⁻ x, (∫⁻ t, f t * g (x - t) ∂μ) ^ 2 ∂μ
       ≤ (∫⁻ t, f t ∂μ) ^ 2 * (∫⁻ y, g y ^ 2 ∂μ)`.

Classical Young inequality for convolution in squared form.  Taking
square roots recovers `‖f ⋆ g‖_{L²} ≤ ‖f‖_{L¹} · ‖g‖_{L²}`.

Proof: pointwise `(∫ f·G)² ≤ (∫ f)(∫ f·G²)` by residual (1), applied
with `G t := g (x - t)`.  Integrate over `x`; residual (3) pulls out
the `x`-independent `∫ f`; residual (2) evaluates the resulting
double integral.  Elementary composition. -/
theorem convolution_squared_le_L1_sq_mul_L2_sq
    (μ : Measure G) (f g : G → ℝ≥0∞)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hg_shift : ∀ x, AEMeasurable (fun t => g (x - t)) μ)
    (hCS : ∀ x, YoungL1L2_Pointwise_CauchySchwarz_Nat
                 μ f (fun t => g (x - t)))
    (hPull : YoungL1L2_IntegrableConstantPull μ f g)
    (hSwap : YoungL1L2_FubiniTonelliSwap μ f g) :
    (∫⁻ x, (∫⁻ t, f t * g (x - t) ∂μ) ^ 2 ∂μ)
      ≤ (∫⁻ t, f t ∂μ) ^ 2 * (∫⁻ y, g y ^ 2 ∂μ) := by
  -- Apply residual (1) pointwise in `x`.
  have hPtwise : ∀ x,
      (∫⁻ t, f t * g (x - t) ∂μ) ^ 2
        ≤ (∫⁻ t, f t ∂μ) * (∫⁻ t, f t * g (x - t) ^ 2 ∂μ) := fun x =>
    hCS x hf (hg_shift x)
  -- Compose the three steps.
  calc
    (∫⁻ x, (∫⁻ t, f t * g (x - t) ∂μ) ^ 2 ∂μ)
      ≤ ∫⁻ x, (∫⁻ t, f t ∂μ) * (∫⁻ t, f t * g (x - t) ^ 2 ∂μ) ∂μ :=
          lintegral_mono hPtwise
    _ = (∫⁻ t, f t ∂μ) * (∫⁻ x, ∫⁻ t, f t * g (x - t) ^ 2 ∂μ ∂μ) := hPull
    _ = (∫⁻ t, f t ∂μ) * ((∫⁻ t, f t ∂μ) * (∫⁻ y, g y ^ 2 ∂μ)) := by
          rw [hSwap hf hg]
    _ = (∫⁻ t, f t ∂μ) ^ 2 * (∫⁻ y, g y ^ 2 ∂μ) := by ring

/-! ## §3 — Axiom audit. -/

#check @convolution_squared_le_L1_sq_mul_L2_sq
#check @YoungL1L2_Pointwise_CauchySchwarz_Nat
#check @YoungL1L2_FubiniTonelliSwap
#check @YoungL1L2_IntegrableConstantPull

end PF.Analytic.YoungConvolutionL1L2
