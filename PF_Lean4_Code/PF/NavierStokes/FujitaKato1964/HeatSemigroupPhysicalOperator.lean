/-
# Fujita-Kato 1964 — Heat Semigroup Physical-Space Operator (CLM Realization)

★ 2026-06-10 — Twenty-eighth brick of real Fujita-Kato infrastructure.
★ Promotes the typed-Prop relation `IsHeatSemigroup` of
  `HeatSemigroupPhysical.lean` into an actual operator
  `ScalarSchwartz3C → ScalarSchwartz3C` realized through
  `SchwartzMultiplication.schwartzMul` post-composed with
  `SchwartzMap.fourierTransformCLE`.

The heat semigroup `e^{tΔ}` acts on a scalar Schwartz function
`f : ℝ³ → ℂ` by

  `e^{tΔ} f := F⁻¹ (m_t · F f)`

where `m_t(ξ) = e^{-t‖ξ‖²}` is the Gaussian Fourier symbol and
`F = SchwartzMap.fourierTransformCLE ℂ` is mathlib's Fourier
transform on scalar Schwartz space. This brick lands the literal
operator in three layers of unconditional content together with a
single hypothesis-typed lift of the general construction:

§1 — Initial-time identity at the literal-operator level. At `t = 0`
the multiplier collapses to the constant `1`, so the operator is the
identity on `ScalarSchwartz3C`. We define
`heatSemigroupAtZeroTime f := f` (a definitional rewrite of the
literal operator at `t = 0`) and verify `IsHeatSemigroup 0 f
(heatSemigroupAtZeroTime f)` and the pointwise identity
`heatSemigroupAtZeroTime f x = f x` (both by `rfl`).

§2 — Zero-input collapse at the literal-operator level. For `f = 0`
the heat semigroup returns `0` for every `t`. We define
`heatSemigroupAtZeroInput t := (0 : ScalarSchwartz3C)` and verify
`IsHeatSemigroup t 0 (heatSemigroupAtZeroInput t)` and the pointwise
identity `heatSemigroupAtZeroInput t x = 0`.

§3 — Conditional general operator under the temperate-growth
hypothesis. Given a witness

  `h : (fun ξ : R3 => (heatMultiplier t ξ : ℂ)).HasTemperateGrowth`

(the complexified Gaussian symbol has temperate growth), we define

  `heatPhysicalUnderTemperate t h f :=
     (SchwartzMap.fourierTransformCLE ℂ).symm
       ((SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) h)
         ((SchwartzMap.fourierTransformCLE ℂ) f))`

as a Schwartz function. This is the literal physical-space heat
semigroup: Fourier-transform, multiply by the Gaussian symbol,
inverse-Fourier-transform. The construction lives in scalar Schwartz
space because each step does: `fourierTransformCLE` is a CLE on
`𝓢(R3, ℂ)`, `bilinLeftCLM` of complex multiplication against a
function of temperate growth is a CLM on `𝓢(R3, ℂ)`, and the
symmetric inverse `(fourierTransformCLE ℂ).symm` returns to
`𝓢(R3, ℂ)`. We verify that this realization satisfies the
relation-form predicate `IsHeatSemigroup` and discharges the
existence residual `HeatSemigroupOperatorExists` conditionally on
the temperate-growth witness.

§4 — Bridge to the existence residual of
`HeatSemigroupPhysical.lean`. Under the temperate-growth witness
(uniformly in `t ∈ ℝ` quantification), the residual
`HeatSemigroupOperatorExists` is *proved*. We isolate the
hypothesis as the typed Prop

  `HeatMultiplierComplexTemperateGrowth :=
     ∀ t : ℝ, Function.HasTemperateGrowth
       (fun ξ : R3 => (heatMultiplier t ξ : ℂ))`

and prove that this Prop is sufficient to close
`HeatSemigroupOperatorExists`.

§5 — Capstone.

Discharge route for `HeatMultiplierComplexTemperateGrowth`:
`HeatMultiplierTemperateGrowth.lean` lands the real-valued
`Function.HasTemperateGrowth (fun ξ : R3 => heatMultiplier t ξ)`
conditionally on the Faà di Bruno expansion
`IteratedFDerivHeatMultiplierPolynomialBounded t`; composing with
the continuous-linear complex coercion `ℝ →L[ℝ] ℂ` (and
restricting scalars to ℝ for the complexified function on the
ℝ-vector space `R3`) lifts that to the ℂ-valued version required
here. The complexification is a routine mathlib-API step and lives
in a follow-on brick.

Scope: scalar (`ℂ`-valued) Schwartz on `EuclideanSpace ℝ (Fin 3)`.

Imports: the typed-Prop scaffold `HeatSemigroupPhysical.lean`, the
multiplication primitive `SchwartzMultiplication.lean`, and the
temperate-growth provider `HeatMultiplierTemperateGrowth.lean`.

Axiom-free under `[propext, Classical.choice, Quot.sound]` only.

Author: Pablo Cohen (framework + formalization, 2026-06-10)
-/

import PF.NavierStokes.FujitaKato1964.HeatSemigroupPhysical
import PF.NavierStokes.FujitaKato1964.SchwartzMultiplication
import PF.NavierStokes.FujitaKato1964.HeatMultiplierTemperateGrowth

set_option autoImplicit false

namespace PF.NavierStokes.FujitaKato1964.HeatSemigroupPhysicalOperator

open SchwartzMap
open PF.NavierStokes.FujitaKato1964.HeatSemigroupFourier
  (R3
   heatMultiplier
   heatMultiplier_at_zero_time)
open PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier
  (ScalarSchwartz3C)
open PF.NavierStokes.FujitaKato1964.HeatSemigroupOperator
  (heatEvolveFreq
   heatEvolveFreq_at_zero_time
   heatEvolveFreq_zero_input)
open PF.NavierStokes.FujitaKato1964.HeatSemigroupPhysical
  (IsHeatSemigroup
   isHeatSemigroup_at_zero_time
   isHeatSemigroup_zero_input
   HeatSemigroupOperatorExists)

/-! ## §1 — Unconditional `t = 0` operator -/

/-- **Literal physical-space heat semigroup at the initial time.**

At `t = 0` the Gaussian Fourier symbol `m_0(ξ) = e^{-0·‖ξ‖²}`
collapses to the constant `1`, so the heat-semigroup formula
`F⁻¹ (m_0 · F f) = F⁻¹ (F f) = f` returns the input. We bake this
literal identity into a Schwartz-to-Schwartz function

  `heatSemigroupAtZeroTime : ScalarSchwartz3C → ScalarSchwartz3C`

defined as the identity, providing the `t = 0` slice of the
physical-space operator unconditionally. -/
def heatSemigroupAtZeroTime (f : ScalarSchwartz3C) : ScalarSchwartz3C := f

/-- **Pointwise content of `heatSemigroupAtZeroTime`.**

`heatSemigroupAtZeroTime f x = f x` for every `x : R3`. By
definition. -/
theorem heatSemigroupAtZeroTime_apply (f : ScalarSchwartz3C) (x : R3) :
    (heatSemigroupAtZeroTime f) x = f x := rfl

/-- **The `t = 0` operator satisfies the `IsHeatSemigroup` relation.**

`IsHeatSemigroup 0 f (heatSemigroupAtZeroTime f)`: the literal
operator at the initial time produces an output that satisfies the
relation-form predicate of `HeatSemigroupPhysical.lean`. -/
theorem isHeatSemigroup_of_heatSemigroupAtZeroTime (f : ScalarSchwartz3C) :
    IsHeatSemigroup 0 f (heatSemigroupAtZeroTime f) :=
  isHeatSemigroup_at_zero_time f

/-! ## §2 — Unconditional zero-input operator -/

/-- **Literal physical-space heat semigroup at zero input.**

For the zero Schwartz function, the heat-semigroup formula
`F⁻¹ (m_t · F 0) = F⁻¹ (m_t · 0) = F⁻¹ 0 = 0` returns the zero
Schwartz function for every `t ∈ ℝ`. We bake this literal identity
into

  `heatSemigroupAtZeroInput : ℝ → ScalarSchwartz3C`

defined as the constant `0` Schwartz function, providing the
zero-input slice of the physical-space operator unconditionally. -/
noncomputable def heatSemigroupAtZeroInput (_t : ℝ) : ScalarSchwartz3C :=
  (0 : ScalarSchwartz3C)

/-- **Pointwise content of `heatSemigroupAtZeroInput`.**

`heatSemigroupAtZeroInput t x = 0` for every `t ∈ ℝ` and `x : R3`.
By definition (the zero Schwartz function is the zero function). -/
theorem heatSemigroupAtZeroInput_apply (t : ℝ) (x : R3) :
    (heatSemigroupAtZeroInput t) x = 0 := by
  unfold heatSemigroupAtZeroInput
  rw [SchwartzMap.zero_apply]

/-- **The zero-input operator satisfies the `IsHeatSemigroup` relation.**

`IsHeatSemigroup t 0 (heatSemigroupAtZeroInput t)`: the literal
operator at the zero input produces the zero output for every `t`,
and this satisfies the relation-form predicate. -/
theorem isHeatSemigroup_of_heatSemigroupAtZeroInput (t : ℝ) :
    IsHeatSemigroup t (0 : ScalarSchwartz3C) (heatSemigroupAtZeroInput t) :=
  isHeatSemigroup_zero_input t

/-! ## §3 — Conditional general operator under temperate growth -/

/-- **Literal physical-space heat semigroup conditional on the
complexified-Gaussian temperate-growth witness.**

Given a temperate-growth witness for the complexified Gaussian
symbol

  `h : (fun ξ : R3 => (heatMultiplier t ξ : ℂ)).HasTemperateGrowth`,

the heat semigroup `e^{tΔ}` is realised as the composition

  `F⁻¹ ∘ M_{m_t} ∘ F`

where `F = SchwartzMap.fourierTransformCLE ℂ` is the Fourier CLE on
scalar Schwartz space, `F⁻¹` is its symmetric inverse, and
`M_{m_t} = SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) h`
is left-multiplication by the complexified Gaussian symbol as a
continuous endomorphism of `𝓢(R3, ℂ)`.

The construction returns an honest Schwartz function for every
input, and is the literal physical-space heat semigroup at time
`t`. -/
noncomputable def heatPhysicalUnderTemperate
    (t : ℝ)
    (h : Function.HasTemperateGrowth (fun ξ : R3 => (heatMultiplier t ξ : ℂ)))
    (f : ScalarSchwartz3C) : ScalarSchwartz3C :=
  (SchwartzMap.fourierTransformCLE (𝕜 := ℂ) (V := R3) (E := ℂ)).symm
    ((SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) h)
      ((SchwartzMap.fourierTransformCLE (𝕜 := ℂ) (V := R3) (E := ℂ)) f))

/-- **The conditional general operator satisfies the
`IsHeatSemigroup` relation.**

Under the complexified-Gaussian temperate-growth hypothesis, the
literal operator `heatPhysicalUnderTemperate t h f` is the unique
Schwartz function whose Fourier transform agrees pointwise with
`heatEvolveFreq t f`. Indeed:

  `F (F⁻¹ (M_{m_t} (F f))) = M_{m_t} (F f)`

by the Fourier inversion formula (right-inverse identity of the CLE
on `𝓢(R3, ℂ)`), and `(M_{m_t} (F f))(ξ) = (F f)(ξ) · (m_t ξ : ℂ)
= (m_t ξ : ℂ) · (F f)(ξ) = heatEvolveFreq t f ξ` by commutativity of
complex multiplication. -/
theorem isHeatSemigroup_of_heatPhysicalUnderTemperate
    (t : ℝ)
    (h : Function.HasTemperateGrowth (fun ξ : R3 => (heatMultiplier t ξ : ℂ)))
    (f : ScalarSchwartz3C) :
    IsHeatSemigroup t f (heatPhysicalUnderTemperate t h f) := by
  intro ξ
  -- Unfold the literal operator.
  unfold heatPhysicalUnderTemperate
  -- Abbreviate the post-multiplication product as X.
  set X : ScalarSchwartz3C :=
    (SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) h)
      ((SchwartzMap.fourierTransformCLE (𝕜 := ℂ) (V := R3) (E := ℂ)) f) with hXdef
  -- The CLE inverse round-trip: F (F⁻¹ X) ξ = X ξ pointwise.
  have hApply :
      (SchwartzMap.fourierTransformCLE (𝕜 := ℂ) (V := R3) (E := ℂ))
        ((SchwartzMap.fourierTransformCLE (𝕜 := ℂ) (V := R3) (E := ℂ)).symm X) = X :=
    (SchwartzMap.fourierTransformCLE (𝕜 := ℂ) (V := R3) (E := ℂ)).apply_symm_apply X
  have hRoundTrip_pt :
      (fourierTransformCLM ℂ
        ((SchwartzMap.fourierTransformCLE (𝕜 := ℂ) (V := R3) (E := ℂ)).symm X)) ξ
        = X ξ := by
    have hpt := congrArg (fun g : ScalarSchwartz3C => g ξ) hApply
    simp only [fourierTransformCLE_apply, fourierTransformCLM_apply] at hpt ⊢
    exact hpt
  -- Apply the round-trip.
  rw [hRoundTrip_pt]
  -- Pointwise content of X via the `bilinLeftCLM` definitional unfolding:
  --   X ξ = (F f) ξ * (m_t ξ : ℂ)
  -- where F = fourierTransformCLE ℂ (definitionally equal to fourierTransformCLM ℂ).
  -- Both sides of the goal equal `heatEvolveFreq t f ξ` once mul_comm is applied.
  show ((SchwartzMap.fourierTransformCLE (𝕜 := ℂ) (V := R3) (E := ℂ)) f) ξ
         * (heatMultiplier t ξ : ℂ)
       = heatEvolveFreq t f ξ
  -- heatEvolveFreq unfolds to (m_t ξ : ℂ) * (F f) ξ via fourierTransformCLM.
  unfold heatEvolveFreq
  -- fourierTransformCLE_apply and fourierTransformCLM_apply both reduce to the
  -- Fourier integral, so the two CLE/CLM applications coincide pointwise.
  have hCLE_eq_CLM :
      ((SchwartzMap.fourierTransformCLE (𝕜 := ℂ) (V := R3) (E := ℂ)) f) ξ
        = (fourierTransformCLM ℂ f) ξ := by
    simp [fourierTransformCLE_apply, fourierTransformCLM_apply]
  rw [hCLE_eq_CLM, mul_comm]

/-! ## §4 — Bridge to the typed-Prop residual -/

/-- **Typed-Prop residual: complexified-Gaussian temperate-growth
witness uniformly in `t ∈ ℝ`.**

The hypothesis that for *every* time `t ∈ ℝ`, the complexified
Gaussian symbol `ξ ↦ (m_t(ξ) : ℂ)` has temperate growth. This is
the input that `bilinLeftCLM` consumes to lift pointwise
multiplication into a Schwartz endomorphism, uniformly in `t`. It is
the ℂ-valued analogue of `HasTemperateGrowth` of
`HeatMultiplierTemperateGrowth.lean`: the real-valued version
together with the standard composition with the continuous-linear
inclusion `ℝ →L[ℝ] ℂ` (suitably scalar-restricted) discharges this
Prop.

Discharging this residual closes the existence residual
`HeatSemigroupOperatorExists` of `HeatSemigroupPhysical.lean`
unconditionally for all `(t, f) ∈ ℝ × ScalarSchwartz3C`. -/
def HeatMultiplierComplexTemperateGrowth : Prop :=
  ∀ t : ℝ, Function.HasTemperateGrowth (fun ξ : R3 => (heatMultiplier t ξ : ℂ))

/-- **The complexified-Gaussian temperate-growth witness discharges
`HeatSemigroupOperatorExists`.**

Under `HeatMultiplierComplexTemperateGrowth`, the existence
statement `HeatSemigroupOperatorExists` of
`HeatSemigroupPhysical.lean` is proved: for every `(t, f)`, the
explicit witness `heatPhysicalUnderTemperate t (H t) f` satisfies
`IsHeatSemigroup t f g`. -/
theorem heatSemigroupOperatorExists_under_complex_temperate_growth
    (H : HeatMultiplierComplexTemperateGrowth) :
    HeatSemigroupOperatorExists := by
  intro t f
  exact ⟨heatPhysicalUnderTemperate t (H t) f,
         isHeatSemigroup_of_heatPhysicalUnderTemperate t (H t) f⟩

/-! ## §5 — Capstone -/

/-- **★ Fujita-Kato heat-semigroup physical-space operator brick capstone ★**

Bundles the literal-operator content of the physical-space heat
semigroup `e^{tΔ} = F⁻¹ ∘ M_{m_t} ∘ F` on scalar complex Schwartz
on `ℝ³`:

  (a) Initial-time literal operator: `heatSemigroupAtZeroTime` is
      the identity on `ScalarSchwartz3C`, with pointwise content
      `f x` and `IsHeatSemigroup 0 f _` relation
  (b) Zero-input literal operator: `heatSemigroupAtZeroInput` is
      the zero Schwartz function for every `t`, with pointwise
      content `0` and `IsHeatSemigroup t 0 _` relation
  (c) Conditional general operator: under the complexified-Gaussian
      temperate-growth witness, the literal operator
      `heatPhysicalUnderTemperate` satisfies the relation
      `IsHeatSemigroup t f _`
  (d) Bridge to the typed-Prop residual: the uniform-in-`t`
      complexified-Gaussian temperate-growth hypothesis
      `HeatMultiplierComplexTemperateGrowth` discharges
      `HeatSemigroupOperatorExists` of `HeatSemigroupPhysical.lean`

The conditional general operator and the bridge to the residual
provide the literal physical-space heat semigroup once the
complexified-Gaussian temperate-growth witness is supplied (the
residual `IteratedFDerivHeatMultiplierPolynomialBounded` of
`HeatMultiplierTemperateGrowth.lean`, composed with the standard
real-to-complex coercion). The two unconditional slices give
real-content `t = 0` and `f = 0` content.

Axiom-free: depends on `[propext, Classical.choice, Quot.sound]`
only. -/
theorem fujitaKato_heat_semigroup_physical_operator_brick_capstone :
    -- (a) Initial-time literal operator
    (∀ (f : ScalarSchwartz3C),
       IsHeatSemigroup 0 f (heatSemigroupAtZeroTime f)) ∧
    (∀ (f : ScalarSchwartz3C) (x : R3),
       (heatSemigroupAtZeroTime f) x = f x) ∧
    -- (b) Zero-input literal operator
    (∀ (t : ℝ),
       IsHeatSemigroup t (0 : ScalarSchwartz3C) (heatSemigroupAtZeroInput t)) ∧
    (∀ (t : ℝ) (x : R3),
       (heatSemigroupAtZeroInput t) x = 0) ∧
    -- (c) Conditional general operator
    (∀ (t : ℝ)
       (h : Function.HasTemperateGrowth
              (fun ξ : R3 => (heatMultiplier t ξ : ℂ)))
       (f : ScalarSchwartz3C),
       IsHeatSemigroup t f (heatPhysicalUnderTemperate t h f)) ∧
    -- (d) Bridge to the typed-Prop residual
    (HeatMultiplierComplexTemperateGrowth → HeatSemigroupOperatorExists) :=
  ⟨isHeatSemigroup_of_heatSemigroupAtZeroTime,
   heatSemigroupAtZeroTime_apply,
   isHeatSemigroup_of_heatSemigroupAtZeroInput,
   heatSemigroupAtZeroInput_apply,
   isHeatSemigroup_of_heatPhysicalUnderTemperate,
   heatSemigroupOperatorExists_under_complex_temperate_growth⟩

/-! ## §6 — Axiom audit -/

#print axioms heatSemigroupAtZeroTime
#print axioms heatSemigroupAtZeroTime_apply
#print axioms isHeatSemigroup_of_heatSemigroupAtZeroTime
#print axioms heatSemigroupAtZeroInput
#print axioms heatSemigroupAtZeroInput_apply
#print axioms isHeatSemigroup_of_heatSemigroupAtZeroInput
#print axioms heatPhysicalUnderTemperate
#print axioms isHeatSemigroup_of_heatPhysicalUnderTemperate
#print axioms HeatMultiplierComplexTemperateGrowth
#print axioms heatSemigroupOperatorExists_under_complex_temperate_growth
#print axioms fujitaKato_heat_semigroup_physical_operator_brick_capstone

end PF.NavierStokes.FujitaKato1964.HeatSemigroupPhysicalOperator
