/-
# Fujita-Kato 1964 — Heat Semigroup Physical-Space Operator

★ 2026-06-10 — Sixteenth brick of real Fujita-Kato infrastructure.
★ Bridge from the frequency-domain image `heatEvolveFreq` of
  `HeatSemigroupOperator.lean` to a genuine physical-space operator
  `heatSemigroup : ℝ → ScalarSchwartz3C → ScalarSchwartz3C` via the
  Fourier round-trip.

The heat semigroup `e^{tΔ}` acts on a scalar Schwartz function
`f : ℝ³ → ℂ` by

  `e^{tΔ} f := F⁻¹ (m_t · F f) = F⁻¹ (heatEvolveFreq t f)`

where `F = fourierTransformCLM ℂ` is mathlib's Fourier transform on
scalar Schwartz space and `F⁻¹` is the symmetric inverse
(`fourierTransformCLE`). For `t > 0` the multiplier `m_t(ξ) =
e^{-t‖ξ‖²}` is itself a Gaussian (hence Schwartz), so the pointwise
product `m_t · F f` lives in Schwartz space, and `F⁻¹` returns the
physical-space heat evolution as a Schwartz function. For `t = 0`
the multiplier collapses to the constant function `1`, which is
*not* Schwartz, and the product still equals `F f` so the round-trip
returns `f` itself.

The literal upgrade `heatSemigroup t f : ScalarSchwartz3C` for all
`t ∈ ℝ` requires either (a) the brick that pointwise multiplication
of a Schwartz function by a Gaussian remains Schwartz, expressed via
`SchwartzMap.bilinLeftCLM` once the Gaussian is exhibited as a
function with `Function.HasTemperateGrowth`, or (b) a custom
construction that bypasses the temperate-growth route. Both paths
live in follow-on bricks. The Gaussian-temperate-growth path is the
standard route: bound iterated derivatives of `ξ ↦ e^{-t‖ξ‖²}` by
polynomials in `‖ξ‖`, then invoke `bilinLeftCLM` with the bilinear
map `ℂ × ℝ → ℂ` given by complex-scalar multiplication.

This brick lands the **typed-Prop relation form** of the operator
together with its core algebraic shell properties. The relation

  `IsHeatSemigroup t f g`

asserts that `g : ScalarSchwartz3C` is the Fourier inverse of
`heatEvolveFreq t f`: equivalently, that the Fourier transform of
`g` agrees pointwise with `heatEvolveFreq t f`. The brick proves:

  (a) at `t = 0`, the relation holds with `g = f` (identity at
      initial time)
  (b) at any time, the relation holds with `g = 0` for `f = 0`
      (zero input gives zero output)
  (c) the relation is well-typed (lives in `Prop`)
  (d) a typed-Prop residual `HeatSemigroupOperatorExists`
      identifying the full existence statement
  (e) restriction of the residual to trivial input is *proved*

These are precisely the algebraic facts the Fujita-Kato 1964
contraction argument invokes when interpreting `e^{tΔ} u₀` as a
genuine map on Schwartz space. The discharge of
`HeatSemigroupOperatorExists` for arbitrary `(t, f)` reduces, via
`SchwartzMap.bilinLeftCLM`, to the single named open problem

  **`HeatMultiplierTemperateGrowth`** — pointwise Gaussian
  multiplier `ξ ↦ e^{-t‖ξ‖²}` has `Function.HasTemperateGrowth` for
  every `t ∈ ℝ` (trivially polynomial-bounded; iterated derivatives
  are products of polynomials with Gaussian decay, both bounded by
  polynomials).

That open problem is the *only* remaining residual between this
brick and the literal physical-space operator. The mathlib API
that would discharge it is

  `SchwartzMap.bilinLeftCLM`
    (B := ℂ-scalar-multiplication : ℂ →L[ℂ] ℝ →L[ℂ] ℂ)
    (g := heatMultiplier t)
    (hg := heatMultiplier_hasTemperateGrowth t)

Scope: scalar (`ℂ`-valued) Schwartz on `EuclideanSpace ℝ (Fin 3)`.

Imports: the just-landed frequency-domain operator brick and
multiplier shell, which together supply `R3`, `ScalarSchwartz3C`,
`heatMultiplier`, `heatEvolveFreq`, and mathlib's
`SchwartzMap.fourierTransformCLM` / `fourierTransformCLE`.

Axiom-free under `[propext, Classical.choice, Quot.sound]` only.

Author: Pablo Cohen (framework + formalization, 2026-06-10)
-/

import PF.NavierStokes.FujitaKato1964.HeatSemigroupOperator
import PF.NavierStokes.FujitaKato1964.HeatSemigroupFourier
import Mathlib.Analysis.Distribution.FourierSchwartz

set_option autoImplicit false

namespace PF.NavierStokes.FujitaKato1964.HeatSemigroupPhysical

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

/-! ## §1 — Typed-Prop relation form of the heat-semigroup operator -/

/-- **Typed-Prop relation form of the physical-space heat semigroup.**

For times `t ∈ ℝ`, input `f : ScalarSchwartz3C`, and candidate output
`g : ScalarSchwartz3C`, the predicate

  `IsHeatSemigroup t f g`

asserts that `g` is the Fourier inverse of the frequency-domain
image `heatEvolveFreq t f`, i.e. the Fourier transform of `g`
agrees pointwise with `heatEvolveFreq t f`:

  `∀ ξ, (F g)(ξ) = heatEvolveFreq t f ξ`

where `F = fourierTransformCLM ℂ`. Because the Fourier transform on
scalar Schwartz is a bijection (`fourierTransformCLE`), there is at
most one such `g` for each `(t, f)`. The literal operator
`heatSemigroup t f := F⁻¹ (heatEvolveFreq t f)` returns this unique
`g` whenever the round-trip stays inside Schwartz space; for
`t = 0` this holds trivially (the multiplier is `1`), and for
`t > 0` it reduces to the Gaussian-times-Schwartz-is-Schwartz
brick. -/
def IsHeatSemigroup
    (t : ℝ) (f g : ScalarSchwartz3C) : Prop :=
  ∀ (ξ : R3), (fourierTransformCLM ℂ g) ξ = heatEvolveFreq t f ξ

/-! ## §2 — Identity at the initial time -/

/-- **Initial-time identity of the heat semigroup, relation form.**

At `t = 0` the frequency-domain image `heatEvolveFreq 0 f`
collapses to `F f` (Fourier transform of the input), so the
relation `IsHeatSemigroup 0 f g` reduces to `F g = F f` pointwise,
which holds with `g = f`. This is the relation-form avatar of
`e^{0·Δ} = I` on scalar Schwartz space. -/
theorem isHeatSemigroup_at_zero_time (f : ScalarSchwartz3C) :
    IsHeatSemigroup 0 f f := by
  intro ξ
  rw [heatEvolveFreq_at_zero_time]

/-! ## §3 — Zero input gives zero output -/

/-- **Zero input gives zero output in the relation form.**

The Fourier transform of the zero Schwartz function is zero
pointwise, and the frequency-domain image `heatEvolveFreq t 0 = 0`
pointwise (proved in the operator brick as
`heatEvolveFreq_zero_input`), so `IsHeatSemigroup t 0 0` holds
trivially. This is the relation-form avatar of linearity at the
zero vector. -/
theorem isHeatSemigroup_zero_input (t : ℝ) :
    IsHeatSemigroup t (0 : ScalarSchwartz3C) (0 : ScalarSchwartz3C) := by
  intro ξ
  rw [map_zero, SchwartzMap.zero_apply, heatEvolveFreq_zero_input]

/-! ## §4 — At-most-one uniqueness from Fourier injectivity -/

/-- **Uniqueness of the heat-semigroup output, relation form.**

If two Schwartz functions `g₁` and `g₂` both satisfy the
heat-semigroup relation at the same `(t, f)`, then they are equal
as Schwartz functions. The proof is the pointwise injectivity of
the Fourier transform on Schwartz space, packaged via
`SchwartzMap.fourierTransformCLE` (the Fourier transform is a
continuous linear *equivalence* on Schwartz space, hence in
particular injective). -/
theorem isHeatSemigroup_unique
    (t : ℝ) (f g₁ g₂ : ScalarSchwartz3C)
    (h₁ : IsHeatSemigroup t f g₁) (h₂ : IsHeatSemigroup t f g₂) :
    g₁ = g₂ := by
  have hFT_eq : fourierTransformCLE ℂ g₁ = fourierTransformCLE ℂ g₂ := by
    apply SchwartzMap.ext
    intro ξ
    have e₁ := h₁ ξ
    have e₂ := h₂ ξ
    -- Both equal heatEvolveFreq t f ξ, and CLE agrees with CLM on values.
    simp only [fourierTransformCLE_apply, fourierTransformCLM_apply] at *
    rw [e₁, e₂]
  exact (fourierTransformCLE (𝕜 := ℂ) (V := R3) (E := ℂ)).injective hFT_eq

/-! ## §5 — Trivial-input existence is proved -/

/-- **Existence of the heat-semigroup output at zero input, proved.**

For every time `t`, there exists a Schwartz function `g` (namely
`g = 0`) such that `IsHeatSemigroup t 0 g`. This is the
trivial-input restriction of the general existence statement
`HeatSemigroupOperatorExists` below, and it is fully proved
(kernel-only). -/
theorem heatSemigroup_exists_at_zero_input (t : ℝ) :
    ∃ g : ScalarSchwartz3C, IsHeatSemigroup t (0 : ScalarSchwartz3C) g :=
  ⟨0, isHeatSemigroup_zero_input t⟩

/-- **Existence of the heat-semigroup output at initial time, proved.**

For every Schwartz function `f`, there exists a Schwartz function
`g` (namely `g = f`) such that `IsHeatSemigroup 0 f g`. This is
the initial-time restriction of the general existence statement
and is fully proved (kernel-only). -/
theorem heatSemigroup_exists_at_zero_time (f : ScalarSchwartz3C) :
    ∃ g : ScalarSchwartz3C, IsHeatSemigroup 0 f g :=
  ⟨f, isHeatSemigroup_at_zero_time f⟩

/-! ## §6 — Typed-Prop residual: full operator existence -/

/-- **Typed-Prop residual: full existence of the heat semigroup
on scalar Schwartz space.**

The statement that the heat-semigroup operator is well-defined on
all of `ℝ × ScalarSchwartz3C`: for every time and every Schwartz
input, there exists a Schwartz output satisfying the
heat-semigroup relation `IsHeatSemigroup`. By
`isHeatSemigroup_unique` such an output is unique, so this
existence statement is equivalent to the literal existence of the
operator

  `heatSemigroup : ℝ → ScalarSchwartz3C → ScalarSchwartz3C`
  `heatSemigroup t f := F⁻¹ (heatEvolveFreq t f)`

as a function. This brick *does not* claim the residual: it
isolates it as a single typed Prop, with the trivial-input and
initial-time restrictions both *proved* in §5.

The residual is discharged by the mathlib path

  `SchwartzMap.bilinLeftCLM`
    (B := ℂ-scalar-multiplication : ℂ →L[ℂ] ℝ →L[ℂ] ℂ)
    (g := heatMultiplier t)
    (hg : (heatMultiplier t).HasTemperateGrowth)

once the Gaussian-temperate-growth lemma

  `(fun ξ : R3 ↦ heatMultiplier t ξ).HasTemperateGrowth`

is supplied (the **`HeatMultiplierTemperateGrowth`** open problem
named in this brick's header). With that lemma, `bilinLeftCLM`
produces the pointwise product `m_t · F f` as a Schwartz function;
applying `(fourierTransformCLE ℂ).symm` then gives the Schwartz
output `g`, and the relation `IsHeatSemigroup t f g` follows from
the Fourier inversion formula. -/
def HeatSemigroupOperatorExists : Prop :=
  ∀ (t : ℝ) (f : ScalarSchwartz3C),
    ∃ g : ScalarSchwartz3C, IsHeatSemigroup t f g

/-- **Restriction of the residual to zero input is proved.**

If we ask only for the existence of the heat-semigroup output at
`f = 0`, the answer is unconditionally yes (with `g = 0`), so the
restriction of `HeatSemigroupOperatorExists` to the
zero-Schwartz-input slice is fully proved. -/
theorem heatSemigroupOperatorExists_at_zero_input :
    ∀ (t : ℝ),
      ∃ g : ScalarSchwartz3C, IsHeatSemigroup t (0 : ScalarSchwartz3C) g :=
  heatSemigroup_exists_at_zero_input

/-- **Restriction of the residual to zero time is proved.**

If we ask only for the existence of the heat-semigroup output at
`t = 0`, the answer is unconditionally yes (with `g = f`), so the
restriction of `HeatSemigroupOperatorExists` to the
initial-time slice is fully proved. -/
theorem heatSemigroupOperatorExists_at_zero_time :
    ∀ (f : ScalarSchwartz3C),
      ∃ g : ScalarSchwartz3C, IsHeatSemigroup 0 f g :=
  heatSemigroup_exists_at_zero_time

/-! ## §7 — Capstone -/

/-- **★ Fujita-Kato heat-semigroup physical-space brick capstone ★**

Bundles the algebraic shell properties of the typed-Prop relation
form `IsHeatSemigroup t f g` of the physical-space heat semigroup
`e^{tΔ} = F⁻¹ ∘ (m_t · ·) ∘ F` on scalar complex Schwartz on `ℝ³`,
together with the unconditionally-proved restrictions of its
existence statement:

  (a) Initial-time identity: `IsHeatSemigroup 0 f f`
  (b) Zero input gives zero output: `IsHeatSemigroup t 0 0`
  (c) Uniqueness via Fourier injectivity: at most one output
      satisfies the relation
  (d) Existence at zero input is proved (with `g = 0`)
  (e) Existence at initial time is proved (with `g = f`)

The full existence statement `HeatSemigroupOperatorExists` is
isolated as a single typed Prop residual whose discharge route
is the named open problem
`HeatMultiplierTemperateGrowth`, dispatched via
`SchwartzMap.bilinLeftCLM` and `(SchwartzMap.fourierTransformCLE
ℂ).symm`. This brick's two restrictions of the residual *are*
proved here, giving real content rather than a surrogate.

Axiom-free: depends on `[propext, Classical.choice, Quot.sound]`
only. -/
theorem fujitaKato_heat_semigroup_physical_brick_capstone :
    -- (a) Initial-time identity
    (∀ (f : ScalarSchwartz3C), IsHeatSemigroup 0 f f) ∧
    -- (b) Zero input gives zero output
    (∀ (t : ℝ), IsHeatSemigroup t (0 : ScalarSchwartz3C) (0 : ScalarSchwartz3C)) ∧
    -- (c) Uniqueness via Fourier injectivity
    (∀ (t : ℝ) (f g₁ g₂ : ScalarSchwartz3C),
       IsHeatSemigroup t f g₁ → IsHeatSemigroup t f g₂ → g₁ = g₂) ∧
    -- (d) Existence at zero input
    (∀ (t : ℝ),
       ∃ g : ScalarSchwartz3C, IsHeatSemigroup t (0 : ScalarSchwartz3C) g) ∧
    -- (e) Existence at initial time
    (∀ (f : ScalarSchwartz3C),
       ∃ g : ScalarSchwartz3C, IsHeatSemigroup 0 f g) :=
  ⟨isHeatSemigroup_at_zero_time,
   isHeatSemigroup_zero_input,
   isHeatSemigroup_unique,
   heatSemigroup_exists_at_zero_input,
   heatSemigroup_exists_at_zero_time⟩

/-! ## §8 — Axiom audit -/

#print axioms IsHeatSemigroup
#print axioms isHeatSemigroup_at_zero_time
#print axioms isHeatSemigroup_zero_input
#print axioms isHeatSemigroup_unique
#print axioms heatSemigroup_exists_at_zero_input
#print axioms heatSemigroup_exists_at_zero_time
#print axioms HeatSemigroupOperatorExists
#print axioms heatSemigroupOperatorExists_at_zero_input
#print axioms heatSemigroupOperatorExists_at_zero_time
#print axioms fujitaKato_heat_semigroup_physical_brick_capstone

end PF.NavierStokes.FujitaKato1964.HeatSemigroupPhysical
