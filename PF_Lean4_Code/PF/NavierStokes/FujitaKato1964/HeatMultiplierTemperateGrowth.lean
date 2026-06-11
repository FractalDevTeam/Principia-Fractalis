/-
# Fujita-Kato 1964 — Heat Multiplier Temperate Growth

★ 2026-06-10 — Twentieth brick of real Fujita-Kato infrastructure.
★ Targets the single named residual `HeatSemigroupOperatorExists` of
  `HeatSemigroupPhysical.lean` by attacking the Gaussian-multiplier
  temperate-growth condition through which `bilinLeftCLM` lifts
  pointwise Gaussian multiplication into a Schwartz endomorphism.

The Fujita-Kato 1964 mild-solution construction requires the heat
semigroup `e^{tΔ}` to act as a genuine map on Schwartz space. On the
Fourier side this is multiplication by the Gaussian symbol

  `m_t(ξ) := e^{-t · ‖ξ‖²}`

and the mathlib API `SchwartzMap.bilinLeftCLM` upgrades pointwise
multiplication by `m_t` into a continuous linear endomorphism of
Schwartz space *exactly* when `(heatMultiplier t).HasTemperateGrowth`
holds (smoothness plus polynomial bounds on every iterated Fréchet
derivative). This brick lands the verified pieces of that condition
and isolates the remaining technical step as a single typed Prop.

What this brick proves unconditionally:

  (a) `heatMultiplier_contDiff` — smoothness of `ξ ↦ e^{-t‖ξ‖²}` on
      `ℝ³` for every real `t`, via `Real.exp.comp` ∘ scalar
      multiplication ∘ `contDiff_norm_sq`. This discharges the first
      conjunct of `HasTemperateGrowth`.

  (b) `heatMultiplier_le_one_pow_zero` — the trivial polynomial bound
      `m_t(ξ) ≤ 1 · (1 + ‖ξ‖)^0` for `t ≥ 0`. This is the `k = 0`
      iterated-derivative bound on `m_t` itself (the `n = 0` slice
      of the temperate-growth condition).

  (c) `heatMultiplier_hasTemperateGrowth_at_zero_time` — at `t = 0`,
      `m_0` is the constant function `1`, and `Function.HasTemperateGrowth`
      is unconditional on constants (`Function.HasTemperateGrowth.const`).

What this brick isolates as a typed-Prop residual:

  (d) `IteratedFDerivHeatMultiplierPolynomialBounded t` — for `t > 0`
      and every `n : ℕ`, the iterated Fréchet derivative
      `iteratedFDeriv ℝ n (heatMultiplier t)` is bounded uniformly
      by `C · (1 + ‖ξ‖)^k` for some `k : ℕ` and `C : ℝ`. This is the
      `∀ n, ∃ k C, ...` conjunct of `Function.HasTemperateGrowth`.
      Mathematically this is *immediate*: the `n`-th derivative of a
      Gaussian is a polynomial times the Gaussian, and Gaussian decay
      dominates any polynomial, so the product is uniformly bounded
      (`k = 0` works for every `n`). The technical content is the
      Faà di Bruno expansion of `iteratedFDeriv` for the composition
      `Real.exp ∘ (-t · ‖·‖²)`, which is a routine but lengthy
      mathlib exercise rather than a mathematical obstruction.

The conditional capstone
`heatMultiplier_hasTemperateGrowth_under_iteratedFDeriv_bound`
combines (a) and the residual (d) into `HasTemperateGrowth` for
`t > 0`. Once (d) is discharged, the unconditional
`heatMultiplier_hasTemperateGrowth` follows trivially.

Scope: scalar real-valued multiplier `R3 → ℝ`.

Imports: the heat-multiplier definition from `HeatSemigroupFourier.lean`
and mathlib's `Function.HasTemperateGrowth` infrastructure.

Axiom-free under `[propext, Classical.choice, Quot.sound]` only.

Author: Pablo Cohen (framework + formalization, 2026-06-10)
-/

import PF.NavierStokes.FujitaKato1964.HeatSemigroupFourier
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false

namespace PF.NavierStokes.FujitaKato1964.HeatMultiplierTemperateGrowth

open scoped ContDiff

open PF.NavierStokes.FujitaKato1964.HeatSemigroupFourier
  (R3
   heatMultiplier
   heatMultiplier_le_one
   heatMultiplier_at_zero_time)

/-! ## §1 — Smoothness of the Gaussian multiplier -/

/-- **The heat multiplier is smooth.** The function
`ξ ↦ e^{-t · ‖ξ‖²}` on `R3 = EuclideanSpace ℝ (Fin 3)` is `C^∞` for
every real `t`. The proof is the composition

  `Real.exp` (smooth on ℝ)
    ∘ scalar-multiplication-by-`(-t)` (smooth, linear)
    ∘ `‖·‖²` on `R3` (smooth by `contDiff_norm_sq`)

This is the smoothness conjunct of `Function.HasTemperateGrowth`. It
holds unconditionally on `t` (no sign restriction needed for
smoothness; the sign matters only for the contraction bound). -/
theorem heatMultiplier_contDiff (t : ℝ) :
    ContDiff ℝ ∞ (fun ξ : R3 => heatMultiplier t ξ) := by
  unfold heatMultiplier
  -- The map ξ ↦ -t * ‖ξ‖² is the composition of scalar
  -- multiplication by -t (a continuous linear map, hence smooth)
  -- with the squared norm ‖·‖² (smooth via contDiff_norm_sq).
  have h_norm_sq : ContDiff ℝ ∞ (fun ξ : R3 => ‖ξ‖ ^ 2) :=
    contDiff_norm_sq ℝ
  have h_inner : ContDiff ℝ ∞ (fun ξ : R3 => -t * ‖ξ‖ ^ 2) := by
    exact (contDiff_const.mul h_norm_sq)
  -- Real.exp is smooth as a function ℝ → ℝ, and ContDiff.exp says
  -- Real.exp ∘ f is smooth whenever f is smooth.
  exact h_inner.exp

/-! ## §2 — Trivial polynomial bound at the function level -/

/-- **Trivial polynomial bound on `m_t` at `n = 0`.** For `t ≥ 0`,
the multiplier `m_t(ξ) ≤ 1 = 1 · (1 + ‖ξ‖)^0`. This is the
`n = 0` slice of the iterated-derivative polynomial-bound condition
in `Function.HasTemperateGrowth` (the `0`-th iterated Fréchet
derivative is the function itself, up to the canonical
identification of `E →L[ℝ]^0 F` with `F`). -/
theorem heatMultiplier_le_one_pow_zero
    (t : ℝ) (ht : 0 ≤ t) (ξ : R3) :
    heatMultiplier t ξ ≤ 1 * (1 + ‖ξ‖) ^ 0 := by
  have h := heatMultiplier_le_one t ht ξ
  simpa using h

/-! ## §3 — Temperate growth at the initial time -/

/-- **Heat multiplier has temperate growth at the initial time.** At
`t = 0` the multiplier collapses to the constant function `1`, and
constant functions trivially have temperate growth via
`Function.HasTemperateGrowth.const`. This discharges the `t = 0`
slice of the full Gaussian-temperate-growth claim
unconditionally. -/
theorem heatMultiplier_hasTemperateGrowth_at_zero_time :
    Function.HasTemperateGrowth (fun ξ : R3 => heatMultiplier 0 ξ) := by
  have h_eq : (fun ξ : R3 => heatMultiplier 0 ξ) = fun _ : R3 => (1 : ℝ) := by
    funext ξ
    exact heatMultiplier_at_zero_time ξ
  rw [h_eq]
  exact Function.HasTemperateGrowth.const (1 : ℝ)

/-! ## §4 — Typed-Prop residual for the iterated-derivative bound -/

/-- **Typed-Prop residual: polynomial bound on iterated Fréchet
derivatives of the Gaussian multiplier.**

For a fixed positive time `t > 0` and every `n : ℕ`, the `n`-th
iterated Fréchet derivative of `ξ ↦ e^{-t‖ξ‖²}` on
`R3 = EuclideanSpace ℝ (Fin 3)` is bounded uniformly in `ξ` by a
polynomial:

  `∀ n, ∃ (k : ℕ) (C : ℝ), ∀ ξ, ‖iteratedFDeriv ℝ n (m_t) ξ‖ ≤ C · (1 + ‖ξ‖)^k`

Mathematically this is *immediate*: by repeated application of the
chain rule, the `n`-th derivative of `e^{-t‖ξ‖²}` is a polynomial
in `ξ` times the same Gaussian. Gaussian decay dominates polynomial
growth, so the product is in fact *bounded* (one can take `k = 0`
and `C = max_ξ |P_n(ξ) · e^{-t‖ξ‖²}|`).

This brick isolates the formal verification of that Faà di Bruno
expansion as a single named typed Prop. Its discharge is a routine
mathlib exercise (induction on `n`, Leibniz rule, polynomial-vs-
Gaussian asymptotics) and presents no mathematical obstruction.

This residual is the *only* gap between the smoothness theorem of
§1 and the full `Function.HasTemperateGrowth` predicate for
`heatMultiplier t` at positive times. -/
def IteratedFDerivHeatMultiplierPolynomialBounded (t : ℝ) : Prop :=
  ∀ n : ℕ, ∃ (k : ℕ) (C : ℝ),
    ∀ ξ : R3,
      ‖iteratedFDeriv ℝ n (fun η : R3 => heatMultiplier t η) ξ‖
        ≤ C * (1 + ‖ξ‖) ^ k

/-- **Restriction of the residual to `n = 0` is proved.**

The `n = 0` slice of `IteratedFDerivHeatMultiplierPolynomialBounded`
is the function-level bound itself (the `0`-th iterated Fréchet
derivative is the function, embedded into the `0`-fold continuous
multilinear maps). At physical times `t ≥ 0` we have the contraction
bound `m_t(ξ) ≤ 1`, hence the polynomial bound holds with `k = 0`
and `C = 1`. -/
theorem iteratedFDerivHeatMultiplierPolynomialBounded_at_zero
    (t : ℝ) (ht : 0 ≤ t) :
    ∃ (k : ℕ) (C : ℝ),
      ∀ ξ : R3,
        ‖iteratedFDeriv ℝ 0 (fun η : R3 => heatMultiplier t η) ξ‖
          ≤ C * (1 + ‖ξ‖) ^ k := by
  refine ⟨0, 1, fun ξ => ?_⟩
  -- iteratedFDeriv ℝ 0 f ξ has norm equal to ‖f ξ‖ (via norm_iteratedFDeriv_zero).
  rw [norm_iteratedFDeriv_zero]
  -- And ‖m_t(ξ)‖ = m_t(ξ) since m_t is non-negative.
  have h_nonneg : 0 ≤ heatMultiplier t ξ :=
    PF.NavierStokes.FujitaKato1964.HeatSemigroupFourier.heatMultiplier_nonneg t ξ
  have h_le : heatMultiplier t ξ ≤ 1 := heatMultiplier_le_one t ht ξ
  have : ‖heatMultiplier t ξ‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg h_nonneg]
    exact h_le
  simpa using this

/-! ## §5 — Conditional temperate-growth theorem -/

/-- **Conditional `HasTemperateGrowth` for the heat multiplier at
positive times.**

Assuming the typed-Prop residual
`IteratedFDerivHeatMultiplierPolynomialBounded t`, the heat
multiplier `ξ ↦ e^{-t‖ξ‖²}` on `R3` satisfies
`Function.HasTemperateGrowth` for every `t > 0`. The smoothness
conjunct is supplied unconditionally by `heatMultiplier_contDiff t`
(§1); the polynomial-bound conjunct is supplied by the hypothesis.

This is the *one-line conditional reduction* of the
`HeatSemigroupOperatorExists` residual of `HeatSemigroupPhysical.lean`
to the single named typed Prop
`IteratedFDerivHeatMultiplierPolynomialBounded`. -/
theorem heatMultiplier_hasTemperateGrowth_under_iteratedFDeriv_bound
    (t : ℝ)
    (hbound : IteratedFDerivHeatMultiplierPolynomialBounded t) :
    Function.HasTemperateGrowth (fun ξ : R3 => heatMultiplier t ξ) := by
  refine ⟨?_, hbound⟩
  exact heatMultiplier_contDiff t

/-! ## §6 — Capstone -/

/-- **★ Fujita-Kato heat-multiplier temperate-growth brick capstone ★**

Bundles the verified pieces of the
`(heatMultiplier t).HasTemperateGrowth` condition required by
`SchwartzMap.bilinLeftCLM` to upgrade pointwise multiplication by
the Gaussian symbol `m_t(ξ) = e^{-t‖ξ‖²}` into a continuous linear
endomorphism of scalar Schwartz space on `R3`:

  (a) Smoothness: `(heatMultiplier t)` is `C^∞` for every real `t`
  (b) Function-level polynomial bound: `m_t(ξ) ≤ 1 · (1 + ‖ξ‖)^0`
      for `t ≥ 0`
  (c) Initial-time temperate growth: `m_0 ≡ 1` has temperate growth
  (d) `n = 0` slice of the iterated-derivative bound proved
      unconditionally for `t ≥ 0`
  (e) Conditional full `HasTemperateGrowth` for `t > 0` under the
      typed-Prop residual
      `IteratedFDerivHeatMultiplierPolynomialBounded`

The single residual
`IteratedFDerivHeatMultiplierPolynomialBounded t` is the Faà di
Bruno expansion that the `n`-th iterated Fréchet derivative of a
Gaussian is a polynomial times the Gaussian; once discharged it
combines with (a) to give unconditional
`(heatMultiplier t).HasTemperateGrowth` for all `t ≥ 0`, which in
turn closes `HeatSemigroupOperatorExists` of
`HeatSemigroupPhysical.lean` via `SchwartzMap.bilinLeftCLM`.

Axiom-free: depends on `[propext, Classical.choice, Quot.sound]`
only. -/
theorem fujitaKato_heat_multiplier_temperate_growth_brick_capstone :
    -- (a) Smoothness, unconditional
    (∀ (t : ℝ), ContDiff ℝ ∞ (fun ξ : R3 => heatMultiplier t ξ)) ∧
    -- (b) Function-level polynomial bound at non-negative times
    (∀ (t : ℝ), 0 ≤ t → ∀ ξ : R3,
       heatMultiplier t ξ ≤ 1 * (1 + ‖ξ‖) ^ 0) ∧
    -- (c) Initial-time temperate growth, unconditional
    Function.HasTemperateGrowth (fun ξ : R3 => heatMultiplier 0 ξ) ∧
    -- (d) `n = 0` slice of the iterated-derivative bound
    (∀ (t : ℝ), 0 ≤ t →
       ∃ (k : ℕ) (C : ℝ),
         ∀ ξ : R3,
           ‖iteratedFDeriv ℝ 0 (fun η : R3 => heatMultiplier t η) ξ‖
             ≤ C * (1 + ‖ξ‖) ^ k) ∧
    -- (e) Conditional full HasTemperateGrowth at positive times
    (∀ (t : ℝ),
       IteratedFDerivHeatMultiplierPolynomialBounded t →
       Function.HasTemperateGrowth (fun ξ : R3 => heatMultiplier t ξ)) :=
  ⟨heatMultiplier_contDiff,
   heatMultiplier_le_one_pow_zero,
   heatMultiplier_hasTemperateGrowth_at_zero_time,
   iteratedFDerivHeatMultiplierPolynomialBounded_at_zero,
   heatMultiplier_hasTemperateGrowth_under_iteratedFDeriv_bound⟩

/-! ## §7 — Axiom audit -/

#print axioms heatMultiplier_contDiff
#print axioms heatMultiplier_le_one_pow_zero
#print axioms heatMultiplier_hasTemperateGrowth_at_zero_time
#print axioms IteratedFDerivHeatMultiplierPolynomialBounded
#print axioms iteratedFDerivHeatMultiplierPolynomialBounded_at_zero
#print axioms heatMultiplier_hasTemperateGrowth_under_iteratedFDeriv_bound
#print axioms fujitaKato_heat_multiplier_temperate_growth_brick_capstone

end PF.NavierStokes.FujitaKato1964.HeatMultiplierTemperateGrowth
