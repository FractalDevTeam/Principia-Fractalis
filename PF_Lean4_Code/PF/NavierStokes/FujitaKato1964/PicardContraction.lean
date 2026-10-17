/-
# Fujita-Kato 1964 — Picard Contraction + Local Existence (step 4 of 4)

**Rio's NS carrier migration, step 4**: with the bilinear estimate shell
in place (`BilinearEstimate.lean`, step 3), we close the Fujita-Kato
construction with the Picard-contraction / local-existence layer.

### What this file provides

* `banachMildBilinear_eq_zero` — the TRIVIAL step-2b realizations make
  the Banach-side mild bilinear identically zero.

* `banachPicardMap_const_u₀` — with the trivial realizations, the Picard
  map is `banachPicardMap u₀ u = fun _ => u₀` **independent of `u`**.
  Lipschitz constant 0 in the `u`-argument — a trivial contraction.

* `banachPicardMap_fixed_point` — the constant time-curve `fun _ => u₀`
  is a fixed point of `banachPicardMap u₀`. In the Picard-iteration
  interpretation, this is the "mild solution" of the trivial-shell
  Cauchy problem.

* `IsMildSolution` — the general definition of a mild solution: a time
  curve fixed by the Picard map.

* `banachMildSolution_exists` — **shell local-existence theorem**: for
  every `u₀ : VectorBanach3C`, the Cauchy problem admits a mild
  solution. For the trivial shell, the solution is the constant curve
  `fun _ => u₀` (trivially: the heat flow of the identity semigroup is
  trivial, and the trivial bilinear contributes nothing).

### Scope and the Fujita-Kato 1964 program

With the step-2b trivial realizations:
* `banachHeatSemigroup = CLM.id` ⇒ heat evolution is trivial.
* `banachLerayProjection = CLM.id` ⇒ Leray projection is trivial.
* `banachConvectiveDerivative = fun _ _ => 0` ⇒ convective term is zero.
* ⇒ bilinear ≡ 0 ⇒ Picard = constant ⇒ fixed point = constant.

This is the **shell local-existence theorem** — the full type-level
machinery with a correct (if degenerate) existence statement. It becomes
the GENUINE Fujita-Kato 1964 theorem when:

1. **Step 2c** supplies density-extended real operators
   (`vectorHeatEvolveFreq`, `lerayProjectFreq`, `convectiveComponent`
   lifted from `VectorSchwartz3C` to `VectorBanach3C`).

2. **Step 3** then becomes a genuine quantitative bilinear estimate.

3. The Picard contraction becomes genuine: a small-data condition
   `‖u₀‖ · T^{1/4} < 1/(4C)` (or analogous), yielding local existence
   for small data — the first *real* NS existence theorem in the repo.

The STATEMENT of `banachMildSolution_exists` does not change under these
upgrades; only the mild solution produced ceases to be degenerate.

### Three-axiom bar

Every declaration kernel-clean `[propext, Classical.choice, Quot.sound]`.
No sorry.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-17.
-/
import PF.NavierStokes.FujitaKato1964.BilinearEstimate
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false

namespace PF.NavierStokes.FujitaKato1964

open MeasureTheory

noncomputable section

/-! ## §1 — The Banach bilinear is identically zero under trivial shells. -/

/-- **Vanishing of the trivial bilinear**: with the step-2b realizations
(`banachConvectiveDerivative = 0`), the mild bilinear is zero at every
time. -/
theorem banachMildBilinear_eq_zero (u v : TimeFieldR3C_Banach) (t : ℝ) :
    banachMildBilinear u v t = (0 : VectorBanach3C) := by
  show (∫ s in (0 : ℝ)..t,
          banachHeatSemigroup (t - s)
            (banachLerayProjection
              (banachConvectiveDerivative (u s) (v s))))
       = 0
  simp only [banachConvectiveDerivative, map_zero,
             intervalIntegral.integral_zero]

/-! ## §2 — The Picard map collapses to the constant initial-datum curve. -/

/-- **Picard-map constant-collapse**: for the step-2b trivial
realizations, `banachPicardMap u₀ u = fun _ => u₀` **independent of `u`**.
Interpretation: the Picard map has Lipschitz constant 0 in its
`u`-argument — a trivial contraction. -/
theorem banachPicardMap_const_u₀ (u₀ : VectorBanach3C) (u : TimeFieldR3C_Banach) :
    banachPicardMap u₀ u = fun _ => u₀ := by
  funext t
  show banachHeatSemigroup t u₀ + banachMildBilinear u u t = u₀
  rw [banachMildBilinear_eq_zero u u t, add_zero]
  show (ContinuousLinearMap.id ℂ VectorBanach3C) u₀ = u₀
  rfl

/-! ## §3 — Fixed point of the Picard map. -/

/-- **Fixed point of the Picard map** (trivial shell): the constant
time-curve `fun _ => u₀` is a fixed point of `banachPicardMap u₀`. -/
theorem banachPicardMap_fixed_point (u₀ : VectorBanach3C) :
    banachPicardMap u₀ (fun _ => u₀) = fun _ => u₀ :=
  banachPicardMap_const_u₀ u₀ _

/-! ## §4 — Mild solutions and local existence. -/

/-- **Mild solution of the Navier-Stokes Cauchy problem** on the
Banach-side carrier: a time-curve `u` fixed by the Picard map
`Φ(u) = e^{tΔ} u₀ + B(u, u)`. -/
def IsMildSolution (u₀ : VectorBanach3C) (u : TimeFieldR3C_Banach) : Prop :=
  banachPicardMap u₀ u = u

/-- **★ Step-4 shell local-existence theorem ★**: for every initial
datum `u₀ : VectorBanach3C`, the mild Cauchy problem admits a solution.

In the current (step-2b-trivial) shell, the mild solution produced is
the constant time-curve `fun _ => u₀`. This is degenerate (reflecting
`banachHeatSemigroup = CLM.id` + `banachMildBilinear ≡ 0`) but kernel-
clean, and becomes the genuine Fujita-Kato local existence theorem when
step 2c (density extension) and the real Ḣ^{1/2} product estimate land.
The theorem statement does not change. -/
theorem banachMildSolution_exists (u₀ : VectorBanach3C) :
    ∃ u : TimeFieldR3C_Banach, IsMildSolution u₀ u :=
  ⟨fun _ => u₀, banachPicardMap_fixed_point u₀⟩

/-- **Initial-datum match for the constant mild solution**: the shell
mild solution evaluated at `t = 0` equals `u₀`. (Trivial — the curve is
constant.) -/
theorem banachMildSolution_at_zero (u₀ : VectorBanach3C) :
    (fun _ : ℝ => u₀) (0 : ℝ) = u₀ := rfl

end

end PF.NavierStokes.FujitaKato1964

/-! ## §Axiom check -/
#print axioms PF.NavierStokes.FujitaKato1964.banachMildBilinear_eq_zero
#print axioms PF.NavierStokes.FujitaKato1964.banachPicardMap_const_u₀
#print axioms PF.NavierStokes.FujitaKato1964.banachPicardMap_fixed_point
#print axioms PF.NavierStokes.FujitaKato1964.banachMildSolution_exists
#print axioms PF.NavierStokes.FujitaKato1964.banachMildSolution_at_zero
