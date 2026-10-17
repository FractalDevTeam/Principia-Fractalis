/-
# Fujita-Kato 1964 — Banach Carrier for the Time Field (step 1 of 4)

**Rio's carrier migration, 2026-10-17.**

Replaces the Fréchet `TimeFieldR3C := ℝ → VectorSchwartz3C` with a Banach
carrier `TimeFieldR3C_Banach := ℝ → VectorBanach3C` where
`VectorBanach3C := Lp C3 2 (volume : Measure R3)` is the Banach space of
`L²(ℝ³, ℂ³)` velocity-field snapshots.

**Why this unblocks the Fujita-Kato bilinear operator.** `intervalIntegral`
requires `[NormedAddCommGroup E]` on its codomain. `SchwartzMap` is
Fréchet with no `NormedAddCommGroup` instance — Bochner integration of a
Schwartz-valued curve will never typecheck, at any mathlib version. The
Banach carrier makes

    `B(u, v)(t) = ∫₀ᵗ e^{(t−s)Δ} ℙ[(u·∇)v(s)] ds`

definable (step 2 of 4; separate file). This step is the structural
precondition.

**What this file provides.**

* `VectorBanach3C := Lp C3 2 (volume : Measure R3)` — the Banach-valued
  velocity-field snapshot. `NormedAddCommGroup` + `NormedSpace ℂ` free
  from mathlib's `Lp` instances.
* `TimeFieldR3C_Banach := ℝ → VectorBanach3C` — the Banach-valued time
  curve, the new carrier for Picard iteration.
* Inhabitant: the zero curve `fun _ => 0`, proving the type is non-empty.

**What this file does NOT do** (deferred to steps 2-4):

* The `Ḣ^{1/2}` norm on `VectorBanach3C` as a predicate / sub-norm (step 1b;
  the seminorm files `SobolevSeminormVector.lean` already compute the
  integrand on Schwartz data — the Banach version uses the same integrand
  via a representative lift).
* The bilinear operator `B(u,v)` (step 2).
* The `Ḣ^{1/2}` product estimate for `(u·∇)v` (step 3).
* Picard contraction ⇒ local existence (step 4).

Three-axiom bar: every declaration kernel-clean
`[propext, Classical.choice, Quot.sound]`. No sorry.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-17.
-/
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import PF.NavierStokes.FujitaKato1964.SobolevSeminormVector

set_option autoImplicit false

namespace PF.NavierStokes.FujitaKato1964

open MeasureTheory
open PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier

noncomputable section

/-! ## §1 — The Banach velocity-field snapshot. -/

/-- **Banach-valued velocity-field snapshot** at a single time: an element of
`L²(ℝ³, ℂ³)`.

Compared with `VectorSchwartz3C := SchwartzMap R3 C3` (Fréchet), this space
carries a `NormedAddCommGroup` instance (free from `Lp`), which is the
exact structural prerequisite for `intervalIntegral`-based Bochner
integration of time-dependent fields. -/
noncomputable abbrev VectorBanach3C : Type := Lp C3 2 (volume : Measure R3)

/-- `VectorBanach3C` is a normed additive commutative group (inherited from
`Lp`). This is the structural precondition that `SchwartzMap` lacks and
`intervalIntegral` requires. -/
example : NormedAddCommGroup VectorBanach3C := inferInstance

/-- `VectorBanach3C` is a complex normed space (inherited from `Lp`). -/
example : NormedSpace ℂ VectorBanach3C := inferInstance

/-! ## §2 — The Banach-valued time curve. -/

/-- **Banach-valued time-field.** `ℝ → L²(ℝ³, ℂ³)`. The new carrier for the
Fujita-Kato mild formulation `u(t) = e^{tΔ} u₀ + B(u, u)(t)`.

The function space `ℝ → VectorBanach3C` auto-inherits pointwise
`NormedAddCommGroup` operations; integrability predicates on time curves
are expressed via `MeasureTheory.IntervalIntegrable` directly. -/
noncomputable abbrev TimeFieldR3C_Banach : Type := ℝ → VectorBanach3C

/-- The zero time-field: identically-zero Banach-valued curve. Proves
`TimeFieldR3C_Banach` is inhabited and exercises `Lp.instZero`. -/
def zeroTimeFieldBanach : TimeFieldR3C_Banach :=
  fun _ => (0 : VectorBanach3C)

/-- At every time `t`, the zero time-field is the zero element of
`VectorBanach3C`. -/
theorem zeroTimeFieldBanach_apply (t : ℝ) :
    zeroTimeFieldBanach t = (0 : VectorBanach3C) := rfl

end

end PF.NavierStokes.FujitaKato1964

/-! ## §Axiom check -/
#print axioms PF.NavierStokes.FujitaKato1964.zeroTimeFieldBanach_apply
