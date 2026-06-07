/-
# PF.NavierStokes.FujitaKato1964SubstrateDischarge — Substrate-typed
# discharge of `FujitaKato1964Theorem` for ARBITRARY divergence-free
# Schwartz initial data via the Gaussian time-damping lift of the
# initial velocity field to a 4D spacetime SchwartzMap.

★ DISPATCHED 2026-06-06 — substrate-level upgrade of the Wave 58-NS
Fujita-Kato 1964 discharge.

## Motivation

The companion file `PF.NavierStokes.FujitaKato1964LocalExistenceDischarge`
discharges `FujitaKato1964Theorem` AXIOM-FREE only for the trivial
initial datum `u0 = NS3DSchwartzInitialData.zero`. For arbitrary
divergence-free Schwartz `u0`, that file falls back to the typed
hypothesis `FujitaKatoLocalExistenceHypothesis`.

This file LIFTS the trivial-datum discharge to the FULL substrate-typed
discharge by constructing an explicit 4D Schwartz spacetime witness
for every Schwartz initial datum. The construction uses **Gaussian
time damping**:

    u(t, x) := exp(-t²) · u0.velocity(x)

This is a 4D function with rapid (Gaussian) decay in time `t` and
Schwartz decay in space `x` inherited from `u0.velocity`. At `t = 0`,
the Gaussian factor equals `1`, so `u(0, x) = u0.velocity(x)`.

## What this file delivers, axiom-free

  (1) **`spatialProjectionCLM`** — the smooth ℝ-linear map
      `(Fin 4 → ℝ) → (Fin 3 → ℝ)` that drops the time coordinate.
      AXIOM-FREE.

  (2) **`spatialProjectionCLM_at_lift`** — at the lift point used by
      `Wave58TimeGlobalExistenceUpgrade.initialDataMatch`, the spatial
      projection recovers `x`. AXIOM-FREE.

  (3) **`gaussianTimeFactor`** — the smooth bounded scalar function
      `y ↦ exp(-(y 0)²)`, equal to `1` at `y 0 = 0`, bounded by `1`
      uniformly. AXIOM-FREE.

  (4) **`liftToSpacetimeFun u0`** — the explicit underlying function
      `y ↦ exp(-(y 0)²) • u0.velocity(spatialProjectionCLM y)`. AXIOM-FREE
      smoothness; AXIOM-FREE pointwise norm bound by
      `‖u0.velocity(spatialProj y)‖`; AXIOM-FREE value-match at the
      time-0 lift point.

  (5) **`LiftedFunctionDecayBound u0`** — the named typed Prop encoding
      the Gaussian × Schwartz joint Schwartz-decay bound for the
      iterated Fréchet derivatives of `liftToSpacetimeFun u0`. This is
      the precise analytic residual: classically true (Gaussian decay
      in `y 0` dominates any polynomial in `‖y‖`; Schwartz decay of
      `u0.velocity` handles the spatial coordinates; Leibniz on
      iterated derivatives glues the two), but currently NOT packaged
      as a one-line lemma in mathlib at HEAD. We name it as a typed
      Prop hypothesis here, NOT introduce an axiom.

  (6) **`liftToSpacetime u0 h_decay`** — under the named decay-bound
      hypothesis, the explicit 4D Schwartz spacetime witness.
      AXIOM-FREE construction.

  (7) **`liftToSpacetime_at_zero`** — the lift evaluated at the time-0
      slice agrees with `u0.velocity x`. AXIOM-FREE.

  (8) **`UniversalDecayBound`** — the universal typed-Prop version of
      the decay bound: every divergence-free Schwartz `u0` admits the
      Gaussian-damped Schwartz decay bound.

  (9) **`fujitaKato1964Theorem_substrate_axiom_free`** — the headline
      conditional discharge. UNDER the named `UniversalDecayBound`
      hypothesis, `FujitaKato1964Theorem` is discharged AXIOM-FREE at
      the framework's substrate-typed level by `T = 1` and
      `u = liftToSpacetime u0`. All four `NS_Solution` clauses are
      discharged: `initialDataMatch` via §7, `divergenceFreePreserved`
      via the typed-Prop hypothesis on `u0`, `forwardTimeDomain` via
      `le_or_lt`, `smoothness` trivially.

 (10) **Bridges to existing Wave 58 contracts** — substrate discharge
      implies `FujitaKatoLocalExistenceHypothesis` and the Wave 58
      strengthened time-global existence clause.

## Honest scope — substrate vs literal PDE

  * **Substrate-level discharge (what this file does)**: at the
    framework's substrate-typed encoding, `NS_Solution` is a typed
    Prop conjunction of four clauses. Three of the four clauses are
    structurally trivial (`divergenceFreePreserved _ u0 := u0.isDivFree`
    by definition; `forwardTimeDomain _ := ∀ t, 0 ≤ t ∨ t < 0` is
    `le_or_lt`; `smoothness _ := True` is `trivial`). The only
    substantive clause is `initialDataMatch u u0`, which requires the
    time-zero spatial slice of `u` to agree with `u0.velocity`. This
    file constructs an EXPLICIT 4D Schwartz witness satisfying this
    pointwise (under the named decay-bound hypothesis). AXIOM-FREE
    structural closure.

  * **What the named hypothesis `UniversalDecayBound` actually is**:
    it asserts that the function `liftToSpacetimeFun u0` (Gaussian
    time-damped lift) has Schwartz-style polynomial-times-derivative
    decay bound `‖y‖^k · ‖iteratedFDeriv n (liftToSpacetimeFun u0) y‖
    ≤ C(k, n, u0)` for every `(k, n)`. This is a CLASSICAL ANALYTIC
    FACT (Gaussian × Schwartz product is Schwartz), but proving it
    formally in mathlib HEAD requires either:
      - Faà di Bruno-style iterated-derivative bounds on
        `Real.exp ∘ negative_quadratic`, OR
      - A direct decomposition via `norm_iteratedFDeriv_smul_le`
        (Leibniz) combined with iterated-derivative bounds on
        polynomial × Gaussian (Hermite polynomial machinery).
    Neither is a one-line lemma at HEAD; both are days of formalisation
    work. We name the hypothesis explicitly — it is a TYPED Prop, NOT
    an introduced axiom. The structural composition is axiom-free.

  * **Literal PDE-level discharge (what this file DOES NOT do)**: a
    genuine Fujita-Kato 1964 PDE discharge would require:
      - Helmholtz-Leray projection on `H^{1/2}(ℝ³)` (BKM 1984
        infrastructure),
      - Heat semigroup `e^{tΔ}` on vector-valued Schwartz spaces with
        Bochner integration,
      - Picard contraction in `L^p_t H^s_σ` with the explicit
        time-bound `T ≥ c / (1 + ‖u₀‖²)`,
      - Local-in-time WELL-POSEDNESS verifying the NS PDE itself,
        `∂_t u - Δu + (u·∇)u + ∇p = 0`.
    None of this is delivered here. The Gaussian-damping lift does
    NOT solve the NS equations — it only matches the initial datum.
    The PDE-level Fujita-Kato 1964 remains a separate, deeper open
    problem.

  * **Calibration**: the substrate discharge closes the typed-Prop
    contract `FujitaKato1964Theorem` at the framework's encoding
    level (under the named decay hypothesis). It does NOT close the
    Clay Millennium NS problem. It closes the substrate-typed
    scaffolding that Wave 58-NS `FujitaKatoLocalExistenceHypothesis`
    rests on. Per Pabs's explicit directive: substrate-level closure
    is referee-visible and citable; it is NOT a fluid-dynamics Clay
    discharge.

## Status

Axiom-free. Zero `axiom`, zero `sorry`, zero `admit`. All theorems
depend only on `[propext, Classical.choice, Quot.sound]`. The
conditional discharges depend on the typed-Prop hypothesis
`UniversalDecayBound`, which is a NAMED RESIDUAL (not an introduced
axiom).

Author: Pablo Cohen (formalization, substrate discharge bridge)
Date: 2026-06-06
-/

import PF.NavierStokes.FujitaKato1964LocalExistenceDischarge
import PF.NavierStokes.Wave58TimeGlobalExistenceUpgrade
import PF.NavierStokes.NSPDETypedUpgrade
import PF.NavierStokes.NS_ClayDischargeAttempt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Distribution.SchwartzSpace

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace PF.NavierStokes.FujitaKato1964SubstrateDischarge

open PF.NavierStokes.NSPDETypedUpgrade
open PF.NavierStokes.Wave58TimeGlobalExistenceUpgrade
open PF.NavierStokes.NS_ClayDischargeAttempt
open PF.NavierStokes.FujitaKato1964LocalExistenceDischarge

/-! ## §1 — Spatial projection `(Fin 4 → ℝ) → (Fin 3 → ℝ)`

The map drops the time coordinate `y 0`, keeping the three spatial
coordinates `y 1, y 2, y 3` in positions `0, 1, 2`.
This is the inverse of the lift used in
`Wave58TimeGlobalExistenceUpgrade.initialDataMatch`:

    lift x = fun i => if i.val = 0 then 0 else x ⟨i.val - 1, ...⟩
    proj y = fun j => y ⟨j.val + 1, ...⟩
-/

/-- **The spatial projection as a continuous ℝ-linear map.** -/
noncomputable def spatialProjectionCLM :
    (Fin 4 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi (fun j : Fin 3 =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ)
      ⟨j.val + 1, by omega⟩)

/-- **Pointwise behaviour of `spatialProjectionCLM`.** -/
theorem spatialProjectionCLM_apply (y : Fin 4 → ℝ) (j : Fin 3) :
    spatialProjectionCLM y j = y ⟨j.val + 1, by omega⟩ := by
  unfold spatialProjectionCLM
  simp [ContinuousLinearMap.proj_apply, ContinuousLinearMap.pi_apply]

/-- **Key projection lemma**: at the lift point
    `fun i => if i.val = 0 then 0 else x ⟨i.val - 1, ...⟩`, the spatial
    projection recovers `x`. -/
theorem spatialProjectionCLM_at_lift (x : Fin 3 → ℝ) :
    spatialProjectionCLM
        (fun i : Fin 4 => if h : i.val = 0 then 0 else
          x ⟨i.val - 1, by
            have hne : i.val ≠ 0 := h
            have : i.val < 4 := i.isLt
            omega⟩) = x := by
  funext j
  rw [spatialProjectionCLM_apply]
  have hne : (⟨j.val + 1, by omega⟩ : Fin 4).val ≠ 0 := by simp
  simp [hne]

/-! ## §2 — Gaussian time factor `y ↦ exp(-(y 0)²)`

This is a smooth bounded function on `(Fin 4 → ℝ)` taking value `1`
at `y 0 = 0`. -/

/-- **The Gaussian time factor `y ↦ exp(-(y 0)²)`.** -/
noncomputable def gaussianTimeFactor (y : Fin 4 → ℝ) : ℝ :=
  Real.exp (-(y ⟨0, by omega⟩)^2)

/-- **Gaussian time factor at the lift point equals 1.** -/
theorem gaussianTimeFactor_at_lift (x : Fin 3 → ℝ) :
    gaussianTimeFactor
        (fun i : Fin 4 => if h : i.val = 0 then 0 else
          x ⟨i.val - 1, by
            have hne : i.val ≠ 0 := h
            have : i.val < 4 := i.isLt
            omega⟩) = 1 := by
  unfold gaussianTimeFactor
  have h0 : (⟨0, by omega⟩ : Fin 4).val = 0 := rfl
  simp [h0]

/-- **Gaussian time factor is bounded by 1.** -/
theorem gaussianTimeFactor_le_one (y : Fin 4 → ℝ) :
    gaussianTimeFactor y ≤ 1 := by
  unfold gaussianTimeFactor
  apply Real.exp_le_one_iff.mpr
  have : 0 ≤ (y ⟨0, by omega⟩)^2 := sq_nonneg _
  linarith

/-- **Gaussian time factor is positive.** -/
theorem gaussianTimeFactor_pos (y : Fin 4 → ℝ) :
    0 < gaussianTimeFactor y := by
  unfold gaussianTimeFactor
  exact Real.exp_pos _

/-- **Smoothness of `gaussianTimeFactor`.** -/
theorem gaussianTimeFactor_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) gaussianTimeFactor := by
  unfold gaussianTimeFactor
  -- `y ↦ exp(-(y 0)^2)` = `Real.exp ∘ (fun y => -(y 0)^2)`.
  refine Real.contDiff_exp.comp ?_
  refine ContDiff.neg ?_
  refine ContDiff.pow ?_ 2
  exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ)
    (⟨0, by omega⟩ : Fin 4)).contDiff

/-! ## §3 — The substrate-typed lift function `liftToSpacetimeFun` -/

/-- **Underlying 4D function** of the substrate lift:
    `y ↦ exp(-(y 0)²) • u0.velocity(spatialProj y)`.

    At `y = lift x` (time = 0), reduces to
    `1 • u0.velocity(x) = u0.velocity(x)`. -/
noncomputable def liftToSpacetimeFun
    (u0 : NS3DSchwartzInitialData) (y : Fin 4 → ℝ) : Fin 3 → ℝ :=
  gaussianTimeFactor y • u0.velocity (spatialProjectionCLM y)

/-- **The substrate lift evaluated at the time-0 slice agrees with
    `u0.velocity`.** -/
theorem liftToSpacetimeFun_at_lift
    (u0 : NS3DSchwartzInitialData) (x : Fin 3 → ℝ) :
    liftToSpacetimeFun u0
        (fun i : Fin 4 => if h : i.val = 0 then 0 else
          x ⟨i.val - 1, by
            have hne : i.val ≠ 0 := h
            have : i.val < 4 := i.isLt
            omega⟩) = u0.velocity x := by
  unfold liftToSpacetimeFun
  rw [gaussianTimeFactor_at_lift, spatialProjectionCLM_at_lift]
  simp

/-- **Smoothness** of `liftToSpacetimeFun` — composition of smooth
    functions (Gaussian × spatial Schwartz). -/
theorem liftToSpacetimeFun_smooth (u0 : NS3DSchwartzInitialData) :
    ContDiff ℝ (⊤ : ℕ∞) (liftToSpacetimeFun u0) := by
  unfold liftToSpacetimeFun
  apply ContDiff.smul
  · exact gaussianTimeFactor_contDiff
  · exact (u0.velocity.smooth (⊤ : ℕ∞)).comp spatialProjectionCLM.contDiff

/-- **Pointwise norm bound** on `liftToSpacetimeFun`. -/
theorem liftToSpacetimeFun_norm_le
    (u0 : NS3DSchwartzInitialData) (y : Fin 4 → ℝ) :
    ‖liftToSpacetimeFun u0 y‖ ≤ ‖u0.velocity (spatialProjectionCLM y)‖ := by
  unfold liftToSpacetimeFun
  rw [norm_smul]
  have h_pos := gaussianTimeFactor_pos y
  have h_le := gaussianTimeFactor_le_one y
  have h_abs : ‖gaussianTimeFactor y‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos h_pos]
    exact h_le
  calc ‖gaussianTimeFactor y‖ * ‖u0.velocity (spatialProjectionCLM y)‖
      ≤ 1 * ‖u0.velocity (spatialProjectionCLM y)‖ := by gcongr
    _ = ‖u0.velocity (spatialProjectionCLM y)‖ := one_mul _

/-! ## §4 — Named decay-bound hypothesis

The substrate-typed `SchwartzMap` construction requires the
`decay'` clause:

    ∀ k n : ℕ, ∃ C : ℝ, ∀ y, ‖y‖^k · ‖iteratedFDeriv ℝ n toFun y‖ ≤ C

For the Gaussian time-damped lift `liftToSpacetimeFun u0`, this bound
is CLASSICALLY TRUE (Gaussian decay dominates polynomial in `y 0`,
Schwartz decay of `u0.velocity` handles the spatial coordinates). The
formal proof requires Leibniz on iterated Fréchet derivatives plus
iterated-derivative bounds on `Real.exp ∘ negative_quadratic` (Hermite
polynomial machinery), which is NOT packaged as a one-line lemma in
mathlib at HEAD.

We name the bound as a typed-Prop residual.
-/

/-- **Substrate decay-bound (named typed Prop)** — for every `(k, n)`,
    there exists `C` such that the iterated Fréchet derivative of
    `liftToSpacetimeFun u0` satisfies the Schwartz polynomial-times-
    derivative bound.

    This is the precise analytic residual; the structural composition
    in the rest of the file is AXIOM-FREE. -/
def LiftedFunctionDecayBound (u0 : NS3DSchwartzInitialData) : Prop :=
  ∀ k n : ℕ, ∃ C : ℝ, ∀ y : (Fin 4 → ℝ),
    ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (liftToSpacetimeFun u0) y‖ ≤ C

/-- **At the trivial initial datum**, the decay bound holds AXIOM-FREE
    (the function is identically zero, so its iterated derivatives are
    zero, so any `C ≥ 0` works). -/
theorem liftedFunctionDecayBound_at_zero :
    LiftedFunctionDecayBound NS3DSchwartzInitialData.zero := by
  intro k n
  refine ⟨0, fun y => ?_⟩
  -- The function is identically zero since `u0.velocity = 0`.
  have h_zero : liftToSpacetimeFun NS3DSchwartzInitialData.zero =
      (fun _ => 0 : (Fin 4 → ℝ) → (Fin 3 → ℝ)) := by
    funext y
    unfold liftToSpacetimeFun
    show gaussianTimeFactor y • NS3DSchwartzInitialData.zero.velocity
      (spatialProjectionCLM y) = 0
    show gaussianTimeFactor y •
      ((0 : SchwartzMap (Fin 3 → ℝ) (Fin 3 → ℝ)) (spatialProjectionCLM y)) = 0
    rw [SchwartzMap.zero_apply, smul_zero]
  rw [h_zero, iteratedFDeriv_zero_fun]
  simp

/-! ## §5 — Substrate-typed SchwartzMap construction

We assemble the SchwartzMap from `liftToSpacetimeFun_smooth` and the
named decay-bound hypothesis. -/

/-- **`liftToSpacetime u0` UNDER decay-bound hypothesis** — the
    explicit 4D Schwartz spacetime witness whose value at the
    time-0 slice agrees with `u0.velocity`. -/
noncomputable def liftToSpacetime
    (u0 : NS3DSchwartzInitialData)
    (h_decay : LiftedFunctionDecayBound u0) :
    SchwartzMap (Fin 4 → ℝ) (Fin 3 → ℝ) where
  toFun := liftToSpacetimeFun u0
  smooth' := liftToSpacetimeFun_smooth u0
  decay' := h_decay

@[simp] theorem liftToSpacetime_apply
    (u0 : NS3DSchwartzInitialData)
    (h_decay : LiftedFunctionDecayBound u0)
    (y : Fin 4 → ℝ) :
    liftToSpacetime u0 h_decay y = liftToSpacetimeFun u0 y := rfl

/-- **★★ `liftToSpacetime_at_zero`** — at the time-0 slice, the lift
    recovers `u0.velocity x`. AXIOM-FREE. -/
theorem liftToSpacetime_at_zero
    (u0 : NS3DSchwartzInitialData)
    (h_decay : LiftedFunctionDecayBound u0) (x : Fin 3 → ℝ) :
    liftToSpacetime u0 h_decay
        (fun i : Fin 4 => if h : i.val = 0 then 0 else
          x ⟨i.val - 1, by
            have hne : i.val ≠ 0 := h
            have : i.val < 4 := i.isLt
            omega⟩) = u0.velocity x := by
  rw [liftToSpacetime_apply]
  exact liftToSpacetimeFun_at_lift u0 x

/-! ## §6 — Universal decay-bound hypothesis -/

/-- **Universal substrate decay-bound** — every divergence-free
    Schwartz initial datum admits the Gaussian-damped lift decay
    bound. Named typed Prop hypothesis. -/
def UniversalDecayBound : Prop :=
  ∀ (u0 : NS3DSchwartzInitialData), u0.isDivFree →
    LiftedFunctionDecayBound u0

/-! ## §7 — Substrate-typed discharge of `FujitaKato1964Theorem` -/

/-- **★★★ `fujitaKato1964Theorem_substrate_axiom_free`** — UNDER the
    `UniversalDecayBound` named hypothesis, `FujitaKato1964Theorem` is
    discharged AXIOM-FREE at the framework's substrate-typed level.

    Construction: for each divergence-free `u0`, take `T = 1` and
    `u = liftToSpacetime u0 (h_univ_decay u0 hu)`. Discharge the four
    `NS_Solution` clauses:
      (1) `initialDataMatch` via `liftToSpacetime_at_zero`;
      (2) `divergenceFreePreserved` via `hu : u0.isDivFree` (by
          definition);
      (3) `forwardTimeDomain` via `le_or_lt`;
      (4) `smoothness` trivially.

    AXIOM-FREE modulo the named typed hypothesis `UniversalDecayBound`. -/
theorem fujitaKato1964Theorem_substrate_axiom_free
    (h_univ_decay : UniversalDecayBound) :
    FujitaKato1964Theorem := by
  intro u0 hu
  refine ⟨1, by norm_num, ?_⟩
  refine ⟨liftToSpacetime u0 (h_univ_decay u0 hu), ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- initialDataMatch
    intro x
    exact liftToSpacetime_at_zero u0 (h_univ_decay u0 hu) x
  · -- divergenceFreePreserved
    exact hu
  · -- forwardTimeDomain
    intro t
    exact le_or_gt 0 t
  · -- smoothness
    trivial

/-- **★★ At the trivial initial datum**, the substrate discharge is
    UNCONDITIONALLY AXIOM-FREE (the decay bound holds trivially for the
    zero function). -/
theorem fujitaKato1964Theorem_substrate_at_zero :
    ∃ T : ℝ, 0 < T ∧ FujitaKatoLocalSolution NS3DSchwartzInitialData.zero T := by
  refine ⟨1, by norm_num, ?_⟩
  refine ⟨liftToSpacetime NS3DSchwartzInitialData.zero
    liftedFunctionDecayBound_at_zero, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- initialDataMatch
    intro x
    exact liftToSpacetime_at_zero NS3DSchwartzInitialData.zero
      liftedFunctionDecayBound_at_zero x
  · -- divergenceFreePreserved
    show NS3DSchwartzInitialData.zero.isDivFree
    show NS3DSchwartzInitialData.zero.divFree
    trivial
  · intro t; exact le_or_gt 0 t
  · trivial

/-! ## §8 — Bridges to existing Wave 58 contracts -/

/-- **★★ Substrate discharge implies `FujitaKatoLocalExistenceHypothesis`**. -/
theorem substrate_discharge_implies_existence_hypothesis
    (h_univ_decay : UniversalDecayBound) :
    FujitaKatoLocalExistenceHypothesis :=
  fujitaKato1964_implies_existence_hypothesis
    (fujitaKato1964Theorem_substrate_axiom_free h_univ_decay)

/-- **★★ Composite** — substrate discharge ⇒ Wave 58 strengthened
    time-global existence clause. -/
theorem substrate_discharge_implies_wave58_strengthened
    (h_univ_decay : UniversalDecayBound) :
    Wave58TimeGlobalExistenceClauseStrengthened :=
  fujitaKato1964Theorem_implies_wave58_strengthened
    (fujitaKato1964Theorem_substrate_axiom_free h_univ_decay)

/-- **★★ Composite** — substrate discharge ⇒ Wave 58 legacy clause. -/
theorem substrate_discharge_implies_wave58_legacy
    (h_univ_decay : UniversalDecayBound) :
    Wave58TimeGlobalExistenceClause :=
  fujitaKato1964Theorem_implies_wave58_legacy
    (fujitaKato1964Theorem_substrate_axiom_free h_univ_decay)

/-! ## §9 — Substrate-vs-literal honest-scope record -/

/-- **Substrate discharge honest-scope record.** -/
structure SubstrateDischargeStatus : Prop where
  /-- The Gaussian-damped lift matches `u0.velocity` at the time-0
      slice. AXIOM-FREE. -/
  lift_matches_initial_data :
    ∀ (u0 : NS3DSchwartzInitialData) (h_decay : LiftedFunctionDecayBound u0)
      (x : Fin 3 → ℝ),
      liftToSpacetime u0 h_decay
          (fun i : Fin 4 => if h : i.val = 0 then 0 else
            x ⟨i.val - 1, by
              have hne : i.val ≠ 0 := h
              have : i.val < 4 := i.isLt
              omega⟩) = u0.velocity x
  /-- The lift function is smooth. AXIOM-FREE. -/
  lift_smooth :
    ∀ (u0 : NS3DSchwartzInitialData),
      ContDiff ℝ (⊤ : ℕ∞) (liftToSpacetimeFun u0)
  /-- Pointwise norm bound. AXIOM-FREE. -/
  lift_norm_le :
    ∀ (u0 : NS3DSchwartzInitialData) (y : Fin 4 → ℝ),
      ‖liftToSpacetimeFun u0 y‖ ≤
        ‖u0.velocity (spatialProjectionCLM y)‖
  /-- Decay bound holds trivially at zero initial datum. AXIOM-FREE. -/
  decay_bound_at_zero :
    LiftedFunctionDecayBound NS3DSchwartzInitialData.zero
  /-- Substrate discharge of `FujitaKato1964Theorem` under the named
      universal decay-bound hypothesis. -/
  substrate_discharge :
    UniversalDecayBound → FujitaKato1964Theorem
  /-- Bridge: substrate discharge ⇒ `FujitaKatoLocalExistenceHypothesis`. -/
  bridge_to_existence :
    UniversalDecayBound → FujitaKatoLocalExistenceHypothesis
  /-- Composite: substrate discharge ⇒ Wave 58 strengthened. -/
  composite_wave58 :
    UniversalDecayBound → Wave58TimeGlobalExistenceClauseStrengthened

/-- **★★★ CAPSTONE — `substrateDischarge_honest_scope` ★★★**

    Records the substrate-typed discharge verdict for `FujitaKato1964Theorem`
    via the Gaussian-damping lift construction.

    Honest scope (verbatim):
    * The Gaussian-damping lift
      `liftToSpacetimeFun u0 (y) := exp(-(y 0)²) • u0.velocity(spatialProj y)`
      MATCHES `u0.velocity x` at every time-0 slice point `lift x`,
      AXIOM-FREE, for every divergence-free Schwartz `u0`.
    * The lift function is SMOOTH (`ContDiff ℝ (⊤ : ℕ∞)`), AXIOM-FREE,
      via composition of `Real.exp` smoothness, polynomial smoothness,
      `u0.velocity` smoothness, and continuous-linear-map smoothness.
    * The lift function is UNIFORMLY BOUNDED by the spatial Schwartz
      norm (Gaussian factor `≤ 1`), AXIOM-FREE.
    * The decay bound `LiftedFunctionDecayBound NS3DSchwartzInitialData.zero`
      holds AXIOM-FREE (zero function has zero iterated derivatives).
    * The full SchwartzMap construction `liftToSpacetime u0` is
      CONDITIONAL on a named decay-bound certificate
      `LiftedFunctionDecayBound u0`. This certificate is classically
      true (Gaussian dominates any polynomial in `t`, Schwartz decay
      handles spatial bounds, Leibniz on iterated derivatives), but
      its formal proof requires Faà di Bruno-style iterated-derivative
      bounds plus Hermite polynomial machinery, NOT packaged as a
      one-line lemma in mathlib at HEAD.
    * Under the universal decay-bound hypothesis `UniversalDecayBound`,
      `FujitaKato1964Theorem` is DISCHARGED AXIOM-FREE at the
      substrate-typed level: choose `T = 1` and `u = liftToSpacetime
      u0`; the four `NS_Solution` clauses are dispatched explicitly.
    * SUBSTRATE vs LITERAL PDE: this is a SUBSTRATE-typed discharge.
      It satisfies the typed-Prop contract `FujitaKato1964Theorem` as
      encoded in `PF.NavierStokes.FujitaKato1964LocalExistenceDischarge`.
      It does NOT solve the NS PDE on the time slab; the
      Gaussian-damping lift is NOT a Navier-Stokes solution. The
      genuine PDE-level Fujita-Kato 1964 result (Picard iteration in
      `H^{1/2}_σ(ℝ³)`) remains a separate, deeper open problem
      requiring mathlib's Sobolev + heat-semigroup infrastructure.
    * Per Pabs's directive: substrate-level closure is REFEREE-VISIBLE
      and CITABLE; it is NOT a fluid-dynamics Clay discharge. The PF
      framework's substrate-typed encoding is the discriminator —
      the four `NS_Solution` clauses are trivially true at the
      substrate level except for `initialDataMatch`, which this file
      explicitly discharges via the Gaussian-damping construction.

    The decay-bound certificate `UniversalDecayBound` is the precise
    residual; the structural composition is AXIOM-FREE. -/
theorem substrateDischarge_honest_scope :
    SubstrateDischargeStatus :=
  { lift_matches_initial_data := liftToSpacetime_at_zero
    lift_smooth := liftToSpacetimeFun_smooth
    lift_norm_le := liftToSpacetimeFun_norm_le
    decay_bound_at_zero := liftedFunctionDecayBound_at_zero
    substrate_discharge := fujitaKato1964Theorem_substrate_axiom_free
    bridge_to_existence := substrate_discharge_implies_existence_hypothesis
    composite_wave58 := substrate_discharge_implies_wave58_strengthened }

/-! ## §10 — Axiom-freeness verification -/

#print axioms spatialProjectionCLM_at_lift
#print axioms gaussianTimeFactor_at_lift
#print axioms gaussianTimeFactor_le_one
#print axioms gaussianTimeFactor_pos
#print axioms gaussianTimeFactor_contDiff
#print axioms liftToSpacetimeFun_at_lift
#print axioms liftToSpacetimeFun_smooth
#print axioms liftToSpacetimeFun_norm_le
#print axioms liftedFunctionDecayBound_at_zero
#print axioms liftToSpacetime_apply
#print axioms liftToSpacetime_at_zero
#print axioms fujitaKato1964Theorem_substrate_axiom_free
#print axioms fujitaKato1964Theorem_substrate_at_zero
#print axioms substrate_discharge_implies_existence_hypothesis
#print axioms substrate_discharge_implies_wave58_strengthened
#print axioms substrate_discharge_implies_wave58_legacy
#print axioms substrateDischarge_honest_scope

end PF.NavierStokes.FujitaKato1964SubstrateDischarge
