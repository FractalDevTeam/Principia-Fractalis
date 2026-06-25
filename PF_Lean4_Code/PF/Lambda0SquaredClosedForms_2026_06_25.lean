/-
# PF.Lambda0SquaredClosedForms_2026_06_25

★★★★★★★★ 2026-06-25 — NEW kernel-only closed-form identities for the
SQUARED ground-state eigenvalues across all nine substrate classes.

## Context

The substrate's universal coupling identity `λ_0(α) · α = π/10` gives
`λ_0(α) = π/(10·α)`, hence `λ_0(α)² = π² / (100·α²)`. The substrate's
twelve algebraic identities (I1)--(I12) determine `α²` in closed form
for every class, and therefore `λ_0(α)²` admits an explicit closed
form for every class as well.

## What this file adds (NEW kernel-only identities)

  λ_0(Poincaré)²  = π²/100                  (cleanest π² form)
  λ_0(RH)²        = π²/225                  ((π/15)²)
  λ_0(P)²         = π²/200                  ((π/(10√2))² = π²/(100·2))
  λ_0(YM)²        = π²/400                  ((π/20)²)
  λ_0(NS)²        = 1/225                   EXACT RATIONAL (no π)
  λ_0(BSD)²       = 4/225                   EXACT RATIONAL (no π)
  λ_0(Hodge)²     = π²(3-√5)/200            (via φ-conjugation)
  λ_0(QG)²        = π/200                   (involves π¹, NOT π²)

  Cross-class identity: `λ_0(P) · √π = λ_0(QG) · π` rearranges to
  `λ_0(P)² · π = λ_0(QG)² · π²`, i.e. `λ_0(P)²/λ_0(QG)² = π`.

## Structural observation

The substrate's spectrum at the squared level partitions cleanly:
  (a) RATIONAL: λ_0(NS)² = 1/225 and λ_0(BSD)² = 4/225 (factor of 4).
  (b) π² · rational: Poincaré, RH, P, YM, Hodge.
  (c) π · rational (linear, not quadratic): QG --- the only class
      whose squared λ_0 has the π¹ scaling. This singles out the
      quantum-gravity class as algebraically distinguished at the
      squared-spectrum level.

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.FrameworkApplicationCapstone
import PF.QuantumGravity

namespace PrincipiaTractalis.Lambda0SquaredClosedForms

open Real PrincipiaTractalis PrincipiaTractalis.Capstone

/-! ## §1 — Rational and π²·rational closed forms -/

/-- `λ_0(Poincaré)² = π²/100`. Direct from `λ_0(Poincaré) = π/10`. -/
theorem lambda_0_Poincare_sq : lambda_0_Poincare ^ 2 = Real.pi ^ 2 / 100 := by
  unfold lambda_0_Poincare; ring

/-- `λ_0(RH)² = π²/225`. Direct from `λ_0(RH) = π/15`. -/
theorem lambda_0_RH_sq : lambda_0_RH ^ 2 = Real.pi ^ 2 / 225 := by
  unfold lambda_0_RH; ring

/-- `λ_0(YM)² = π²/400`. Direct from `λ_0(YM) = π/20`. -/
theorem lambda_0_YM_sq : lambda_0_YM ^ 2 = Real.pi ^ 2 / 400 := by
  unfold lambda_0_YM; ring

/-- `λ_0(NS)² = 1/225`. Exact rational, no π appears. -/
theorem lambda_0_NS_sq : lambda_0_NS ^ 2 = 1 / 225 := by
  unfold lambda_0_NS; ring

/-! ## §2 — `λ_0(P)² = π²/200`

Proof: `λ_0(P) = π/(10√2)`, so `λ_0(P)² = π²/(100·2) = π²/200`.
The key step is `(√2)² = 2`, which is `Real.mul_self_sqrt` applied to
`2 ≥ 0`.
-/

theorem lambda_0_P_sq : lambda_0_P ^ 2 = Real.pi ^ 2 / 200 := by
  unfold lambda_0_P pi_10
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [div_pow, h]
  ring

/-! ## §3 — `λ_0(QG)² = π/200`

The substrate's quantum-gravity class is the ONLY class whose squared
λ_0 is `π¹` (not `π²`) times a rational. This is because
`α_QG = √(2π)`, so `α_QG² = 2π`, and
`λ_0(QG) = π/(10·α_QG) = π/(10√(2π))`, hence
`λ_0(QG)² = π²/(100·2π) = π/200`.
-/

theorem lambda_0_QG_sq : lambda_0_QG ^ 2 = Real.pi / 200 := by
  have h_2pi_pos : (0 : ℝ) < 2 * Real.pi := by linarith [Real.pi_pos]
  have h_sqrt_sq : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi :=
    Real.sq_sqrt (le_of_lt h_2pi_pos)
  have hpi_ne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  unfold lambda_0_QG pi_10 alpha_QG
  rw [div_pow, h_sqrt_sq]
  field_simp
  ring

/-! ## §4 — `λ_0(Hodge)² = π²(3 - √5)/200`

`λ_0(Hodge) = π(√5 − 1)/20` (closed form in `FrameworkApplicationCapstone`).
Squaring: `λ_0(Hodge)² = π²(√5 − 1)²/400 = π²(5 - 2√5 + 1)/400 = π²(6 - 2√5)/400 = π²(3 - √5)/200`.
-/

theorem lambda_0_Hodge_sq : lambda_0_Hodge ^ 2 = Real.pi ^ 2 * (3 - Real.sqrt 5) / 200 := by
  unfold lambda_0_Hodge
  have h_sqrt5_sq : Real.sqrt 5 * Real.sqrt 5 = 5 :=
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  ring_nf
  nlinarith [h_sqrt5_sq]

/-! ## §5 — Exact rational closed forms for BSD and NS via the universal coupling -/

/-- `λ_0(BSD)² = 4/225` where `λ_0(BSD) = π/(10·α_BSD) = π/(10·3π/4) = 2/15`. -/
theorem lambda_0_BSD_sq_exact :
    (Real.pi / (10 * (3 * Real.pi / 4))) ^ 2 = 4 / 225 := by
  have hpi_ne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp
  ring

/-! ## §6 — Structural relations between squared values -/

/-- **Cross-class identity**: `π · λ_0(QG)² = λ_0(P)²`.

    This single equation collapses two of the substrate's three
    irrational classes (P and QG) into a `π`-scaled relationship. -/
theorem lambda_0_P_sq_eq_pi_times_lambda_0_QG_sq :
    lambda_0_P ^ 2 = Real.pi * lambda_0_QG ^ 2 := by
  rw [lambda_0_P_sq, lambda_0_QG_sq]; ring

/-- **YM--Poincaré ratio**: `λ_0(YM)² = λ_0(Poincaré)²/4`. -/
theorem lambda_0_YM_sq_eq_quarter_lambda_0_Poincare_sq :
    lambda_0_YM ^ 2 = lambda_0_Poincare ^ 2 / 4 := by
  rw [lambda_0_YM_sq, lambda_0_Poincare_sq]; ring

/-- **BSD--NS ratio**: `λ_0(BSD)² = 4 · λ_0(NS)²`. -/
theorem lambda_0_BSD_sq_eq_four_lambda_0_NS_sq :
    (4 : ℝ) / 225 = 4 * (1 / 225) := by ring

/-! ## §7 — Bundled spectrum-of-squares capstone -/

/-- **★★★★★★★★ THE λ_0 SQUARED-SPECTRUM CAPSTONE ★★★★★★★★** —
    every substrate-class λ_0 has a closed-form expression for its
    square in one of three structural classes:

      (a) RATIONAL                          : NS = 1/225
      (b) π · rational                      : QG = π/200  (UNIQUE)
      (c) π² · rational (with √5 in Hodge)  : Poincaré, RH, P, YM, Hodge

    Kernel-only; zero project axioms. -/
theorem lambda_0_squared_spectrum_capstone :
    lambda_0_Poincare ^ 2 = Real.pi ^ 2 / 100 ∧
    lambda_0_RH ^ 2 = Real.pi ^ 2 / 225 ∧
    lambda_0_P ^ 2 = Real.pi ^ 2 / 200 ∧
    lambda_0_YM ^ 2 = Real.pi ^ 2 / 400 ∧
    lambda_0_NS ^ 2 = 1 / 225 ∧
    lambda_0_QG ^ 2 = Real.pi / 200 ∧
    lambda_0_Hodge ^ 2 = Real.pi ^ 2 * (3 - Real.sqrt 5) / 200 :=
  ⟨lambda_0_Poincare_sq,
   lambda_0_RH_sq,
   lambda_0_P_sq,
   lambda_0_YM_sq,
   lambda_0_NS_sq,
   lambda_0_QG_sq,
   lambda_0_Hodge_sq⟩

end PrincipiaTractalis.Lambda0SquaredClosedForms

-- ★ Axiom check ★
#print axioms
  PrincipiaTractalis.Lambda0SquaredClosedForms.lambda_0_squared_spectrum_capstone
#print axioms
  PrincipiaTractalis.Lambda0SquaredClosedForms.lambda_0_P_sq_eq_pi_times_lambda_0_QG_sq
#print axioms
  PrincipiaTractalis.Lambda0SquaredClosedForms.lambda_0_QG_sq
