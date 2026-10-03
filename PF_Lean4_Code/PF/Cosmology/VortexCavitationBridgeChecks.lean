/-
# PF.Cosmology.VortexCavitationBridgeChecks

Companion to `codex/PF_VORTEX_CAVITATION_WHOLE_TOE_INVESTIGATION.md` (2026-10-03).

## What this file is

Four small NEGATIVE / consistency propositions about the counter-rotating
vortex chain, each with its premises explicit.  Nothing here formalizes an
experimental effect, and nothing here is derived from the substrate: every
statement is elementary real / matrix arithmetic about objects the book or
`CounterRotatingVorticesZeroPointFreeEnergy.lean` already defines.

1. `ch2Matrix_le_half`, `ch2Matrix_lt_threshold`,
   `thresholdGate_ch2Matrix_eq_zero` — the book's matrix formula for `ch_2`
   (ch06 Thm "Neural Consciousness Formula",
   `ch_2(W) = (Tr(W²) − (Tr W)²) / (2‖W‖_F²)`) is bounded above by `1/2` on
   EVERY real square matrix.  It therefore never reaches the `19/20` gate, so
   the Heaviside factor `Θ(ch_2 − 0.95)` in ch08 Def "Consciousness
   Stress-Energy" vanishes identically whenever `ch_2` is read off a real
   matrix by that formula — in particular off a velocity-gradient tensor.
   PREMISE (not derived, not in the book): the observable map
   "flow state ↦ `ch2Matrix (∇u)`".
2. `ch2Matrix_pureRotation`, `ch2Matrix_pureStrain` — the bound is attained;
   a pure rotation (a vortex axis) sits at `−1/2`, the far end from the gate.
3. `counter_rotation_angular_momentum_zero_iff`,
   `counter_rotation_energy_pos` — opposite angular velocities cancel angular
   momentum iff the moments of inertia agree (or nothing rotates), and never
   cancel kinetic energy.
4. `reservoir_inequality_not_scale_invariant` — an inequality of the shape
   `2ω² < R` between a squared angular velocity and a fixed pure number flips
   under a change of the unit of `ω`; it is not a physical statement and
   carries no power.

Verification status is recorded in the codex document, not here: a source
file is not evidence.  Imports are mathlib-only so the module can be checked
without touching any project build.
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace PrincipiaTractalis.Cosmology.VortexCavitationBridge

open Matrix Finset

section MatrixCh2

variable {n : Type*} [Fintype n]

/-- Frobenius norm squared, written out entrywise (`‖W‖_F² = Σ_ij W_ij²`,
    ch06 Thm "Neural Consciousness Formula"). -/
def frobSq (W : Matrix n n ℝ) : ℝ := ∑ i, ∑ j, W i j ^ 2

/-- The book's matrix formula for `ch_2` (ch06 Thm "Neural Consciousness
    Formula"): `(Tr(W²) − (Tr W)²) / (2‖W‖_F²)`. -/
noncomputable def ch2Matrix (W : Matrix n n ℝ) : ℝ :=
  ((W * W).trace - W.trace ^ 2) / (2 * frobSq W)

theorem frobSq_nonneg (W : Matrix n n ℝ) : 0 ≤ frobSq W :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem trace_mul_self (W : Matrix n n ℝ) :
    (W * W).trace = ∑ i, ∑ j, W i j * W j i := by
  simp [Matrix.trace, Matrix.mul_apply]

theorem frobSq_swap (W : Matrix n n ℝ) : ∑ i, ∑ j, W j i ^ 2 = frobSq W :=
  Finset.sum_comm

/-- `Tr(W²) ≤ ‖W‖_F²` (Cauchy–Schwarz in its `2ab ≤ a² + b²` form). -/
theorem trace_mul_self_le_frobSq (W : Matrix n n ℝ) :
    (W * W).trace ≤ frobSq W := by
  rw [trace_mul_self]
  have h0 : 0 ≤ ∑ i, ∑ j, (W i j - W j i) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1 : ∑ i, ∑ j, (W i j - W j i) ^ 2
      = (∑ i, ∑ j, W i j ^ 2) + (∑ i, ∑ j, W j i ^ 2)
          - 2 * ∑ i, ∑ j, W i j * W j i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hs := frobSq_swap W
  unfold frobSq at *
  linarith

/-- `−‖W‖_F² ≤ Tr(W²)`. -/
theorem neg_frobSq_le_trace_mul_self (W : Matrix n n ℝ) :
    -frobSq W ≤ (W * W).trace := by
  rw [trace_mul_self]
  have h0 : 0 ≤ ∑ i, ∑ j, (W i j + W j i) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1 : ∑ i, ∑ j, (W i j + W j i) ^ 2
      = (∑ i, ∑ j, W i j ^ 2) + (∑ i, ∑ j, W j i ^ 2)
          + 2 * ∑ i, ∑ j, W i j * W j i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hs := frobSq_swap W
  unfold frobSq at *
  linarith

/-- **The matrix `ch_2` never exceeds `1/2`.**  No hypothesis on `W`. -/
theorem ch2Matrix_le_half (W : Matrix n n ℝ) : ch2Matrix W ≤ 1 / 2 := by
  unfold ch2Matrix
  rcases (frobSq_nonneg W).eq_or_lt with h | h
  · rw [← h]; norm_num
  · rw [div_le_iff₀ (by positivity)]
    have h1 := trace_mul_self_le_frobSq W
    nlinarith [sq_nonneg W.trace]

/-- For a traceless matrix (incompressible velocity gradient) the matrix
    `ch_2` is also bounded below by `−1/2`. -/
theorem neg_half_le_ch2Matrix_of_trace_eq_zero (W : Matrix n n ℝ)
    (hW : W.trace = 0) : -(1 / 2) ≤ ch2Matrix W := by
  unfold ch2Matrix
  rcases (frobSq_nonneg W).eq_or_lt with h | h
  · rw [← h]; norm_num
  · rw [le_div_iff₀ (by positivity), hW]
    have h1 := neg_frobSq_le_trace_mul_self W
    nlinarith

/-- **The `19/20` gate is unreachable by the matrix formula.** -/
theorem ch2Matrix_lt_threshold (W : Matrix n n ℝ) : ch2Matrix W < 19 / 20 :=
  lt_of_le_of_lt (ch2Matrix_le_half W) (by norm_num)

/-- The Heaviside gate `Θ(ch_2 − 0.95)` of ch08 Def "Consciousness
    Stress-Energy", as a real-valued function. -/
noncomputable def thresholdGate (x : ℝ) : ℝ := if (19 / 20 : ℝ) ≤ x then 1 else 0

/-- Under the matrix formula the gate is identically closed. -/
theorem thresholdGate_ch2Matrix_eq_zero (W : Matrix n n ℝ) :
    thresholdGate (ch2Matrix W) = 0 := by
  unfold thresholdGate
  rw [if_neg (not_le.mpr (ch2Matrix_lt_threshold W))]

/-- Any integrand multiplied by the gate vanishes: the gated source term
    contributes nothing, whatever stress operator `T` is supplied. -/
theorem gated_source_eq_zero (W : Matrix n n ℝ) (T : ℝ) :
    T * thresholdGate (ch2Matrix W) = 0 := by
  rw [thresholdGate_ch2Matrix_eq_zero, mul_zero]

end MatrixCh2

section Sharpness

/-- Planar pure rotation (velocity gradient on a vortex axis). -/
def pureRotation : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- Planar pure strain (velocity gradient at a hyperbolic stagnation point). -/
def pureStrain : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- On a pure rotation the matrix `ch_2` equals `−1/2`. -/
theorem ch2Matrix_pureRotation : ch2Matrix pureRotation = -(1 / 2) := by
  simp [ch2Matrix, frobSq, pureRotation, Matrix.trace,
    Fin.sum_univ_two]
  norm_num

/-- On a pure strain the matrix `ch_2` equals `+1/2`: the upper bound of
    `ch2Matrix_le_half` is attained. -/
theorem ch2Matrix_pureStrain : ch2Matrix pureStrain = 1 / 2 := by
  simp [ch2Matrix, frobSq, pureStrain, Matrix.trace,
    Fin.sum_univ_two]
  norm_num

end Sharpness

section Rotors

/-- **Check (a).** Two bodies with moments of inertia `I₁, I₂` and opposite
    angular velocities `ω, −ω` have zero total angular momentum iff nothing
    rotates or the moments of inertia coincide.  `ω₁ + ω₂ = 0` alone does
    not cancel angular momentum. -/
theorem counter_rotation_angular_momentum_zero_iff (I₁ I₂ ω : ℝ) :
    I₁ * ω + I₂ * (-ω) = 0 ↔ ω = 0 ∨ I₁ = I₂ := by
  constructor
  · intro h
    have h' : (I₁ - I₂) * ω = 0 := by linarith
    rcases mul_eq_zero.mp h' with h1 | h1
    · right; linarith
    · left; exact h1
  · rintro (h | h)
    · rw [h]; ring
    · rw [h]; ring

/-- A counter-rotating configuration with nonzero angular momentum exists. -/
theorem exists_counter_rotating_with_angular_momentum :
    ∃ I₁ I₂ ω : ℝ, 0 < I₁ ∧ 0 < I₂ ∧ I₁ * ω + I₂ * (-ω) ≠ 0 :=
  ⟨2, 1, 1, by norm_num, by norm_num, by norm_num⟩

/-- **Check (b).** Counter-rotation never cancels kinetic energy. -/
theorem counter_rotation_energy_pos {I₁ I₂ ω : ℝ} (hI₁ : 0 < I₁) (hI₂ : 0 < I₂)
    (hω : ω ≠ 0) : 0 < I₁ * ω ^ 2 / 2 + I₂ * (-ω) ^ 2 / 2 := by
  have h : 0 < ω ^ 2 := by positivity
  have h1 := mul_pos hI₁ h
  have h2 := mul_pos hI₂ h
  nlinarith

end Rotors

section Reservoir

/-- **Check (c).** The shape of `FreeEnergyExtractable`
    (`CounterRotatingVorticesZeroPointFreeEnergy.lean`): `2ω² < R` for a fixed
    pure number `R`.  It holds at `ω = 1` and fails after rescaling the unit
    of angular velocity by the factor `R`.  A statement whose truth value
    depends on the unit of `ω` asserts nothing about extractable power. -/
theorem reservoir_inequality_not_scale_invariant (R : ℝ) (hR : 2 < R) :
    2 * (1 : ℝ) ^ 2 < R ∧ ∃ c : ℝ, 0 < c ∧ ¬ (2 * (c * 1) ^ 2 < R) := by
  refine ⟨by linarith, R, by linarith, ?_⟩
  rw [not_lt]
  nlinarith

end Reservoir

/-! ## Axiom report -/

#print axioms ch2Matrix_le_half
#print axioms neg_half_le_ch2Matrix_of_trace_eq_zero
#print axioms ch2Matrix_lt_threshold
#print axioms thresholdGate_ch2Matrix_eq_zero
#print axioms gated_source_eq_zero
#print axioms ch2Matrix_pureRotation
#print axioms ch2Matrix_pureStrain
#print axioms counter_rotation_angular_momentum_zero_iff
#print axioms exists_counter_rotating_with_angular_momentum
#print axioms counter_rotation_energy_pos
#print axioms reservoir_inequality_not_scale_invariant

end PrincipiaTractalis.Cosmology.VortexCavitationBridge
