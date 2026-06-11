/-
# Fujita-Kato 1964 — Leray Projector at the Fourier Symbol Level

★ 2026-06-10 — Fourth brick of real Fujita-Kato infrastructure.
★ The Leray projector at the Fourier symbol level on real `ℝ³`
  vectors, using mathlib's `EuclideanSpace ℝ (Fin 3)` carrier.

At the Fourier symbol level, the Leray projector

  `P̂(ξ) v := v - (⟨ξ, v⟩ / ‖ξ‖²) ξ`   for `ξ ≠ 0`
  `P̂(0) v := v`

projects an `ℝ³`-valued frequency-mode `v` onto the subspace
orthogonal to `ξ`. Integrated against the full Fourier transform
of a velocity field, `P̂` enforces the incompressibility constraint
`div u = 0` at every frequency.

This file lives at the **pointwise symbol layer** on a fixed
frequency `ξ`. The lift to Schwartz fields (where one composes
`P̂` with the Fourier transform of a vector field) is the next
brick. Here we prove the algebraic properties of the symbol
itself, all kernel-only:

  §1 — Symbol definition `lerayFourierSymbol`.
  §2 — Pointwise properties (zero-freq identity, zero-data zero,
       perpendicular fixed, parallel annihilated).
  §3 — Single-frequency idempotence `P̂(P̂ v) = P̂ v`.
  §4 — Capstone bundling all properties.
  §5 — `#print axioms` audit.

Axiom-free; depends only on `[propext, Classical.choice, Quot.sound]`.

Author: Pablo Cohen (2026-06-10)
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic

set_option autoImplicit false

namespace PF.NavierStokes.FujitaKato1964.LerayProjectorFourier

/-! ## §1 — The Leray Fourier symbol on a single frequency -/

/-- **Three-dimensional real Euclidean frequency space.** Same
carrier as `PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier.R3`
but re-declared here to keep this file standalone at the symbol
layer. -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-- **★ Leray projector at the Fourier symbol level.**

For a frequency `ξ ∈ ℝ³` and a velocity Fourier mode `v ∈ ℝ³`,

  `lerayFourierSymbol ξ v := v - (⟨ξ, v⟩ / ‖ξ‖²) ξ`   if `ξ ≠ 0`,
  `lerayFourierSymbol 0 v := v`.

The branching at `ξ = 0` is the standard convention: the zero
Fourier mode (the spatial average) is treated as already
divergence-free. For `ξ ≠ 0`, the formula subtracts the component
of `v` along `ξ`, leaving the part orthogonal to `ξ` — which is
exactly the incompressibility (`ξ · v̂ = 0`) constraint at that
frequency. -/
noncomputable def lerayFourierSymbol
    (ξ : R3) (v : R3) : R3 :=
  if ξ = 0 then v else v - (inner ℝ ξ v / ‖ξ‖ ^ 2) • ξ

/-! ## §2 — Pointwise properties -/

/-- **Zero-frequency identity**: `P̂(0) v = v`. The spatial-average
mode is always divergence-free by convention. -/
theorem lerayFourierSymbol_zero_freq (v : R3) :
    lerayFourierSymbol 0 v = v := by
  unfold lerayFourierSymbol
  rw [if_pos rfl]

/-- **Zero-data is annihilated**: `P̂(ξ) 0 = 0` for any frequency. -/
theorem lerayFourierSymbol_zero_field (ξ : R3) :
    lerayFourierSymbol ξ 0 = 0 := by
  unfold lerayFourierSymbol
  by_cases h : ξ = 0
  · rw [if_pos h]
  · rw [if_neg h]
    simp

/-- **Perpendicular vectors are fixed**: if `v` is already
orthogonal to the frequency `ξ`, then the projector leaves `v`
unchanged. The orthogonality hypothesis `⟨ξ, v⟩ = 0` makes the
parallel-component subtraction vanish. -/
theorem lerayFourierSymbol_perp_fixed
    (ξ v : R3) (hperp : inner ℝ ξ v = (0 : ℝ)) :
    lerayFourierSymbol ξ v = v := by
  unfold lerayFourierSymbol
  by_cases h : ξ = 0
  · rw [if_pos h]
  · rw [if_neg h, hperp]
    simp

/-- **Parallel vectors are annihilated**: `P̂(ξ) ξ = 0` whenever
`ξ ≠ 0`. The projector kills the parallel component. -/
theorem lerayFourierSymbol_par_zero
    (ξ : R3) (h : ξ ≠ 0) :
    lerayFourierSymbol ξ ξ = 0 := by
  unfold lerayFourierSymbol
  rw [if_neg h]
  -- Goal: ξ - (⟨ξ, ξ⟩ / ‖ξ‖²) • ξ = 0
  -- Use ⟨ξ, ξ⟩ = ‖ξ‖² and ‖ξ‖² ≠ 0
  have hnorm_sq : (‖ξ‖ : ℝ) ^ 2 = inner ℝ ξ ξ := by
    rw [@real_inner_self_eq_norm_sq]
  have hξ_ne : (‖ξ‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr h
  have hξsq_ne : (‖ξ‖ : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hξ_ne
  rw [← hnorm_sq]
  rw [div_self hξsq_ne]
  rw [one_smul]
  exact sub_self ξ

/-! ## §3 — Single-frequency idempotence -/

/-- **Inner product of `ξ` with the projected vector vanishes**
for `ξ ≠ 0`. Computationally:

  `⟨ξ, v - (⟨ξ, v⟩ / ‖ξ‖²) ξ⟩`
    `= ⟨ξ, v⟩ - (⟨ξ, v⟩ / ‖ξ‖²) ⟨ξ, ξ⟩`
    `= ⟨ξ, v⟩ - (⟨ξ, v⟩ / ‖ξ‖²) ‖ξ‖²`
    `= ⟨ξ, v⟩ - ⟨ξ, v⟩ = 0`.

This is the Fourier-level statement of divergence-freeness of the
projected vector field. -/
theorem lerayFourierSymbol_inner_eq_zero
    (ξ v : R3) (h : ξ ≠ 0) :
    inner ℝ ξ (lerayFourierSymbol ξ v) = (0 : ℝ) := by
  unfold lerayFourierSymbol
  rw [if_neg h]
  -- Goal: ⟨ξ, v - (⟨ξ, v⟩ / ‖ξ‖²) • ξ⟩ = 0
  rw [inner_sub_right, inner_smul_right]
  -- Goal: ⟨ξ, v⟩ - (⟨ξ, v⟩ / ‖ξ‖²) * ⟨ξ, ξ⟩ = 0
  have hnorm_sq : (‖ξ‖ : ℝ) ^ 2 = inner ℝ ξ ξ := by
    rw [@real_inner_self_eq_norm_sq]
  have hξ_ne : (‖ξ‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr h
  have hξsq_ne : (‖ξ‖ : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hξ_ne
  rw [← hnorm_sq]
  field_simp
  ring

/-- **★ Single-frequency idempotence**: `P̂(ξ) (P̂(ξ) v) = P̂(ξ) v`.

For `ξ = 0` the projector is the identity, so idempotence is trivial.
For `ξ ≠ 0`, the key lemma `lerayFourierSymbol_inner_eq_zero` shows
the projected vector is orthogonal to `ξ`; applying the projector
again therefore subtracts zero, leaving the vector unchanged.
Together with `lerayFourierSymbol_perp_fixed`, this gives the result
in one line. -/
theorem lerayFourierSymbol_idempotent (ξ v : R3) :
    lerayFourierSymbol ξ (lerayFourierSymbol ξ v) =
      lerayFourierSymbol ξ v := by
  by_cases h : ξ = 0
  · rw [h, lerayFourierSymbol_zero_freq, lerayFourierSymbol_zero_freq]
  · exact lerayFourierSymbol_perp_fixed ξ (lerayFourierSymbol ξ v)
      (lerayFourierSymbol_inner_eq_zero ξ v h)

/-! ## §4 — Capstone -/

/-- **★★★ Leray Fourier-symbol brick capstone ★★★**

Bundles the algebraic properties of the Leray projector at the
Fourier symbol level on `EuclideanSpace ℝ (Fin 3)`:

  (a) Zero-frequency identity: `P̂(0) v = v`
  (b) Zero data is annihilated: `P̂(ξ) 0 = 0`
  (c) Perpendicular vectors are fixed: `⟨ξ, v⟩ = 0 ⟹ P̂(ξ) v = v`
  (d) Parallel vectors are annihilated: `ξ ≠ 0 ⟹ P̂(ξ) ξ = 0`
  (e) Divergence-free output: `ξ ≠ 0 ⟹ ⟨ξ, P̂(ξ) v⟩ = 0`
  (f) Idempotence: `P̂(ξ) (P̂(ξ) v) = P̂(ξ) v` for all `ξ`

These are the literal projector axioms one needs in order to
identify `P̂` with the orthogonal projection onto `ξ^⊥` at every
nonzero frequency, with the spatial-average mode left untouched.

Axiom-free: `[propext, Classical.choice, Quot.sound]` only. -/
theorem lerayFourierSymbol_capstone :
    -- (a) Zero frequency is identity
    (∀ v : R3, lerayFourierSymbol 0 v = v) ∧
    -- (b) Zero data is annihilated
    (∀ ξ : R3, lerayFourierSymbol ξ 0 = 0) ∧
    -- (c) Perpendicular vectors are fixed
    (∀ (ξ v : R3), inner ℝ ξ v = (0 : ℝ) →
       lerayFourierSymbol ξ v = v) ∧
    -- (d) Parallel vectors are annihilated for ξ ≠ 0
    (∀ ξ : R3, ξ ≠ 0 → lerayFourierSymbol ξ ξ = 0) ∧
    -- (e) Divergence-free output for ξ ≠ 0
    (∀ (ξ v : R3), ξ ≠ 0 →
       inner ℝ ξ (lerayFourierSymbol ξ v) = (0 : ℝ)) ∧
    -- (f) Idempotence for all ξ
    (∀ ξ v : R3,
       lerayFourierSymbol ξ (lerayFourierSymbol ξ v) =
         lerayFourierSymbol ξ v) :=
  ⟨lerayFourierSymbol_zero_freq,
   lerayFourierSymbol_zero_field,
   lerayFourierSymbol_perp_fixed,
   lerayFourierSymbol_par_zero,
   lerayFourierSymbol_inner_eq_zero,
   lerayFourierSymbol_idempotent⟩

/-! ## §5 — Axiom audit -/

#print axioms lerayFourierSymbol_zero_freq
#print axioms lerayFourierSymbol_zero_field
#print axioms lerayFourierSymbol_perp_fixed
#print axioms lerayFourierSymbol_par_zero
#print axioms lerayFourierSymbol_inner_eq_zero
#print axioms lerayFourierSymbol_idempotent
#print axioms lerayFourierSymbol_capstone

end PF.NavierStokes.FujitaKato1964.LerayProjectorFourier
