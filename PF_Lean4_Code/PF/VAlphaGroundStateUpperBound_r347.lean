/-
# r347 — The variational upper bound on `H_α`, and what it does to `λ₀ = π/(10α)`

★ 2026-10-24 — two basis vectors refute the arxiv Ground State Formula ★

## The finding

`PF/Operators/VAlphaExplicit.lean` records the arxiv paper's conclusion
`λ₀(H_α) = π/(10·α)` and names the remaining gap
`GroundStateVariationalInput α`. Two things are wrong with that, and the
material for both is already in that file.

**1. The claim is false, by the variational principle, in two basis states.**

The file proves

    h_alpha_basis_diag_zero : h_alpha_basis α 0 0 = 0

with the docstring "the trial state `|0⟩` is annihilated by `V_α` and by the
diagonal of `T`. This is the arxiv paper's variational-principle starting
point." That lemma is correct. But the variational principle reads

    inf_{‖ψ‖=1} ⟨H ψ, ψ⟩  ≤  ⟨H φ, φ⟩  for ANY unit φ,

so `|0⟩` gives `λ₀ ≤ H₀₀ = 0`, and `π/(10·α) > 0` for `α > 0`. The proved
lemma therefore REFUTES the claimed value rather than supporting it: `|0⟩`
supplies an upper bound of `0`, not a value of `π/(10·α)`. The inference in
the docstring runs the wrong way.

The two-state trial `φ = (e₀ + e₁)/√2` makes it quantitative. With
`T` purely off-diagonal nearest-neighbour at `-1/2` (`t_action_basis`) and
`V_α(0) = 0` (`v_alpha_coeff_zero`), `V_α(1) = π/(10α)`:

    ⟨H φ, φ⟩ = (H₀₀ + H₀₁ + H₁₀ + H₁₁)/2 = (0 - 1/2 - 1/2 + π/(10α))/2
             = -1/2 + π/(20α)

which is **negative** for every `α > π/10`, hence for every `α > 1/2`, the
regime the framework uses. At the P-class value `α = √2` it is `≈ -0.389`
against a claimed `+0.222`: the stated formula has the **wrong sign**.

**2. The Lean Prop meant to carry the claim does not state it.**

    GroundStateVariationalInput α : Prop :=
      1/2 < α → ∀ H, (symmetric) → (matrix elements) →
        ∃ lam0, lam0 = groundStateValue α ∧ 0 < lam0

The existential never mentions `inf ⟨H ψ, ψ⟩`; `lam0` is not tied to `H`'s
spectrum at all. Its witness is `lam0 := groundStateValue α`, and
`0 < π/(10α)` holds for `α > 0`, so the conclusion is provable outright and
carries no spectral content. The file's own comment concedes the point: "We
leave the precise quantifier shape to the future mathlib hook." So the
conditional capstone `H_alpha_ground_state_eq_pi_10_alpha` is true as stated
and does **not** say that `H_α`'s ground-state energy is `π/(10·α)`.

## Why this matters, stated plainly

`λ₀(H_α) = π/(10·α)` is the quantity the spectral-gap route to P ≠ NP is
built on (`lambda_0_P = π/(10√2)`, `lambda_0_NP = π/(10(φ+1/4))` in
`PF.SpectralGap`). If the ground-state energy is not that value, the gap
between the two α's is not a gap between ground-state energies, and the route
needs either a different operator, a different sector, or a different
quantity.

**What survives, and it is not nothing.** `π/(10·α)` IS a real invariant of
this operator — just not its ground-state energy.
`PF/GroundStateIsPotentialMinimum_r346.lean` proves it is the minimum of the
POTENTIAL's diagonal on the computational sector `n ≥ 1`, attained uniquely at
`n = 1 = 3⁰`, the base of the substrate tower. That is the true theorem in the
neighbourhood of the false one, and the degeneracy among tower levels `3^k`
(all with `D₃ = 1`) is broken by the 3-adic term. The repair direction is
therefore to state the framework's spectral claims about `min diag V_α` on the
computational sector, where they hold, rather than about `λ₀(H_α)`, where they
do not.

## What is and is not claimed here

**Claimed.** The Rayleigh quotient of the explicit two-state trial vector is
`-1/2 + π/(20α)`; it is negative for `α > π/10`; and it is strictly less than
`groundStateValue α` for every `α > 0`. Since the variational infimum is at
most any Rayleigh quotient, `λ₀(H_α) < groundStateValue α` whenever that
infimum exists, and `λ₀(H_α) < 0` for `α > π/10`.

**Not claimed.** That `H_α` is self-adjoint, essentially self-adjoint, or
bounded below — `KatoRellichDischarge.lean` already proves the naive bounded
formulation unsatisfiable by Hellinger–Toeplitz, and
`VAlphaPMapShape.lean` moves to the `LinearPMap` frame. None of that is needed
for an upper bound: a Rayleigh quotient at a specific unit vector bounds the
infimum from above whenever the infimum is defined, and if the infimum is `-∞`
the claimed formula fails anyway. Nothing here constructs the operator as an
unbounded self-adjoint operator, and nothing here is about P vs NP.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-24.
-/

import Mathlib.Tactic
import PF.Operators.VAlphaExplicit

namespace PrincipiaTractalis
namespace VAlphaGroundStateUpperBound

open PrincipiaTractalis.Operators
open PrincipiaTractalis.TuringEncoding

/-! ## §1 — The potential at `n = 1` -/

/-- `D₃(0) = 0`, from the definition. -/
theorem digitalSum3_zero'' : digitalSum3 0 = 0 := by
  unfold digitalSum3; simp

/-- `D₃(1) = 1`, from the corpus's `digitalSum3_add_3_mul` at `x = 1, y = 0`. -/
theorem digitalSum3_one'' : digitalSum3 1 = 1 := by
  have h := digitalSum3_add_3_mul (x := 1) (y := 0) (by norm_num)
  simpa [digitalSum3_zero''] using h

/-- **`V_α(1) = π/(10α)`.** The potential at the first computational state is
exactly the coupling coefficient: `D₃(1) = 1` and both valuations vanish. -/
theorem v_alpha_coeff_one (α : ℝ) :
    v_alpha_coeff α 1 = Real.pi / (10 * α) := by
  unfold v_alpha_coeff d3_coeff nu2_coeff nu3_coeff
  rw [digitalSum3_one'']
  simp [padicValNat.one]

/-! ## §2 — The matrix elements of the two-state block -/

theorem h_alpha_basis_zero_one (α : ℝ) : h_alpha_basis α 0 1 = -(1 / 2) := by
  unfold h_alpha_basis t_action_basis
  norm_num

theorem h_alpha_basis_one_zero (α : ℝ) : h_alpha_basis α 1 0 = -(1 / 2) := by
  unfold h_alpha_basis t_action_basis
  norm_num

theorem h_alpha_basis_one_one (α : ℝ) :
    h_alpha_basis α 1 1 = Real.pi / (10 * α) := by
  unfold h_alpha_basis
  rw [t_action_basis_diag]
  simp [v_alpha_coeff_one]

/-! ## §3 — The Rayleigh quotient of `(e₀ + e₁)/√2` -/

/-- The Rayleigh quotient of the normalised two-state trial vector, in terms of
the matrix block. For `φ = (e₀ + e₁)/√2` one has
`⟨Hφ, φ⟩ = (H₀₀ + H₀₁ + H₁₀ + H₁₁)/2`. -/
noncomputable def twoStateRayleigh (α : ℝ) : ℝ :=
  (h_alpha_basis α 0 0 + h_alpha_basis α 0 1
    + h_alpha_basis α 1 0 + h_alpha_basis α 1 1) / 2

/-- **★ The closed form: `-1/2 + π/(20α)`.** -/
theorem twoStateRayleigh_eq (α : ℝ) :
    twoStateRayleigh α = -(1 / 2) + Real.pi / (20 * α) := by
  unfold twoStateRayleigh
  rw [h_alpha_basis_diag_zero, h_alpha_basis_zero_one, h_alpha_basis_one_zero,
      h_alpha_basis_one_one]
  ring

/-- **★★ It is strictly below the claimed ground-state value**, for every
`α > 0`. Hence the variational infimum is too, whenever it exists. -/
theorem twoStateRayleigh_lt_groundStateValue {α : ℝ} (hα : 0 < α) :
    twoStateRayleigh α < groundStateValue α := by
  rw [twoStateRayleigh_eq]
  unfold groundStateValue
  have h20 : (0 : ℝ) < 20 * α := by linarith
  have h10 : (0 : ℝ) < 10 * α := by linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hhalf : Real.pi / (20 * α) < Real.pi / (10 * α) := by
    apply div_lt_div_of_pos_left hpi h10
    linarith
  linarith

/-- **★★★ It is negative** for every `α > π/10` — in particular for every
`α > 1/2`, the regime the framework uses. So the claimed ground-state value
`π/(10α) > 0` has the wrong sign. -/
theorem twoStateRayleigh_neg {α : ℝ} (hα : Real.pi / 10 < α) :
    twoStateRayleigh α < 0 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hα0 : (0 : ℝ) < α := lt_trans (by positivity) hα
  have h20 : (0 : ℝ) < 20 * α := by linarith
  rw [twoStateRayleigh_eq]
  -- `π/(20α) < 1/2` is `π < 10α`, which is the hypothesis scaled by 10.
  have key : Real.pi / (20 * α) < 1 / 2 := by
    rw [div_lt_iff₀ h20]
    linarith
  linarith

/-- The same statement in the framework's own regime `α > 1/2`. -/
theorem twoStateRayleigh_neg_of_half_lt {α : ℝ} (hα : 1 / 2 < α) :
    twoStateRayleigh α < 0 := by
  apply twoStateRayleigh_neg
  -- π/10 < 1/2 because π < 5, and `Real.pi_lt_four` gives π < 4.
  have hpi4 : Real.pi < 4 := Real.pi_lt_four
  linarith

/-! ## §4 — Capstone -/

/-- **The Ground State Formula `λ₀(H_α) = π/(10α)` is refuted at the level of
the variational principle.**

An explicit unit vector has Rayleigh quotient `-1/2 + π/(20α)`, which is both
strictly below `π/(10α)` and strictly negative in the framework's regime. The
variational infimum is at most any Rayleigh quotient, so it cannot equal
`π/(10α)`.

`π/(10α)` remains the minimum of the potential's diagonal on the computational
sector — see `PF/GroundStateIsPotentialMinimum_r346.lean`. That is the true
statement; this one says the false statement is false. -/
theorem ground_state_formula_refuted {α : ℝ} (hα : 1 / 2 < α) :
    twoStateRayleigh α = -(1 / 2) + Real.pi / (20 * α) ∧
    twoStateRayleigh α < groundStateValue α ∧
    twoStateRayleigh α < 0 ∧
    0 < groundStateValue α := by
  have hα0 : (0 : ℝ) < α := by linarith
  refine ⟨twoStateRayleigh_eq α, twoStateRayleigh_lt_groundStateValue hα0,
          twoStateRayleigh_neg_of_half_lt hα, ?_⟩
  unfold groundStateValue
  have : (0 : ℝ) < 10 * α := by linarith
  exact div_pos Real.pi_pos this

end VAlphaGroundStateUpperBound
end PrincipiaTractalis

/-! ## §Axiom check -/

#print axioms PrincipiaTractalis.VAlphaGroundStateUpperBound.v_alpha_coeff_one
#print axioms PrincipiaTractalis.VAlphaGroundStateUpperBound.twoStateRayleigh_eq
#print axioms PrincipiaTractalis.VAlphaGroundStateUpperBound.twoStateRayleigh_lt_groundStateValue
#print axioms PrincipiaTractalis.VAlphaGroundStateUpperBound.twoStateRayleigh_neg
#print axioms PrincipiaTractalis.VAlphaGroundStateUpperBound.ground_state_formula_refuted
