/-
# r322: ω STRUCTURAL SYMMETRIES — period-2 of the character map ω(α) = e^{iπα}.

★ 2026-08-24 r322 — the character-map companion to r240's σ symmetries. ★

## Purpose

The r220 character map is `omega α := Complex.exp ((π α) · I)` (`PF/LogPeriodicity_r220.lean:248`).
Every substrate invariant defined via `omega` — the block factor `χ(omega α)`,
its norm `‖χ(omega α)‖`, r212's `sigma`, r221's `chi_norm_unity_*`, r224's
`chi_norm_three_iff_even_integer` — necessarily inherits `omega`'s
periodicity in `α`.

This file proves the underlying identity

    omega (α + 2 · k) = omega α          for every  k : ℤ

and derives its reusable factorisation consequence: any invariant `F` that
factors through `omega` satisfies `F (α + 2·k) = F α`.

## Why this matters — the α-selector obstruction

Combined with r240 (`sigma_add_two`, `sigma_add_two_int`), r321 (frequency
provenance reconciliation), r221 (`chi_norm_unity_iff_half_or_odd_integer`),
and r224 (`chi_norm_three_iff_even_integer`), this file makes explicit that
**the entire ω / χ / σ character sector of the r220 substrate cannot
distinguish any exact real α from `α + 2·k`**. Level-set membership is
substrate-native; the choice of representative within a `2·ℤ`-orbit is not.

Consequences already visible in the corpus:

- r224 gives `‖χ‖ = 3 ↔ α ∈ 2·ℤ`. This is an orbit-class characterisation
  containing α_YM = 2 but ALSO α = 0, 4, −2, …
- r221 gives `‖χ‖ = 1 ↔ α ∈ ½ℤ + ½ ∪ 2·ℤ + 1`. This is an orbit-class
  characterisation containing α_RH = 3/2 and α_Poincaré = 1 but ALSO
  α = 5/2, 3, 5, …

Neither identifies the specific corpus α uniquely from substrate data
alone.

## Scope

* IS an elementary structural fact about `omega`, framework-generic.
* IS the exact obstruction theorem underlying the orbit-class
  reinterpretation of r221 and r224.
* IS the ω-companion to r240's σ-side statement.
* NOT a Millennium discharge.
* NOT a claim that α_RH or α_YM cannot be selected — only that they
  cannot be selected by any invariant factoring through `omega`.

## Contents

§1 `omega_add_two` — `omega (α + 2) = omega α`.
§2 `omega_add_two_int` — `omega (α + 2·k) = omega α` for `k : ℤ`.
§3 `omega_zero_eq_omega_two` — explicit witness at `α = 0`, `α = 2`.
§4 `invariant_factors_through_omega_add_two` — reusable factorisation.
§5 `not_injective_of_factors_through_omega_zero_two` — explicit
   non-injectivity witness for any function factoring through `omega`.
§6 Axiom check.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.LogPeriodicity_r220

open scoped Real

namespace PrincipiaTractalis.OmegaSymmetries

open PrincipiaTractalis.LogPeriodicity

/-! ## §1 Period-2 of the character map -/

/-- **`omega_add_two`** — the r220 character map has period 2 in α.

`omega (α + 2) = exp(iπ(α+2)) = exp(iπα) · exp(2πi) = exp(iπα) · 1 = omega α`
via mathlib's `Complex.exp_two_pi_mul_I`. -/
theorem omega_add_two (α : ℝ) : omega (α + 2) = omega α := by
  unfold omega
  have hcast : ((π * (α + 2) : ℝ) : ℂ) = ((π * α : ℝ) : ℂ) + ((2 * π : ℝ) : ℂ) := by
    push_cast; ring
  rw [hcast, add_mul, Complex.exp_add]
  have h2pi : ((2 * π : ℝ) : ℂ) * Complex.I = 2 * π * Complex.I := by push_cast; ring
  rw [h2pi, Complex.exp_two_pi_mul_I, mul_one]

/-! ## §2 Integer period-2 shift -/

/-- **`omega_add_two_int`** — the integer-shift form: `omega (α + 2·k) = omega α`
for every `k : ℤ`.

Direct via mathlib's `Complex.exp_int_mul_two_pi_mul_I`. -/
theorem omega_add_two_int (α : ℝ) (k : ℤ) :
    omega (α + 2 * k) = omega α := by
  unfold omega
  have hcast :
      ((π * (α + 2 * (k : ℝ)) : ℝ) : ℂ) = ((π * α : ℝ) : ℂ) + (k : ℂ) * ((2 * π : ℝ) : ℂ) := by
    push_cast; ring
  rw [hcast, add_mul, Complex.exp_add]
  have hexp :
      ((k : ℂ) * ((2 * π : ℝ) : ℂ)) * Complex.I = (k : ℂ) * (2 * π * Complex.I) := by
    push_cast; ring
  rw [hexp, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-! ## §3 Explicit non-vacuity witness -/

/-- **`omega_zero_eq_omega_two`** — the character map takes the same value at
`α = 0` and `α = 2`, giving an explicit non-vacuous witness of the period-2
identity.  Both values equal `1` (the trivial character), but the theorem is
stated as an equality of `omega` values, since that is the shape downstream
users need. -/
theorem omega_zero_eq_omega_two : omega 0 = omega 2 := by
  have h : omega ((0 : ℝ) + 2) = omega 0 := omega_add_two 0
  have h0 : (0 : ℝ) + 2 = 2 := by norm_num
  rw [h0] at h
  exact h.symm

/-! ## §4 Reusable factorisation -/

/-- **`invariant_factors_through_omega_add_two`** — any invariant `F : ℂ → β`
composed with `omega : ℝ → ℂ` inherits `omega`'s period-2 identity:
`F (omega (α + 2)) = F (omega α)`.

This is the exact obstruction theorem underlying the orbit-class
reinterpretation of r221 and r224. -/
theorem invariant_factors_through_omega_add_two
    {β : Sort*} (F : ℂ → β) (α : ℝ) :
    F (omega (α + 2)) = F (omega α) := by
  rw [omega_add_two]

/-- **Integer form of the factorisation.** -/
theorem invariant_factors_through_omega_add_two_int
    {β : Sort*} (F : ℂ → β) (α : ℝ) (k : ℤ) :
    F (omega (α + 2 * k)) = F (omega α) := by
  rw [omega_add_two_int]

/-! ## §5 Non-injectivity of any ω-factoring real-valued invariant -/

/-- **`not_injective_of_factors_through_omega_zero_two`** — if `F : ℝ → β`
factors through `omega` (i.e. there exists `G : ℂ → β` with `F α = G (omega α)`
for every `α`), then `F 0 = F 2`.

This is the concrete non-injectivity witness: no such `F` can distinguish
`α = 0` from `α = 2`. -/
theorem not_injective_of_factors_through_omega_zero_two
    {β : Sort*} {F : ℝ → β} {G : ℂ → β}
    (h : ∀ α, F α = G (omega α)) : F 0 = F 2 := by
  rw [h 0, h 2, omega_zero_eq_omega_two]

/-- **General integer form.**  If `F : ℝ → β` factors through `omega`, then
`F (α + 2·k) = F α` for every `α : ℝ` and every `k : ℤ`. -/
theorem factors_through_omega_period_two_int
    {β : Sort*} {F : ℝ → β} {G : ℂ → β}
    (h : ∀ α, F α = G (omega α)) (α : ℝ) (k : ℤ) :
    F (α + 2 * k) = F α := by
  rw [h (α + 2 * k), h α, omega_add_two_int]

/-! ## §6 The three-conjunct capstone -/

/-- **`omega_symmetries_capstone`** — the framework-generic ω-side companion
to r240's `sigma_symmetries_capstone`.

Three conjuncts:
- `omega (α + 2) = omega α`.
- `omega (α + 2·k) = omega α` for every `k : ℤ`.
- `omega 0 = omega 2` (explicit non-vacuous witness).

Any substrate invariant defined via `omega` inherits these symmetries
(§4 factorisation lemmas). -/
theorem omega_symmetries_capstone :
    (∀ α : ℝ, omega (α + 2) = omega α) ∧
    (∀ (α : ℝ) (k : ℤ), omega (α + 2 * k) = omega α) ∧
    omega 0 = omega 2 :=
  ⟨omega_add_two, omega_add_two_int, omega_zero_eq_omega_two⟩

end PrincipiaTractalis.OmegaSymmetries

/-! ## §7 Axiom check -/

#print axioms PrincipiaTractalis.OmegaSymmetries.omega_add_two
#print axioms PrincipiaTractalis.OmegaSymmetries.omega_add_two_int
#print axioms PrincipiaTractalis.OmegaSymmetries.omega_zero_eq_omega_two
#print axioms PrincipiaTractalis.OmegaSymmetries.invariant_factors_through_omega_add_two
#print axioms PrincipiaTractalis.OmegaSymmetries.invariant_factors_through_omega_add_two_int
#print axioms PrincipiaTractalis.OmegaSymmetries.not_injective_of_factors_through_omega_zero_two
#print axioms PrincipiaTractalis.OmegaSymmetries.factors_through_omega_period_two_int
#print axioms PrincipiaTractalis.OmegaSymmetries.omega_symmetries_capstone
