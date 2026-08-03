/-
# PF.ModifiedFriedmann_r187

★★★ 2026-08-03 — THE MODIFIED EINSTEIN SECTOR GETS REAL LEAN CONTENT ★★★

## What this replaces, honestly

`PF/GeneralRelativity.lean` contains
`ModifiedEinsteinWithConsciousnessHypothesis := ∃ Λ G, Λ = Λ ∧ G = G ∧ True` —
a vacuous marker (True-Prop audit, 2026-08-01; my authorship).  The book's
modified-gravity claims (ch08, ch13, ch27) had NO kernel content.  Full
tensorial Einstein equations cannot be formalized at this pin — mathlib has no
pseudo-Riemannian curvature — but the **FLRW-reduced** sector is honest ODE
mathematics on ℝ, and mathlib has everything it needs.  This stone provides:

1. **The modified continuity equation** ch08 postulates —
   `ρ' + 3(a'/a)(ρ + p) = J`, with `J` the consciousness source — and the
   kernel-checked **energy-balance identity**: it is *equivalent* to
   `d/dt(ρ·a³) = (J − 3(a'/a)·p)·a³`.  This is the exact statement of "energy
   is not conserved; the source J books the deficit" — a theorem about the
   postulated system, not a physics claim.
2. **The Λ-suppression dynamics** ch08/ch26/ch27 use —
   `Λ_eff(t) = Λ₀·exp(−∫₀ᵗ g)` — proved to satisfy the ODE
   `Λ_eff' = −g·Λ_eff` (FTC + chain rule), together with positivity and
   monotone decay for `g ≥ 0`.  The book's `Λ_eff/Λ₀ = 10⁻¹²⁰` numerology is
   NOT touched: what is kernel-checked is the differential law, which is the
   part that is mathematics.

Scope: these are theorems about the framework's postulated equations.  They
assert nothing about physical spacetime; the chapter ledgers' EMPIRICAL
HYPOTHESIS classification of the physics is unchanged.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-08-03.
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option maxHeartbeats 400000

namespace PrincipiaTractalis.ModifiedFriedmann

open MeasureTheory intervalIntegral

noncomputable section

/-! ### Part 1 — the modified continuity equation and energy balance -/

variable (a ρ p J : ℝ → ℝ)

/-- ch08's modified conservation law, FLRW-reduced:
`ρ' + 3(a'/a)(ρ+p) = J`, with `J` the consciousness source term. -/
def ModifiedContinuity : Prop :=
  ∀ t, deriv ρ t + 3 * (deriv a t / a t) * (ρ t + p t) = J t

variable {a ρ p J}

/-- **Energy balance**: under the modified continuity equation, the comoving
energy `ρ·a³` changes exactly at the rate the source and the pressure work
dictate.  "Energy is not conserved — J books the deficit," as an identity. -/
theorem energy_balance (ha : Differentiable ℝ a) (hρ : Differentiable ℝ ρ)
    (hne : ∀ t, a t ≠ 0) (h : ModifiedContinuity a ρ p J) (t : ℝ) :
    deriv (fun s => ρ s * (a s) ^ 3) t
      = (J t - 3 * (deriv a t / a t) * p t) * (a t) ^ 3 := by
  have hda : HasDerivAt a (deriv a t) t := (ha t).hasDerivAt
  have hdρ : HasDerivAt ρ (deriv ρ t) t := (hρ t).hasDerivAt
  have hcube : HasDerivAt (fun s => (a s) ^ 3)
      (3 * (a t) ^ 2 * deriv a t) t := by
    simpa [mul_comm, mul_assoc, mul_left_comm] using hda.pow 3
  have hprod : HasDerivAt (fun s => ρ s * (a s) ^ 3)
      (deriv ρ t * (a t) ^ 3 + ρ t * (3 * (a t) ^ 2 * deriv a t)) t :=
    hdρ.mul hcube
  rw [hprod.deriv]
  have hJ := h t
  have hρ' : deriv ρ t = J t - 3 * (deriv a t / a t) * (ρ t + p t) := by
    linarith
  rw [hρ']
  field_simp [hne t]
  ring

/-- The converse: the energy-balance identity recovers the modified
continuity equation, so the two are equivalent formulations. -/
theorem modifiedContinuity_of_energy_balance
    (ha : Differentiable ℝ a) (hρ : Differentiable ℝ ρ)
    (hne : ∀ t, a t ≠ 0)
    (h : ∀ t, deriv (fun s => ρ s * (a s) ^ 3) t
      = (J t - 3 * (deriv a t / a t) * p t) * (a t) ^ 3) :
    ModifiedContinuity a ρ p J := by
  intro t
  have hda : HasDerivAt a (deriv a t) t := (ha t).hasDerivAt
  have hdρ : HasDerivAt ρ (deriv ρ t) t := (hρ t).hasDerivAt
  have hcube : HasDerivAt (fun s => (a s) ^ 3)
      (3 * (a t) ^ 2 * deriv a t) t := by
    simpa [mul_comm, mul_assoc, mul_left_comm] using hda.pow 3
  have hprod : HasDerivAt (fun s => ρ s * (a s) ^ 3)
      (deriv ρ t * (a t) ^ 3 + ρ t * (3 * (a t) ^ 2 * deriv a t)) t :=
    hdρ.mul hcube
  have hEq := h t
  rw [hprod.deriv] at hEq
  field_simp [hne t] at hEq
  field_simp [hne t]
  linear_combination hEq

/-! ### Part 2 — the Λ-suppression dynamics -/

/-- The framework's effective cosmological term:
`Λ_eff(t) = Λ₀ · exp(−∫₀ᵗ g)`, with `g` the (consciousness-weighted)
suppression rate `ch₂ · R_f`-type integrand of ch08/ch26. -/
def LambdaEff (Λ₀ : ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  Λ₀ * Real.exp (-∫ s in (0 : ℝ)..t, g s)

/-- **The suppression law**: `Λ_eff` satisfies the linear decay ODE
`Λ_eff' = −g · Λ_eff`.  FTC-2 plus the chain rule, kernel-checked. -/
theorem hasDerivAt_lambdaEff (Λ₀ : ℝ) {g : ℝ → ℝ} (hg : Continuous g)
    (t : ℝ) :
    HasDerivAt (LambdaEff Λ₀ g) (-(g t) * LambdaEff Λ₀ g t) t := by
  have hint : HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, g s) (g t) t :=
    integral_hasDerivAt_right (hg.intervalIntegrable 0 t)
      (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt
  have hneg : HasDerivAt (fun u => -∫ s in (0 : ℝ)..u, g s) (-(g t)) t :=
    hint.neg
  have hexp : HasDerivAt (fun u => Real.exp (-∫ s in (0 : ℝ)..u, g s))
      (Real.exp (-∫ s in (0 : ℝ)..t, g s) * (-(g t))) t := hneg.exp
  have := hexp.const_mul Λ₀
  simpa [LambdaEff, mul_comm, mul_assoc, mul_left_comm] using this

/-- `Λ_eff` never vanishes and keeps the sign of `Λ₀`; for `Λ₀ > 0` it is
positive at all times — suppression, never extinction. -/
theorem lambdaEff_pos {Λ₀ : ℝ} (hΛ : 0 < Λ₀) (g : ℝ → ℝ) (t : ℝ) :
    0 < LambdaEff Λ₀ g t :=
  mul_pos hΛ (Real.exp_pos _)

/-- For a nonnegative suppression rate the decay is monotone on `t ≥ 0`:
later times mean no larger `Λ_eff`. -/
theorem lambdaEff_antitone {Λ₀ : ℝ} (hΛ : 0 ≤ Λ₀) {g : ℝ → ℝ}
    (hg : Continuous g) (hg0 : ∀ s, 0 ≤ g s)
    {t₁ t₂ : ℝ} (h0 : 0 ≤ t₁) (h12 : t₁ ≤ t₂) :
    LambdaEff Λ₀ g t₂ ≤ LambdaEff Λ₀ g t₁ := by
  unfold LambdaEff
  apply mul_le_mul_of_nonneg_left _ hΛ
  apply Real.exp_le_exp.mpr
  simp only [neg_le_neg_iff]
  have hsplit : (∫ s in (0 : ℝ)..t₂, g s)
      = (∫ s in (0 : ℝ)..t₁, g s) + ∫ s in t₁..t₂, g s :=
    (integral_add_adjacent_intervals
      (hg.intervalIntegrable 0 t₁) (hg.intervalIntegrable t₁ t₂)).symm
  rw [hsplit, le_add_iff_nonneg_right]
  exact intervalIntegral.integral_nonneg h12 (fun s _ => hg0 s)

end

end PrincipiaTractalis.ModifiedFriedmann

#print axioms PrincipiaTractalis.ModifiedFriedmann.energy_balance
#print axioms PrincipiaTractalis.ModifiedFriedmann.modifiedContinuity_of_energy_balance
#print axioms PrincipiaTractalis.ModifiedFriedmann.hasDerivAt_lambdaEff
#print axioms PrincipiaTractalis.ModifiedFriedmann.lambdaEff_antitone
