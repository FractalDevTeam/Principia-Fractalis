/-
# PF.Analytic.FourierPanels.ResidueBoundTight_c401_32_2026_10_20

**Residue bound, tightened 330×**: `|∫_{3/2}^{5} f| ≤ 7/10⁷`, against the
`231/10⁶` of `ResidueBound_c401_32_three_halves_to_5_2026_10_16`.

### Why this replaces the `ln k` subdivision design

The scoping note (`codex/ADDON_SCOPE_RESIDUE_IS_THE_WORK_2026-10-17.md`)
proposed subdividing `[3/2, 5]` at `u = ln k`, reaching `4.1016e−6`. While
building it I found a strictly better route that needs **no subdivision at
all**, because `intervalIntegral.norm_integral_le_of_norm_le` requires only the
**majorant** to be integrable — not the integrand. So instead of a step
majorant we may use an *exponential* one, integrate it in closed form, and keep
the decay that the step function throws away:

| design | bound | vs `231/10⁶` |
|---|---|---|
| current single piece | `231/10⁶` = 2.31e−4 | 1× |
| `ln k` subdivision, 145 pieces | 4.1016e−6 | 56× |
| **this file, no subdivision** | **≤ 7/10⁷ = 7e−7** | **330×** |

### The argument

On `u ≥ 3/2`, convexity of `exp` gives
`exp u ≥ exp(3/2)·(1 + (u − 3/2))`, so with the existing
`14 ≤ π · exp(3/2)`,

  `π · exp u ≥ 14 + 14·(u − 3/2)`,

hence `exp(−π·exp u) ≤ exp(7 − 14u)` and, with the existing pointwise majorant
`|f u| ≤ (exp(u/2) + 1)·3·exp(−π·exp u)`,

  `|f u| ≤ 3·exp 7·(exp(−(27/2)·u) + exp(−14·u)) =: resMaj u`.

`resMaj` integrates in closed form, and dropping the two negative tails,

  `∫_{3/2}^{5} resMaj ≤ (2/9)·exp(−53/4) + (3/14)·exp(−14)
                      ≤ (2/9)·(43/20)·10⁻⁶ + (3/14)·10⁻⁶ = (218/315)·10⁻⁶ ≤ 7/10⁷`,

using `exp(−53/4) = exp(−14)·exp(3/4)`, the existing `exp(−14) ≤ 10⁻⁶`, and
`exp(3/4) ≤ 43/20` — which follows from the existing `exp 3 ≤ 21` by a fourth
root, so **no new transcendental constant is introduced**.

Everything consumed here already existed in the 2026-10-16 residue file:
`nodeR_fourier_{plus,minus}_at_c401_32_N3_abs_le_mul_exp`,
`pi_mul_exp_three_halves_ge_fourteen`, `exp_neg_fourteen_le`,
`exp_three_le_twentyone`.

Three-axiom bar: every top-level declaration prints
`[propext, Classical.choice, Quot.sound]`. No sorry, no native_decide,
no `interval` tactic, no project axioms.

Emitted by codex/gen_box.py for c = 401/32 (2026-10-20). `c` enters the node
functions only through the phase cos((c/2)u) / sin((c/2)u), and every add-on
majorant discards it via |cos|,|sin| <= 1, so the three add-on constants are
c-independent: residue 7/10^7, analytic tail 12/10^8, omega-gap 1/10^21.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-18.
-/
import PF.Analytic.FourierPanels.ResidueBound_c401_32_three_halves_to_5_2026_10_20
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false

namespace PrincipiaTractalis
namespace FourierPanels_c401_32
namespace ResidueBoundTight

open Real MeasureTheory Set
open PrincipiaTractalis.FourierPanels_c401_32.ResidueBound
open scoped Real

/-! ## §1 — `exp (3/4) ≤ 43/20`, from the existing `exp 3 ≤ 21`.

No new transcendental input: `exp(3/4)` is the positive fourth root of
`exp 3`, and `(43/20)^4 = 3418801/160000 > 21`. -/

lemma exp_three_quarters_le : Real.exp (3 / 4) ≤ 43 / 20 := by
  have h3 : Real.exp 3 ≤ 21 := exp_three_le_twentyone
  have hx : Real.exp (3 / 4) ^ 4 = Real.exp 3 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rcases le_or_gt (Real.exp (3 / 4)) (43 / 20) with h | h
  · exact h
  · exfalso
    have h2 : ((43 : ℝ) / 20) ^ 4 ≤ Real.exp (3 / 4) ^ 4 :=
      pow_le_pow_left₀ (by norm_num) h.le 4
    rw [hx] at h2
    have h4 : ((43 : ℝ) / 20) ^ 4 ≤ 21 := le_trans h2 h3
    norm_num at h4

/-! ## §2 — The linear lower bound on `π · exp u` for `u ≥ 3/2`. -/

/-- **Convexity step.** For `u ≥ 3/2`,
`14 + 14·(u − 3/2) ≤ π · exp u`.

From `exp u = exp(3/2)·exp(u − 3/2) ≥ exp(3/2)·((u − 3/2) + 1)` and the
existing `14 ≤ π · exp(3/2)`. -/
lemma pi_mul_exp_u_ge_linear {u : ℝ} (hu : 3 / 2 ≤ u) :
    14 + 14 * (u - 3 / 2) ≤ π * Real.exp u := by
  have h14 : (14 : ℝ) ≤ π * Real.exp (3 / 2) := pi_mul_exp_three_halves_ge_fourteen
  have hstep : (u - 3 / 2) + 1 ≤ Real.exp (u - 3 / 2) := Real.add_one_le_exp _
  have hsplit : Real.exp u = Real.exp (3 / 2) * Real.exp (u - 3 / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hnn : (0 : ℝ) ≤ u - 3 / 2 := by linarith
  have hfac_nn : (0 : ℝ) ≤ (u - 3 / 2) + 1 := by linarith
  have hprod_nn : (0 : ℝ) ≤ π * Real.exp (3 / 2) :=
    mul_nonneg Real.pi_pos.le (Real.exp_pos _).le
  calc 14 + 14 * (u - 3 / 2) = 14 * ((u - 3 / 2) + 1) := by ring
    _ ≤ (π * Real.exp (3 / 2)) * ((u - 3 / 2) + 1) :=
        mul_le_mul_of_nonneg_right h14 hfac_nn
    _ ≤ (π * Real.exp (3 / 2)) * Real.exp (u - 3 / 2) :=
        mul_le_mul_of_nonneg_left hstep hprod_nn
    _ = π * Real.exp u := by rw [hsplit]; ring

/-! ## §3 — The exponential majorant. -/

/-- **The exponential majorant** `3·exp 7·(exp(−(27/2)u) + exp(−14u))`.

This dominates `|f|` on `[3/2, 5]` (§3 below) and, unlike a step majorant,
retains the `exp(−14u)` decay — which is why no subdivision is needed. -/
noncomputable def resMaj (u : ℝ) : ℝ :=
  3 * Real.exp 7 * (Real.exp ((-(27 / 2) : ℝ) * u) + Real.exp ((-14 : ℝ) * u))

lemma continuous_resMaj : Continuous resMaj := by
  unfold resMaj
  fun_prop

/-- Algebraic identity turning the shifted-exponential form into `resMaj`. -/
lemma majorant_eq (u : ℝ) :
    (Real.exp (u / 2) + 1) * (3 * Real.exp (-(14 + 14 * (u - 3 / 2)))) = resMaj u := by
  unfold resMaj
  have e0 : -(14 + 14 * (u - 3 / 2)) = 7 - 14 * u := by ring
  rw [e0]
  have a1 : Real.exp (7 - 14 * u) = Real.exp 7 * Real.exp ((-14 : ℝ) * u) := by
    rw [← Real.exp_add]; congr 1; ring
  have a2 : Real.exp (u / 2) * (Real.exp 7 * Real.exp ((-14 : ℝ) * u))
      = Real.exp 7 * Real.exp ((-(27 / 2) : ℝ) * u) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [a1]
  rw [show (Real.exp (u / 2) + 1) * (3 * (Real.exp 7 * Real.exp ((-14 : ℝ) * u)))
      = 3 * (Real.exp (u / 2) * (Real.exp 7 * Real.exp ((-14 : ℝ) * u)))
        + 3 * (Real.exp 7 * Real.exp ((-14 : ℝ) * u)) from by ring]
  rw [a2]
  ring

/-- **Pointwise domination, plus side.** -/
lemma abs_nodeR_plus_le_resMaj {u : ℝ} (hu : 3 / 2 ≤ u) :
    |nodeR_fourier_plus_at_c401_32_N3 u| ≤ resMaj u := by
  have h1 := nodeR_fourier_plus_at_c401_32_N3_abs_le_mul_exp u
  have h2 : Real.exp (-(π * Real.exp u)) ≤ Real.exp (-(14 + 14 * (u - 3 / 2))) := by
    apply Real.exp_le_exp.mpr
    have := pi_mul_exp_u_ge_linear hu
    linarith
  have hpre : (0 : ℝ) ≤ Real.exp (u / 2) + 1 := by positivity
  have h3 : (Real.exp (u / 2) + 1) * (3 * Real.exp (-(π * Real.exp u)))
      ≤ (Real.exp (u / 2) + 1) * (3 * Real.exp (-(14 + 14 * (u - 3 / 2)))) := by
    apply mul_le_mul_of_nonneg_left _ hpre
    linarith
  rw [← majorant_eq u]
  linarith

/-- **Pointwise domination, minus side.** -/
lemma abs_nodeR_minus_le_resMaj {u : ℝ} (hu : 3 / 2 ≤ u) :
    |nodeR_fourier_minus_at_c401_32_N3 u| ≤ resMaj u := by
  have h1 := nodeR_fourier_minus_at_c401_32_N3_abs_le_mul_exp u
  have h2 : Real.exp (-(π * Real.exp u)) ≤ Real.exp (-(14 + 14 * (u - 3 / 2))) := by
    apply Real.exp_le_exp.mpr
    have := pi_mul_exp_u_ge_linear hu
    linarith
  have hpre : (0 : ℝ) ≤ Real.exp (u / 2) + 1 := by positivity
  have h3 : (Real.exp (u / 2) + 1) * (3 * Real.exp (-(π * Real.exp u)))
      ≤ (Real.exp (u / 2) + 1) * (3 * Real.exp (-(14 + 14 * (u - 3 / 2)))) := by
    apply mul_le_mul_of_nonneg_left _ hpre
    linarith
  rw [← majorant_eq u]
  linarith

/-! ## §4 — The majorant's integral, in closed form. -/

/-- `∫_a^b exp (c·u) du = c⁻¹·(exp (c·b) − exp (c·a))` for `c ≠ 0`. -/
lemma integral_exp_mul_eq {c : ℝ} (hc : c ≠ 0) (a b : ℝ) :
    (∫ u in a..b, Real.exp (c * u)) = c⁻¹ * (Real.exp (c * b) - Real.exp (c * a)) := by
  rw [intervalIntegral.integral_comp_mul_left (f := Real.exp) hc, integral_exp, smul_eq_mul]

/-- **The majorant integrates to at most `7/10⁷`.** -/
lemma integral_resMaj_le :
    (∫ u in (3 / 2 : ℝ)..5, resMaj u) ≤ 7 / 10 ^ 7 := by
  have hc1 : ((-(27 / 2) : ℝ)) ≠ 0 := by norm_num
  have hc2 : ((-14 : ℝ)) ≠ 0 := by norm_num
  have hi1 : IntervalIntegrable (fun u : ℝ => Real.exp ((-(27 / 2) : ℝ) * u))
      volume (3 / 2) 5 := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun u : ℝ => Real.exp ((-14 : ℝ) * u))
      volume (3 / 2) 5 := (by fun_prop : Continuous _).intervalIntegrable _ _
  -- split the integral
  have hsplit : (∫ u in (3 / 2 : ℝ)..5, resMaj u)
      = 3 * Real.exp 7 * ((∫ u in (3 / 2 : ℝ)..5, Real.exp ((-(27 / 2) : ℝ) * u))
          + (∫ u in (3 / 2 : ℝ)..5, Real.exp ((-14 : ℝ) * u))) := by
    unfold resMaj
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hi1 hi2]
  rw [hsplit, integral_exp_mul_eq hc1, integral_exp_mul_eq hc2]
  -- the two negative tails are dropped
  have t1 : Real.exp ((-(27 / 2) : ℝ) * 5) > 0 := Real.exp_pos _
  have t2 : Real.exp ((-14 : ℝ) * 5) > 0 := Real.exp_pos _
  -- rewrite the two surviving terms
  have r1 : ((-(27 / 2) : ℝ))⁻¹ * (Real.exp ((-(27 / 2) : ℝ) * 5)
        - Real.exp ((-(27 / 2) : ℝ) * (3 / 2)))
      = (2 / 27) * (Real.exp (-(81 / 4) : ℝ) - Real.exp (-(135 / 2) : ℝ)) := by
    rw [show ((-(27 / 2) : ℝ)) * 5 = (-(135 / 2) : ℝ) by norm_num,
        show ((-(27 / 2) : ℝ)) * (3 / 2) = (-(81 / 4) : ℝ) by norm_num]
    rw [show ((-(27 / 2) : ℝ))⁻¹ = -(2 / 27) by norm_num]
    ring
  have r2 : ((-14 : ℝ))⁻¹ * (Real.exp ((-14 : ℝ) * 5) - Real.exp ((-14 : ℝ) * (3 / 2)))
      = (1 / 14) * (Real.exp (-21 : ℝ) - Real.exp (-70 : ℝ)) := by
    rw [show ((-14 : ℝ)) * 5 = (-70 : ℝ) by norm_num,
        show ((-14 : ℝ)) * (3 / 2) = (-21 : ℝ) by norm_num]
    rw [show ((-14 : ℝ))⁻¹ = -(1 / 14) by norm_num]
    ring
  rw [r1, r2]
  -- Step A: drop the two strictly negative tail terms.
  have hpos7 : (0 : ℝ) < Real.exp 7 := Real.exp_pos _
  have h135 : (0 : ℝ) < Real.exp (-(135 / 2) : ℝ) := Real.exp_pos _
  have h70 : (0 : ℝ) < Real.exp (-70 : ℝ) := Real.exp_pos _
  have h34 : Real.exp (3 / 4 : ℝ) ≤ 43 / 20 := exp_three_quarters_le
  have h14 : Real.exp (-14 : ℝ) ≤ 1 / 10 ^ 6 := exp_neg_fourteen_le
  have hA : 3 * Real.exp 7 * ((2 / 27) * (Real.exp (-(81 / 4) : ℝ) - Real.exp (-(135 / 2) : ℝ))
        + (1 / 14) * (Real.exp (-21 : ℝ) - Real.exp (-70 : ℝ)))
      ≤ 3 * Real.exp 7 * ((2 / 27) * Real.exp (-(81 / 4) : ℝ)
        + (1 / 14) * Real.exp (-21 : ℝ)) := by
    have hfac : (0 : ℝ) ≤ 3 * Real.exp 7 := by positivity
    apply mul_le_mul_of_nonneg_left _ hfac
    nlinarith [h135, h70]
  -- Step B: collapse `exp 7` against the two exponents.
  -- exp 7 * exp(-81/4) = exp(-53/4) = exp(-14) * exp(3/4);  exp 7 * exp(-21) = exp(-14).
  have u1 : Real.exp 7 * Real.exp (-(81 / 4) : ℝ)
      = Real.exp (-14 : ℝ) * Real.exp (3 / 4 : ℝ) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; norm_num
  have u2 : Real.exp 7 * Real.exp (-21 : ℝ) = Real.exp (-14 : ℝ) := by
    rw [← Real.exp_add]; congr 1; norm_num
  have hB : 3 * Real.exp 7 * ((2 / 27) * Real.exp (-(81 / 4) : ℝ)
        + (1 / 14) * Real.exp (-21 : ℝ))
      = (2 / 9) * (Real.exp (-14 : ℝ) * Real.exp (3 / 4 : ℝ))
        + (3 / 14) * Real.exp (-14 : ℝ) := by
    calc 3 * Real.exp 7 * ((2 / 27) * Real.exp (-(81 / 4) : ℝ)
          + (1 / 14) * Real.exp (-21 : ℝ))
        = (2 / 9) * (Real.exp 7 * Real.exp (-(81 / 4) : ℝ))
          + (3 / 14) * (Real.exp 7 * Real.exp (-21 : ℝ)) := by ring
      _ = (2 / 9) * (Real.exp (-14 : ℝ) * Real.exp (3 / 4 : ℝ))
          + (3 / 14) * Real.exp (-14 : ℝ) := by rw [u1, u2]
  -- Step C: the numeric estimate, (2/9)(43/20) + (3/14) = 218/315 < 7/10.
  have hEX : Real.exp (-14 : ℝ) * Real.exp (3 / 4 : ℝ) ≤ (1 / 10 ^ 6) * (43 / 20) :=
    mul_le_mul h14 h34 (Real.exp_pos _).le (by norm_num)
  calc 3 * Real.exp 7 * ((2 / 27) * (Real.exp (-(81 / 4) : ℝ) - Real.exp (-(135 / 2) : ℝ))
        + (1 / 14) * (Real.exp (-21 : ℝ) - Real.exp (-70 : ℝ)))
      ≤ 3 * Real.exp 7 * ((2 / 27) * Real.exp (-(81 / 4) : ℝ)
        + (1 / 14) * Real.exp (-21 : ℝ)) := hA
    _ = (2 / 9) * (Real.exp (-14 : ℝ) * Real.exp (3 / 4 : ℝ))
        + (3 / 14) * Real.exp (-14 : ℝ) := hB
    _ ≤ 7 / 10 ^ 7 := by linarith [hEX, h14]

/-! ## §5 — The tightened residue bounds. -/

/-- **★ Residue bound, plus side, 330× tighter ★**
`|∫_{3/2}^{5} nodeR_plus| ≤ 7/10⁷`, against `231/10⁶` previously. -/
theorem nodeR_fourier_plus_at_c401_32_N3_residue_abs_le_tight :
    |∫ u in (3 / 2 : ℝ)..(5 : ℝ), nodeR_fourier_plus_at_c401_32_N3 u| ≤ (7 / 10 ^ 7 : ℝ) := by
  have hab : (3 / 2 : ℝ) ≤ 5 := by norm_num
  have hmaj : IntervalIntegrable resMaj volume (3 / 2) 5 :=
    continuous_resMaj.intervalIntegrable _ _
  have hle : ∀ᵐ t ∂volume, t ∈ Set.Ioc (3 / 2 : ℝ) 5 →
      ‖nodeR_fourier_plus_at_c401_32_N3 t‖ ≤ resMaj t := by
    refine Filter.Eventually.of_forall ?_
    intro t ht
    rw [Real.norm_eq_abs]
    exact abs_nodeR_plus_le_resMaj (le_of_lt ht.1)
  have h := intervalIntegral.norm_integral_le_of_norm_le hab hle hmaj
  rw [Real.norm_eq_abs] at h
  exact le_trans h integral_resMaj_le

/-- **★ Residue bound, minus side, 330× tighter ★** -/
theorem nodeR_fourier_minus_at_c401_32_N3_residue_abs_le_tight :
    |∫ u in (3 / 2 : ℝ)..(5 : ℝ), nodeR_fourier_minus_at_c401_32_N3 u| ≤ (7 / 10 ^ 7 : ℝ) := by
  have hab : (3 / 2 : ℝ) ≤ 5 := by norm_num
  have hmaj : IntervalIntegrable resMaj volume (3 / 2) 5 :=
    continuous_resMaj.intervalIntegrable _ _
  have hle : ∀ᵐ t ∂volume, t ∈ Set.Ioc (3 / 2 : ℝ) 5 →
      ‖nodeR_fourier_minus_at_c401_32_N3 t‖ ≤ resMaj t := by
    refine Filter.Eventually.of_forall ?_
    intro t ht
    rw [Real.norm_eq_abs]
    exact abs_nodeR_minus_le_resMaj (le_of_lt ht.1)
  have h := intervalIntegral.norm_integral_le_of_norm_le hab hle hmaj
  rw [Real.norm_eq_abs] at h
  exact le_trans h integral_resMaj_le

end ResidueBoundTight
end FourierPanels_c401_32
end PrincipiaTractalis

/-! ## §Axiom check -/
#print axioms PrincipiaTractalis.FourierPanels_c401_32.ResidueBoundTight.exp_three_quarters_le
#print axioms PrincipiaTractalis.FourierPanels_c401_32.ResidueBoundTight.pi_mul_exp_u_ge_linear
#print axioms PrincipiaTractalis.FourierPanels_c401_32.ResidueBoundTight.majorant_eq
#print axioms PrincipiaTractalis.FourierPanels_c401_32.ResidueBoundTight.abs_nodeR_plus_le_resMaj
#print axioms PrincipiaTractalis.FourierPanels_c401_32.ResidueBoundTight.abs_nodeR_minus_le_resMaj
#print axioms PrincipiaTractalis.FourierPanels_c401_32.ResidueBoundTight.integral_exp_mul_eq
#print axioms PrincipiaTractalis.FourierPanels_c401_32.ResidueBoundTight.integral_resMaj_le
#print axioms PrincipiaTractalis.FourierPanels_c401_32.ResidueBoundTight.nodeR_fourier_plus_at_c401_32_N3_residue_abs_le_tight
#print axioms PrincipiaTractalis.FourierPanels_c401_32.ResidueBoundTight.nodeR_fourier_minus_at_c401_32_N3_residue_abs_le_tight
