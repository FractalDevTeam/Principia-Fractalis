/-
# r349 — The three remaining Ch 11 predictions, formalised

★ 2026-10-25 — demonstrating a claim I made in a commit, and finding two
overstatements in the process ★

## Why this file exists

`PF/Consciousness/WeinsteinGUResonantRescue.lean` carried four experimental
predictions as `Prop := True`, with a section note saying they are "empirical /
observational, **not Lean-formalisable**". The muon g−2 clause was repaired
first (its real content was already in `MuonG2Prediction.lean`), and in doing
so I corrected that note to say the four are *unformalised stubs* rather than
unformalisable — asserting, on my own authority, that the other three could be
done.

This file does them, so the claim rests on theorems instead of my word. Each
is an explicit numerical formula from Ch 11 and each brackets exactly as
`XENONExactMatch.lean` already does for the XENONnT ratio — the Lithium one is
literally the XENON computation with a sign flip.

## What formalising them found

Two of the three claims are overstated at their own numbers. This is the same
kind of numerical-close check that caught the muon and Gaussian routes in
Ch 11, and it is the reason stubs are worth discharging rather than labelling.

**(1) Hubble — "within 1σ" is false; it is 1.026σ.** Ch 11 §Hubble Tension:

    H_eff = H₀ √(1 + (π/10)·ch₂·ρ_Φ/ρ_crit),  H₀ = 67.4, ch₂ = 0.95,
    ρ_Φ/ρ_crit = 0.7

Exactly: `(π/10)(0.95)(0.7) = 0.2089159…`, `√1.2089159… = 1.0995071…`, so
`H_eff = 74.1068…`. The local measurement is `73.04 ± 1.04`, so the 1σ band
tops out at `74.08`. **`H_eff` exceeds it.** The chapter reaches "within 1σ"
by rounding `√1.209` to `1.10` (giving `74.14`) and then not checking the
band. The discrepancy is small — `1.026σ` rather than `≤ 1σ` — and the honest
statement is "marginally outside 1σ", not "resolving the tension".

**(2) Lithium — the rate factor does not give the abundance deficit.**
Ch 11 §Primordial Lithium Abundance:

    Γ_RQG = Γ_SM (1 − (π/10)·ch₂·T/T_c),   T_c = 10⁹ K

At `T = T_c`, the factor is `1 − 0.29845… = 0.70155…`. But the same section
gives the datum: BBN predicts `Li/H = 5.24×10⁻¹⁰`, observation is
`1.6×10⁻¹⁰`, so the required abundance ratio is `1.6/5.24 = 0.3053…`.
**`0.3053 ≠ 0.7016`.** The chapter asserts the `0.70` rate factor "reduc[es]
lithium production by factor 3"; that step is a claim about the BBN reaction
network, not arithmetic, and nothing here or in the corpus establishes it. The
factor is real and computable; the bridge to the observed deficit is not
supplied.

**(3) ANITA — correct, and exactly the ternary structure.** Ch 11 §ANITA:
observed `E ≈ 0.6 × 10¹⁸ eV`, predicted `E ≈ 1.8 × 10¹⁸ eV`. The content is
the ratio, and `1.8 = 3 × 0.6` exactly — one step of the resonance ladder
`E_ν = 10¹⁸ · 3ⁿ`. This clause stands as stated.

## What is and is not claimed

**Claimed.** The three numerical formulas of Ch 11 §6.2–§6.4 evaluate to the
brackets below; `H_eff` exceeds the local 1σ upper bound; the Lithium rate
factor is strictly greater than the abundance ratio the observation requires;
and the ANITA energy ratio is exactly 3.

**Not claimed.** That any of these three is confirmed or refuted *as physics*.
These are arithmetic facts about the chapter's own formulas at the chapter's
own inputs. In particular: nothing here says the Hubble mechanism is wrong
(1.026σ is not a refutation), nothing here computes a BBN network, and nothing
here says fractal neutrinos exist. What the file does is make the numbers
checkable instead of asserted, and record where a stated conclusion does not
follow from the stated formula.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-25.
-/

import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace Ch11PredictionsFormalized

/-! ## §1 — Shared inputs (Ch 11's own values) -/

/-- Consciousness threshold used throughout Ch 11. -/
def ch2 : ℝ := 0.95

/-! ## §2 — Hubble tension (Ch 11 §6.2) -/

/-- `ρ_Φ/ρ_crit ≈ 0.7`, the dark-energy fraction Ch 11 uses at `z = 0`. -/
def rho_frac : ℝ := 0.7

/-- CMB-inferred `H₀ = 67.4 km/s/Mpc`. -/
def H0_CMB : ℝ := 67.4

/-- Local measurement `H₀ = 73.04 ± 1.04 km/s/Mpc`. -/
def H0_local : ℝ := 73.04

/-- The local 1σ uncertainty. -/
def H0_local_sigma : ℝ := 1.04

/-- The radicand `1 + (π/10)·ch₂·ρ_Φ/ρ_crit`. -/
noncomputable def hubbleRadicand : ℝ := 1 + (Real.pi / 10) * ch2 * rho_frac

/-- **The radicand brackets at `1.2089…`.** -/
theorem hubbleRadicand_bracket :
    (1.20891 : ℝ) < hubbleRadicand ∧ hubbleRadicand < (1.20892 : ℝ) := by
  unfold hubbleRadicand ch2 rho_frac
  constructor
  · have := Real.pi_gt_d6; nlinarith
  · have := Real.pi_lt_d6; nlinarith

/-- `H_eff = H₀ √(radicand)`, Ch 11 §6.2. -/
noncomputable def H_eff : ℝ := H0_CMB * Real.sqrt hubbleRadicand

/-- **The square root brackets at `1.09950…`.** -/
theorem sqrt_hubbleRadicand_bracket :
    (1.09950 : ℝ) < Real.sqrt hubbleRadicand ∧
    Real.sqrt hubbleRadicand < (1.09951 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := hubbleRadicand_bracket
  have hpos : (0 : ℝ) < hubbleRadicand := by linarith
  constructor
  · have h : ((1.09950 : ℝ)) ^ 2 < hubbleRadicand := by nlinarith
    have := Real.sqrt_lt_sqrt (by positivity) h
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1.09950)] at this
  · have h : hubbleRadicand < ((1.09951 : ℝ)) ^ 2 := by nlinarith
    have := Real.sqrt_lt_sqrt hpos.le h
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1.09951)] at this

/-- **`H_eff ≈ 74.107 km/s/Mpc`.** -/
theorem H_eff_bracket : (74.106 : ℝ) < H_eff ∧ H_eff < (74.108 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := sqrt_hubbleRadicand_bracket
  unfold H_eff H0_CMB
  constructor <;> nlinarith

/-- **★★ `H_eff` is OUTSIDE the local 1σ band.**

Ch 11 §6.2 concludes "This is within 1σ of the local measurement, resolving
the tension." The band's upper edge is `73.04 + 1.04 = 74.08`, and
`H_eff > 74.106`. So the stated conclusion does not hold at the chapter's own
numbers; the agreement is `1.026σ`, obtained by rounding `√1.209` to `1.10`. -/
theorem H_eff_exceeds_local_one_sigma :
    H0_local + H0_local_sigma < H_eff := by
  have h := H_eff_bracket.1
  unfold H0_local H0_local_sigma
  linarith

/-! ## §3 — Primordial lithium (Ch 11 §6.4) -/

/-- The RQG rate factor `1 − (π/10)·ch₂·(T/T_c)` at `T = T_c`. -/
noncomputable def lithiumRateFactor : ℝ := 1 - (Real.pi / 10) * ch2

/-- **The rate factor brackets at `0.7015…`.** -/
theorem lithiumRateFactor_bracket :
    (0.70154 : ℝ) < lithiumRateFactor ∧ lithiumRateFactor < (0.70156 : ℝ) := by
  unfold lithiumRateFactor ch2
  constructor
  · have := Real.pi_lt_d6; nlinarith
  · have := Real.pi_gt_d6; nlinarith

/-- BBN-predicted `Li/H`, in units of `10⁻¹⁰` (Ch 11 §6.4). -/
def Li_H_BBN : ℝ := 5.24

/-- Observed `Li/H`, same units. -/
def Li_H_observed : ℝ := 1.6

/-- The abundance ratio the observation requires: `1.6/5.24 ≈ 0.3053`. -/
noncomputable def requiredAbundanceRatio : ℝ := Li_H_observed / Li_H_BBN

theorem requiredAbundanceRatio_bracket :
    (0.305 : ℝ) < requiredAbundanceRatio ∧
    requiredAbundanceRatio < (0.306 : ℝ) := by
  unfold requiredAbundanceRatio Li_H_observed Li_H_BBN
  constructor <;> norm_num

/-- **★★ The rate factor does NOT equal the required abundance ratio.**

Ch 11 §6.4 states the `0.70` rate factor reduces lithium production "by factor
3 to match observations". The factor is `0.7016`; the ratio the data requires
is `1.6/5.24 = 0.3053`. They differ by more than a factor of two, so the
chapter's conclusion is a claim about the BBN reaction network's response to a
rate change, not an arithmetic consequence of the formula. Nothing in the
corpus supplies that network. -/
theorem lithium_factor_ne_required_ratio :
    requiredAbundanceRatio < lithiumRateFactor := by
  have h1 := requiredAbundanceRatio_bracket.2
  have h2 := lithiumRateFactor_bracket.1
  linarith

/-! ## §4 — ANITA (Ch 11 §6.3) -/

/-- Observed ANITA energy, in units of `10¹⁸ eV`. -/
def E_ANITA_observed : ℝ := 0.6

/-- Predicted second ANITA energy, same units. -/
def E_ANITA_predicted : ℝ := 1.8

/-- **★ The ANITA energy ratio is exactly 3** — one step of the ternary
resonance ladder `E_ν = 10¹⁸ · 3ⁿ`. This clause of Ch 11 stands as stated. -/
theorem ANITA_ratio_eq_three :
    E_ANITA_predicted = 3 * E_ANITA_observed := by
  unfold E_ANITA_predicted E_ANITA_observed
  norm_num

/-! ## §5 — Capstone -/

/-- **The three remaining Ch 11 predictions, formalised.**

Clause 1: `H_eff ≈ 74.107` and exceeds the local 1σ upper bound `74.08` —
Ch 11's "within 1σ" does not hold at its own numbers.
Clause 2: the Lithium rate factor `0.7016` exceeds the required abundance
ratio `0.3053` — the "factor 3" bridge is not arithmetic.
Clause 3: the ANITA ratio is exactly 3 — correct as stated.

None of this adjudicates the physics; see the header's "Not claimed". -/
theorem ch11_three_predictions_formalized :
    H0_local + H0_local_sigma < H_eff ∧
    requiredAbundanceRatio < lithiumRateFactor ∧
    E_ANITA_predicted = 3 * E_ANITA_observed :=
  ⟨H_eff_exceeds_local_one_sigma, lithium_factor_ne_required_ratio,
   ANITA_ratio_eq_three⟩

end Ch11PredictionsFormalized
end PrincipiaTractalis

/-! ## §Axiom check -/

#print axioms PrincipiaTractalis.Ch11PredictionsFormalized.hubbleRadicand_bracket
#print axioms PrincipiaTractalis.Ch11PredictionsFormalized.H_eff_bracket
#print axioms PrincipiaTractalis.Ch11PredictionsFormalized.H_eff_exceeds_local_one_sigma
#print axioms PrincipiaTractalis.Ch11PredictionsFormalized.lithiumRateFactor_bracket
#print axioms PrincipiaTractalis.Ch11PredictionsFormalized.lithium_factor_ne_required_ratio
#print axioms PrincipiaTractalis.Ch11PredictionsFormalized.ANITA_ratio_eq_three
#print axioms PrincipiaTractalis.Ch11PredictionsFormalized.ch11_three_predictions_formalized
