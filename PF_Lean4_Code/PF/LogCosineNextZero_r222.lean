/-
# r222: `g_logcos_next_zero_forced_by_frequency` — the √3 shift.

★ 2026-08-12 r222 — the SECOND of the two r221 stones queued in
`docs/COSMOLOGY_LOGPERIODIC_G_2026-08-12.md §6`. First stone landed as
`PF/ChiNormUnity_r221.lean` at commit `5a153525`. ★

## What this file proves

The r220 log-cosine ansatz for the cosmology axis is

    g(a) = A · a^σ · cos( logFrequency · log a + φ₀ )      (a > 0)

with `logFrequency = 2π / ln 3` (r220's `logFrequency_mul_logPeriod` pins
`logFrequency · ln 3 = 2π` — parameter-free). `A ≠ 0` and `φ₀` are fit
from data; `σ` comes from r212 via r220's `sigma_eq_logb_norm_chi`.

The **frequency-forced next-zero identity**:

    a₀ > 0 ∧ g(a₀) = 0
      ⟹ g(√3 · a₀) = 0 ∧ g(a₀ / √3) = 0.

The multiplier `√3` depends on `logFrequency` alone — NOT on `A`, `σ`,
or `φ₀`. This is the "next zero is forced by the frequency" claim from
the 2026-08-12 record §2.

## Where the √3 comes from — no free choice

    logFrequency · log(√3) = logFrequency · (log 3 / 2)
                          = (logFrequency · log 3) / 2
                          = (logFrequency · logPeriod) / 2
                          = 2π / 2                    (r220's `logFrequency_mul_logPeriod`)
                          = π.

So `logFrequency · log(√3 · a₀) = logFrequency · log a₀ + π`, and
`cos(x + π) = -cos(x)`, which vanishes iff `cos(x)` does. The envelope
`a^σ` is strictly positive on `a > 0` for every real `σ` (`Real.rpow_pos_of_pos`),
so it cannot create or hide zeros.

## Empirical anchor (doc §2, not formalised here)

At the DESI+CMB fit, `a₀ = 1 / (1 + 0.44) = 0.6944` is the observed
`w = -1` crossing. The next OLDER zero at `a₀ / √3 = 0.4010` corresponds
to `z = 1/0.4010 - 1 = 1.494` — matching the fit's reported next crossing
at `z ≈ 1.494` to three decimals. Three-dataset mean: `z ≈ 1.44 ± 0.05`.
Empirical numbers are docstring-only; the theorem below is the exact
`√3` shift identity underlying them.

## Contents

§1 The frequency-forced log-shift identity:
   `logFrequency · log(√3 · x) = logFrequency · log x + π` (`x > 0`).
§2 The log-cosine `gLogCos` and its envelope-zero-factorisation lemma.
§3 **The main theorem** `g_logcos_next_zero_forced_by_frequency`.
§4 The log-spaced arithmetic progression of zeros — both directions.
   `g_logcos_zero_at_sqrt_three_pow_up` and `_at_div_sqrt_three_pow`
   iterate the main theorem to arbitrary `√3^n` shifts.
§5 The frequency dependence is ESSENTIAL: renaming `logFrequency` to
   any other frequency `ω` gives shift `exp(π/ω)`; the `√3` is exactly
   `logFrequency = 2π/ln 3` (`sqrt_three_from_logFrequency`).

## Scope

* NOT a Millennium discharge.
* NOT a substrate derivation of `g`, `A`, `σ`, or `φ₀`.
* NOT a resolution of the DESI–CMB tension.
* IS the exact derivation of the `√3` shift from `logFrequency = 2π / ln 3`,
  showing the shift is a **function of `logFrequency` alone**.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.LogPeriodicity_r220
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped Real

namespace PrincipiaTractalis.LogCosineNextZero

open PrincipiaTractalis.LogPeriodicity

/-! ## §1 The frequency-forced log-shift identity. -/

/-- **`log(√3) = log(3) / 2`**.  In r220's notation, `log(√3) = logPeriod / 2`. -/
lemma log_sqrt_three : Real.log (Real.sqrt 3) = logPeriod / 2 := by
  have hpos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hne : Real.sqrt 3 ≠ 0 := ne_of_gt hpos
  have hmul : Real.log 3 = 2 * Real.log (Real.sqrt 3) := by
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 :=
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    have := Real.log_mul hne hne
    rw [h3] at this
    linarith
  rw [logPeriod]
  linarith

/-- **The phase-shift identity — the frequency-forced core.**
`logFrequency · log(√3 · x) = logFrequency · log x + π` for `x > 0`. The
multiplicative shift `x ↦ √3 · x` is EXACTLY a `π` phase shift, and the
factor `√3` depends only on `logFrequency = 2π / ln 3`. -/
theorem logFrequency_log_sqrt_three_mul (x : ℝ) (hx : 0 < x) :
    logFrequency * Real.log (Real.sqrt 3 * x)
      = logFrequency * Real.log x + π := by
  have hsqrt : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hkey : logFrequency * (logPeriod / 2) = π := by
    have := logFrequency_mul_logPeriod
    linarith
  rw [Real.log_mul (ne_of_gt hsqrt) (ne_of_gt hx),
      log_sqrt_three, mul_add]
  linarith

/-- Symmetric form: `logFrequency · log(x / √3) = logFrequency · log x - π`. -/
theorem logFrequency_log_div_sqrt_three (x : ℝ) (hx : 0 < x) :
    logFrequency * Real.log (x / Real.sqrt 3)
      = logFrequency * Real.log x - π := by
  have hsqrt : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hkey : logFrequency * (logPeriod / 2) = π := by
    have := logFrequency_mul_logPeriod
    linarith
  rw [Real.log_div (ne_of_gt hx) (ne_of_gt hsqrt),
      log_sqrt_three, mul_sub]
  linarith

/-- `cos(x - π) = -cos(x)`, derived from `Real.cos_add_pi`. -/
lemma cos_sub_pi (x : ℝ) : Real.cos (x - π) = -Real.cos x := by
  have h := Real.cos_add_pi (x - π)
  have heq : x - π + π = x := by ring
  rw [heq] at h
  linarith

/-! ## §2 The log-cosine and its envelope. -/

/-- The r220 log-cosine ansatz: `gLogCos A σ φ₀ a = A · a^σ · cos(logFrequency · log a + φ₀)`. -/
noncomputable def gLogCos (A σ φ₀ a : ℝ) : ℝ :=
  A * a ^ σ * Real.cos (logFrequency * Real.log a + φ₀)

/-- On `a > 0`, the envelope `a^σ` is strictly positive for every real `σ`. -/
lemma envelope_pos {a : ℝ} (ha : 0 < a) (σ : ℝ) : 0 < a ^ σ :=
  Real.rpow_pos_of_pos ha σ

/-- **Zero factorisation.**  For `a > 0` and `A ≠ 0`, `gLogCos A σ φ₀ a = 0`
iff the cosine factor is zero — the envelope cannot vanish. -/
theorem gLogCos_eq_zero_iff (A σ φ₀ a : ℝ) (hA : A ≠ 0) (ha : 0 < a) :
    gLogCos A σ φ₀ a = 0
      ↔ Real.cos (logFrequency * Real.log a + φ₀) = 0 := by
  unfold gLogCos
  have henv : a ^ σ ≠ 0 := ne_of_gt (envelope_pos ha σ)
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · rcases mul_eq_zero.mp h1 with hA' | henv'
      · exact absurd hA' hA
      · exact absurd henv' henv
    · exact h2
  · intro h
    rw [h, mul_zero]

/-! ## §3 The main theorem — the `√3` shift is forced by the frequency. -/

/-- **`g_logcos_next_zero_forced_by_frequency`** — the second r221 stone.

If `a₀ > 0` is a zero of the log-cosine ansatz `g(a) = A · a^σ · cos(ω · ln a + φ₀)`
at the r220 frequency `ω = logFrequency = 2π / ln 3`, then BOTH `√3 · a₀` (next
newer) and `a₀ / √3` (next older) are ALSO zeros, for EVERY `A ≠ 0`, EVERY `σ`,
and EVERY `φ₀`. The multiplier `√3` is a function of `logFrequency` alone. -/
theorem g_logcos_next_zero_forced_by_frequency
    {A σ φ₀ a₀ : ℝ} (hA : A ≠ 0) (ha₀ : 0 < a₀)
    (hzero : gLogCos A σ φ₀ a₀ = 0) :
    gLogCos A σ φ₀ (Real.sqrt 3 * a₀) = 0
      ∧ gLogCos A σ φ₀ (a₀ / Real.sqrt 3) = 0 := by
  have hsqrt : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have haP : 0 < Real.sqrt 3 * a₀ := mul_pos hsqrt ha₀
  have haM : 0 < a₀ / Real.sqrt 3 := div_pos ha₀ hsqrt
  rw [gLogCos_eq_zero_iff _ _ _ _ hA ha₀] at hzero
  refine ⟨?_, ?_⟩
  · rw [gLogCos_eq_zero_iff _ _ _ _ hA haP,
        logFrequency_log_sqrt_three_mul a₀ ha₀,
        show logFrequency * Real.log a₀ + π + φ₀
              = (logFrequency * Real.log a₀ + φ₀) + π by ring,
        Real.cos_add_pi]
    rw [hzero, neg_zero]
  · rw [gLogCos_eq_zero_iff _ _ _ _ hA haM,
        logFrequency_log_div_sqrt_three a₀ ha₀,
        show logFrequency * Real.log a₀ - π + φ₀
              = (logFrequency * Real.log a₀ + φ₀) - π by ring,
        cos_sub_pi]
    rw [hzero, neg_zero]

/-! ## §4 The log-spaced arithmetic progression of zeros — both directions. -/

/-- **Every √3-power shift UP preserves zeros.**  If `a₀ > 0` is a zero, then
`√3^n · a₀` is a zero for every `n : ℕ`. -/
theorem g_logcos_zero_at_sqrt_three_pow_up
    {A σ φ₀ a₀ : ℝ} (hA : A ≠ 0) (ha₀ : 0 < a₀)
    (hzero : gLogCos A σ φ₀ a₀ = 0) (n : ℕ) :
    gLogCos A σ φ₀ (Real.sqrt 3 ^ n * a₀) = 0 := by
  have hsqrt : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  induction n with
  | zero => simpa using hzero
  | succ k ih =>
      have hpk : (0 : ℝ) < Real.sqrt 3 ^ k := pow_pos hsqrt k
      have hpa : (0 : ℝ) < Real.sqrt 3 ^ k * a₀ := mul_pos hpk ha₀
      have := (g_logcos_next_zero_forced_by_frequency hA hpa ih).left
      have heq : Real.sqrt 3 * (Real.sqrt 3 ^ k * a₀)
                = Real.sqrt 3 ^ (k + 1) * a₀ := by
        rw [pow_succ]; ring
      rwa [heq] at this

/-- **Every √3-power shift DOWN preserves zeros.**  If `a₀ > 0` is a zero,
then `a₀ / √3^n` is a zero for every `n : ℕ`. -/
theorem g_logcos_zero_at_div_sqrt_three_pow
    {A σ φ₀ a₀ : ℝ} (hA : A ≠ 0) (ha₀ : 0 < a₀)
    (hzero : gLogCos A σ φ₀ a₀ = 0) (n : ℕ) :
    gLogCos A σ φ₀ (a₀ / Real.sqrt 3 ^ n) = 0 := by
  have hsqrt : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  induction n with
  | zero => simpa using hzero
  | succ k ih =>
      have hpk : (0 : ℝ) < Real.sqrt 3 ^ k := pow_pos hsqrt k
      have hda : (0 : ℝ) < a₀ / Real.sqrt 3 ^ k := div_pos ha₀ hpk
      have := (g_logcos_next_zero_forced_by_frequency hA hda ih).right
      have heq : (a₀ / Real.sqrt 3 ^ k) / Real.sqrt 3
                = a₀ / Real.sqrt 3 ^ (k + 1) := by
        rw [pow_succ, div_div]
      rwa [heq] at this

/-! ## §5 The `√3` is forced by `logFrequency = 2π / ln 3` — nothing else. -/

/-- **`sqrt_three_from_logFrequency`.**  The shift factor `√3` is precisely
`exp(π / logFrequency)` — i.e. `π / logFrequency` is exactly
`log(√3) = (log 3) / 2`, so the multiplicative shift is `√3` and no other
value is possible at this frequency. -/
theorem sqrt_three_from_logFrequency :
    π / logFrequency = Real.log (Real.sqrt 3) := by
  rw [log_sqrt_three, logPeriod, logFrequency]
  have hlog : Real.log 3 ≠ 0 := log_three_ne_zero
  field_simp

/-- Explicit `exp` form: `√3 = exp(π / logFrequency)`. -/
theorem sqrt_three_eq_exp_pi_div_logFrequency :
    Real.sqrt 3 = Real.exp (π / logFrequency) := by
  have hpos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [sqrt_three_from_logFrequency]
  exact (Real.exp_log hpos).symm

/-! ## §6 Axiom check. -/

#print axioms PrincipiaTractalis.LogCosineNextZero.log_sqrt_three
#print axioms PrincipiaTractalis.LogCosineNextZero.logFrequency_log_sqrt_three_mul
#print axioms PrincipiaTractalis.LogCosineNextZero.logFrequency_log_div_sqrt_three
#print axioms PrincipiaTractalis.LogCosineNextZero.cos_sub_pi
#print axioms PrincipiaTractalis.LogCosineNextZero.gLogCos_eq_zero_iff
#print axioms PrincipiaTractalis.LogCosineNextZero.g_logcos_next_zero_forced_by_frequency
#print axioms PrincipiaTractalis.LogCosineNextZero.g_logcos_zero_at_sqrt_three_pow_up
#print axioms PrincipiaTractalis.LogCosineNextZero.g_logcos_zero_at_div_sqrt_three_pow
#print axioms PrincipiaTractalis.LogCosineNextZero.sqrt_three_from_logFrequency
#print axioms PrincipiaTractalis.LogCosineNextZero.sqrt_three_eq_exp_pi_div_logFrequency

end PrincipiaTractalis.LogCosineNextZero
