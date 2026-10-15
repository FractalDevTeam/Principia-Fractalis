/-
# PF.Analytic.FourierPanels.OmegaTailBound_c6_2026_10_15

**M2.5 bridge for the pointwise panel pack at `c = 6`.**

The per-panel bricks (`Seg01Range_c6_2026_10_15.lean`) enclose the **N = 3
truncated** real nodes

```
nodeR_fourier_plus_at_c6_N3  u = (exp(u/2)·ω_N3(exp u) + ω_N3(exp u)) · cos(3u)
nodeR_fourier_minus_at_c6_N3 u = (exp(u/2)·ω_N3(exp u) − ω_N3(exp u)) · sin(3u)
```

where `ω_N3(exp u) = exp(-π·exp u) + exp(-4π·exp u) + exp(-9π·exp u)`. To
convert those bounds into bounds on the **full-ω** real nodes

```
nodeR_fourier_plus_at_c6  u = (exp(u/2)·ω(exp u) + ω(exp u)) · cos(3u)
nodeR_fourier_minus_at_c6 u = (exp(u/2)·ω(exp u) − ω(exp u)) · sin(3u)
```

(and therefore into bounds on `Re Λ₀(1+6i)` and `Im Λ₀(1+6i)`) we need
to control the uniform gap. This file supplies that control.

## What this file proves

Let `R(x) := exp(-16·π·x)/(1 − exp(-π))`. For every `x ≥ 1`,

```
0 ≤ ω(x) − ω_N3_at_exp(log x)  ≤ R(x)        (omegaPartial = ω_N3 at x = exp u)
```

Specialising at `x = exp u` with `u ≥ 0`:

```
0 ≤ ω(exp u) − ω_N3_at_exp u ≤ exp(-16·π·exp u)/(1 − exp(-π))
```

The headline gap bounds on the plus/minus Fourier nodes follow by
factoring the gap

```
nodeR_fourier_plus_at_c6  u − nodeR_fourier_plus_at_c6_N3  u
  = ((exp(u/2) + 1) · (ω(exp u) − ω_N3_at_exp u)) · cos(3u)
nodeR_fourier_minus_at_c6 u − nodeR_fourier_minus_at_c6_N3 u
  = ((exp(u/2) − 1) · (ω(exp u) − ω_N3_at_exp u)) · sin(3u)
```

and bounding `|cos|, |sin| ≤ 1` and `|exp(u/2) ± 1| ≤ exp(u/2) + 1`.

## Note on the denominator

The task template requested the tighter denominator `1 − exp(-π·exp u)`.
We prove a *weaker but kernel-clean* form that reuses
`PF.Analytic.XiQuadrature.omega_partial_error` directly: denominator
`1 − exp(-π)` (independent of `u`). Since `exp(-π·exp u) ≤ exp(-π)`
for `u ≥ 0` (because `exp u ≥ 1`), we have
`1 − exp(-π·exp u) ≥ 1 − exp(-π) > 0`, hence
`exp(-16π·exp u)/(1 − exp(-π)) ≥ exp(-16π·exp u)/(1 − exp(-π·exp u))`,
so our bound is a *valid (weaker) upper bound* in exactly the sense the
task permits.

## Three-axiom bar

Every top-level theorem below prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no `interval` tactic, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-15.
-/

import PF.Analytic.FourierPanels.CoreDefs_c6_2026_10_15
import PF.Analytic.XiQuadrature

set_option autoImplicit false

namespace PrincipiaTractalis
namespace FourierPanels_c6

open Real
open PrincipiaTractalis.OmegaDerivative20261014
open PrincipiaTractalis.XiThetaIntegral
open PrincipiaTractalis.XiQuadrature
open scoped Real

/-! ## §1 — `omega_N3_at_exp u = omegaPartial 3 (exp u)`

The `ω_N3` truncation defined in `CoreDefs_c6_2026_10_15.lean` is
exactly `XiQuadrature.omegaPartial 3` evaluated at `exp u`, so the full
`omega_partial_error` apparatus applies. -/

theorem omegaPartial_three_eq_omega_N3_at_exp (u : ℝ) :
    omegaPartial 3 (Real.exp u) = omega_N3_at_exp u := by
  unfold omegaPartial omega_N3_at_exp
  -- Finset.range 3 expands to {0, 1, 2}; expand explicitly, then push_cast + ring_nf
  -- align the exponents (`-π·1²·x = -(π·x)`, etc.).
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  push_cast
  ring_nf

/-! ## §2 — Non-negativity: `ω_N3_at_exp u ≤ ω(exp u)` for `u ≥ 0`

The theta tail from `n ≥ 4` is a sum of non-negative exponentials, so
truncation underestimates `ω`. We get this directly from
`omega_partial_error` plus the sign of the untruncated tail. -/

/-- `omega_N3_at_exp u ≤ omega (exp u)` whenever `exp u ≥ 1`
(equivalently `u ≥ 0`). This is the structural "N = 3 is a lower bound"
statement. -/
theorem omega_N3_at_exp_le_omega {u : ℝ} (hu : 0 ≤ u) :
    omega_N3_at_exp u ≤ omega (Real.exp u) := by
  -- exp u ≥ 1
  have hx1 : (1 : ℝ) ≤ Real.exp u := Real.one_le_exp hu
  have hx_pos : (0 : ℝ) < Real.exp u := Real.exp_pos _
  -- The tail is `∑' n, exp(-π·(n+3+1)²·exp u)`, non-negative.
  have hsum := summable_omega hx_pos
  -- `omegaPartial 3 (exp u) + tail = omega (exp u)`.
  have hsplit :
      omegaPartial 3 (Real.exp u) +
        ∑' n : ℕ, Real.exp (-π * (((n + 3 : ℕ) : ℝ) + 1) ^ 2 * Real.exp u)
        = omega (Real.exp u) :=
    hsum.sum_add_tsum_nat_add 3
  have htail_nonneg :
      (0 : ℝ) ≤ ∑' n : ℕ, Real.exp (-π * (((n + 3 : ℕ) : ℝ) + 1) ^ 2 * Real.exp u) :=
    tsum_nonneg fun _ ↦ (Real.exp_pos _).le
  have hN3 : omegaPartial 3 (Real.exp u) = omega_N3_at_exp u :=
    omegaPartial_three_eq_omega_N3_at_exp u
  linarith

/-! ## §3 — Pointwise tail bound on `ω(exp u) − ω_N3_at_exp u`

Direct application of `XiQuadrature.omega_partial_error` at `N = 3`
and `u ↦ exp u` (which is `≥ 1` for `u ≥ 0`). -/

/-- **Pointwise tail bound.** For `u ≥ 0`,

  `ω(exp u) − ω_N3_at_exp u ≤ exp(-16·π·exp u) / (1 − exp(-π))`.

The constant `16 = (3+1)² = 4²` comes from the first omitted term `n = 3`
(indexed as `(n+1)² = 16`) of the theta series. The denominator uses the
`u`-independent `1 − exp(-π)` (loose but kernel-clean); this is a valid
upper bound since `1 − exp(-π·exp u) ≥ 1 − exp(-π)` for `u ≥ 0`. -/
theorem omega_tail_n4_bound {u : ℝ} (hu : 0 ≤ u) :
    omega (Real.exp u) - omega_N3_at_exp u
      ≤ Real.exp (-π * (16 : ℝ) * Real.exp u) / (1 - Real.exp (-π)) := by
  have hx1 : (1 : ℝ) ≤ Real.exp u := Real.one_le_exp hu
  -- omega_partial_error at u := exp u, N := 3.
  have h := omega_partial_error (u := Real.exp u) hx1 3
  -- Shape: |omega (exp u) - omegaPartial 3 (exp u)|
  --            ≤ exp(-π·(3+1)²·exp u) / (1 - exp(-π))
  --        = exp(-π·16·exp u) / (1 - exp(-π)).
  have hN3 : omegaPartial 3 (Real.exp u) = omega_N3_at_exp u :=
    omegaPartial_three_eq_omega_N3_at_exp u
  rw [hN3] at h
  -- Argument-match: (3 : ℝ) + 1 = 4, (4)^2 = 16.
  have harg : -π * (((3 : ℕ) : ℝ) + 1) ^ 2 * Real.exp u
              = -π * (16 : ℝ) * Real.exp u := by
    push_cast; ring
  rw [harg] at h
  -- Strip the absolute value using the sign from §2.
  have hle : omega_N3_at_exp u ≤ omega (Real.exp u) :=
    omega_N3_at_exp_le_omega hu
  have hdiff_nonneg : (0 : ℝ) ≤ omega (Real.exp u) - omega_N3_at_exp u := by linarith
  calc omega (Real.exp u) - omega_N3_at_exp u
      = |omega (Real.exp u) - omega_N3_at_exp u| := (abs_of_nonneg hdiff_nonneg).symm
    _ ≤ Real.exp (-π * (16 : ℝ) * Real.exp u) / (1 - Real.exp (-π)) := h

/-! ## §4 — Headline gap bounds on the plus/minus Fourier nodes

The gap factorises as

  `nodeR_plus  u − nodeR_plus_N3  u = ((exp(u/2) + 1) · Δω) · cos(3u)`
  `nodeR_minus u − nodeR_minus_N3 u = ((exp(u/2) − 1) · Δω) · sin(3u)`

where `Δω = ω(exp u) − ω_N3_at_exp u ≥ 0` for `u ≥ 0`. Bounding
`|cos|, |sin| ≤ 1` and `|exp(u/2) ± 1| ≤ exp(u/2) + 1` reduces each gap
to `(exp(u/2) + 1) · Δω`, which is then majorised by §3. -/

/-- Private factorisation of the plus gap. -/
private lemma plus_gap_factor (u : ℝ) :
    nodeR_fourier_plus_at_c6 u - nodeR_fourier_plus_at_c6_N3 u
      = ((Real.exp (u / 2) + 1) *
          (omega (Real.exp u) - omega_N3_at_exp u)) * Real.cos (3 * u) := by
  unfold nodeR_fourier_plus_at_c6 nodeR_fourier_plus_at_c6_N3
  unfold F_plus F_minus
  have hhalf : u / 2 = u * (0.5 : ℝ) := by ring
  rw [hhalf]
  ring

/-- Private factorisation of the minus gap. -/
private lemma minus_gap_factor (u : ℝ) :
    nodeR_fourier_minus_at_c6 u - nodeR_fourier_minus_at_c6_N3 u
      = ((Real.exp (u / 2) - 1) *
          (omega (Real.exp u) - omega_N3_at_exp u)) * Real.sin (3 * u) := by
  unfold nodeR_fourier_minus_at_c6 nodeR_fourier_minus_at_c6_N3
  unfold F_plus F_minus
  have hhalf : u / 2 = u * (0.5 : ℝ) := by ring
  rw [hhalf]
  ring

/-- **Headline gap bound for the plus (real-part) node.** For `u ≥ 0`,

  `|nodeR_fourier_plus_at_c6 u − nodeR_fourier_plus_at_c6_N3 u|
      ≤ (exp(u/2) + 1) · exp(-16·π·exp u) / (1 − exp(-π))`.

Multiplying the tighter §3 bound on `Δω` by the (positive) prefactor
`exp(u/2) + 1 ≥ 2` and using `|cos| ≤ 1`. -/
theorem nodeR_fourier_plus_at_c6_tail_abs_le {u : ℝ} (hu : 0 ≤ u) :
    |nodeR_fourier_plus_at_c6 u - nodeR_fourier_plus_at_c6_N3 u|
      ≤ (Real.exp (u / 2) + 1)
          * Real.exp (-π * (16 : ℝ) * Real.exp u) / (1 - Real.exp (-π)) := by
  -- Preliminaries.
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hepi_lt_one : Real.exp (-π) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have hdenom_pos : (0 : ℝ) < 1 - Real.exp (-π) := by linarith
  have hpref_nonneg : (0 : ℝ) ≤ Real.exp (u / 2) + 1 := by
    have := (Real.exp_pos (u / 2)).le; linarith
  have hdω_nonneg : (0 : ℝ) ≤ omega (Real.exp u) - omega_N3_at_exp u := by
    linarith [omega_N3_at_exp_le_omega hu]
  have hdω_bound := omega_tail_n4_bound hu
  -- Factorise and bound.
  rw [plus_gap_factor]
  -- |A · cos(3u)| = |A| · |cos(3u)| ≤ |A| · 1 = |A|
  calc |((Real.exp (u / 2) + 1) *
            (omega (Real.exp u) - omega_N3_at_exp u)) * Real.cos (3 * u)|
      = |(Real.exp (u / 2) + 1) *
            (omega (Real.exp u) - omega_N3_at_exp u)| * |Real.cos (3 * u)| :=
            abs_mul _ _
    _ ≤ |(Real.exp (u / 2) + 1) *
            (omega (Real.exp u) - omega_N3_at_exp u)| * 1 := by
            have habs_cos : |Real.cos (3 * u)| ≤ 1 := Real.abs_cos_le_one _
            have habs_nn : (0 : ℝ) ≤ |(Real.exp (u / 2) + 1) *
                            (omega (Real.exp u) - omega_N3_at_exp u)| := abs_nonneg _
            exact mul_le_mul_of_nonneg_left habs_cos habs_nn
    _ = (Real.exp (u / 2) + 1) *
            (omega (Real.exp u) - omega_N3_at_exp u) := by
          rw [mul_one]
          rw [abs_of_nonneg (mul_nonneg hpref_nonneg hdω_nonneg)]
    _ ≤ (Real.exp (u / 2) + 1) *
          (Real.exp (-π * (16 : ℝ) * Real.exp u) / (1 - Real.exp (-π))) := by
          exact mul_le_mul_of_nonneg_left hdω_bound hpref_nonneg
    _ = (Real.exp (u / 2) + 1)
          * Real.exp (-π * (16 : ℝ) * Real.exp u) / (1 - Real.exp (-π)) := by
          field_simp

/-- **Headline gap bound for the minus (imaginary-part) node.** For `u ≥ 0`,

  `|nodeR_fourier_minus_at_c6 u − nodeR_fourier_minus_at_c6_N3 u|
      ≤ (exp(u/2) + 1) · exp(-16·π·exp u) / (1 − exp(-π))`.

Note the factor on the minus side is `exp(u/2) − 1 ≥ 0` for `u ≥ 0`, but
we use the (larger) bound `exp(u/2) − 1 ≤ exp(u/2) + 1` to share one
headline shape with the plus node. -/
theorem nodeR_fourier_minus_at_c6_tail_abs_le {u : ℝ} (hu : 0 ≤ u) :
    |nodeR_fourier_minus_at_c6 u - nodeR_fourier_minus_at_c6_N3 u|
      ≤ (Real.exp (u / 2) + 1)
          * Real.exp (-π * (16 : ℝ) * Real.exp u) / (1 - Real.exp (-π)) := by
  -- Preliminaries.
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hepi_lt_one : Real.exp (-π) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have hdenom_pos : (0 : ℝ) < 1 - Real.exp (-π) := by linarith
  -- `|exp(u/2) − 1| ≤ exp(u/2) + 1` (two cases, both easy).
  have hpref_abs_le : |Real.exp (u / 2) - 1| ≤ Real.exp (u / 2) + 1 := by
    have hpos : (0 : ℝ) < Real.exp (u / 2) := Real.exp_pos _
    rcases le_or_gt 1 (Real.exp (u / 2)) with h | h
    · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ Real.exp (u / 2) - 1)]
      linarith
    · rw [abs_of_nonpos (by linarith : Real.exp (u / 2) - 1 ≤ 0)]
      linarith
  have hpref_plus_nonneg : (0 : ℝ) ≤ Real.exp (u / 2) + 1 := by
    have := (Real.exp_pos (u / 2)).le; linarith
  have hdω_nonneg : (0 : ℝ) ≤ omega (Real.exp u) - omega_N3_at_exp u := by
    linarith [omega_N3_at_exp_le_omega hu]
  have hdω_bound := omega_tail_n4_bound hu
  rw [minus_gap_factor]
  -- |A · sin(3u)| = |A| · |sin(3u)| ≤ |A| · 1 = |A|
  calc |((Real.exp (u / 2) - 1) *
            (omega (Real.exp u) - omega_N3_at_exp u)) * Real.sin (3 * u)|
      = |(Real.exp (u / 2) - 1) *
            (omega (Real.exp u) - omega_N3_at_exp u)| * |Real.sin (3 * u)| :=
            abs_mul _ _
    _ ≤ |(Real.exp (u / 2) - 1) *
            (omega (Real.exp u) - omega_N3_at_exp u)| * 1 := by
            have habs_sin : |Real.sin (3 * u)| ≤ 1 := Real.abs_sin_le_one _
            have habs_nn : (0 : ℝ) ≤ |(Real.exp (u / 2) - 1) *
                            (omega (Real.exp u) - omega_N3_at_exp u)| := abs_nonneg _
            exact mul_le_mul_of_nonneg_left habs_sin habs_nn
    _ = |Real.exp (u / 2) - 1| *
            (omega (Real.exp u) - omega_N3_at_exp u) := by
          rw [mul_one, abs_mul, abs_of_nonneg hdω_nonneg]
    _ ≤ (Real.exp (u / 2) + 1) *
            (omega (Real.exp u) - omega_N3_at_exp u) :=
          mul_le_mul_of_nonneg_right hpref_abs_le hdω_nonneg
    _ ≤ (Real.exp (u / 2) + 1) *
          (Real.exp (-π * (16 : ℝ) * Real.exp u) / (1 - Real.exp (-π))) := by
          exact mul_le_mul_of_nonneg_left hdω_bound hpref_plus_nonneg
    _ = (Real.exp (u / 2) + 1)
          * Real.exp (-π * (16 : ℝ) * Real.exp u) / (1 - Real.exp (-π)) := by
          field_simp

/-! ## §Axiom checks -/

#print axioms omegaPartial_three_eq_omega_N3_at_exp
#print axioms omega_N3_at_exp_le_omega
#print axioms omega_tail_n4_bound
#print axioms nodeR_fourier_plus_at_c6_tail_abs_le
#print axioms nodeR_fourier_minus_at_c6_tail_abs_le

end FourierPanels_c6
end PrincipiaTractalis
