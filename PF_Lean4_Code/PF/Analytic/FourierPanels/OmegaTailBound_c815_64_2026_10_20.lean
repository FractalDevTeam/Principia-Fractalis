/-
# PF.Analytic.FourierPanels.OmegaTailBound_c815_64_2026_10_20

**M2.5 bridge for the pointwise panel pack at `c = 815/64`.**

Mirror of `OmegaTailBound_c6_2026_10_15.lean` for the frequency
`(c/2)·u = (815/128)·u = 6.3671875·u`. The analytic argument is independent of
`c` modulo renaming of the sin/cos frequency: we bound `|cos|, |sin| ≤ 1`
and leverage `omega_partial_error` identically.

## What this file proves

Let `R(x) := exp(-16·π·x)/(1 − exp(-π))`. For every `x ≥ 1`,

```
0 ≤ ω(x) − ω_N3_at_exp(log x)  ≤ R(x)
```

Specialising at `x = exp u` with `u ≥ 0`:

```
0 ≤ ω(exp u) − ω_N3_at_exp u ≤ exp(-16·π·exp u)/(1 − exp(-π))
```

The headline gap bounds on the plus/minus Fourier nodes follow by
factoring the gap

```
nodeR_fourier_plus_at_c815_64  u − nodeR_fourier_plus_at_c815_64_N3  u
  = ((exp(u/2) + 1) · (ω(exp u) − ω_N3_at_exp u)) · cos(6.3671875u)
nodeR_fourier_minus_at_c815_64 u − nodeR_fourier_minus_at_c815_64_N3 u
  = ((exp(u/2) − 1) · (ω(exp u) − ω_N3_at_exp u)) · sin(6.3671875u)
```

and bounding `|cos|, |sin| ≤ 1` and `|exp(u/2) ± 1| ≤ exp(u/2) + 1`.

## Three-axiom bar

Every top-level theorem below prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no `interval` tactic, no project axioms.

Emitted by codex/gen_box.py for c = 815/64 (2026-10-20). `c` enters the node
functions only through the phase cos((c/2)u) / sin((c/2)u), and every add-on
majorant discards it via |cos|,|sin| <= 1, so the three add-on constants are
c-independent: residue 7/10^7, analytic tail 12/10^8, omega-gap 1/10^21.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-16.
-/

import PF.Analytic.FourierPanels.CoreDefs_c815_64_2026_10_16
import PF.Analytic.XiQuadrature

set_option autoImplicit false

namespace PrincipiaTractalis
namespace FourierPanels_c815_64

open Real
open PrincipiaTractalis.OmegaDerivative20261014
open PrincipiaTractalis.XiThetaIntegral
open PrincipiaTractalis.XiQuadrature
open scoped Real

/-! ## §1 — `omega_N3_at_exp u = omegaPartial 3 (exp u)` -/

theorem omegaPartial_three_eq_omega_N3_at_exp (u : ℝ) :
    omegaPartial 3 (Real.exp u) = omega_N3_at_exp u := by
  unfold omegaPartial omega_N3_at_exp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  push_cast
  ring_nf

/-! ## §2 — Non-negativity: `ω_N3_at_exp u ≤ ω(exp u)` for `u ≥ 0` -/

theorem omega_N3_at_exp_le_omega {u : ℝ} (hu : 0 ≤ u) :
    omega_N3_at_exp u ≤ omega (Real.exp u) := by
  have hx1 : (1 : ℝ) ≤ Real.exp u := Real.one_le_exp hu
  have hx_pos : (0 : ℝ) < Real.exp u := Real.exp_pos _
  have hsum := summable_omega hx_pos
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

/-! ## §3 — Pointwise tail bound on `ω(exp u) − ω_N3_at_exp u` -/

theorem omega_tail_n4_bound {u : ℝ} (hu : 0 ≤ u) :
    omega (Real.exp u) - omega_N3_at_exp u
      ≤ Real.exp (-π * (16 : ℝ) * Real.exp u) / (1 - Real.exp (-π)) := by
  have hx1 : (1 : ℝ) ≤ Real.exp u := Real.one_le_exp hu
  have h := omega_partial_error (u := Real.exp u) hx1 3
  have hN3 : omegaPartial 3 (Real.exp u) = omega_N3_at_exp u :=
    omegaPartial_three_eq_omega_N3_at_exp u
  rw [hN3] at h
  have harg : -π * (((3 : ℕ) : ℝ) + 1) ^ 2 * Real.exp u
              = -π * (16 : ℝ) * Real.exp u := by
    push_cast; ring
  rw [harg] at h
  have hle : omega_N3_at_exp u ≤ omega (Real.exp u) :=
    omega_N3_at_exp_le_omega hu
  have hdiff_nonneg : (0 : ℝ) ≤ omega (Real.exp u) - omega_N3_at_exp u := by linarith
  calc omega (Real.exp u) - omega_N3_at_exp u
      = |omega (Real.exp u) - omega_N3_at_exp u| := (abs_of_nonneg hdiff_nonneg).symm
    _ ≤ Real.exp (-π * (16 : ℝ) * Real.exp u) / (1 - Real.exp (-π)) := h

/-! ## §4 — Headline gap bounds on the plus/minus Fourier nodes -/

/-- Private factorisation of the plus gap. -/
private lemma plus_gap_factor (u : ℝ) :
    nodeR_fourier_plus_at_c815_64 u - nodeR_fourier_plus_at_c815_64_N3 u
      = ((Real.exp (u / 2) + 1) *
          (omega (Real.exp u) - omega_N3_at_exp u)) * Real.cos ((6.3671875 : ℝ) * u) := by
  unfold nodeR_fourier_plus_at_c815_64 nodeR_fourier_plus_at_c815_64_N3
  unfold F_plus F_minus
  have hhalf : u / 2 = u * (0.5 : ℝ) := by ring
  rw [hhalf]
  ring

/-- Private factorisation of the minus gap. -/
private lemma minus_gap_factor (u : ℝ) :
    nodeR_fourier_minus_at_c815_64 u - nodeR_fourier_minus_at_c815_64_N3 u
      = ((Real.exp (u / 2) - 1) *
          (omega (Real.exp u) - omega_N3_at_exp u)) * Real.sin ((6.3671875 : ℝ) * u) := by
  unfold nodeR_fourier_minus_at_c815_64 nodeR_fourier_minus_at_c815_64_N3
  unfold F_plus F_minus
  have hhalf : u / 2 = u * (0.5 : ℝ) := by ring
  rw [hhalf]
  ring

/-- **Headline gap bound for the plus (real-part) node.** For `u ≥ 0`,

  `|nodeR_fourier_plus_at_c815_64 u − nodeR_fourier_plus_at_c815_64_N3 u|
      ≤ (exp(u/2) + 1) · exp(-16·π·exp u) / (1 − exp(-π))`. -/
theorem nodeR_fourier_plus_at_c815_64_tail_abs_le {u : ℝ} (hu : 0 ≤ u) :
    |nodeR_fourier_plus_at_c815_64 u - nodeR_fourier_plus_at_c815_64_N3 u|
      ≤ (Real.exp (u / 2) + 1)
          * Real.exp (-π * (16 : ℝ) * Real.exp u) / (1 - Real.exp (-π)) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hepi_lt_one : Real.exp (-π) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have hdenom_pos : (0 : ℝ) < 1 - Real.exp (-π) := by linarith
  have hpref_nonneg : (0 : ℝ) ≤ Real.exp (u / 2) + 1 := by
    have := (Real.exp_pos (u / 2)).le; linarith
  have hdω_nonneg : (0 : ℝ) ≤ omega (Real.exp u) - omega_N3_at_exp u := by
    linarith [omega_N3_at_exp_le_omega hu]
  have hdω_bound := omega_tail_n4_bound hu
  rw [plus_gap_factor]
  calc |((Real.exp (u / 2) + 1) *
            (omega (Real.exp u) - omega_N3_at_exp u)) * Real.cos ((6.3671875 : ℝ) * u)|
      = |(Real.exp (u / 2) + 1) *
            (omega (Real.exp u) - omega_N3_at_exp u)| * |Real.cos ((6.3671875 : ℝ) * u)| :=
            abs_mul _ _
    _ ≤ |(Real.exp (u / 2) + 1) *
            (omega (Real.exp u) - omega_N3_at_exp u)| * 1 := by
            have habs_cos : |Real.cos ((6.3671875 : ℝ) * u)| ≤ 1 := Real.abs_cos_le_one _
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

  `|nodeR_fourier_minus_at_c815_64 u − nodeR_fourier_minus_at_c815_64_N3 u|
      ≤ (exp(u/2) + 1) · exp(-16·π·exp u) / (1 − exp(-π))`. -/
theorem nodeR_fourier_minus_at_c815_64_tail_abs_le {u : ℝ} (hu : 0 ≤ u) :
    |nodeR_fourier_minus_at_c815_64 u - nodeR_fourier_minus_at_c815_64_N3 u|
      ≤ (Real.exp (u / 2) + 1)
          * Real.exp (-π * (16 : ℝ) * Real.exp u) / (1 - Real.exp (-π)) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hepi_lt_one : Real.exp (-π) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have hdenom_pos : (0 : ℝ) < 1 - Real.exp (-π) := by linarith
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
  calc |((Real.exp (u / 2) - 1) *
            (omega (Real.exp u) - omega_N3_at_exp u)) * Real.sin ((6.3671875 : ℝ) * u)|
      = |(Real.exp (u / 2) - 1) *
            (omega (Real.exp u) - omega_N3_at_exp u)| * |Real.sin ((6.3671875 : ℝ) * u)| :=
            abs_mul _ _
    _ ≤ |(Real.exp (u / 2) - 1) *
            (omega (Real.exp u) - omega_N3_at_exp u)| * 1 := by
            have habs_sin : |Real.sin ((6.3671875 : ℝ) * u)| ≤ 1 := Real.abs_sin_le_one _
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
#print axioms nodeR_fourier_plus_at_c815_64_tail_abs_le
#print axioms nodeR_fourier_minus_at_c815_64_tail_abs_le

end FourierPanels_c815_64
end PrincipiaTractalis
