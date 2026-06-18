/-
# PF.AlphaLeibnizSeriesBundle

★★★★ 2026-06-17 — FUN: Leibniz's series for π in framework form.

## Headline

  1 − 1/3 + 1/5 − 1/7 + ... = π/4 = α_BSD / 3 = α_QG² / α_YM³

The Madhava–Leibniz–Gregory alternating series for π/4 anchors
cleanly to one-third of the BSD axis, equivalently to α_QG² divided
by α_YM³ = 8.

## Equivalent forms

  π/4 = α_BSD / 3                    (BSD-axis form)
  π/4 = α_QG² / α_YM³                (= 2π/8 = π/4)
  π/4 = α_NS / 6                     (= (3π/2)/6 = π/4)

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants
import Mathlib.Analysis.Real.Pi.Leibniz

namespace PrincipiaTractalis
namespace AlphaLeibnizSeriesBundle

open Real Filter Topology Finset
open PrincipiaTractalis.CrossMillenniumSharedInvariants

/-! ## §1 — π / 4 = α_BSD / 3 -/

/-- **`π/4 = α_BSD / 3`** — π/4 in framework form. -/
theorem pi_div_four_eq_α_BSD_div_three :
    Real.pi / 4 = α_BSD / 3 := by
  unfold α_BSD
  ring

/-! ## §2 — π / 4 = α_QG² / α_YM³ -/

/-- **`π/4 = α_QG² / α_YM³`** — alternative axis form. -/
theorem pi_div_four_eq_α_QG_sq_div_α_YM_cubed :
    Real.pi / 4 = α_QG ^ 2 / α_YM ^ 3 := by
  rw [α_QG_sq_eq_two_pi]
  unfold α_YM
  ring

/-! ## §3 — Leibniz series tends to α_BSD/3 -/

/-- **★★★ LEIBNIZ SERIES IN FRAMEWORK FORM ★★★** —
    `1 − 1/3 + 1/5 − 1/7 + ... → α_BSD / 3`. -/
theorem tendsto_leibniz_sum_α_BSD_div_three :
    Tendsto (fun k => ∑ i ∈ range k, (-1 : ℝ) ^ i / (2 * i + 1))
      atTop (𝓝 (α_BSD / 3)) := by
  have h := tendsto_sum_pi_div_four
  rw [pi_div_four_eq_α_BSD_div_three] at h
  exact h

/-! ## §4 — Bundle capstone -/

/-- **★★★★ THE LEIBNIZ-SERIES BUNDLE CAPSTONE ★★★★** —
    three identities exhibiting the classical Madhava–Leibniz–Gregory
    alternating series `1 − 1/3 + 1/5 − 1/7 + ... = π/4` in framework form:

      π/4 = α_BSD / 3                      (BSD-axis form)
      π/4 = α_QG² / α_YM³                  (gravitational/YM form)
      Leibniz sum → α_BSD / 3              (Leibniz in framework form)

    The historical first power-series representation of π — discovered
    by Madhava (~1400), rediscovered by Leibniz and Gregory in the 17th
    century — anchors to one-third of the BSD axis. -/
theorem α_leibniz_series_bundle_capstone :
    Real.pi / 4 = α_BSD / 3 ∧
    Real.pi / 4 = α_QG ^ 2 / α_YM ^ 3 ∧
    Tendsto (fun k => ∑ i ∈ range k, (-1 : ℝ) ^ i / (2 * i + 1))
      atTop (𝓝 (α_BSD / 3)) :=
  ⟨pi_div_four_eq_α_BSD_div_three,
   pi_div_four_eq_α_QG_sq_div_α_YM_cubed,
   tendsto_leibniz_sum_α_BSD_div_three⟩

end AlphaLeibnizSeriesBundle
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaLeibnizSeriesBundle.pi_div_four_eq_α_BSD_div_three
#print axioms PrincipiaTractalis.AlphaLeibnizSeriesBundle.pi_div_four_eq_α_QG_sq_div_α_YM_cubed
#print axioms PrincipiaTractalis.AlphaLeibnizSeriesBundle.tendsto_leibniz_sum_α_BSD_div_three
#print axioms PrincipiaTractalis.AlphaLeibnizSeriesBundle.α_leibniz_series_bundle_capstone
