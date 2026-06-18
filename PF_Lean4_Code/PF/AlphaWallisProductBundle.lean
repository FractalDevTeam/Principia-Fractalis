/-
# PF.AlphaWallisProductBundle

★★★★ 2026-06-17 — FUN: Wallis' infinite product for π/2 in framework form.

## Headline

  ∏_{k=1}^∞ (2k)²/((2k-1)(2k+1)) = π / 2 = α_QG² / α_YM² = α_NS / 3

The classical Wallis product (1656) for π/2 equals the ratio of the
gravitational axis squared to the Yang-Mills axis squared, or equivalently
one-third of the NS axis.

## Equivalent forms

  π/2 = α_QG² / α_YM²            (= 2π / 4)
  π/2 = α_NS / 3                  (= (3π/2) / 3)
  π/2 = α_BSD · 2/3               (= (3π/4) · 2/3)

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants
import Mathlib.Analysis.Real.Pi.Wallis

namespace PrincipiaTractalis
namespace AlphaWallisProductBundle

open Real Filter Topology
open PrincipiaTractalis.CrossMillenniumSharedInvariants

/-! ## §1 — π / 2 = α_QG² / α_YM² -/

/-- **`π/2 = α_QG² / α_YM²`** — the Wallis target in framework form. -/
theorem pi_div_two_eq_α_QG_sq_div_α_YM_sq :
    Real.pi / 2 = α_QG ^ 2 / α_YM ^ 2 := by
  rw [α_QG_sq_eq_two_pi]
  unfold α_YM
  ring

/-! ## §2 — Wallis tends to α_QG² / α_YM² -/

/-- **★★★ WALLIS PRODUCT IN FRAMEWORK FORM ★★★** —
    `∏_{k=0}^{n-1} ((2k+2)/(2k+1))·((2k+2)/(2k+3)) → α_QG² / α_YM²`. -/
theorem tendsto_wallis_α_QG_sq_div_α_YM_sq :
    Tendsto (fun k =>
      ∏ i ∈ Finset.range k,
        ((2 : ℝ) * i + 2) / (2 * i + 1) * ((2 * i + 2) / (2 * i + 3)))
      atTop (𝓝 (α_QG ^ 2 / α_YM ^ 2)) := by
  have h := Real.tendsto_prod_pi_div_two
  rw [pi_div_two_eq_α_QG_sq_div_α_YM_sq] at h
  exact h

/-! ## §3 — π / 2 = α_NS / 3 -/

/-- **`π/2 = α_NS / 3`** — alternative axis form. -/
theorem pi_div_two_eq_α_NS_div_three :
    Real.pi / 2 = α_NS / 3 := by
  unfold α_NS
  ring

/-! ## §4 — Bundle capstone -/

/-- **★★★★ THE WALLIS-PRODUCT BUNDLE CAPSTONE ★★★★** —
    three identities exhibiting Wallis' classical infinite product
    `π/2 = ∏ (2k)²/((2k-1)(2k+1))` in framework form:

      π/2 = α_QG² / α_YM²            (gravitational/YM ratio)
      π/2 = α_NS / 3                  (NS-axis form)
      Wallis product → α_QG² / α_YM²  (mathlib Wallis in framework form)

    The 1656 Wallis product for π/2 — the first infinite product for
    π in mathematical history — anchors cleanly to α_QG² / α_YM² = α_NS/3. -/
theorem α_wallis_product_bundle_capstone :
    Real.pi / 2 = α_QG ^ 2 / α_YM ^ 2 ∧
    Real.pi / 2 = α_NS / 3 ∧
    Tendsto (fun k =>
      ∏ i ∈ Finset.range k,
        ((2 : ℝ) * i + 2) / (2 * i + 1) * ((2 * i + 2) / (2 * i + 3)))
      atTop (𝓝 (α_QG ^ 2 / α_YM ^ 2)) :=
  ⟨pi_div_two_eq_α_QG_sq_div_α_YM_sq,
   pi_div_two_eq_α_NS_div_three,
   tendsto_wallis_α_QG_sq_div_α_YM_sq⟩

end AlphaWallisProductBundle
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaWallisProductBundle.pi_div_two_eq_α_QG_sq_div_α_YM_sq
#print axioms PrincipiaTractalis.AlphaWallisProductBundle.tendsto_wallis_α_QG_sq_div_α_YM_sq
#print axioms PrincipiaTractalis.AlphaWallisProductBundle.pi_div_two_eq_α_NS_div_three
#print axioms PrincipiaTractalis.AlphaWallisProductBundle.α_wallis_product_bundle_capstone
