/-
# PF.AlphaStirlingFormulaBundle

★★★★ 2026-06-17 — FUN: Stirling's formula `lim n!/(√(2n)(n/e)^n) = √π`
in framework form via `√π = α_QG / α_P`.

## Stirling in framework form

  lim_{n→∞} n! / (√(2n)·(n/e)^n) = α_QG / α_P

The asymptotic ratio that anchors Stirling's formula (and through it,
the saddle-point method, the binomial-coefficient asymptotics, the
Wallis product, and the n-sphere volume) is exactly the framework's
α_QG / α_P.

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants
import PF.AlphaSqrtPiViaQGDividedByPBundle
import Mathlib.Analysis.SpecialFunctions.Stirling

namespace PrincipiaTractalis
namespace AlphaStirlingFormulaBundle

open Real Filter Topology
open PrincipiaTractalis.CrossMillenniumSharedInvariants
open PrincipiaTractalis.AlphaSqrtPiViaQGDividedByPBundle

/-! ## §1 — Stirling tends to α_QG / α_P -/

/-- **★★★★ STIRLING'S FORMULA IN FRAMEWORK FORM ★★★★** —
    `lim n!/(√(2n)·(n/e)^n) = α_QG/α_P` -/
theorem tendsto_stirlingSeq_α_QG_div_α_P :
    Tendsto Stirling.stirlingSeq atTop (𝓝 (α_QG / α_P)) := by
  have h := Stirling.tendsto_stirlingSeq_sqrt_pi
  have h_eq : Real.sqrt Real.pi = α_QG / α_P := sqrt_pi_eq_α_QG_div_α_P
  rw [h_eq] at h
  exact h

/-! ## §2 — Capstone -/

/-- **★★★★ THE STIRLING-FORMULA-VIA-α_QG/α_P CAPSTONE ★★★★** —
    Stirling's formula in framework form. The framework's α_QG/α_P
    (= √π) is the asymptotic constant for the factorial sequence:

      n! ~ (α_QG/α_P) · √(2n) · (n/e)^n      as n → ∞

    via `lim_{n→∞} n!/(√(2n)·(n/e)^n) = α_QG/α_P`. -/
theorem α_stirling_formula_bundle_capstone :
    Tendsto Stirling.stirlingSeq atTop (𝓝 (α_QG / α_P)) :=
  tendsto_stirlingSeq_α_QG_div_α_P

end AlphaStirlingFormulaBundle
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaStirlingFormulaBundle.tendsto_stirlingSeq_α_QG_div_α_P
#print axioms PrincipiaTractalis.AlphaStirlingFormulaBundle.α_stirling_formula_bundle_capstone
