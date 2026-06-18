/-
# PF.AlphaGeometricSeriesBundle

★★★★ 2026-06-17 — FUN: the geometric series for 1/2 in framework form.

## Headline

  ∑_{n=0}^∞ (1/α_YM)^n = α_YM

The sum of reciprocal powers of the Yang-Mills axis equals α_YM itself.
A beautiful self-referential identity: the YM axis IS the sum of its
own negative powers.

## Equivalent forms

  ∑_{n=0}^∞ (1/α_YM)^n = α_YM
  ∑'_{n} (1/2)^n = α_YM                    (mathlib's tsum_geometric_two)

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants
import Mathlib.Analysis.SpecificLimits.Basic

namespace PrincipiaTractalis
namespace AlphaGeometricSeriesBundle

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants

/-! ## §1 — Geometric series for 1/α_YM = α_YM -/

/-- **★★★ `HasSum (fun n => (1/α_YM)^n) α_YM` ★★★** —
    the geometric series for 1/α_YM equals α_YM itself. -/
theorem hasSum_geometric_α_YM :
    HasSum (fun n : ℕ => ((1 : ℝ) / α_YM) ^ n) α_YM := by
  have h := hasSum_geometric_two
  unfold α_YM
  exact h

/-! ## §2 — tsum version -/

/-- **`∑' n, (1/α_YM)^n = α_YM`** — tsum form. -/
theorem tsum_geometric_α_YM :
    (∑' n : ℕ, ((1 : ℝ) / α_YM) ^ n) = α_YM := by
  exact hasSum_geometric_α_YM.tsum_eq

/-! ## §3 — Self-referential statement -/

/-- **★★★ `α_YM · (α_YM − α_Poincaré) = α_YM` ★★★** —
    the YM axis satisfies its self-referential geometric-series equation. -/
theorem α_YM_mul_α_YM_sub_α_Poincare_eq_α_YM :
    α_YM * (α_YM - α_Poincare) = α_YM := by
  unfold α_YM α_Poincare
  norm_num

/-! ## §4 — Bundle capstone -/

/-- **★★★★ THE GEOMETRIC-SERIES BUNDLE CAPSTONE ★★★★** —
    three identities exhibiting the self-referential geometric
    series for 1/α_YM:

      ∑_{n=0}^∞ (1/α_YM)^n = α_YM           (HasSum form)
      ∑'_{n} (1/α_YM)^n = α_YM              (tsum form)
      α_YM · (α_YM − α_Poincaré) = α_YM     (self-referential)

    The Yang-Mills axis α_YM = 2 is the unique positive number that
    equals the sum of its own reciprocal powers — a self-defining
    property captured by the geometric series. -/
theorem α_geometric_series_bundle_capstone :
    HasSum (fun n : ℕ => ((1 : ℝ) / α_YM) ^ n) α_YM ∧
    (∑' n : ℕ, ((1 : ℝ) / α_YM) ^ n) = α_YM ∧
    α_YM * (α_YM - α_Poincare) = α_YM :=
  ⟨hasSum_geometric_α_YM,
   tsum_geometric_α_YM,
   α_YM_mul_α_YM_sub_α_Poincare_eq_α_YM⟩

end AlphaGeometricSeriesBundle
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaGeometricSeriesBundle.hasSum_geometric_α_YM
#print axioms PrincipiaTractalis.AlphaGeometricSeriesBundle.tsum_geometric_α_YM
#print axioms PrincipiaTractalis.AlphaGeometricSeriesBundle.α_YM_mul_α_YM_sub_α_Poincare_eq_α_YM
#print axioms PrincipiaTractalis.AlphaGeometricSeriesBundle.α_geometric_series_bundle_capstone
