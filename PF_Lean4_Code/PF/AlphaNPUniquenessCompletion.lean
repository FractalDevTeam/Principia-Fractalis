/-
# PF.AlphaNPUniquenessCompletion

★★ 2026-06-17 — Complete the FRAMEWORK UNIQUENESS CAPSTONE with the
α_NP-axis uniqueness witness, parallel to the existing α_Hodge,
α_P, and α_QG unique-positive-root theorems.

The framework's `framework_uniqueness_capstone` covers three of the
four nontrivial α-axes:
  * α_Hodge: unique positive solution of `x² = x + 1`
  * α_P:     unique positive solution of `x² = 2`
  * α_QG:    unique positive solution of `x² = 2π`

α_NP was missing. This file adds:
  * α_NP: unique positive solution of `16·x² − 24·x − 11 = 0`

## Derivation

The quadratic `16x² − 24x − 11 = 0` has discriminant
`576 + 4·16·11 = 1280 = 64·20`, hence roots
`x = (24 ± 8√20)/32 = (3 ± 2√5)/4`.

The negative root `(3 − 2√5)/4 ≈ −0.368` is excluded by positivity;
the positive root `(3 + 2√5)/4` equals `(1 + √5)/2 + 1/4 = φ + 1/4 = α_NP`.

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants
import PF.TuringEncoding.AlphaCanonical

namespace PrincipiaTractalis
namespace AlphaNPUniquenessCompletion

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants
open PrincipiaTractalis.CrossMillenniumMoreInvariants
open PrincipiaTractalis.TuringEncoding

/-! ## §1 — α_NP is the unique positive root of `16x² − 24x − 11 = 0` -/

/-- **★ α_NP IS THE UNIQUE POSITIVE ROOT ★** — any positive real `x`
    satisfying `16·x² − 24·x − 11 = 0` equals `α_NP`. -/
theorem α_NP_is_unique_positive_root :
    ∀ x : ℝ, 0 < x → 16 * x ^ 2 - 24 * x - 11 = 0 → x = α_NP := by
  intro x hx_pos hx_eq
  have h_α_NP_quad : 16 * α_NP ^ 2 - 24 * α_NP - 11 = 0 := by
    show 16 * (phi + 1/4) ^ 2 - 24 * (phi + 1/4) - 11 = 0
    exact alpha_NP_quadratic
  -- Subtract: 16(x² - α_NP²) - 24(x - α_NP) = 0
  -- Factor: (x - α_NP) · (16(x + α_NP) - 24) = 0
  have h_diff : (x - α_NP) * (16 * (x + α_NP) - 24) = 0 := by
    have h : 16 * (x ^ 2 - α_NP ^ 2) - 24 * (x - α_NP) = 0 := by linarith
    nlinarith [h]
  rcases mul_eq_zero.mp h_diff with h1 | h2
  · linarith
  · -- 16(x + α_NP) = 24, so x = 3/2 - α_NP.
    -- But α_NP > 3/2, so x < 0, contradicting x > 0.
    exfalso
    have h_α_NP_gt : α_NP > 3 / 2 := by
      show phi + 1/4 > 3 / 2
      have h_sqrt5_sq : Real.sqrt 5 ^ 2 = 5 :=
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
      have h_sqrt5_pos : (0 : ℝ) < Real.sqrt 5 :=
        Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0)
      have h_sqrt5_gt_two : (2 : ℝ) < Real.sqrt 5 := by
        nlinarith [h_sqrt5_sq, h_sqrt5_pos]
      unfold phi
      linarith
    linarith

/-! ## §2 — The completed four-axis uniqueness capstone -/

/-- **★★★★★ FOUR-AXIS UNIQUENESS CAPSTONE (COMPLETED) ★★★★★** —
    every nontrivial α-axis is the unique positive real solution of its
    substrate equation:

      * α_Hodge: `x² = x + 1`           (golden ratio defining quadratic)
      * α_P:     `x² = 2`                (P-axis self-adjointness equation)
      * α_NP:    `16·x² − 24·x − 11 = 0` (NP-axis self-adjointness quadratic)
      * α_QG:    `x² = 2·π`              (gravitational kernel equation)

    Together with the substrate-equation distinctness witnesses, the
    four nontrivial α-axes are LITERALLY FORCED, not chosen. The
    remaining five axes (α_Poincaré, α_RH, α_YM, α_BSD, α_NS) are
    rational or rational·π constants pinned by definition. -/
theorem framework_four_axis_uniqueness_completed :
    (∀ x : ℝ, 0 < x → x ^ 2 = x + 1 → x = α_Hodge) ∧
    (∀ x : ℝ, 0 < x → x ^ 2 = 2 → x = α_P) ∧
    (∀ x : ℝ, 0 < x → 16 * x ^ 2 - 24 * x - 11 = 0 → x = α_NP) ∧
    (∀ x : ℝ, 0 < x → x ^ 2 = 2 * Real.pi → x = α_QG) :=
  ⟨α_Hodge_is_unique_positive_root,
   α_P_is_unique_positive_root,
   α_NP_is_unique_positive_root,
   α_QG_is_unique_positive_root⟩

end AlphaNPUniquenessCompletion
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaNPUniquenessCompletion.α_NP_is_unique_positive_root
#print axioms
  PrincipiaTractalis.AlphaNPUniquenessCompletion.framework_four_axis_uniqueness_completed
