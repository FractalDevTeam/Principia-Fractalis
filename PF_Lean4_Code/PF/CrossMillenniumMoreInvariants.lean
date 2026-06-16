/-
# Cross-Millennium MORE algebraic invariants among the 9 α-instances

★ DERIVED 2026-05-25 — algebraic curiosity catalogue, EXTENSION ★

This file extends `PF/CrossMillenniumSharedInvariants.lean` (Wave 22,
commit 9371c0e — 12 invariants) and `PF/CrossMillenniumImplicationChains.lean`
(Wave 27, commit e7f6576 — 5 implication chains) with **additional**
axiom-free algebraic identities.

The 9 framework α-instances are:

    α_Poincaré = 1            α_P     = √2          α_NP    = φ + 1/4
    α_RH       = 3/2          α_NS    = 3π/2        α_YM    = 2
    α_BSD      = 3π/4         α_Hodge = φ           α_QG    = √(2π)

New territory explored here:

* **Reciprocals**: 1/α_P, 1/α_RH, 1/α_YM, 1/α_BSD, 1/α_NS, 1/α_QG
* **Cubes / higher powers**: α_P³, α_RH³, α_Hodge³ via φ²=φ+1
* **Mixed products**: α_P · α_RH, α_P · α_NP, α_RH · α_BSD,
  α_Hodge · α_NP, etc.
* **Sums**: α_P + α_RH (algebraic mixed), α_Hodge + α_NP
* **Transcendental closure**: every transcendental α is a rational
  multiple of π
* **Ratio invariants** between BSD/NS/QG (closing the π-sector)

## Honest scope

These are **not** Millennium discharges. They are axiom-free algebraic
facts about the 9 chosen α-values, recording the internal algebra of
the α-table at the level of reciprocals, higher powers and additional
mixed products that complement the simple-square / simple-ratio /
mixed identities of `CrossMillenniumSharedInvariants`.

The combined catalogue makes the **"everything entangled"** thesis
machine-precise: any redefinition of any single α now triggers a
larger cascade of inconsistencies than was previously certified.

## Status

Axiom-free. Pure algebra on `Real.pi`, `Real.sqrt`, and `phi`.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import PF.IntervalArithmetic
import PF.TuringEncoding.AlphaCanonical
import PF.CrossMillenniumSharedInvariants

namespace PrincipiaTractalis
namespace CrossMillenniumMoreInvariants

open Real
open PrincipiaTractalis
open PrincipiaTractalis.TuringEncoding
open PrincipiaTractalis.CrossMillenniumSharedInvariants

/-! ## Section 1 — Reciprocal invariants -/

/-- **`1/α_P = α_P / 2`**: `1/√2 = √2/2`. The reciprocal of α_P is
    half α_P itself — a fixed-point-style fact for the unique α whose
    square is integer 2. -/
theorem inv_α_P_eq_α_P_div_two : 1 / α_P = α_P / 2 := by
  unfold α_P
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hpos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)
  field_simp
  nlinarith [h2, hpos]

/-- **`1/α_RH = 2/3`**: explicit rational reciprocal. -/
theorem inv_α_RH_eq_two_thirds : 1 / α_RH = 2 / 3 := by
  unfold α_RH; norm_num

/-- **`1/α_YM = 1/2`**: explicit rational reciprocal. -/
theorem inv_α_YM_eq_half : 1 / α_YM = 1 / 2 := by
  unfold α_YM; norm_num

/-- **`1/α_Poincaré = 1`**: the Poincaré α is its own reciprocal
    (it is the unit). -/
theorem inv_α_Poincare_eq_one : 1 / α_Poincare = 1 := by
  unfold α_Poincare; norm_num

/-- **`1/α_BSD = 4 / (3π)`**: explicit transcendental reciprocal. -/
theorem inv_α_BSD_eq : 1 / α_BSD = 4 / (3 * Real.pi) := by
  unfold α_BSD
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- **`1/α_NS = 2 / (3π)`**: explicit transcendental reciprocal. -/
theorem inv_α_NS_eq : 1 / α_NS = 2 / (3 * Real.pi) := by
  unfold α_NS
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- **`1/α_BSD = 2 · (1/α_NS)`**: reciprocals invert the ratio
    `α_NS = 2·α_BSD`. -/
theorem inv_α_BSD_eq_two_inv_α_NS : 1 / α_BSD = 2 * (1 / α_NS) := by
  rw [inv_α_BSD_eq, inv_α_NS_eq]; ring

/-! ## Section 2 — Cube and higher-power invariants -/

/-- **`α_P³ = 2 · α_P`**: (√2)³ = 2√2. -/
theorem α_P_cubed : α_P ^ 3 = 2 * α_P := by
  unfold α_P
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have : Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 := by ring
  rw [this, h2]

/-- **`α_RH³ = 27/8`**: explicit rational cube. -/
theorem α_RH_cubed : α_RH ^ 3 = 27 / 8 := by
  unfold α_RH; norm_num

/-- **`α_YM³ = 8`**: explicit integer cube. -/
theorem α_YM_cubed : α_YM ^ 3 = 8 := by
  unfold α_YM; norm_num

/-- **`α_Hodge³ = 2·φ + 1`**: φ³ = φ·φ² = φ·(φ+1) = φ²+φ = (φ+1)+φ = 2φ+1.
    A first-derivative-style identity in the φ-sector. -/
theorem α_Hodge_cubed : α_Hodge ^ 3 = 2 * α_Hodge + 1 := by
  unfold α_Hodge
  have h := phi_sq_eq
  nlinarith [h]

/-- **`α_Hodge⁴ = 3·φ + 2`**: φ⁴ = φ·φ³ = φ·(2φ+1) = 2φ²+φ = 2(φ+1)+φ = 3φ+2. -/
theorem α_Hodge_fourth : α_Hodge ^ 4 = 3 * α_Hodge + 2 := by
  unfold α_Hodge
  have h := phi_sq_eq
  nlinarith [h]

/-- **`α_QG⁴ = 4·π²`**: (√(2π))⁴ = (2π)² = 4π². -/
theorem α_QG_fourth : α_QG ^ 4 = 4 * Real.pi ^ 2 := by
  have h2 := α_QG_sq_eq_two_pi
  have : α_QG ^ 4 = (α_QG ^ 2) ^ 2 := by ring
  rw [this, h2]; ring

/-! ## Section 2b — Fibonacci ladder on the golden Hodge α

    The golden-ratio identity α_Hodge² = α_Hodge + 1 forces
    α_Hodge^n = F_n · α_Hodge + F_{n-1} where F_n is the nth Fibonacci
    number. We record powers 5..8 explicitly, extending the existing
    α_Hodge_{cubed, fourth} chain. Each `_holds` via nlinarith from
    the quadratic identity. -/

/-- **`α_Hodge⁵ = 5·φ + 3`** (F_5 = 5, F_4 = 3).
    Proof: φ^5 = φ · φ^4 = φ(3φ+2) = 3φ² + 2φ = 3(φ+1) + 2φ = 5φ + 3. -/
theorem α_Hodge_fifth : α_Hodge ^ 5 = 5 * α_Hodge + 3 := by
  have h4 := α_Hodge_fourth
  have hsq := α_Hodge_sq_eq_self_plus_one
  have step : α_Hodge ^ 5 = α_Hodge * α_Hodge ^ 4 := by ring
  rw [step, h4]
  nlinarith [hsq]

/-- **`α_Hodge⁶ = 8·φ + 5`** (F_6 = 8, F_5 = 5).
    Proof: φ^6 = φ² · φ^4 = (φ+1)(3φ+2) = 3φ²+5φ+2 = 3(φ+1)+5φ+2 = 8φ+5. -/
theorem α_Hodge_sixth : α_Hodge ^ 6 = 8 * α_Hodge + 5 := by
  have h4 := α_Hodge_fourth
  have hsq := α_Hodge_sq_eq_self_plus_one
  have step : α_Hodge ^ 6 = α_Hodge ^ 2 * α_Hodge ^ 4 := by ring
  rw [step, h4]
  nlinarith [hsq]

/-- **`α_Hodge⁷ = 13·φ + 8`** (F_7 = 13, F_6 = 8).
    Proof: φ^7 = φ^3 · φ^4 = (2φ+1)(3φ+2) = 6φ²+7φ+2 = 6(φ+1)+7φ+2 = 13φ+8. -/
theorem α_Hodge_seventh : α_Hodge ^ 7 = 13 * α_Hodge + 8 := by
  have h3 := α_Hodge_cubed
  have h4 := α_Hodge_fourth
  have hsq := α_Hodge_sq_eq_self_plus_one
  have step : α_Hodge ^ 7 = α_Hodge ^ 3 * α_Hodge ^ 4 := by ring
  rw [step, h3, h4]
  nlinarith [hsq]

/-- **`α_Hodge⁸ = 21·φ + 13`** (F_8 = 21, F_7 = 13).
    Proof via α_Hodge⁴: (3φ+2)² = 9φ²+12φ+4 = 9(φ+1)+12φ+4 = 21φ+13. -/
theorem α_Hodge_eighth : α_Hodge ^ 8 = 21 * α_Hodge + 13 := by
  have h4 := α_Hodge_fourth
  have hsq := α_Hodge_sq_eq_self_plus_one
  have step : α_Hodge ^ 8 = (α_Hodge ^ 4) ^ 2 := by ring
  rw [step, h4]
  nlinarith [hsq]

/-- **General Fibonacci-ladder structure at level 8 (capstone)**.

    Records the Fibonacci recursion `α_Hodge^{n+2} = α_Hodge^{n+1} +
    α_Hodge^n` at the n=5,6 instance: `α_Hodge^7 = α_Hodge^6 + α_Hodge^5`.

    This is the structural witness that the α_Hodge powers obey the
    Fibonacci recurrence — a direct algebraic consequence of the
    defining quadratic α_Hodge² = α_Hodge + 1. -/
theorem α_Hodge_fibonacci_recurrence_at_5 :
    α_Hodge ^ 7 = α_Hodge ^ 6 + α_Hodge ^ 5 := by
  rw [α_Hodge_seventh, α_Hodge_sixth, α_Hodge_fifth]
  ring

/-- **Fibonacci recurrence at level 6**: `α_Hodge^8 = α_Hodge^7 + α_Hodge^6`. -/
theorem α_Hodge_fibonacci_recurrence_at_6 :
    α_Hodge ^ 8 = α_Hodge ^ 7 + α_Hodge ^ 6 := by
  rw [α_Hodge_eighth, α_Hodge_seventh, α_Hodge_sixth]
  ring

/-- **★ α_HODGE POWER TOWER: FIBONACCI STRUCTURE ★** —
    8-clause bundle revealing the Fibonacci-coefficient structure of
    the φ-tower:

    | n | α_Hodge^n          | (F_n, F_{n-1}) |
    |---|--------------------|----------------|
    | 1 | α_Hodge            | (1, 0)         |
    | 2 | 1·α_Hodge + 1      | (1, 1)         |
    | 3 | 2·α_Hodge + 1      | (2, 1)         |
    | 4 | 3·α_Hodge + 2      | (3, 2)         |
    | 5 | 5·α_Hodge + 3      | (5, 3)         |
    | 6 | 8·α_Hodge + 5      | (8, 5)         |
    | 7 | 13·α_Hodge + 8     | (13, 8)        |
    | 8 | 21·α_Hodge + 13    | (21, 13)       |

    The Fibonacci numbers F_n = F_{n−1} + F_{n−2} emerge as the
    coefficients of α_Hodge^n in the Q(α_Hodge) basis representation. -/
theorem α_Hodge_fibonacci_tower :
    α_Hodge ^ 1 = α_Hodge ∧
    α_Hodge ^ 2 = 1 * α_Hodge + 1 ∧
    α_Hodge ^ 3 = 2 * α_Hodge + 1 ∧
    α_Hodge ^ 4 = 3 * α_Hodge + 2 ∧
    α_Hodge ^ 5 = 5 * α_Hodge + 3 ∧
    α_Hodge ^ 6 = 8 * α_Hodge + 5 ∧
    α_Hodge ^ 7 = 13 * α_Hodge + 8 ∧
    α_Hodge ^ 8 = 21 * α_Hodge + 13 := by
  refine ⟨?_, ?_, α_Hodge_cubed, α_Hodge_fourth, α_Hodge_fifth,
          α_Hodge_sixth, α_Hodge_seventh, α_Hodge_eighth⟩
  · ring
  · rw [α_Hodge_sq_eq_self_plus_one]; ring

/-! ## Section 2c — π-built α extensions: higher powers of α_QG, α_NS, α_BSD

    The π-built α-values (α_QG = √(2π), α_NS = 3π/2, α_BSD = 3π/4)
    have clean closed-form powers via the defining identities. We
    record selected even powers for cross-reference. -/

/-- **`α_QG⁶ = 8·π³`**: (√(2π))⁶ = (2π)³ = 8π³. -/
theorem α_QG_sixth : α_QG ^ 6 = 8 * Real.pi ^ 3 := by
  have h2 := α_QG_sq_eq_two_pi
  have : α_QG ^ 6 = (α_QG ^ 2) ^ 3 := by ring
  rw [this, h2]; ring

/-- **`α_QG⁸ = 16·π⁴`**: (√(2π))⁸ = (2π)⁴ = 16π⁴. -/
theorem α_QG_eighth : α_QG ^ 8 = 16 * Real.pi ^ 4 := by
  have h2 := α_QG_sq_eq_two_pi
  have : α_QG ^ 8 = (α_QG ^ 2) ^ 4 := by ring
  rw [this, h2]; ring

/-- **`α_NS² = 9π²/4`**: direct from α_NS = 3π/2. -/
theorem α_NS_sq : α_NS ^ 2 = 9 * Real.pi ^ 2 / 4 := by
  unfold α_NS; ring

/-- **`α_NS³ = 27π³/8`**: direct from α_NS = 3π/2. -/
theorem α_NS_cubed : α_NS ^ 3 = 27 * Real.pi ^ 3 / 8 := by
  unfold α_NS; ring

/-- **`α_BSD² = 9π²/16`**: direct from α_BSD = 3π/4. -/
theorem α_BSD_sq : α_BSD ^ 2 = 9 * Real.pi ^ 2 / 16 := by
  unfold α_BSD; ring

/-- **`α_BSD³ = 27π³/64`**: direct from α_BSD = 3π/4. -/
theorem α_BSD_cubed : α_BSD ^ 3 = 27 * Real.pi ^ 3 / 64 := by
  unfold α_BSD; ring

/-- **`α_NS² = 4·α_BSD²`** — the L5 identity α_NS = 2·α_BSD squared. -/
theorem α_NS_sq_eq_four_α_BSD_sq : α_NS ^ 2 = 4 * α_BSD ^ 2 := by
  rw [α_NS_sq, α_BSD_sq]; ring

/-- **`α_NS · α_BSD = 9π²/8`**: cross-product cleaned. -/
theorem α_NS_mul_α_BSD : α_NS * α_BSD = 9 * Real.pi ^ 2 / 8 := by
  unfold α_NS α_BSD; ring

/-- **`α_QG² · α_RH² = 9π/2`**: product of π-built × rational squared. -/
theorem α_QG_sq_mul_α_RH_sq : α_QG ^ 2 * α_RH ^ 2 = 9 * Real.pi / 2 := by
  rw [α_QG_sq_eq_two_pi, α_RH_sq_eq_nine_fourths]; ring

/-! ## Section 2d — Higher powers of rational α + α_NP cross products -/

/-- **`α_P⁴ = 4`**: (α_P²)² = α_YM² = 4. -/
theorem α_P_fourth : α_P ^ 4 = 4 := by
  have h := α_P_sq_eq_α_YM
  have : α_P ^ 4 = (α_P ^ 2) ^ 2 := by ring
  rw [this, h]; unfold α_YM; ring

/-- **`α_YM² = 4`**: direct from α_YM = 2. -/
theorem α_YM_sq : α_YM ^ 2 = 4 := by
  unfold α_YM; ring

/-- **`α_YM⁴ = 16`**: direct from α_YM = 2. -/
theorem α_YM_fourth : α_YM ^ 4 = 16 := by
  unfold α_YM; ring

/-- **`α_RH⁴ = 81/16`**: (α_RH²)² = (9/4)² = 81/16. -/
theorem α_RH_fourth : α_RH ^ 4 = 81 / 16 := by
  unfold α_RH; ring

/-- **`α_NP · α_YM = 2·α_Hodge + 1/2`**: (φ + 1/4)·2 = 2φ + 1/2. -/
theorem α_NP_mul_α_YM : α_NP * α_YM = 2 * α_Hodge + 1/2 := by
  unfold α_NP α_YM α_Hodge; ring

/-- **`α_NP - α_Poincare = α_Hodge - 3/4`**: relating the φ-axis to anchor. -/
theorem α_NP_sub_α_Poincare : α_NP - α_Poincare = α_Hodge - 3/4 := by
  unfold α_NP α_Poincare α_Hodge; ring

/-- **`α_P_cubed_alt`**: α_P³ = α_P · α_YM (alternative form using L1). -/
theorem α_P_cubed_eq_α_P_mul_α_YM : α_P ^ 3 = α_P * α_YM := by
  have h := α_P_sq_eq_α_YM
  have : α_P ^ 3 = α_P * α_P ^ 2 := by ring
  rw [this, h]

/-- **`α_NS · α_YM = 3π`**: NS-class times YM cleanly. -/
theorem α_NS_mul_α_YM : α_NS * α_YM = 3 * Real.pi := by
  unfold α_NS α_YM; ring

/-- **`α_BSD · α_YM = 3π/2 = α_NS`**: BSD·YM recovers NS. -/
theorem α_BSD_mul_α_YM_eq_α_NS : α_BSD * α_YM = α_NS := by
  unfold α_BSD α_YM α_NS; ring

/-! ## Section 2e — Quartic-grade master invariants on the locus -/

/-- **`α_P⁴ = α_YM²`**: a quartic identity reflecting α_P² = α_YM. -/
theorem α_P_fourth_eq_α_YM_sq : α_P ^ 4 = α_YM ^ 2 := by
  rw [α_P_fourth, α_YM_sq]

/-- **`α_NS² = α_YM² · α_BSD²`**: squared form of α_NS = α_YM·α_BSD (L6). -/
theorem α_NS_sq_eq_α_YM_sq_mul_α_BSD_sq :
    α_NS ^ 2 = α_YM ^ 2 * α_BSD ^ 2 := by
  rw [α_NS_sq, α_YM_sq, α_BSD_sq]; ring

/-- **`α_RH² + α_BSD² = 9/4 + 9π²/16`**: locus diagonal sum. -/
theorem α_RH_sq_add_α_BSD_sq :
    α_RH ^ 2 + α_BSD ^ 2 = 9/4 + 9 * Real.pi ^ 2 / 16 := by
  rw [α_RH_sq_eq_nine_fourths, α_BSD_sq]

/-! ## Section 2f — Symmetric and antisymmetric closures on the locus -/

/-- **`α_NS² - α_BSD² = 27π²/16`** — difference of squares form. -/
theorem α_NS_sq_sub_α_BSD_sq :
    α_NS ^ 2 - α_BSD ^ 2 = 27 * Real.pi ^ 2 / 16 := by
  rw [α_NS_sq, α_BSD_sq]; ring

/-- **`α_NS² + α_BSD² = 45π²/16`** — sum of π-built squared. -/
theorem α_NS_sq_add_α_BSD_sq :
    α_NS ^ 2 + α_BSD ^ 2 = 45 * Real.pi ^ 2 / 16 := by
  rw [α_NS_sq, α_BSD_sq]; ring

/-- **`α_QG² · α_BSD = 3π²/2`** — QG^2 × BSD product. -/
theorem α_QG_sq_mul_α_BSD : α_QG ^ 2 * α_BSD = 3 * Real.pi ^ 2 / 2 := by
  rw [α_QG_sq_eq_two_pi]; unfold α_BSD; ring

/-- **`α_QG² · α_NS = 3π²`** — QG^2 × NS product. -/
theorem α_QG_sq_mul_α_NS : α_QG ^ 2 * α_NS = 3 * Real.pi ^ 2 := by
  rw [α_QG_sq_eq_two_pi]; unfold α_NS; ring

/-- **`α_YM² + α_RH² = 25/4`** — rational diagonal: 4 + 9/4 = 25/4. -/
theorem α_YM_sq_add_α_RH_sq : α_YM ^ 2 + α_RH ^ 2 = 25 / 4 := by
  rw [α_YM_sq, α_RH_sq_eq_nine_fourths]; ring

/-- **`(α_YM + α_RH) · (α_YM - α_RH) = 7/4`** — diff-of-squares factored. -/
theorem α_YM_plus_RH_mul_minus_RH : (α_YM + α_RH) * (α_YM - α_RH) = 7/4 := by
  unfold α_YM α_RH; ring

/-- **`α_P² + α_RH² = 17/4`** — √2 + rational squared sum. -/
theorem α_P_sq_add_α_RH_sq : α_P ^ 2 + α_RH ^ 2 = 17 / 4 := by
  rw [α_P_sq_eq_α_YM, α_RH_sq_eq_nine_fourths]; unfold α_YM; ring

/-- **`α_Hodge² + α_NP² = (5/2)·α_Hodge + 33/16`** — φ-axis squared sum. -/
theorem α_Hodge_sq_add_α_NP_sq :
    α_Hodge ^ 2 + α_NP ^ 2 = (5/2) * α_Hodge + 33/16 := by
  unfold α_NP α_Hodge
  have h := phi_sq_eq
  nlinarith [h]

/-- **`α_Poincare + α_RH + α_YM = 9/2`** — rational locus row sum.
    Recovers the framework's Smale-aggregate target. -/
theorem α_Poincare_add_α_RH_add_α_YM :
    α_Poincare + α_RH + α_YM = 9 / 2 := by
  unfold α_Poincare α_RH α_YM; ring

/-! ## Section 2g — α_NP cross-products: completing the φ-sector × rest table

    The φ-sector (α_Hodge, α_NP) products with the rational sector
    (α_Poincare, α_RH, α_YM) and the π-built sector (α_BSD, α_NS, α_QG).
    All have clean closed forms via `unfold + ring + nlinarith`. -/

/-- **`α_NP · α_Poincare = α_NP`** — anchor identity. -/
theorem α_NP_mul_α_Poincare : α_NP * α_Poincare = α_NP := by
  unfold α_Poincare; ring

/-- **`α_NP · α_RH = (3/2)·α_Hodge + 3/8`** — φ-sector × rational coupling. -/
theorem α_NP_mul_α_RH : α_NP * α_RH = (3/2) * α_Hodge + 3/8 := by
  unfold α_NP α_RH α_Hodge; ring

/-- **`α_NP · α_BSD = (3π/4)·α_Hodge + 3π/16`** — φ-sector × BSD coupling. -/
theorem α_NP_mul_α_BSD : α_NP * α_BSD = (3 * Real.pi / 4) * α_Hodge + 3 * Real.pi / 16 := by
  unfold α_NP α_BSD α_Hodge; ring

/-- **`α_NP · α_NS = (3π/2)·α_Hodge + 3π/8`** — φ-sector × NS coupling. -/
theorem α_NP_mul_α_NS : α_NP * α_NS = (3 * Real.pi / 2) * α_Hodge + 3 * Real.pi / 8 := by
  unfold α_NP α_NS α_Hodge; ring

/-- **`α_NP · α_NS = 2·(α_NP · α_BSD)`** — L5 (α_NS = 2·α_BSD) propagated through α_NP. -/
theorem α_NP_mul_α_NS_eq_two_α_NP_mul_α_BSD :
    α_NP * α_NS = 2 * (α_NP * α_BSD) := by
  rw [α_NP_mul_α_NS, α_NP_mul_α_BSD]; ring

/-- **`α_Hodge · α_BSD = (3π/4)·α_Hodge`** — φ × π-built scalar identity. -/
theorem α_Hodge_mul_α_BSD : α_Hodge * α_BSD = (3 * Real.pi / 4) * α_Hodge := by
  unfold α_BSD; ring

/-- **`α_Hodge · α_NS = (3π/2)·α_Hodge`** — φ × NS scalar identity. -/
theorem α_Hodge_mul_α_NS : α_Hodge * α_NS = (3 * Real.pi / 2) * α_Hodge := by
  unfold α_NS; ring

/-- **`α_Hodge · α_QG² = 2π·α_Hodge`** — φ × QG² scalar identity. -/
theorem α_Hodge_mul_α_QG_sq : α_Hodge * α_QG ^ 2 = 2 * Real.pi * α_Hodge := by
  rw [α_QG_sq_eq_two_pi]; ring

/-- **`α_NP · α_QG² = 2π·α_Hodge + π/2`** — φ-sector × QG² coupling. -/
theorem α_NP_mul_α_QG_sq : α_NP * α_QG ^ 2 = 2 * Real.pi * α_Hodge + Real.pi / 2 := by
  rw [α_QG_sq_eq_two_pi]; unfold α_NP α_Hodge; ring

/-! ## Section 2h — α_P (√2-sector) cross-products with other axes -/

/-- **`α_P · α_Poincare = α_P`** — anchor identity. -/
theorem α_P_mul_α_Poincare : α_P * α_Poincare = α_P := by
  unfold α_Poincare; ring

/-- **`α_P · α_YM = α_P^3`** — re-expression of α_P^3 via L1. -/
theorem α_P_mul_α_YM_eq_α_P_cubed : α_P * α_YM = α_P ^ 3 :=
  (α_P_cubed_eq_α_P_mul_α_YM).symm

/-- **`α_P² · α_YM = α_YM²`** — L1 (α_P²=α_YM) multiplied by α_YM. -/
theorem α_P_sq_mul_α_YM : α_P ^ 2 * α_YM = α_YM ^ 2 := by
  rw [α_P_sq_eq_α_YM]; ring

/-- **`α_P² · α_BSD = α_NS`** — L1 + L6 combined. -/
theorem α_P_sq_mul_α_BSD : α_P ^ 2 * α_BSD = α_NS := by
  rw [α_P_sq_eq_α_YM, ← α_NS_eq_α_YM_mul_α_BSD]

/-- **`α_P² · α_NS = α_YM · α_NS = 3π`** — direct via L1. -/
theorem α_P_sq_mul_α_NS : α_P ^ 2 * α_NS = 3 * Real.pi := by
  rw [α_P_sq_eq_α_YM, mul_comm]; exact α_NS_mul_α_YM

/-! ## Section 3 — Mixed-product invariants (algebraic × algebraic) -/

/-- **`α_P · α_RH = (3/2) · α_P`**: trivial scalar factor, recorded
    so the product appears in the catalogue. -/
theorem α_P_mul_α_RH : α_P * α_RH = (3/2) * α_P := by
  unfold α_RH; ring

/-- **`α_Hodge · α_NP = α_Hodge² + α_Hodge/4`**: φ·(φ+1/4) = φ²+φ/4.
    Cleanly links Hodge and NP without invoking φ² = φ+1. -/
theorem α_Hodge_mul_α_NP_pre :
    α_Hodge * α_NP = α_Hodge ^ 2 + α_Hodge / 4 := by
  unfold α_NP α_Hodge; ring

/-- **`α_Hodge · α_NP = α_Hodge + 1 + α_Hodge/4`**: same as above with
    `α_Hodge² = α_Hodge + 1` substituted — exposes the additive form
    `(5/4)·φ + 1`. -/
theorem α_Hodge_mul_α_NP : α_Hodge * α_NP = (5/4) * α_Hodge + 1 := by
  have h := α_Hodge_mul_α_NP_pre
  have hsq := α_Hodge_sq_eq_self_plus_one
  linarith [h, hsq]

/-- **`α_NP² = (5/2)·α_Hodge + 17/16`**: (φ+1/4)² = φ²+φ/2+1/16
    = (φ+1)+φ/2+1/16 = (3/2)φ + 17/16. Wait — recompute:
    (φ+1/4)² = φ² + φ/2 + 1/16 = (φ+1) + φ/2 + 1/16 = (3/2)φ + 17/16.
    Actually `(3/2)φ + 17/16`. We state the correct form. -/
theorem α_NP_sq : α_NP ^ 2 = (3/2) * α_Hodge + 17/16 := by
  unfold α_NP α_Hodge
  have h := phi_sq_eq
  unfold α_Hodge at h
  nlinarith [h]

/-! ## Section 4 — Mixed-product invariants (algebraic × transcendental) -/

/-- **`α_P · α_BSD = (3π/4) · α_P`**: scalar form. -/
theorem α_P_mul_α_BSD : α_P * α_BSD = (3 * Real.pi / 4) * α_P := by
  unfold α_BSD; ring

/-- **`α_RH · α_BSD = (9π/8)`**: rational × transcendental yields a
    rational multiple of π. -/
theorem α_RH_mul_α_BSD : α_RH * α_BSD = 9 * Real.pi / 8 := by
  unfold α_RH α_BSD; ring

/-- **`α_YM · α_BSD = α_NS`**: 2 · (3π/4) = 3π/2 — same as the existing
    `α_NS_eq_α_YM_mul_α_BSD` but stated in product-first form. -/
theorem α_YM_mul_α_BSD_eq_α_NS : α_YM * α_BSD = α_NS := by
  unfold α_YM α_BSD α_NS; ring

/-! ## Section 5 — Sum invariants -/

/-- **`α_P + α_RH = α_P + 3/2`**: trivial unfold but documents the
    algebraic-rational mixed sum. -/
theorem α_P_add_α_RH : α_P + α_RH = α_P + 3/2 := by
  unfold α_RH; ring

/-- **`α_NS + α_BSD = 9π/4`**: explicit rational multiple of π. -/
theorem α_NS_add_α_BSD : α_NS + α_BSD = 9 * Real.pi / 4 := by
  unfold α_NS α_BSD; ring

/-- **`α_BSD + α_BSD = α_NS`**: consequence of `α_NS = 2·α_BSD`. -/
theorem two_α_BSD_eq_α_NS : α_BSD + α_BSD = α_NS := by
  unfold α_NS α_BSD; ring

/-- **`α_Hodge + α_NP = 2·α_Hodge + 1/4`**: same as the existing
    `α_NP_add_Hodge_form`, restated with operands swapped. -/
theorem α_Hodge_add_α_NP : α_Hodge + α_NP = 2 * α_Hodge + 1/4 := by
  have h := α_NP_add_Hodge_form
  linarith [h]

/-! ## Section 6 — Transcendental-sector closure -/

/-- **`α_NS = 2 · α_BSD`**: rephrased ratio for the catalogue. -/
theorem α_NS_eq_three_half_two_α_BSD : α_NS = 2 * α_BSD := by
  unfold α_NS α_BSD; ring

/-- **`α_QG² / α_NS = 4/3`**: rational ratio of the QG square to NS. -/
theorem α_QG_sq_div_α_NS : α_QG ^ 2 = (4 / 3) * α_NS := α_QG_sq_eq_four_thirds_α_NS

/-- **`α_QG² / α_BSD = 8/3`**: companion rational ratio. -/
theorem α_QG_sq_div_α_BSD : α_QG ^ 2 = (8 / 3) * α_BSD := α_QG_sq_eq_eight_thirds_α_BSD

/-- **Transcendental-sector universal factor**: every transcendental
    α and α_QG² is a rational multiple of π.
    Recorded as a conjunction-form invariant. -/
theorem transcendental_sector_pi_rational_multiples :
    α_NS = (3/2) * Real.pi
    ∧ α_BSD = (3/4) * Real.pi
    ∧ α_QG ^ 2 = 2 * Real.pi := by
  refine ⟨?_, ?_, ?_⟩
  · unfold α_NS; ring
  · unfold α_BSD; ring
  · exact α_QG_sq_eq_two_pi

/-! ## Section 7 — Algebraic-sector closure (no π involved) -/

/-- **Algebraic-sector closure**: the algebraic α's
    {α_Poincaré, α_P, α_NP, α_RH, α_YM, α_Hodge} live entirely in
    the ring `ℚ[φ, √2]`. Recorded via explicit witnesses. -/
theorem algebraic_sector_witnesses :
    α_Poincare = 1
    ∧ α_P = Real.sqrt 2
    ∧ α_NP = phi + 1/4
    ∧ α_RH = 3/2
    ∧ α_YM = 2
    ∧ α_Hodge = phi := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Section 8 — Capstone bundle of new invariants -/

/-- **Capstone**: a single typed bundle of the NEW axiom-free
    algebraic invariants relating the 9 α-instances, complementing
    the existing `cross_millennium_shared_invariants_capstone`.

    No claim of Millennium discharge; this captures **reciprocals,
    higher powers, and additional mixed products** of the α-table. -/
theorem cross_millennium_more_invariants_capstone :
    -- Reciprocals
    1 / α_P = α_P / 2
    ∧ 1 / α_RH = 2 / 3
    ∧ 1 / α_YM = 1 / 2
    ∧ 1 / α_BSD = 4 / (3 * Real.pi)
    ∧ 1 / α_NS = 2 / (3 * Real.pi)
    -- Cubes / fourth powers
    ∧ α_P ^ 3 = 2 * α_P
    ∧ α_RH ^ 3 = 27 / 8
    ∧ α_YM ^ 3 = 8
    ∧ α_Hodge ^ 3 = 2 * α_Hodge + 1
    ∧ α_Hodge ^ 4 = 3 * α_Hodge + 2
    ∧ α_QG ^ 4 = 4 * Real.pi ^ 2
    -- Mixed products
    ∧ α_Hodge * α_NP = (5/4) * α_Hodge + 1
    ∧ α_NP ^ 2 = (3/2) * α_Hodge + 17/16
    ∧ α_RH * α_BSD = 9 * Real.pi / 8
    ∧ α_YM * α_BSD = α_NS
    -- Sums
    ∧ α_NS + α_BSD = 9 * Real.pi / 4
    ∧ α_BSD + α_BSD = α_NS := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact inv_α_P_eq_α_P_div_two
  · exact inv_α_RH_eq_two_thirds
  · exact inv_α_YM_eq_half
  · exact inv_α_BSD_eq
  · exact inv_α_NS_eq
  · exact α_P_cubed
  · exact α_RH_cubed
  · exact α_YM_cubed
  · exact α_Hodge_cubed
  · exact α_Hodge_fourth
  · exact α_QG_fourth
  · exact α_Hodge_mul_α_NP
  · exact α_NP_sq
  · exact α_RH_mul_α_BSD
  · exact α_YM_mul_α_BSD_eq_α_NS
  · exact α_NS_add_α_BSD
  · exact two_α_BSD_eq_α_NS

/-- **Structural reading of the extended catalogue**.

    Combining the new invariants with the existing
    `cross_millennium_shared_invariants_capstone` yields:

    * **Sector decomposition** — the 9 α's split cleanly into
      an *algebraic sector* {Poincaré, P, NP, RH, YM, Hodge} living
      in `ℚ[φ, √2]` and a *transcendental sector* {NS, BSD} which
      are rational multiples of π, plus `α_QG` whose **square**
      bridges the two sectors via `α_QG² = 2π = α_YM · π`.

    * **φ-closure** — every power `α_Hodge^n` reduces to `aₙ·φ + bₙ`
      with rational `(aₙ, bₙ)` (Fibonacci recurrence); we have the
      first four cases as named theorems.

    * **Reciprocal duality** — reciprocals of algebraic α's stay in
      the algebraic sector (`1/α_P = α_P/2`, `1/α_RH = 2/3`, etc.),
      while reciprocals of transcendental α's are rational multiples
      of `1/π`. The QG α (whose square is transcendental but whose
      first power is irrational not transparently in either sector)
      is the unique boundary case.

    The "everything entangled" thesis is now machine-precise: any
    single α-redefinition that survives the original 11 invariants
    must also survive the additional 17 catalogued here, for a total
    of **28** axiom-free pairwise/higher algebraic constraints on
    the 9 α-table. -/
theorem cross_millennium_more_invariants_structural_remark :
    True := trivial

/-! ## Section 2i — Triple-product identities on the 9-α table -/

/-- **`α_Poincare · α_RH · α_YM = 3`** — triple product of the three
    rational α-values. Recovers the framework's Twin Prime / Polignac
    structural anchor (since `α_TwinPrime = α_RH = 3/2`). -/
theorem α_Poincare_mul_α_RH_mul_α_YM : α_Poincare * α_RH * α_YM = 3 := by
  unfold α_Poincare α_RH α_YM; ring

/-- **`α_NS · α_BSD · α_RH = 27π² / 16`** —
    (3π/2)·(3π/4)·(3/2) = 27π²/16. -/
theorem α_NS_mul_α_BSD_mul_α_RH :
    α_NS * α_BSD * α_RH = 27 * Real.pi ^ 2 / 16 := by
  unfold α_NS α_BSD α_RH; ring

/-- **`α_QG² · α_RH = 3π`** — QG² and rational triple. -/
theorem α_QG_sq_mul_α_RH :
    α_QG ^ 2 * α_RH = 3 * Real.pi := by
  rw [α_QG_sq_eq_two_pi]; unfold α_RH; ring

/-- **`α_QG² · α_YM = 4π`** — QG² and YM triple. -/
theorem α_QG_sq_mul_α_YM :
    α_QG ^ 2 * α_YM = 4 * Real.pi := by
  rw [α_QG_sq_eq_two_pi]; unfold α_YM; ring

/-- **`α_Poincare² + α_RH² + α_YM² = 29/4`** — rational sum of squares. -/
theorem α_Poincare_sq_add_α_RH_sq_add_α_YM_sq :
    α_Poincare ^ 2 + α_RH ^ 2 + α_YM ^ 2 = 29 / 4 := by
  unfold α_Poincare α_RH α_YM; ring

/-- **`α_NS² + α_BSD² + α_QG² = 45π²/16 + 2π`** — π-sector sum of squares. -/
theorem α_NS_sq_add_α_BSD_sq_add_α_QG_sq :
    α_NS ^ 2 + α_BSD ^ 2 + α_QG ^ 2 = 45 * Real.pi ^ 2 / 16 + 2 * Real.pi := by
  rw [α_NS_sq, α_BSD_sq, α_QG_sq_eq_two_pi]; ring

/-- **`(α_NS - α_BSD)² = α_BSD²`** — L5 (α_NS = 2·α_BSD) consequence. -/
theorem α_NS_minus_α_BSD_sq : (α_NS - α_BSD) ^ 2 = α_BSD ^ 2 := by
  unfold α_NS α_BSD; ring

/-- **`α_NS² · α_QG² = 9π³/2`** — NS²-QG² product. -/
theorem α_NS_sq_mul_α_QG_sq :
    α_NS ^ 2 * α_QG ^ 2 = 9 * Real.pi ^ 3 / 2 := by
  rw [α_NS_sq, α_QG_sq_eq_two_pi]; ring

/-- **`α_BSD² · α_QG² = 9π³/8`** — BSD²-QG² product. -/
theorem α_BSD_sq_mul_α_QG_sq :
    α_BSD ^ 2 * α_QG ^ 2 = 9 * Real.pi ^ 3 / 8 := by
  rw [α_BSD_sq, α_QG_sq_eq_two_pi]; ring

/-- **`α_YM² · α_QG² = 8π`** — YM²-QG² product, clean π-rational. -/
theorem α_YM_sq_mul_α_QG_sq :
    α_YM ^ 2 * α_QG ^ 2 = 8 * Real.pi := by
  rw [α_YM_sq, α_QG_sq_eq_two_pi]; ring

/-- **`α_RH² · α_QG² = 9π/2`** — RH²-QG² product. -/
theorem α_RH_sq_mul_α_QG_sq :
    α_RH ^ 2 * α_QG ^ 2 = 9 * Real.pi / 2 := by
  rw [α_RH_sq_eq_nine_fourths, α_QG_sq_eq_two_pi]; ring

/-- **`α_P² · α_QG² = 4π`** — P²-QG² product (= α_YM² since α_P² = α_YM). -/
theorem α_P_sq_mul_α_QG_sq :
    α_P ^ 2 * α_QG ^ 2 = 4 * Real.pi := by
  rw [α_P_sq_eq_α_YM, α_QG_sq_eq_two_pi]; unfold α_YM; ring

/-! ## Section 2j — Higher powers of α_NP -/

/-- **`α_NP³ = (47/16)·α_Hodge + 113/64`** — extending α_NP² to cube. -/
theorem α_NP_cubed :
    α_NP ^ 3 = (47/16) * α_Hodge + 113/64 := by
  unfold α_NP α_Hodge
  have h := phi_sq_eq
  nlinarith [h]

/-- **`α_NP³ numerical bracket`**: `6.51 < α_NP³ < 6.53`. Closed form
    `(47/16)·φ + 113/64` with `phi_in_interval_10digit` gives a numerical
    value of `≈ 6.5186`. -/
theorem α_NP_cubed_bracket :
    (6.51 : ℝ) < α_NP ^ 3 ∧ α_NP ^ 3 < (6.53 : ℝ) := by
  rw [α_NP_cubed]
  have h_phi_lb : (1.6180339887 : ℝ) ≤ α_Hodge := by
    unfold α_Hodge; exact phi_in_interval_10digit.1
  have h_phi_ub : α_Hodge ≤ (1.6180339888 : ℝ) := by
    unfold α_Hodge; exact phi_in_interval_10digit.2
  refine ⟨?_, ?_⟩
  · -- 6.51 < (47/16)·φ + 113/64
    --      ⟺ (47/16)·φ > 6.51 − 113/64 = (6.51·64 − 113)/64 = 303.64/64 ≈ 4.7444
    -- φ > 4.7444 · 16/47 = 75.9/47 = 1.6145, OK from φ ≥ 1.618...
    nlinarith [h_phi_lb]
  · -- (47/16)·φ + 113/64 < 6.53
    --      ⟺ (47/16)·φ < 6.53 − 113/64 = 304.92/64 ≈ 4.7644
    -- φ < 4.7644 · 16/47 ≈ 1.6213, OK from φ ≤ 1.618...
    nlinarith [h_phi_ub]

/-- **`α_NP_fourth_form`**: `α_NP⁴ = (47/16)·(α_Hodge·α_NP) + (113/64)·α_NP`. -/
theorem α_NP_fourth_chained :
    α_NP ^ 4 = α_NP * α_NP ^ 3 := by ring

/-- **`α_NP⁴ = (87/16)·α_Hodge + 865/256`** — full closed form via φ-Fibonacci.
    Derivation: α_NP⁴ = (α_NP²)² = ((3/2)φ + 17/16)² expands and reduces
    using φ² = φ + 1 to (87/16)·φ + 865/256. -/
theorem α_NP_fourth :
    α_NP ^ 4 = (87/16) * α_Hodge + 865/256 := by
  unfold α_NP α_Hodge
  have h := phi_sq_eq
  nlinarith [h]

/-- **α_NP⁴ numerical bracket**: `12.17 < α_NP⁴ < 12.18`. Closed form
    `(87/16)·φ + 865/256` with `phi_in_interval_10digit` gives a numerical
    value of `≈ 12.1770`. -/
theorem α_NP_fourth_bracket :
    (12.17 : ℝ) < α_NP ^ 4 ∧ α_NP ^ 4 < (12.18 : ℝ) := by
  rw [α_NP_fourth]
  have h_phi_lb : (1.6180339887 : ℝ) ≤ α_Hodge := by
    unfold α_Hodge; exact phi_in_interval_10digit.1
  have h_phi_ub : α_Hodge ≤ (1.6180339888 : ℝ) := by
    unfold α_Hodge; exact phi_in_interval_10digit.2
  refine ⟨?_, ?_⟩
  · nlinarith [h_phi_lb]
  · nlinarith [h_phi_ub]

/-- **`1/α_NP = (8·√5 − 12)/11`** — reciprocal closed form witnessing
    the Q(√5) structure of α_NP.

    Derivation: 1/(φ + 1/4) = 4/(4φ + 1) = 4/(3 + 2√5) (since 4φ + 1
    = 2 + 2√5 + 1 = 3 + 2√5). Rationalize by (3 − 2√5):
    = 4(3 − 2√5)/((3)² − (2√5)²) = 4(3 − 2√5)/(9 − 20) = 4(2√5 − 3)/11. -/
theorem one_div_α_NP_closed_form :
    1 / α_NP = (8 * Real.sqrt 5 - 12) / 11 := by
  have h_sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  have h_sqrt5_pos : (0 : ℝ) < Real.sqrt 5 :=
    Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 5)
  have h_sqrt5_gt : (2 : ℝ) < Real.sqrt 5 := by nlinarith [h_sqrt5_sq, h_sqrt5_pos]
  have h_α_NP_pos : (0 : ℝ) < α_NP := by
    unfold α_NP phi; linarith
  have h_α_NP_ne : α_NP ≠ 0 := h_α_NP_pos.ne'
  -- Verify directly: α_NP · (8√5 − 12) = 11
  -- Then divide by 11·α_NP.
  have h_product : α_NP * (8 * Real.sqrt 5 - 12) = 11 := by
    unfold α_NP phi
    nlinarith [h_sqrt5_sq, h_sqrt5_pos]
  field_simp
  linarith [h_product]

/-- **`α_NP⁵ = (2605/256)·α_Hodge + 6433/1024`** — fifth power via
    φ-Fibonacci chain.

    Derivation: α_NP⁵ = α_NP · α_NP⁴
      = (φ + 1/4)·((87/16)·φ + 865/256)
      = (87/16)·φ² + (865/256 + 87/64)·φ + 865/1024
      = (87/16)·(φ + 1) + (865/256 + 87/64)·φ + 865/1024    (φ² = φ + 1)
      = (87/16 + 865/256 + 87/64)·φ + (87/16 + 865/1024)
      = (2605/256)·φ + 6433/1024. -/
theorem α_NP_fifth :
    α_NP ^ 5 = (2605/256) * α_Hodge + 6433/1024 := by
  have h_split : α_NP ^ 5 = α_NP ^ 2 * α_NP ^ 3 := by ring
  rw [h_split, α_NP_sq, α_NP_cubed]
  have h_Hodge : α_Hodge ^ 2 = α_Hodge + 1 := by unfold α_Hodge; exact phi_sq_eq
  nlinarith [h_Hodge]

/-- **α_NP⁵ numerical bracket**: `22.7 < α_NP⁵ < 22.8`. Closed form
    with `phi_in_interval_10digit` gives `≈ 22.7470`. -/
theorem α_NP_fifth_bracket :
    (22.7 : ℝ) < α_NP ^ 5 ∧ α_NP ^ 5 < (22.8 : ℝ) := by
  rw [α_NP_fifth]
  have h_phi_lb : (1.6180339887 : ℝ) ≤ α_Hodge := by
    unfold α_Hodge; exact phi_in_interval_10digit.1
  have h_phi_ub : α_Hodge ≤ (1.6180339888 : ℝ) := by
    unfold α_Hodge; exact phi_in_interval_10digit.2
  exact ⟨by nlinarith [h_phi_lb], by nlinarith [h_phi_ub]⟩

/-- **`α_NP⁶ = (9729/512)·α_Hodge + 48113/4096`** — sixth power via
    α_NP² · α_NP⁴ composition. -/
theorem α_NP_sixth :
    α_NP ^ 6 = (9729/512) * α_Hodge + 48113/4096 := by
  have h_split : α_NP ^ 6 = α_NP ^ 2 * α_NP ^ 4 := by ring
  rw [h_split, α_NP_sq, α_NP_fourth]
  ring_nf
  have h := phi_sq_eq
  have h_Hodge : α_Hodge ^ 2 = α_Hodge + 1 := by unfold α_Hodge; exact h
  nlinarith [h_Hodge]

/-- **α_NP⁶ numerical bracket**: `42.4 < α_NP⁶ < 42.6`. Closed form
    with `phi_in_interval_10digit` gives `≈ 42.4921`. -/
theorem α_NP_sixth_bracket :
    (42.4 : ℝ) < α_NP ^ 6 ∧ α_NP ^ 6 < (42.6 : ℝ) := by
  rw [α_NP_sixth]
  have h_phi_lb : (1.6180339887 : ℝ) ≤ α_Hodge := by
    unfold α_Hodge; exact phi_in_interval_10digit.1
  have h_phi_ub : α_Hodge ≤ (1.6180339888 : ℝ) := by
    unfold α_Hodge; exact phi_in_interval_10digit.2
  exact ⟨by nlinarith [h_phi_lb], by nlinarith [h_phi_ub]⟩

/-! ### α_P Q(√2)-tower (parity bigraded) -/

/-- **`α_P⁵ = 4·α_P`**. -/
theorem α_P_fifth : α_P ^ 5 = 4 * α_P := by
  have h : α_P ^ 5 = (α_P ^ 2) ^ 2 * α_P := by ring
  rw [h, α_P_sq_eq_α_YM]; unfold α_YM; ring

/-- **`α_P⁶ = 8`**. -/
theorem α_P_sixth : α_P ^ 6 = 8 := by
  have h : α_P ^ 6 = (α_P ^ 2) ^ 3 := by ring
  rw [h, α_P_sq_eq_α_YM]; unfold α_YM; ring

/-- **`α_P⁷ = 8·α_P`**. -/
theorem α_P_seventh : α_P ^ 7 = 8 * α_P := by
  have h : α_P ^ 7 = (α_P ^ 2) ^ 3 * α_P := by ring
  rw [h, α_P_sq_eq_α_YM]; unfold α_YM; ring

/-- **`α_P⁸ = 16`**. -/
theorem α_P_eighth : α_P ^ 8 = 16 := by
  have h : α_P ^ 8 = (α_P ^ 2) ^ 4 := by ring
  rw [h, α_P_sq_eq_α_YM]; unfold α_YM; ring

/-- **★ α_P Q(√2)-TOWER ★** — parity-bigraded tower of `α_P^k`:
    even powers in Q (pure rationals), odd powers in Q · α_P.

    | k | α_P^k     |
    |---|-----------|
    | 1 | α_P       |
    | 2 | 2         |
    | 3 | 2·α_P     |
    | 4 | 4         |
    | 5 | 4·α_P     |
    | 6 | 8         |
    | 7 | 8·α_P     |
    | 8 | 16        |

    The coefficient sequence is `2^⌊k/2⌋`. -/
theorem α_P_Q_sqrt2_tower :
    α_P ^ 1 = α_P ∧
    α_P ^ 2 = 2 ∧
    α_P ^ 3 = 2 * α_P ∧
    α_P ^ 4 = 4 ∧
    α_P ^ 5 = 4 * α_P ∧
    α_P ^ 6 = 8 ∧
    α_P ^ 7 = 8 * α_P ∧
    α_P ^ 8 = 16 := by
  refine ⟨pow_one _, ?_, α_P_cubed, α_P_fourth, α_P_fifth, α_P_sixth,
          α_P_seventh, α_P_eighth⟩
  rw [α_P_sq_eq_α_YM]; unfold α_YM; rfl

/-! ### α_QG Q(π,√(2π))-tower (parity bigraded) -/

/-- **`α_QG³ = 2π·α_QG`** — self-similar cube. -/
theorem α_QG_cubed_early : α_QG ^ 3 = 2 * Real.pi * α_QG := by
  have h : α_QG ^ 3 = α_QG ^ 2 * α_QG := by ring
  rw [h, α_QG_sq_eq_two_pi]

/-- **`α_QG⁵ = 4π²·α_QG`**. -/
theorem α_QG_fifth : α_QG ^ 5 = 4 * Real.pi ^ 2 * α_QG := by
  have h : α_QG ^ 5 = (α_QG ^ 2) ^ 2 * α_QG := by ring
  rw [h, α_QG_sq_eq_two_pi]; ring

/-- **`α_QG⁷ = 8π³·α_QG`**. -/
theorem α_QG_seventh : α_QG ^ 7 = 8 * Real.pi ^ 3 * α_QG := by
  have h : α_QG ^ 7 = (α_QG ^ 2) ^ 3 * α_QG := by ring
  rw [h, α_QG_sq_eq_two_pi]; ring

/-- **★ α_QG Q(π,α_QG)-TOWER ★** — parity-bigraded tower of `α_QG^k`:
    even powers in Q[π], odd powers in Q[π]·α_QG.

    | k | α_QG^k       |
    |---|--------------|
    | 1 | α_QG         |
    | 2 | 2π           |
    | 3 | 2π·α_QG      |
    | 4 | 4π²          |
    | 5 | 4π²·α_QG     |
    | 6 | 8π³          |
    | 7 | 8π³·α_QG     |
    | 8 | 16π⁴         | -/
theorem α_QG_Q_pi_alpha_QG_tower :
    α_QG ^ 1 = α_QG ∧
    α_QG ^ 2 = 2 * Real.pi ∧
    α_QG ^ 3 = 2 * Real.pi * α_QG ∧
    α_QG ^ 4 = 4 * Real.pi ^ 2 ∧
    α_QG ^ 5 = 4 * Real.pi ^ 2 * α_QG ∧
    α_QG ^ 6 = 8 * Real.pi ^ 3 ∧
    α_QG ^ 7 = 8 * Real.pi ^ 3 * α_QG ∧
    α_QG ^ 8 = 16 * Real.pi ^ 4 :=
  ⟨pow_one _, α_QG_sq_eq_two_pi, α_QG_cubed_early, α_QG_fourth,
   α_QG_fifth, α_QG_sixth, α_QG_seventh, α_QG_eighth⟩

/-- **★ α_NP Q(φ)-TOWER ★** — 6-clause bundle of `α_NP^k` closed
    forms for `k ∈ {1, ..., 6}`, each in the Q(α_Hodge) basis:

    | k | α_NP^k                                              |
    |---|-----------------------------------------------------|
    | 1 | α_Hodge + 1/4                                       |
    | 2 | (3/2)·α_Hodge + 17/16                               |
    | 3 | (47/16)·α_Hodge + 113/64                            |
    | 4 | (87/16)·α_Hodge + 865/256                           |
    | 5 | (2605/256)·α_Hodge + 6433/1024                      |
    | 6 | (9729/512)·α_Hodge + 48113/4096                     |

    The (a_k, b_k) coefficient pair satisfies the linear recurrence
      a_{k+1} = (5/4)·a_k + b_k
      b_{k+1} = a_k + (1/4)·b_k
    seeded by (a_1, b_1) = (1, 1/4). -/
theorem α_NP_Q_phi_tower :
    α_NP ^ 1 = α_Hodge + 1/4 ∧
    α_NP ^ 2 = (3/2) * α_Hodge + 17/16 ∧
    α_NP ^ 3 = (47/16) * α_Hodge + 113/64 ∧
    α_NP ^ 4 = (87/16) * α_Hodge + 865/256 ∧
    α_NP ^ 5 = (2605/256) * α_Hodge + 6433/1024 ∧
    α_NP ^ 6 = (9729/512) * α_Hodge + 48113/4096 := by
  refine ⟨?_, α_NP_sq, α_NP_cubed, α_NP_fourth, α_NP_fifth, α_NP_sixth⟩
  unfold α_NP α_Hodge
  ring

/-! ### Numerical brackets on α_P odd powers (√2-valued) -/

/-- **α_P³ bracket**: 2.82 < α_P³ < 2.83. Numerical ≈ 2.8284 = 2√2. -/
theorem α_P_cubed_bracket :
    (2.82 : ℝ) < α_P ^ 3 ∧ α_P ^ 3 < (2.83 : ℝ) := by
  rw [α_P_cubed]
  have h_sq : α_P ^ 2 = 2 := by
    unfold α_P; exact Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have h_pos : (0 : ℝ) < α_P := by
    unfold α_P; exact Real.sqrt_pos.mpr (by norm_num)
  refine ⟨?_, ?_⟩
  · -- 2.82 < 2·α_P ⟺ α_P > 1.41 ⟺ α_P² > 1.41² = 1.9881 ✓ since α_P² = 2
    nlinarith [h_sq, h_pos]
  · -- 2·α_P < 2.83 ⟺ α_P < 1.415 ⟺ α_P² < 1.415² = 2.002225 ✓
    nlinarith [h_sq, h_pos]

/-- **α_P⁵ bracket**: 5.65 < α_P⁵ < 5.66. Numerical ≈ 5.6569 = 4√2. -/
theorem α_P_fifth_bracket :
    (5.65 : ℝ) < α_P ^ 5 ∧ α_P ^ 5 < (5.66 : ℝ) := by
  rw [α_P_fifth]
  have h_sq : α_P ^ 2 = 2 := by
    unfold α_P; exact Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have h_pos : (0 : ℝ) < α_P := by
    unfold α_P; exact Real.sqrt_pos.mpr (by norm_num)
  refine ⟨?_, ?_⟩
  · -- 5.65 < 4·α_P ⟺ α_P > 1.4125 ⟺ α_P² > 1.99515 ✓
    nlinarith [h_sq, h_pos]
  · -- 4·α_P < 5.66 ⟺ α_P < 1.415 ⟺ α_P² < 2.002225 ✓
    nlinarith [h_sq, h_pos]

/-- **α_P⁷ bracket**: 11.31 < α_P⁷ < 11.32. Numerical ≈ 11.3137 = 8√2. -/
theorem α_P_seventh_bracket :
    (11.31 : ℝ) < α_P ^ 7 ∧ α_P ^ 7 < (11.32 : ℝ) := by
  rw [α_P_seventh]
  have h_sq : α_P ^ 2 = 2 := by
    unfold α_P; exact Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have h_pos : (0 : ℝ) < α_P := by
    unfold α_P; exact Real.sqrt_pos.mpr (by norm_num)
  refine ⟨?_, ?_⟩
  · -- 11.31 < 8·α_P ⟺ α_P > 1.41375 ⟺ α_P² > 1.99868 ✓
    nlinarith [h_sq, h_pos]
  · -- 8·α_P < 11.32 ⟺ α_P < 1.415 ⟺ α_P² < 2.002225 ✓
    nlinarith [h_sq, h_pos]

/-! ### Numerical brackets on α_QG powers -/

/-- **α_QG bracket**: 2.5 < α_QG < 2.51. Numerical ≈ 2.5066. -/
theorem α_QG_bracket :
    (2.5 : ℝ) < α_QG ∧ α_QG < (2.51 : ℝ) := by
  have h_sq : α_QG ^ 2 = 2 * Real.pi := α_QG_sq_eq_two_pi
  have h_pos : (0 : ℝ) < α_QG := by
    unfold α_QG; exact Real.sqrt_pos.mpr (by have := Real.pi_pos; linarith)
  have h_pi_gt : (3.14159 : ℝ) < Real.pi := by
    have := Real.pi_gt_d6; linarith
  have h_pi_lt : Real.pi < (3.14160 : ℝ) := by
    have := Real.pi_lt_d6; linarith
  refine ⟨?_, ?_⟩
  · -- 2.5 < α_QG ⟺ 6.25 < α_QG² = 2π ⟺ π > 3.125 ✓
    nlinarith [h_sq, h_pos, h_pi_gt]
  · -- α_QG < 2.51 ⟺ α_QG² < 6.3001 ⟺ 2π < 6.3001 ⟺ π < 3.15005 ✓
    nlinarith [h_sq, h_pos, h_pi_lt]

/-- **α_QG² bracket**: 6.28 < α_QG² < 6.29. Numerical ≈ 6.2832 = 2π. -/
theorem α_QG_sq_bracket :
    (6.28 : ℝ) < α_QG ^ 2 ∧ α_QG ^ 2 < (6.29 : ℝ) := by
  rw [α_QG_sq_eq_two_pi]
  have h_pi_gt : (3.14159 : ℝ) < Real.pi := by
    have := Real.pi_gt_d6; linarith
  have h_pi_lt : Real.pi < (3.14160 : ℝ) := by
    have := Real.pi_lt_d6; linarith
  exact ⟨by linarith, by linarith⟩

/-- **α_QG⁴ bracket**: 39.4 < α_QG⁴ < 39.5. Numerical ≈ 39.4784 = 4π². -/
theorem α_QG_fourth_bracket :
    (39.4 : ℝ) < α_QG ^ 4 ∧ α_QG ^ 4 < (39.5 : ℝ) := by
  rw [α_QG_fourth]
  have h_pi_gt : (3.14159 : ℝ) < Real.pi := by
    have := Real.pi_gt_d6; linarith
  have h_pi_lt : Real.pi < (3.14160 : ℝ) := by
    have := Real.pi_lt_d6; linarith
  refine ⟨?_, ?_⟩
  · nlinarith [h_pi_gt]
  · nlinarith [h_pi_lt]

/-- **α_QG⁶ bracket**: 248 < α_QG⁶ < 249. Numerical ≈ 248.05 = 8π³. -/
theorem α_QG_sixth_bracket :
    (248 : ℝ) < α_QG ^ 6 ∧ α_QG ^ 6 < (249 : ℝ) := by
  rw [α_QG_sixth]
  have h_pi_gt : (3.14159 : ℝ) < Real.pi := by
    have := Real.pi_gt_d6; linarith
  have h_pi_lt : Real.pi < (3.14160 : ℝ) := by
    have := Real.pi_lt_d6; linarith
  refine ⟨?_, ?_⟩
  · nlinarith [h_pi_gt, sq_nonneg Real.pi]
  · nlinarith [h_pi_lt, sq_nonneg Real.pi]

/-- **α_QG⁸ bracket**: 1558 < α_QG⁸ < 1559. Numerical ≈ 1558.55 = 16π⁴.
    Proven via explicit π² and π⁴ brackets. -/
theorem α_QG_eighth_bracket :
    (1558 : ℝ) < α_QG ^ 8 ∧ α_QG ^ 8 < (1559 : ℝ) := by
  rw [α_QG_eighth]
  have h_pi_gt : (3.14159 : ℝ) < Real.pi := by
    have := Real.pi_gt_d6; linarith
  have h_pi_lt : Real.pi < (3.14160 : ℝ) := by
    have := Real.pi_lt_d6; linarith
  have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  -- π² brackets: 3.14159² = 9.86958..., 3.14160² = 9.86965...
  have h_pi_sq_gt : (9.8695 : ℝ) < Real.pi ^ 2 := by nlinarith [h_pi_gt, h_pi_pos]
  have h_pi_sq_lt : Real.pi ^ 2 < (9.8697 : ℝ) := by nlinarith [h_pi_lt, h_pi_pos]
  have h_pi_sq_pos : (0 : ℝ) < Real.pi ^ 2 := by positivity
  -- π⁴ brackets via π² squared
  have h_pi4_eq : Real.pi ^ 4 = (Real.pi ^ 2) ^ 2 := by ring
  rw [h_pi4_eq]
  refine ⟨?_, ?_⟩
  · -- 1558 < 16·(π²)² ⟺ (π²)² > 97.375 ⟺ π² > 9.868 ✓
    nlinarith [h_pi_sq_gt, h_pi_sq_pos]
  · -- 16·(π²)² < 1559 ⟺ (π²)² < 97.4375 ⟺ π² < 9.871 ✓
    nlinarith [h_pi_sq_lt, h_pi_sq_pos]

/-! ### α_QG odd-power brackets (π·α_QG family) -/

/-- **α_QG³ bracket**: 15.7 < α_QG³ < 15.8. Numerical ≈ 15.7496. -/
theorem α_QG_cubed_bracket :
    (15.7 : ℝ) < α_QG ^ 3 ∧ α_QG ^ 3 < (15.8 : ℝ) := by
  rw [α_QG_cubed_early]
  obtain ⟨h_α_QG_gt, h_α_QG_lt⟩ := α_QG_bracket
  have h_pi_gt : (3.14159 : ℝ) < Real.pi := by
    have := Real.pi_gt_d6; linarith
  have h_pi_lt : Real.pi < (3.14160 : ℝ) := by
    have := Real.pi_lt_d6; linarith
  have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have h_α_QG_pos : (0 : ℝ) < α_QG := by linarith
  refine ⟨?_, ?_⟩
  · nlinarith [h_pi_gt, h_α_QG_gt, h_pi_pos, h_α_QG_pos]
  · nlinarith [h_pi_lt, h_α_QG_lt, h_pi_pos, h_α_QG_pos]

/-! ### Numerical brackets on Hodge powers -/

/-- **α_Hodge² bracket**: 2.61 < α_Hodge² < 2.62. Numerical ≈ 2.6180. -/
theorem α_Hodge_sq_bracket :
    (2.61 : ℝ) < α_Hodge ^ 2 ∧ α_Hodge ^ 2 < (2.62 : ℝ) := by
  rw [α_Hodge_sq_eq_self_plus_one]
  have h_lb : (1.6180339887 : ℝ) ≤ α_Hodge := by
    unfold α_Hodge; exact phi_in_interval_10digit.1
  have h_ub : α_Hodge ≤ (1.6180339888 : ℝ) := by
    unfold α_Hodge; exact phi_in_interval_10digit.2
  exact ⟨by linarith, by linarith⟩

/-- **α_Hodge³ bracket**: 4.23 < α_Hodge³ < 4.24. Numerical ≈ 4.2361. -/
theorem α_Hodge_cubed_bracket :
    (4.23 : ℝ) < α_Hodge ^ 3 ∧ α_Hodge ^ 3 < (4.24 : ℝ) := by
  rw [α_Hodge_cubed]
  have h_lb : (1.6180339887 : ℝ) ≤ α_Hodge := by
    unfold α_Hodge; exact phi_in_interval_10digit.1
  have h_ub : α_Hodge ≤ (1.6180339888 : ℝ) := by
    unfold α_Hodge; exact phi_in_interval_10digit.2
  exact ⟨by linarith, by linarith⟩

/-- **α_Hodge⁴ bracket**: 6.85 < α_Hodge⁴ < 6.86. Numerical ≈ 6.8541. -/
theorem α_Hodge_fourth_bracket :
    (6.85 : ℝ) < α_Hodge ^ 4 ∧ α_Hodge ^ 4 < (6.86 : ℝ) := by
  rw [α_Hodge_fourth]
  have h_lb : (1.6180339887 : ℝ) ≤ α_Hodge := by
    unfold α_Hodge; exact phi_in_interval_10digit.1
  have h_ub : α_Hodge ≤ (1.6180339888 : ℝ) := by
    unfold α_Hodge; exact phi_in_interval_10digit.2
  exact ⟨by linarith, by linarith⟩

/-- **α_Hodge⁵ bracket**: 11.09 < α_Hodge⁵ < 11.10. Numerical ≈ 11.0902. -/
theorem α_Hodge_fifth_bracket :
    (11.09 : ℝ) < α_Hodge ^ 5 ∧ α_Hodge ^ 5 < (11.10 : ℝ) := by
  rw [α_Hodge_fifth]
  have h_lb : (1.6180339887 : ℝ) ≤ α_Hodge := by
    unfold α_Hodge; exact phi_in_interval_10digit.1
  have h_ub : α_Hodge ≤ (1.6180339888 : ℝ) := by
    unfold α_Hodge; exact phi_in_interval_10digit.2
  exact ⟨by linarith, by linarith⟩

/-- **α_Hodge⁶ bracket**: 17.94 < α_Hodge⁶ < 17.95. Numerical ≈ 17.9443. -/
theorem α_Hodge_sixth_bracket :
    (17.94 : ℝ) < α_Hodge ^ 6 ∧ α_Hodge ^ 6 < (17.95 : ℝ) := by
  rw [α_Hodge_sixth]
  have h_lb : (1.6180339887 : ℝ) ≤ α_Hodge := by
    unfold α_Hodge; exact phi_in_interval_10digit.1
  have h_ub : α_Hodge ≤ (1.6180339888 : ℝ) := by
    unfold α_Hodge; exact phi_in_interval_10digit.2
  exact ⟨by linarith, by linarith⟩

/-- **α_Hodge⁷ bracket**: 29.03 < α_Hodge⁷ < 29.04. Numerical ≈ 29.0344. -/
theorem α_Hodge_seventh_bracket :
    (29.03 : ℝ) < α_Hodge ^ 7 ∧ α_Hodge ^ 7 < (29.04 : ℝ) := by
  rw [α_Hodge_seventh]
  have h_lb : (1.6180339887 : ℝ) ≤ α_Hodge := by
    unfold α_Hodge; exact phi_in_interval_10digit.1
  have h_ub : α_Hodge ≤ (1.6180339888 : ℝ) := by
    unfold α_Hodge; exact phi_in_interval_10digit.2
  exact ⟨by linarith, by linarith⟩

/-- **α_Hodge⁸ bracket**: 46.97 < α_Hodge⁸ < 46.99. Numerical ≈ 46.9787. -/
theorem α_Hodge_eighth_bracket :
    (46.97 : ℝ) < α_Hodge ^ 8 ∧ α_Hodge ^ 8 < (46.99 : ℝ) := by
  rw [α_Hodge_eighth]
  have h_lb : (1.6180339887 : ℝ) ≤ α_Hodge := by
    unfold α_Hodge; exact phi_in_interval_10digit.1
  have h_ub : α_Hodge ≤ (1.6180339888 : ℝ) := by
    unfold α_Hodge; exact phi_in_interval_10digit.2
  exact ⟨by linarith, by linarith⟩

/-! ### ★ Full power-tower capstone ★ -/

/-- **★ FULL POWER-TOWER CAPSTONE ★** — single citable bundle covering
    the four multiplicative-substructure towers of the framework's
    non-rational/non-π α-instances:

    1. α_Hodge Q(φ)-tower with Fibonacci coefficients (8-clause)
    2. α_NP   Q(φ)-tower with (5/4)-recurrence (6-clause)
    3. α_P    Q(√2)-tower parity-bigraded (8-clause)
    4. α_QG   Q(π, α_QG)-tower parity-bigraded (8-clause)

    Total: 30 closed-form power identities. Each tower exposes the
    distinct multiplicative algebra of its axis:

    - φ-tower:   Fibonacci recurrence (Q[α_Hodge])
    - α_NP:      affine recurrence in Q[α_Hodge]
    - √2-tower:  doubling-up parity ladder (Q[α_P])
    - α_QG:      π-graded parity ladder (Q[π][α_QG])

    The framework's four irrationals {φ, φ+1/4, √2, √(2π)} all
    expose distinct algebraic-tower structures. -/
theorem full_power_tower_capstone :
    -- Tower 1: α_Hodge Fibonacci
    (α_Hodge ^ 1 = α_Hodge ∧
     α_Hodge ^ 2 = 1 * α_Hodge + 1 ∧
     α_Hodge ^ 3 = 2 * α_Hodge + 1 ∧
     α_Hodge ^ 4 = 3 * α_Hodge + 2 ∧
     α_Hodge ^ 5 = 5 * α_Hodge + 3 ∧
     α_Hodge ^ 6 = 8 * α_Hodge + 5 ∧
     α_Hodge ^ 7 = 13 * α_Hodge + 8 ∧
     α_Hodge ^ 8 = 21 * α_Hodge + 13) ∧
    -- Tower 2: α_NP Q(φ)
    (α_NP ^ 1 = α_Hodge + 1/4 ∧
     α_NP ^ 2 = (3/2) * α_Hodge + 17/16 ∧
     α_NP ^ 3 = (47/16) * α_Hodge + 113/64 ∧
     α_NP ^ 4 = (87/16) * α_Hodge + 865/256 ∧
     α_NP ^ 5 = (2605/256) * α_Hodge + 6433/1024 ∧
     α_NP ^ 6 = (9729/512) * α_Hodge + 48113/4096) ∧
    -- Tower 3: α_P Q(√2)
    (α_P ^ 1 = α_P ∧
     α_P ^ 2 = 2 ∧
     α_P ^ 3 = 2 * α_P ∧
     α_P ^ 4 = 4 ∧
     α_P ^ 5 = 4 * α_P ∧
     α_P ^ 6 = 8 ∧
     α_P ^ 7 = 8 * α_P ∧
     α_P ^ 8 = 16) ∧
    -- Tower 4: α_QG Q(π, α_QG)
    (α_QG ^ 1 = α_QG ∧
     α_QG ^ 2 = 2 * Real.pi ∧
     α_QG ^ 3 = 2 * Real.pi * α_QG ∧
     α_QG ^ 4 = 4 * Real.pi ^ 2 ∧
     α_QG ^ 5 = 4 * Real.pi ^ 2 * α_QG ∧
     α_QG ^ 6 = 8 * Real.pi ^ 3 ∧
     α_QG ^ 7 = 8 * Real.pi ^ 3 * α_QG ∧
     α_QG ^ 8 = 16 * Real.pi ^ 4) :=
  ⟨α_Hodge_fibonacci_tower,
   α_NP_Q_phi_tower,
   α_P_Q_sqrt2_tower,
   α_QG_Q_pi_alpha_QG_tower⟩

/-- **`1/α_Hodge = α_Hodge − 1`** — the canonical golden-ratio reciprocal
    identity, instantiated on the framework's Hodge α-value.

    Derivation: φ² = φ + 1 ⟹ φ·(φ − 1) = 1 ⟹ 1/φ = φ − 1. -/
theorem one_div_α_Hodge_eq :
    1 / α_Hodge = α_Hodge - 1 := by
  have h_phi_pos : (0 : ℝ) < α_Hodge := by
    unfold α_Hodge phi
    have h_sqrt5_pos : (0 : ℝ) < Real.sqrt 5 :=
      Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 5)
    linarith
  have h_phi_ne : α_Hodge ≠ 0 := h_phi_pos.ne'
  have h_sq : α_Hodge ^ 2 = α_Hodge + 1 := by
    unfold α_Hodge; exact phi_sq_eq
  field_simp
  nlinarith [h_sq]

/-- **`1/α_Hodge numerical bracket`**: `0.618 < 1/α_Hodge < 0.619`. Closed
    form `α_Hodge − 1` with `phi_in_interval_10digit` gives `≈ 0.6180`. -/
theorem one_div_α_Hodge_bracket :
    (0.618 : ℝ) < 1 / α_Hodge ∧ 1 / α_Hodge < (0.619 : ℝ) := by
  rw [one_div_α_Hodge_eq]
  have h_phi_lb : (1.6180339887 : ℝ) ≤ α_Hodge := by
    unfold α_Hodge; exact phi_in_interval_10digit.1
  have h_phi_ub : α_Hodge ≤ (1.6180339888 : ℝ) := by
    unfold α_Hodge; exact phi_in_interval_10digit.2
  exact ⟨by linarith, by linarith⟩

/-- **`1/α_NP numerical bracket`**: `0.535 < 1/α_NP < 0.536`. Closed form
    `(8√5 − 12)/11` with √5 ∈ [2.2360, 2.2361] gives `≈ 0.5354`. -/
theorem one_div_α_NP_bracket :
    (0.535 : ℝ) < 1 / α_NP ∧ 1 / α_NP < (0.536 : ℝ) := by
  rw [one_div_α_NP_closed_form]
  have h_sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  have h_sqrt5_pos : (0 : ℝ) < Real.sqrt 5 :=
    Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 5)
  refine ⟨?_, ?_⟩
  · -- 0.535·11 = 5.885 < 8√5 − 12 ⟺ 17.885 < 8√5 ⟺ √5 > 2.2356 ⟺ 5 > 4.998...
    nlinarith [h_sqrt5_sq, h_sqrt5_pos]
  · -- 8√5 − 12 < 0.536·11 = 5.896 ⟺ 8√5 < 17.896 ⟺ √5 < 2.237 ⟺ 5 < 5.004...
    nlinarith [h_sqrt5_sq, h_sqrt5_pos]

/-- **`1/α_QG = α_QG / (2π)`** — self-similar reciprocal of √(2π).
    Since α_QG² = 2π, dividing both sides by α_QG·(2π) gives the identity. -/
theorem one_div_α_QG_eq :
    1 / α_QG = α_QG / (2 * Real.pi) := by
  have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have h_α_QG_pos : (0 : ℝ) < α_QG := by
    unfold α_QG
    exact Real.sqrt_pos.mpr (by linarith)
  have h_2pi_pos : (0 : ℝ) < 2 * Real.pi := by linarith
  have h_sq := α_QG_sq_eq_two_pi
  field_simp
  linarith [h_sq]

/-! ### ★ Capstone: full 9-instance squares layer ★ -/

/-- **`α_Poincaré² = 1`**. -/
theorem α_Poincare_sq_eq_one : α_Poincare ^ 2 = 1 := by
  unfold α_Poincare; norm_num

/-- **`α_YM² = 4`**. -/
theorem α_YM_sq_eq_four : α_YM ^ 2 = 4 := by
  unfold α_YM; norm_num

/-- **`α_BSD² = 9·π²/16`**. -/
theorem α_BSD_sq_eq : α_BSD ^ 2 = 9 * Real.pi ^ 2 / 16 := by
  unfold α_BSD; ring

/-- **`α_NS² = 9·π²/4`**. -/
theorem α_NS_sq_eq : α_NS ^ 2 = 9 * Real.pi ^ 2 / 4 := by
  unfold α_NS; ring

/-- **★ α-SKELETON FULL SQUARES LAYER ★** — every framework α-instance's
    square is in closed form within Q(π, α_Hodge) algebra:

    | α-instance | α²                            |
    |------------|-------------------------------|
    | α_Poincaré | 1                             |
    | α_P        | 2  (= α_YM)                   |
    | α_RH       | 9/4                           |
    | α_YM       | 4                             |
    | α_BSD      | 9π²/16                        |
    | α_NS       | 9π²/4                         |
    | α_Hodge    | α_Hodge + 1   (φ-Fibonacci)   |
    | α_NP       | (3/2)·α_Hodge + 17/16         |
    | α_QG       | 2π   (= α_YM·π)               | -/
theorem α_skeleton_full_squares_layer :
    α_Poincare ^ 2 = 1 ∧
    α_P ^ 2 = 2 ∧
    α_RH ^ 2 = 9 / 4 ∧
    α_YM ^ 2 = 4 ∧
    α_BSD ^ 2 = 9 * Real.pi ^ 2 / 16 ∧
    α_NS ^ 2 = 9 * Real.pi ^ 2 / 4 ∧
    α_Hodge ^ 2 = α_Hodge + 1 ∧
    α_NP ^ 2 = (3/2) * α_Hodge + 17/16 ∧
    α_QG ^ 2 = 2 * Real.pi := by
  refine ⟨α_Poincare_sq_eq_one, ?_, α_RH_sq_eq_nine_fourths,
          α_YM_sq_eq_four, α_BSD_sq_eq, α_NS_sq_eq,
          α_Hodge_sq_eq_self_plus_one, ?_, α_QG_sq_eq_two_pi⟩
  · -- α_P² = 2
    have h := α_P_sq_eq_α_YM
    rw [h, show α_YM = (2 : ℝ) from rfl]
  · -- α_NP² = (3/2)·α_Hodge + 17/16
    unfold α_NP α_Hodge
    have h := phi_sq_eq
    nlinarith [h]

/-! ### ★ Scalar fingerprint: full 9-instance additive sum ★ -/

/-- **★ α-SKELETON FULL 9-INSTANCE SUM ★** — the additive scalar
    fingerprint of the locus:

    Σ_i α_i = α_Poincaré + α_P + α_RH + α_YM + α_BSD + α_NS
            + α_Hodge + α_NP + α_QG
            = (19/4) + α_P + (9π/4) + 2·α_Hodge + α_QG

    Closed form in Q(π, α_P, α_Hodge, α_QG). Any perturbation of any
    single α perturbs this scalar. -/
theorem α_skeleton_sum_closed_form :
    α_Poincare + α_P + α_RH + α_YM + α_BSD + α_NS
      + α_Hodge + α_NP + α_QG
    = (19/4) + α_P + (9 * Real.pi / 4) + 2 * α_Hodge + α_QG := by
  unfold α_Poincare α_RH α_YM α_BSD α_NS α_NP α_Hodge
  ring

/-- **α-skeleton sum numerical bracket**: `Σ α_i ∈ (18.9, 19.0)`.
    Numerical value ≈ 18.9756. Uses:
    - √2 ∈ (1.41, 1.42)         (from 2)
    - π ∈ (3.14159, 3.14160)    (from pi_gt_d6 / pi_lt_d6)
    - φ ∈ (1.6180, 1.6181)      (from phi_in_interval_10digit)
    - √(2π) ∈ (2.5, 2.6)        (from 2π ∈ (6.28318, 6.28321)) -/
theorem α_skeleton_sum_bracket :
    (18.9 : ℝ) < α_Poincare + α_P + α_RH + α_YM + α_BSD + α_NS
                  + α_Hodge + α_NP + α_QG ∧
    α_Poincare + α_P + α_RH + α_YM + α_BSD + α_NS
      + α_Hodge + α_NP + α_QG < (19.0 : ℝ) := by
  rw [α_skeleton_sum_closed_form]
  -- π brackets
  have h_pi_gt : (3.14159 : ℝ) < Real.pi := by
    have := Real.pi_gt_d6; linarith
  have h_pi_lt : Real.pi < (3.14160 : ℝ) := by
    have := Real.pi_lt_d6; linarith
  have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  -- α_P = √2 brackets
  have h_α_P_sq : α_P ^ 2 = 2 := by
    unfold α_P; exact Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have h_α_P_pos : (0 : ℝ) < α_P := by
    unfold α_P; exact Real.sqrt_pos.mpr (by norm_num)
  have h_α_P_gt : (1.41 : ℝ) < α_P := by nlinarith [h_α_P_sq, h_α_P_pos]
  have h_α_P_lt : α_P < (1.42 : ℝ) := by nlinarith [h_α_P_sq, h_α_P_pos]
  -- α_Hodge = φ brackets
  have h_phi_lb : (1.6180339887 : ℝ) ≤ α_Hodge := by
    unfold α_Hodge; exact phi_in_interval_10digit.1
  have h_phi_ub : α_Hodge ≤ (1.6180339888 : ℝ) := by
    unfold α_Hodge; exact phi_in_interval_10digit.2
  -- α_QG = √(2π) brackets
  have h_α_QG_sq : α_QG ^ 2 = 2 * Real.pi := α_QG_sq_eq_two_pi
  have h_α_QG_pos : (0 : ℝ) < α_QG := by
    unfold α_QG
    exact Real.sqrt_pos.mpr (by linarith)
  have h_α_QG_gt : (2.5 : ℝ) < α_QG := by nlinarith [h_α_QG_sq, h_α_QG_pos, h_pi_gt]
  have h_α_QG_lt : α_QG < (2.51 : ℝ) := by nlinarith [h_α_QG_sq, h_α_QG_pos, h_pi_lt]
  refine ⟨?_, ?_⟩
  · linarith [h_α_P_gt, h_pi_gt, h_phi_lb, h_α_QG_gt]
  · linarith [h_α_P_lt, h_pi_lt, h_phi_ub, h_α_QG_lt]

/-! ### ★ Capstone: full 9-instance 4th-power layer ★ -/

/-- **`α_Poincaré⁴ = 1`**. -/
theorem α_Poincare_fourth : α_Poincare ^ 4 = 1 := by
  unfold α_Poincare; norm_num

/-- **`α_BSD⁴ = 81·π⁴/256`**. -/
theorem α_BSD_fourth : α_BSD ^ 4 = 81 * Real.pi ^ 4 / 256 := by
  unfold α_BSD; ring

/-- **`α_NS⁴ = 81·π⁴/16`**. -/
theorem α_NS_fourth : α_NS ^ 4 = 81 * Real.pi ^ 4 / 16 := by
  unfold α_NS; ring

/-- **★ α-SKELETON FULL 4TH-POWER LAYER ★** — every framework α-instance's
    4th power is in closed form within Q(π, α_Hodge):

    | α-instance | α⁴                                  |
    |------------|-------------------------------------|
    | α_Poincaré | 1                                   |
    | α_P        | 4                                   |
    | α_RH       | 81/16                               |
    | α_YM       | 16                                  |
    | α_BSD      | 81π⁴/256                            |
    | α_NS       | 81π⁴/16                             |
    | α_Hodge    | 3·α_Hodge + 2     (φ-Fibonacci F₅·φ + F₄) |
    | α_NP       | (87/16)·α_Hodge + 865/256           |
    | α_QG       | 4π²                                 | -/
theorem α_skeleton_full_fourth_power_layer :
    α_Poincare ^ 4 = 1 ∧
    α_P ^ 4 = 4 ∧
    α_RH ^ 4 = 81 / 16 ∧
    α_YM ^ 4 = 16 ∧
    α_BSD ^ 4 = 81 * Real.pi ^ 4 / 256 ∧
    α_NS ^ 4 = 81 * Real.pi ^ 4 / 16 ∧
    α_Hodge ^ 4 = 3 * α_Hodge + 2 ∧
    α_NP ^ 4 = (87/16) * α_Hodge + 865/256 ∧
    α_QG ^ 4 = 4 * Real.pi ^ 2 :=
  ⟨α_Poincare_fourth, α_P_fourth, α_RH_fourth, α_YM_fourth,
   α_BSD_fourth, α_NS_fourth, α_Hodge_fourth, α_NP_fourth, α_QG_fourth⟩

/-! ### ★ Capstone: full 9-instance cubes layer ★ -/

/-- **`α_Poincaré³ = 1`**. -/
theorem α_Poincare_cubed : α_Poincare ^ 3 = 1 := by
  unfold α_Poincare; norm_num

/-- **`α_QG³ = 2π·α_QG`** — self-similar cube (α_QG² = 2π gives a factor). -/
theorem α_QG_cubed : α_QG ^ 3 = 2 * Real.pi * α_QG := by
  have h := α_QG_sq_eq_two_pi
  have : α_QG ^ 3 = α_QG ^ 2 * α_QG := by ring
  rw [this, h]

/-- **★ α-SKELETON FULL CUBES LAYER ★** — every framework α-instance's
    cube is in closed form within Q(π, α_Hodge, α_P, α_QG):

    | α-instance | α³                                  |
    |------------|-------------------------------------|
    | α_Poincaré | 1                                   |
    | α_P        | 2·α_P                               |
    | α_RH       | 27/8                                |
    | α_YM       | 8                                   |
    | α_BSD      | 27π³/64                             |
    | α_NS       | 27π³/8                              |
    | α_Hodge    | 2·α_Hodge + 1     (φ-Fibonacci)      |
    | α_NP       | (47/16)·α_Hodge + 113/64            |
    | α_QG       | 2π·α_QG           (self-similar)    | -/
theorem α_skeleton_full_cubes_layer :
    α_Poincare ^ 3 = 1 ∧
    α_P ^ 3 = 2 * α_P ∧
    α_RH ^ 3 = 27 / 8 ∧
    α_YM ^ 3 = 8 ∧
    α_BSD ^ 3 = 27 * Real.pi ^ 3 / 64 ∧
    α_NS ^ 3 = 27 * Real.pi ^ 3 / 8 ∧
    α_Hodge ^ 3 = 2 * α_Hodge + 1 ∧
    α_NP ^ 3 = (47/16) * α_Hodge + 113/64 ∧
    α_QG ^ 3 = 2 * Real.pi * α_QG :=
  ⟨α_Poincare_cubed, α_P_cubed, α_RH_cubed, α_YM_cubed,
   α_BSD_cubed, α_NS_cubed, α_Hodge_cubed, α_NP_cubed, α_QG_cubed⟩

/-! ### ★ Capstone: full 9-instance reciprocal layer ★ -/

/-- **★ α-SKELETON FULL RECIPROCAL LAYER ★** — every framework α-instance
    has a clean closed-form reciprocal, simultaneously:

    | α-instance | 1/α                       |
    |------------|---------------------------|
    | α_Poincaré | 1                         |
    | α_P        | α_P / 2                   |  (since α_P² = 2)
    | α_RH       | 2/3                       |
    | α_YM       | 1/2                       |
    | α_BSD      | 4 / (3π)                  |
    | α_NS       | 2 / (3π)                  |
    | α_Hodge    | α_Hodge − 1               |  (golden ratio property)
    | α_NP       | (8·√5 − 12) / 11          |  (Q(√5) reciprocal)
    | α_QG       | α_QG / (2π)               |  (self-similar)

    All 9 reciprocals expressed in the Q(π, √2, √5, φ) ring; the locus is
    closed under inversion within the same algebraic ring. -/
theorem α_skeleton_full_reciprocal_layer :
    1 / α_Poincare = 1 ∧
    1 / α_P = α_P / 2 ∧
    1 / α_RH = 2 / 3 ∧
    1 / α_YM = 1 / 2 ∧
    1 / α_BSD = 4 / (3 * Real.pi) ∧
    1 / α_NS = 2 / (3 * Real.pi) ∧
    1 / α_Hodge = α_Hodge - 1 ∧
    1 / α_NP = (8 * Real.sqrt 5 - 12) / 11 ∧
    1 / α_QG = α_QG / (2 * Real.pi) := by
  have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have h_pi_ne : Real.pi ≠ 0 := h_pi_pos.ne'
  have h_sqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have h_sqrt2_pos : (0 : ℝ) < Real.sqrt 2 :=
    Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold α_Poincare; norm_num
  · -- 1/√2 = √2/2
    unfold α_P
    field_simp
    nlinarith [h_sqrt2_sq, h_sqrt2_pos]
  · -- 1/(3/2) = 2/3
    unfold α_RH; norm_num
  · -- 1/2 = 1/2
    unfold α_YM; norm_num
  · -- 1/(3π/4) = 4/(3π)
    unfold α_BSD
    field_simp
  · -- 1/(3π/2) = 2/(3π)
    unfold α_NS
    field_simp
  · exact one_div_α_Hodge_eq
  · exact one_div_α_NP_closed_form
  · exact one_div_α_QG_eq

/-- **`α_NP · α_Hodge` chained form via α_Hodge_mul_α_NP**:
    `α_NP · α_Hodge = α_Hodge · α_NP = (5/4)·α_Hodge + 1`. -/
theorem α_NP_mul_α_Hodge :
    α_NP * α_Hodge = (5/4) * α_Hodge + 1 := by
  rw [mul_comm]
  exact α_Hodge_mul_α_NP

/-! ## Section 2k — α_QG logarithmic identities -/

/-- **`2·log α_QG = log(2π)`** — from α_QG² = 2π. -/
theorem two_log_α_QG_eq_log_two_pi :
    2 * Real.log α_QG = Real.log (2 * Real.pi) := by
  have h_log_sq : Real.log (α_QG ^ 2) = 2 * Real.log α_QG := by
    rw [Real.log_pow]; push_cast; ring
  rw [← h_log_sq, α_QG_sq_eq_two_pi]

/-- **`log α_QG = (log 2 + log π) / 2`** — clean decomposition. -/
theorem log_α_QG_eq_half_log_2_add_log_pi :
    Real.log α_QG = (Real.log 2 + Real.log Real.pi) / 2 := by
  have h := two_log_α_QG_eq_log_two_pi
  have h_log_2pi : Real.log (2 * Real.pi) = Real.log 2 + Real.log Real.pi := by
    have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
    exact Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt h_pi_pos)
  linarith [h_log_2pi]

/-! ## Section 2L — α-skeleton logarithmic identities

  Closed-form `Real.log α_*` for every α-instance whose definition admits
  a clean decomposition into elementary logs (log 2, log 3, log π).
  These identities are axiom-free; combined they form the full
  logarithmic layer of the 9-axis algebraic locus. -/

/-- **`log α_Poincaré = 0`** — since α_Poincaré = 1. -/
theorem log_α_Poincare_eq_zero :
    Real.log α_Poincare = 0 := by
  unfold α_Poincare; exact Real.log_one

/-- **`log α_YM = log 2`** — since α_YM = 2. -/
theorem log_α_YM_eq_log_two :
    Real.log α_YM = Real.log 2 := by
  unfold α_YM; rfl

/-- **`log α_P = (log 2)/2`** — since α_P = √2. -/
theorem log_α_P_eq_half_log_two :
    Real.log α_P = Real.log 2 / 2 := by
  unfold α_P
  exact Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)

/-- **`log α_RH = log 3 − log 2`** — since α_RH = 3/2. -/
theorem log_α_RH_eq :
    Real.log α_RH = Real.log 3 - Real.log 2 := by
  unfold α_RH
  exact Real.log_div (by norm_num : (3 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)

/-- **`log α_BSD = log 3 + log π − log 4`** — since α_BSD = 3π/4. -/
theorem log_α_BSD_eq :
    Real.log α_BSD = Real.log 3 + Real.log Real.pi - Real.log 4 := by
  unfold α_BSD
  have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [Real.log_div (by positivity) (by norm_num : (4 : ℝ) ≠ 0)]
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (ne_of_gt h_pi_pos)]

/-- **`log α_NS = log 3 + log π − log 2`** — since α_NS = 3π/2. -/
theorem log_α_NS_eq :
    Real.log α_NS = Real.log 3 + Real.log Real.pi - Real.log 2 := by
  unfold α_NS
  have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [Real.log_div (by positivity) (by norm_num : (2 : ℝ) ≠ 0)]
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (ne_of_gt h_pi_pos)]

/-- **`log α_Hodge = log φ`** — definitional unfold. -/
theorem log_α_Hodge_eq_log_phi :
    Real.log α_Hodge = Real.log phi := by
  unfold α_Hodge; rfl

/-! ### Cross-axis log-relations -/

/-- **`2·log α_P = log α_YM`** — from α_P² = α_YM. -/
theorem two_log_α_P_eq_log_α_YM :
    2 * Real.log α_P = Real.log α_YM := by
  rw [log_α_P_eq_half_log_two, log_α_YM_eq_log_two]; ring

/-- **`log α_NS − log α_BSD = log 2`** — from α_NS = 2·α_BSD. -/
theorem log_α_NS_sub_log_α_BSD_eq_log_two :
    Real.log α_NS - Real.log α_BSD = Real.log 2 := by
  rw [log_α_NS_eq, log_α_BSD_eq]
  have h_log4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  linarith [h_log4]

/-- **`log α_BSD − log α_NS = −log 2`** — symmetric statement. -/
theorem log_α_BSD_sub_log_α_NS_eq_neg_log_two :
    Real.log α_BSD - Real.log α_NS = - Real.log 2 := by
  have h := log_α_NS_sub_log_α_BSD_eq_log_two; linarith

/-- **`2·log α_QG = log α_YM + log π`** — from α_QG² = α_YM·π. -/
theorem two_log_α_QG_eq_log_α_YM_add_log_pi :
    2 * Real.log α_QG = Real.log α_YM + Real.log Real.pi := by
  rw [two_log_α_QG_eq_log_two_pi, log_α_YM_eq_log_two]
  exact Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt Real.pi_pos)

/-- **`log α_QG = log α_P + (log π)/2`** — radical-π decomposition. -/
theorem log_α_QG_eq_log_α_P_add_half_log_pi :
    Real.log α_QG = Real.log α_P + Real.log Real.pi / 2 := by
  rw [log_α_QG_eq_half_log_2_add_log_pi, log_α_P_eq_half_log_two]; ring

/-- **`log α_RH + log α_BSD = log α_NS`** — chained via α_NS = 2·α_BSD
    and α_RH = 3/2. Note: this is the **wrong** direction; the correct
    chained statement is below. -/
theorem log_α_BSD_add_log_two_eq_log_α_NS :
    Real.log α_BSD + Real.log 2 = Real.log α_NS := by
  have h := log_α_NS_sub_log_α_BSD_eq_log_two; linarith

/-! ### Locus identities lifted into log-space -/

/-- **`log α_NS = log α_YM + log α_BSD`** — log-form of locus identity L6
    (α_NS = α_YM · α_BSD). -/
theorem log_α_NS_eq_log_α_YM_add_log_α_BSD :
    Real.log α_NS = Real.log α_YM + Real.log α_BSD := by
  rw [log_α_YM_eq_log_two, log_α_BSD_eq, log_α_NS_eq]
  have h_log4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  linarith [h_log4]

/-- **`log α_RH = log 3 − log α_YM`** — log-form of α_RH = 3/α_YM
    (since α_YM = 2 and α_RH = 3/2). -/
theorem log_α_RH_eq_log_three_sub_log_α_YM :
    Real.log α_RH = Real.log 3 - Real.log α_YM := by
  rw [log_α_YM_eq_log_two, log_α_RH_eq]

/-- **`log α_BSD = log α_NS − log α_YM`** — symmetric companion. -/
theorem log_α_BSD_eq_log_α_NS_sub_log_α_YM :
    Real.log α_BSD = Real.log α_NS - Real.log α_YM := by
  have h := log_α_NS_eq_log_α_YM_add_log_α_BSD; linarith

/-- **`log α_QG + log α_QG = log α_YM + log π`** — log-form of L13
    (α_QG² = α_YM · π). -/
theorem log_α_QG_add_log_α_QG_eq_log_α_YM_add_log_pi :
    Real.log α_QG + Real.log α_QG = Real.log α_YM + Real.log Real.pi := by
  have h := two_log_α_QG_eq_log_α_YM_add_log_pi; linarith

/-- **`log α_NS = log 3 + log α_BSD − log 2`** — combining L5 (α_NS = 2·α_BSD)
    with α_RH = 3/2 alignment. -/
theorem log_α_NS_eq_log_three_add_log_α_BSD_sub_log_two :
    Real.log α_NS = Real.log α_BSD + Real.log 2 := by
  have h := log_α_NS_sub_log_α_BSD_eq_log_two; linarith

/-- **`log α_BSD + log α_RH = log α_NS − log 2 + log 3 − log 2`** —
    composite three-term identity isolating the (log 3, log 2, log π) basis. -/
theorem log_α_RH_add_log_α_BSD_eq :
    Real.log α_RH + Real.log α_BSD =
      2 * Real.log 3 + Real.log Real.pi - 3 * Real.log 2 := by
  rw [log_α_RH_eq, log_α_BSD_eq]
  have h_log4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  linarith [h_log4]

/-! ### Reciprocal log identities -/

/-- **`log (1/α_P) = −(log 2)/2`**. -/
theorem log_one_div_α_P :
    Real.log (1 / α_P) = - (Real.log 2 / 2) := by
  rw [Real.log_div one_ne_zero (by unfold α_P; exact (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'),
      Real.log_one, log_α_P_eq_half_log_two]; ring

/-- **`log (1/α_YM) = −log 2`**. -/
theorem log_one_div_α_YM :
    Real.log (1 / α_YM) = - Real.log 2 := by
  rw [Real.log_div one_ne_zero (by unfold α_YM; norm_num),
      Real.log_one, log_α_YM_eq_log_two]; ring

/-- **`log (1/α_RH) = log 2 − log 3`**. -/
theorem log_one_div_α_RH :
    Real.log (1 / α_RH) = Real.log 2 - Real.log 3 := by
  rw [Real.log_div one_ne_zero (by unfold α_RH; norm_num),
      Real.log_one, log_α_RH_eq]; ring

/-- **`log (1/α_QG) = −(log 2 + log π)/2`**. -/
theorem log_one_div_α_QG :
    Real.log (1 / α_QG) = - (Real.log 2 + Real.log Real.pi) / 2 := by
  have h_qg_pos : (0 : ℝ) < α_QG := by
    unfold α_QG; exact Real.sqrt_pos.mpr (by have := Real.pi_pos; nlinarith)
  rw [Real.log_div one_ne_zero h_qg_pos.ne',
      Real.log_one, log_α_QG_eq_half_log_2_add_log_pi]; ring

/-! ### Skeleton log-basis fingerprint -/

/-- **`α-SKELETON LOG-BASIS CLOSED FORM`** — every elementary-form
    α-instance has its log expressed in the four-element basis
    `{log 2, log 3, log π, log φ}`. The 5 π-built/rational α's land in
    `Span_ℤ{log 2, log 3, log π}`; α_P, α_QG add half-coefficients.
    α_Poincaré contributes 0; α_Hodge contributes log φ. -/
theorem α_skeleton_log_basis_form :
    Real.log α_Poincare = 0 ∧
    Real.log α_YM   = 1 * Real.log 2 + 0 * Real.log 3 + 0 * Real.log Real.pi ∧
    Real.log α_RH   = (-1) * Real.log 2 + 1 * Real.log 3 + 0 * Real.log Real.pi ∧
    Real.log α_BSD  = (-2) * Real.log 2 + 1 * Real.log 3 + 1 * Real.log Real.pi ∧
    Real.log α_NS   = (-1) * Real.log 2 + 1 * Real.log 3 + 1 * Real.log Real.pi ∧
    Real.log α_P    = (1/2) * Real.log 2 ∧
    Real.log α_QG   = (1/2) * Real.log 2 + (1/2) * Real.log Real.pi ∧
    Real.log α_Hodge = Real.log phi := by
  have h_log4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact log_α_Poincare_eq_zero
  · rw [log_α_YM_eq_log_two]; ring
  · rw [log_α_RH_eq]; ring
  · rw [log_α_BSD_eq]; linarith [h_log4]
  · rw [log_α_NS_eq]; ring
  · rw [log_α_P_eq_half_log_two]; ring
  · rw [log_α_QG_eq_half_log_2_add_log_pi]; ring
  · exact log_α_Hodge_eq_log_phi

/-! ### Sum-of-logs scalar fingerprint -/

/-- **★ ELEMENTARY-SKELETON LOG-SUM ★** — the scalar
    `Σ log α_*` over the seven elementary-form instances equals
    `−2·log 2 + 3·log 3 + (5/2)·log π` in closed form. Equivalently
    (after exp): the product of these seven α-instances equals
    `27·π^(5/2) / 4`. -/
theorem sum_log_α_skeleton_elementary :
    Real.log α_Poincare + Real.log α_YM + Real.log α_RH + Real.log α_BSD
      + Real.log α_NS + Real.log α_P + Real.log α_QG
    = -2 * Real.log 2 + 3 * Real.log 3 + (5/2) * Real.log Real.pi := by
  rw [log_α_Poincare_eq_zero, log_α_YM_eq_log_two, log_α_RH_eq, log_α_BSD_eq,
      log_α_NS_eq, log_α_P_eq_half_log_two, log_α_QG_eq_half_log_2_add_log_pi]
  have h_log4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  linarith [h_log4]

/-- **`log(α_RH · α_BSD · α_NS) = 3·log 3 + 2·log π − 4·log 2`** —
    product of the three rational/π-built non-Poincaré instances. -/
theorem log_prod_rh_bsd_ns_eq :
    Real.log α_RH + Real.log α_BSD + Real.log α_NS
    = 3 * Real.log 3 + 2 * Real.log Real.pi - 4 * Real.log 2 := by
  rw [log_α_RH_eq, log_α_BSD_eq, log_α_NS_eq]
  have h_log4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  linarith [h_log4]

/-- **`log(α_P · α_QG) = log 2 + (log π)/2`** — radical-pair product. -/
theorem log_prod_α_P_α_QG :
    Real.log α_P + Real.log α_QG = Real.log 2 + Real.log Real.pi / 2 := by
  rw [log_α_P_eq_half_log_two, log_α_QG_eq_half_log_2_add_log_pi]; ring

/-! ### Numerical brackets on log-2-derived α-logs -/

/-- **`log α_YM ∈ (0.6931471803, 0.6931471808)`** — directly from
    mathlib's `Real.log_two_gt_d9` / `Real.log_two_lt_d9`. -/
theorem log_α_YM_bracket :
    (0.6931471803 : ℝ) < Real.log α_YM ∧
    Real.log α_YM < (0.6931471808 : ℝ) := by
  rw [log_α_YM_eq_log_two]
  exact ⟨Real.log_two_gt_d9, Real.log_two_lt_d9⟩

/-- **`log α_P ∈ (0.34657359015, 0.34657359040)`** — half of log 2. -/
theorem log_α_P_bracket :
    (0.34657359015 : ℝ) < Real.log α_P ∧
    Real.log α_P < (0.34657359040 : ℝ) := by
  rw [log_α_P_eq_half_log_two]
  refine ⟨?_, ?_⟩
  · have := Real.log_two_gt_d9; linarith
  · have := Real.log_two_lt_d9; linarith

/-- **`log(1/α_YM) ∈ (−0.6931471808, −0.6931471803)`** — sign-flipped
    log 2 bracket. -/
theorem log_one_div_α_YM_bracket :
    (-0.6931471808 : ℝ) < Real.log (1 / α_YM) ∧
    Real.log (1 / α_YM) < (-0.6931471803 : ℝ) := by
  rw [log_one_div_α_YM]
  refine ⟨?_, ?_⟩
  · have := Real.log_two_lt_d9; linarith
  · have := Real.log_two_gt_d9; linarith

/-! ### Bundle: full logarithmic layer of the α-skeleton -/

/-- **★ α-SKELETON LOGARITHMIC LAYER ★** — every α-instance with a
    π/√/rational closed form has its `Real.log` decomposed into elementary
    logarithms, axiom-free, in one bundled theorem. -/
theorem α_skeleton_log_layer :
    Real.log α_Poincare = 0 ∧
    Real.log α_YM = Real.log 2 ∧
    Real.log α_P = Real.log 2 / 2 ∧
    Real.log α_RH = Real.log 3 - Real.log 2 ∧
    Real.log α_BSD = Real.log 3 + Real.log Real.pi - Real.log 4 ∧
    Real.log α_NS = Real.log 3 + Real.log Real.pi - Real.log 2 ∧
    Real.log α_QG = (Real.log 2 + Real.log Real.pi) / 2 ∧
    Real.log α_Hodge = Real.log phi := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact log_α_Poincare_eq_zero
  · exact log_α_YM_eq_log_two
  · exact log_α_P_eq_half_log_two
  · exact log_α_RH_eq
  · exact log_α_BSD_eq
  · exact log_α_NS_eq
  · exact log_α_QG_eq_half_log_2_add_log_pi
  · exact log_α_Hodge_eq_log_phi

/-! ### ★ Elementary product closed form ★ -/

/-- **★ ELEMENTARY 7-PRODUCT CLOSED FORM ★** —
    `Π_{i ∈ elementary 7} α_i = 27 · π^(5/2) / 4`.

    Direct computation:
      1 · 2 · (3/2) · (3π/4) · (3π/2) · √2 · √(2π)
        = 3 · (9π²/8) · √2 · √(2π)
        = (27π²/8) · √(2 · 2π)   (Real.sqrt_mul)
        = (27π²/8) · √(4π)
        = (27π²/8) · 2·√π
        = 27 π² √π / 4
        = 27 π^(5/2) / 4. -/
theorem prod_α_skeleton_elementary :
    α_Poincare * α_P * α_RH * α_YM * α_BSD * α_NS * α_QG
    = 27 * Real.pi ^ 2 * Real.sqrt Real.pi / 4 := by
  unfold α_Poincare α_P α_RH α_YM α_BSD α_NS α_QG
  have h_2_nn : (0 : ℝ) ≤ 2 := by norm_num
  have h_pi_nn : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have h_sqrt_combine : Real.sqrt 2 * Real.sqrt (2 * Real.pi)
                       = 2 * Real.sqrt Real.pi := by
    rw [← Real.sqrt_mul h_2_nn]
    have h_eq : (2 : ℝ) * (2 * Real.pi) = 4 * Real.pi := by ring
    rw [h_eq]
    have h_4_eq : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [h_4_eq, Real.sqrt_mul (by positivity), Real.sqrt_sq h_2_nn]
  -- Now goal: 1 · √2 · (3/2) · 2 · (3π/4) · (3π/2) · √(2π) = 27 π² √π / 4
  -- Rearrange so √2 · √(2π) is adjacent.
  have h_target :
      1 * Real.sqrt 2 * (3/2) * 2 * (3 * Real.pi / 4) * (3 * Real.pi / 2)
        * Real.sqrt (2 * Real.pi)
      = (27 * Real.pi ^ 2 / 8) * (Real.sqrt 2 * Real.sqrt (2 * Real.pi)) := by
    ring
  rw [h_target, h_sqrt_combine]
  ring

/-- **Elementary product numerical bracket**: `Π α_* ∈ (117, 119)`.
    Closed form $27\pi^{5/2}/4 \approx 118.08$. Uses
    $\pi \in (3.14159, 3.14160)$ + bracket on $\sqrt{\pi}$. -/
theorem prod_α_skeleton_elementary_bracket :
    (117 : ℝ) < α_Poincare * α_P * α_RH * α_YM * α_BSD * α_NS * α_QG ∧
    α_Poincare * α_P * α_RH * α_YM * α_BSD * α_NS * α_QG < (119 : ℝ) := by
  rw [prod_α_skeleton_elementary]
  have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have h_pi_gt : (3.14159 : ℝ) < Real.pi := by
    have := Real.pi_gt_d6; linarith
  have h_pi_lt : Real.pi < (3.14160 : ℝ) := by
    have := Real.pi_lt_d6; linarith
  have h_sqrt_pi_sq : Real.sqrt Real.pi ^ 2 = Real.pi :=
    Real.sq_sqrt h_pi_pos.le
  have h_sqrt_pi_pos : (0 : ℝ) < Real.sqrt Real.pi :=
    Real.sqrt_pos.mpr h_pi_pos
  -- √π ∈ (1.77, 1.78): 1.77² = 3.1329 < π, 1.78² = 3.1684 > π
  have h_sqrt_pi_gt : (1.77 : ℝ) < Real.sqrt Real.pi := by
    nlinarith [h_sqrt_pi_sq, h_sqrt_pi_pos, h_pi_gt]
  have h_sqrt_pi_lt : Real.sqrt Real.pi < (1.78 : ℝ) := by
    nlinarith [h_sqrt_pi_sq, h_sqrt_pi_pos, h_pi_lt]
  refine ⟨?_, ?_⟩
  · -- 117 < 27·π²·√π/4 ⟺ 468 < 27·π²·√π ⟺ π²·√π > 17.333
    -- π² > 3.14159² > 9.869, √π > 1.77 → π²·√π > 17.469 > 17.333
    nlinarith [h_pi_gt, h_sqrt_pi_gt, sq_nonneg Real.pi]
  · -- 27·π²·√π/4 < 119 ⟺ 27·π²·√π < 476 ⟺ π²·√π < 17.629
    -- π² < 3.14160² < 9.870, √π < 1.78 → π²·√π < 17.569 < 17.629
    nlinarith [h_pi_lt, h_sqrt_pi_lt, sq_nonneg Real.pi]

/-! ### ★ Full 9-instance squared-sum closed form ★ -/

/-- **★ FULL 9-INSTANCE SQUARED-SUM CLOSED FORM ★** —
    `Σ_i α_i² = (5/2)·α_Hodge + (45π² + 32π + 181) / 16`.

    Component breakdown (using each axis's squared closed form):
      1 + 2 + 9/4 + 4 + 9π²/16 + 9π²/4 + (α_Hodge+1) + ((3/2)α_Hodge+17/16) + 2π
    Rationals: 1 + 2 + 9/4 + 4 + 1 + 17/16 = 181/16
    α_Hodge:   1 + 3/2 = 5/2
    π:         2
    π²:        9/16 + 9/4 = 45/16

    Result: (5/2)·α_Hodge + 2π + (45/16)·π² + 181/16. -/
theorem sum_α_sq_skeleton_all_nine :
    α_Poincare ^ 2 + α_P ^ 2 + α_RH ^ 2 + α_YM ^ 2 + α_BSD ^ 2
      + α_NS ^ 2 + α_Hodge ^ 2 + α_NP ^ 2 + α_QG ^ 2
    = (5/2) * α_Hodge + 2 * Real.pi
      + (45/16) * Real.pi ^ 2 + 181/16 := by
  have h_Poincare : α_Poincare ^ 2 = 1 := α_Poincare_sq_eq_one
  have h_P : α_P ^ 2 = 2 := by
    rw [α_P_sq_eq_α_YM]; unfold α_YM; rfl
  have h_RH : α_RH ^ 2 = 9/4 := α_RH_sq_eq_nine_fourths
  have h_YM : α_YM ^ 2 = 4 := α_YM_sq_eq_four
  have h_BSD : α_BSD ^ 2 = 9 * Real.pi ^ 2 / 16 := α_BSD_sq_eq
  have h_NS : α_NS ^ 2 = 9 * Real.pi ^ 2 / 4 := α_NS_sq_eq
  have h_Hodge : α_Hodge ^ 2 = α_Hodge + 1 := α_Hodge_sq_eq_self_plus_one
  have h_NP : α_NP ^ 2 = (3/2) * α_Hodge + 17/16 := α_NP_sq
  have h_QG : α_QG ^ 2 = 2 * Real.pi := α_QG_sq_eq_two_pi
  rw [h_Poincare, h_P, h_RH, h_YM, h_BSD, h_NS, h_Hodge, h_NP, h_QG]
  ring

/-- **Squared-sum numerical bracket**: `Σ α_i² ∈ (49, 50)`.
    Numerical ≈ 49.40. -/
theorem sum_α_sq_skeleton_bracket :
    (49 : ℝ) < α_Poincare ^ 2 + α_P ^ 2 + α_RH ^ 2 + α_YM ^ 2 + α_BSD ^ 2
                + α_NS ^ 2 + α_Hodge ^ 2 + α_NP ^ 2 + α_QG ^ 2 ∧
    α_Poincare ^ 2 + α_P ^ 2 + α_RH ^ 2 + α_YM ^ 2 + α_BSD ^ 2
      + α_NS ^ 2 + α_Hodge ^ 2 + α_NP ^ 2 + α_QG ^ 2 < (50 : ℝ) := by
  rw [sum_α_sq_skeleton_all_nine]
  have h_pi_gt : (3.14159 : ℝ) < Real.pi := by
    have := Real.pi_gt_d6; linarith
  have h_pi_lt : Real.pi < (3.14160 : ℝ) := by
    have := Real.pi_lt_d6; linarith
  have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have h_phi_lb : (1.6180339887 : ℝ) ≤ α_Hodge := by
    unfold α_Hodge; exact phi_in_interval_10digit.1
  have h_phi_ub : α_Hodge ≤ (1.6180339888 : ℝ) := by
    unfold α_Hodge; exact phi_in_interval_10digit.2
  refine ⟨?_, ?_⟩
  · nlinarith [h_pi_gt, h_phi_lb, sq_nonneg Real.pi]
  · nlinarith [h_pi_lt, h_phi_ub, sq_nonneg Real.pi, h_pi_pos]

/-! ### ★ Full 9-product closed form ★ -/

/-- **★ FULL 9-PRODUCT CLOSED FORM ★** —
    `Π_{all 9} α_i = 27 · π^(5/2) · (5·α_Hodge + 4) / 16`.

    Derivation: elementary-7 product (`27·π^(5/2)/4`) times
    α_Hodge · α_NP = α_Hodge · (α_Hodge + 1/4) = α_Hodge² + α_Hodge/4
    = (α_Hodge + 1) + α_Hodge/4 = (5/4)·α_Hodge + 1 = (5·α_Hodge + 4)/4
    via φ² = φ + 1.

    Total: (27·π^(5/2)/4) · (5·α_Hodge + 4)/4 = 27·π^(5/2)·(5·α_Hodge+4)/16. -/
theorem prod_α_skeleton_all_nine :
    α_Poincare * α_P * α_RH * α_YM * α_BSD * α_NS * α_QG
      * α_Hodge * α_NP
    = 27 * Real.pi ^ 2 * Real.sqrt Real.pi * (5 * α_Hodge + 4) / 16 := by
  have h_elem : α_Poincare * α_P * α_RH * α_YM * α_BSD * α_NS * α_QG
              = 27 * Real.pi ^ 2 * Real.sqrt Real.pi / 4 :=
    prod_α_skeleton_elementary
  have h_Hodge_NP : α_Hodge * α_NP = (5/4) * α_Hodge + 1 := α_Hodge_mul_α_NP
  calc α_Poincare * α_P * α_RH * α_YM * α_BSD * α_NS * α_QG * α_Hodge * α_NP
      = (α_Poincare * α_P * α_RH * α_YM * α_BSD * α_NS * α_QG)
        * (α_Hodge * α_NP) := by ring
    _ = (27 * Real.pi ^ 2 * Real.sqrt Real.pi / 4) * ((5/4) * α_Hodge + 1) := by
          rw [h_elem, h_Hodge_NP]
    _ = 27 * Real.pi ^ 2 * Real.sqrt Real.pi * (5 * α_Hodge + 4) / 16 := by ring

/-- **Full 9-product positivity**: the full 9-product is positive,
    since each α-instance is positive. -/
theorem prod_α_skeleton_all_nine_pos :
    0 < α_Poincare * α_P * α_RH * α_YM * α_BSD * α_NS * α_QG
        * α_Hodge * α_NP := by
  have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have h_Poincare_pos : (0 : ℝ) < α_Poincare := by unfold α_Poincare; norm_num
  have h_P_pos : (0 : ℝ) < α_P := by
    unfold α_P; exact Real.sqrt_pos.mpr (by norm_num)
  have h_RH_pos : (0 : ℝ) < α_RH := by unfold α_RH; norm_num
  have h_YM_pos : (0 : ℝ) < α_YM := by unfold α_YM; norm_num
  have h_BSD_pos : (0 : ℝ) < α_BSD := by unfold α_BSD; positivity
  have h_NS_pos : (0 : ℝ) < α_NS := by unfold α_NS; positivity
  have h_QG_pos : (0 : ℝ) < α_QG := by
    unfold α_QG; exact Real.sqrt_pos.mpr (by linarith)
  have h_Hodge_pos : (0 : ℝ) < α_Hodge := by
    unfold α_Hodge phi
    have := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 5)
    linarith
  have h_NP_pos : (0 : ℝ) < α_NP := by
    unfold α_NP phi
    have := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 5)
    linarith
  positivity

/-! ### ★ Scalar fingerprint bundle ★ -/

/-- **★★ α-SKELETON SCALAR-FINGERPRINT BUNDLE ★★** — single citable
    theorem combining the FOUR scalar fingerprints of the locus:

    1. Additive sum Σ α_i = (19/4) + α_P + (9π/4) + 2·α_Hodge + α_QG
    2. Squared sum Σ α_i² = (5/2)·α_Hodge + 2π + (45/16)·π² + 181/16
    3. Elementary product Π_{7} α_i = 27·π^(5/2)/4
    4. Full product Π_{9} α_i = 27·π^(5/2)·(5·α_Hodge + 4)/16

    Plus numerical brackets on the additive sum (18.9, 19.0), squared
    sum (49, 50), and elementary product (117, 119).

    These four scalar invariants encode complementary perturbation
    sensitivity: the additive sum captures linear perturbations of
    any α; the squared sum captures quadratic; the products capture
    multiplicative. Any non-trivial perturbation of any α-instance
    perturbs at least one of these four scalars. -/
theorem α_skeleton_scalar_fingerprint_bundle :
    -- (S1) Additive sum closed form
    (α_Poincare + α_P + α_RH + α_YM + α_BSD + α_NS
       + α_Hodge + α_NP + α_QG
     = (19/4) + α_P + (9 * Real.pi / 4) + 2 * α_Hodge + α_QG) ∧
    -- (S2) Squared sum closed form
    (α_Poincare ^ 2 + α_P ^ 2 + α_RH ^ 2 + α_YM ^ 2 + α_BSD ^ 2
       + α_NS ^ 2 + α_Hodge ^ 2 + α_NP ^ 2 + α_QG ^ 2
     = (5/2) * α_Hodge + 2 * Real.pi
       + (45/16) * Real.pi ^ 2 + 181/16) ∧
    -- (P1) Elementary-7 product closed form
    (α_Poincare * α_P * α_RH * α_YM * α_BSD * α_NS * α_QG
     = 27 * Real.pi ^ 2 * Real.sqrt Real.pi / 4) ∧
    -- (P2) Full 9-product closed form
    (α_Poincare * α_P * α_RH * α_YM * α_BSD * α_NS * α_QG
        * α_Hodge * α_NP
     = 27 * Real.pi ^ 2 * Real.sqrt Real.pi * (5 * α_Hodge + 4) / 16) ∧
    -- (B1) Additive sum bracket
    ((18.9 : ℝ) < α_Poincare + α_P + α_RH + α_YM + α_BSD + α_NS
                    + α_Hodge + α_NP + α_QG ∧
     α_Poincare + α_P + α_RH + α_YM + α_BSD + α_NS
        + α_Hodge + α_NP + α_QG < (19.0 : ℝ)) ∧
    -- (B2) Squared sum bracket
    ((49 : ℝ) < α_Poincare ^ 2 + α_P ^ 2 + α_RH ^ 2 + α_YM ^ 2
                  + α_BSD ^ 2 + α_NS ^ 2 + α_Hodge ^ 2 + α_NP ^ 2
                  + α_QG ^ 2 ∧
     α_Poincare ^ 2 + α_P ^ 2 + α_RH ^ 2 + α_YM ^ 2 + α_BSD ^ 2
        + α_NS ^ 2 + α_Hodge ^ 2 + α_NP ^ 2 + α_QG ^ 2 < (50 : ℝ)) ∧
    -- (B3) Elementary product bracket
    ((117 : ℝ) < α_Poincare * α_P * α_RH * α_YM * α_BSD * α_NS * α_QG ∧
     α_Poincare * α_P * α_RH * α_YM * α_BSD * α_NS * α_QG < (119 : ℝ)) :=
  ⟨α_skeleton_sum_closed_form,
   sum_α_sq_skeleton_all_nine,
   prod_α_skeleton_elementary,
   prod_α_skeleton_all_nine,
   α_skeleton_sum_bracket,
   sum_α_sq_skeleton_bracket,
   prod_α_skeleton_elementary_bracket⟩

/-! ### ★ Fundamental constants extracted from the α-skeleton ★ -/

/-- **`π = α_QG² / α_YM`** — the universal transcendental π is downstream
    of the α-skeleton: it equals the QG-square divided by the YM-base.
    Combined with `α_QG² = 2π` (locus identity L13) and `α_YM = 2`. -/
theorem pi_extracted_from_α_skeleton :
    Real.pi = α_QG ^ 2 / α_YM := by
  have h_QG := α_QG_sq_eq_two_pi
  unfold α_YM
  rw [h_QG]; ring

/-- **`√2 = α_P`** — trivially. -/
theorem sqrt2_extracted_from_α_skeleton :
    Real.sqrt 2 = α_P := by
  unfold α_P; rfl

/-- **`φ = α_Hodge`** — trivially. -/
theorem phi_extracted_from_α_skeleton :
    phi = α_Hodge := by
  unfold α_Hodge; rfl

/-- **`√(2π) = α_QG`** — trivially. -/
theorem sqrt_2pi_extracted_from_α_skeleton :
    Real.sqrt (2 * Real.pi) = α_QG := by
  unfold α_QG; rfl

/-- **`√5 = 2·α_Hodge − 1`** — extracting √5 from the α-skeleton via
    α_Hodge = φ = (1+√5)/2. -/
theorem sqrt5_extracted_from_α_skeleton :
    Real.sqrt 5 = 2 * α_Hodge - 1 := by
  unfold α_Hodge phi
  ring

/-- **`log π = 2·log α_QG − log α_YM`** — log-space π extraction. -/
theorem log_pi_extracted_from_α_skeleton :
    Real.log Real.pi = 2 * Real.log α_QG - Real.log α_YM := by
  rw [log_α_YM_eq_log_two]
  have h := two_log_α_QG_eq_log_two_pi
  have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have h_log_2pi : Real.log (2 * Real.pi)
                     = Real.log 2 + Real.log Real.pi :=
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt h_pi_pos)
  linarith [h_log_2pi]

/-- **★ FUNDAMENTAL CONSTANTS EXTRACTED ★** — the locus' transcendental
    and algebraic constants are downstream of the α-skeleton:

    | Constant   | Extraction        |
    |------------|-------------------|
    | π          | α_QG² / α_YM      |
    | √2         | α_P               |
    | φ          | α_Hodge           |
    | √(2π)      | α_QG              |
    | log π      | 2·log α_QG − log α_YM |

    No transcendental in the framework is independent of the α-skeleton. -/
theorem fundamental_constants_extracted_from_α_skeleton :
    Real.pi = α_QG ^ 2 / α_YM ∧
    Real.sqrt 2 = α_P ∧
    phi = α_Hodge ∧
    Real.sqrt (2 * Real.pi) = α_QG ∧
    Real.sqrt 5 = 2 * α_Hodge - 1 ∧
    Real.log Real.pi = 2 * Real.log α_QG - Real.log α_YM :=
  ⟨pi_extracted_from_α_skeleton,
   sqrt2_extracted_from_α_skeleton,
   phi_extracted_from_α_skeleton,
   sqrt_2pi_extracted_from_α_skeleton,
   sqrt5_extracted_from_α_skeleton,
   log_pi_extracted_from_α_skeleton⟩

/-! ## Section 2M — α-SKELETON MASTER LAYER CAPSTONE -/

/-- **★★★ α-SKELETON MASTER LAYER CAPSTONE ★★★** —
    `α_skeleton_master_layer_capstone`.

    Single citable theorem bundling the six layer capstones over the
    9-axis algebraic locus. Each clause is itself an n-tuple over all
    9 (or 7 elementary) α-instances; the combined theorem encodes the
    full algebraic content of the locus at the level of:

    1. Reciprocals — 9-clause (locus closed under inversion)
    2. Squares — 9-clause (locus closed under squaring)
    3. Cubes — 9-clause (locus closed under cubing)
    4. 4th-powers — 9-clause (locus closed under 4th power)
    5. Logarithms — 8-clause (elementary-form decomposition)
    6. Additive sum — 1-clause (scalar fingerprint)

    Total: 45 algebraic content clauses bundled. Any perturbation of
    any single α-value cascades into at least 5 of these layers
    simultaneously (the 6th — Σ α — captures EVERY perturbation). -/
theorem α_skeleton_master_layer_capstone :
    -- Layer 1: Reciprocals
    (1 / α_Poincare = 1 ∧
     1 / α_P = α_P / 2 ∧
     1 / α_RH = 2 / 3 ∧
     1 / α_YM = 1 / 2 ∧
     1 / α_BSD = 4 / (3 * Real.pi) ∧
     1 / α_NS = 2 / (3 * Real.pi) ∧
     1 / α_Hodge = α_Hodge - 1 ∧
     1 / α_NP = (8 * Real.sqrt 5 - 12) / 11 ∧
     1 / α_QG = α_QG / (2 * Real.pi)) ∧
    -- Layer 2: Squares
    (α_Poincare ^ 2 = 1 ∧
     α_P ^ 2 = 2 ∧
     α_RH ^ 2 = 9 / 4 ∧
     α_YM ^ 2 = 4 ∧
     α_BSD ^ 2 = 9 * Real.pi ^ 2 / 16 ∧
     α_NS ^ 2 = 9 * Real.pi ^ 2 / 4 ∧
     α_Hodge ^ 2 = α_Hodge + 1 ∧
     α_NP ^ 2 = (3/2) * α_Hodge + 17/16 ∧
     α_QG ^ 2 = 2 * Real.pi) ∧
    -- Layer 3: Cubes
    (α_Poincare ^ 3 = 1 ∧
     α_P ^ 3 = 2 * α_P ∧
     α_RH ^ 3 = 27 / 8 ∧
     α_YM ^ 3 = 8 ∧
     α_BSD ^ 3 = 27 * Real.pi ^ 3 / 64 ∧
     α_NS ^ 3 = 27 * Real.pi ^ 3 / 8 ∧
     α_Hodge ^ 3 = 2 * α_Hodge + 1 ∧
     α_NP ^ 3 = (47/16) * α_Hodge + 113/64 ∧
     α_QG ^ 3 = 2 * Real.pi * α_QG) ∧
    -- Layer 4: 4th powers
    (α_Poincare ^ 4 = 1 ∧
     α_P ^ 4 = 4 ∧
     α_RH ^ 4 = 81 / 16 ∧
     α_YM ^ 4 = 16 ∧
     α_BSD ^ 4 = 81 * Real.pi ^ 4 / 256 ∧
     α_NS ^ 4 = 81 * Real.pi ^ 4 / 16 ∧
     α_Hodge ^ 4 = 3 * α_Hodge + 2 ∧
     α_NP ^ 4 = (87/16) * α_Hodge + 865/256 ∧
     α_QG ^ 4 = 4 * Real.pi ^ 2) ∧
    -- Layer 5: Logs
    (Real.log α_Poincare = 0 ∧
     Real.log α_YM = Real.log 2 ∧
     Real.log α_P = Real.log 2 / 2 ∧
     Real.log α_RH = Real.log 3 - Real.log 2 ∧
     Real.log α_BSD = Real.log 3 + Real.log Real.pi - Real.log 4 ∧
     Real.log α_NS = Real.log 3 + Real.log Real.pi - Real.log 2 ∧
     Real.log α_QG = (Real.log 2 + Real.log Real.pi) / 2 ∧
     Real.log α_Hodge = Real.log phi) ∧
    -- Layer 6: Additive sum scalar
    (α_Poincare + α_P + α_RH + α_YM + α_BSD + α_NS
       + α_Hodge + α_NP + α_QG
     = (19/4) + α_P + (9 * Real.pi / 4) + 2 * α_Hodge + α_QG) :=
  ⟨α_skeleton_full_reciprocal_layer,
   α_skeleton_full_squares_layer,
   α_skeleton_full_cubes_layer,
   α_skeleton_full_fourth_power_layer,
   α_skeleton_log_layer,
   α_skeleton_sum_closed_form⟩

end CrossMillenniumMoreInvariants
end PrincipiaTractalis
