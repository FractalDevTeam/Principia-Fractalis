/-
# α_PvsNP = 5/4 Identities

★ 2026-06-06 — Polylog chain piece 27 ★

## Why this file exists

The framework's P-vs-NP COMPARISON axis α-value is `α_PvsNP = 5/4`
(cross-Millennium-cascade-derived from a_Poincare = 1). This is the
*comparison* axis, NOT to be confused with α_NP = φ + 1/4 (the NP-class
self-adjointness axis). The two axes are algebraically distinct — this
file collects basic numerical identities for α_PvsNP = 5/4.

## What gets closed

- `alphaPvsNP_pos`: 0 < 5/4
- `alphaPvsNP_gt_one`: 1 < 5/4
- `alphaPvsNP_lt_two`: 5/4 < 2
- `alphaPvsNP_sq`: (5/4)² = 25/16
- `alphaPvsNP_ne_alphaNP`: 5/4 ≠ φ + 1/4 (the two NP-axes are distinct)
- Cross-Millennium relations to α_Poincaré

## Axiom budget

Zero project axioms.

Stage 2026-06-06.
-/

import PF.TuringEncoding.AlphaHodgeIdentities
import PF.TuringEncoding.AlphaYMIdentities
import PF.TuringEncoding.AlphaRHIdentities

namespace PrincipiaTractalis.TuringEncoding

open Real

/-! ## §1 — α_PvsNP definition and basic identities -/

/-- **The framework's P-vs-NP comparison axis α-value**: `α_PvsNP = 5/4`
    (cross-Millennium cascade from α_Poincaré = 1). -/
noncomputable def alphaPvsNP : ℝ := 5 / 4

/-- **`α_PvsNP > 0`**. -/
theorem alphaPvsNP_pos : 0 < alphaPvsNP := by unfold alphaPvsNP; norm_num

/-- **`α_PvsNP > 1`**. -/
theorem alphaPvsNP_gt_one : 1 < alphaPvsNP := by unfold alphaPvsNP; norm_num

/-- **`α_PvsNP < 2`**. -/
theorem alphaPvsNP_lt_two : alphaPvsNP < 2 := by unfold alphaPvsNP; norm_num

/-- **`α_PvsNP² = 25/16`**. -/
theorem alphaPvsNP_sq : alphaPvsNP ^ 2 = 25 / 16 := by
  unfold alphaPvsNP; norm_num

/-! ## §2 — Distinctness from α_NP (the two NP-axes are algebraically distinct) -/

/-- **`α_PvsNP = 5/4 ≠ φ + 1/4 = α_NP`**: the comparison axis and
    the NP-class self-adjointness axis are algebraically distinct.
    Substrate cascade gives 5/4; self-adjointness quadratic gives φ + 1/4. -/
theorem alphaPvsNP_ne_alphaNP : alphaPvsNP ≠ alphaNP := by
  unfold alphaPvsNP alphaNP phi
  intro h
  -- h : 5/4 = (1 + √5)/2 + 1/4
  -- ↔ √5 = 1 (false since √5 > 1)
  have h5 : Real.sqrt 5 > 1 := by
    have h1 : (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    calc (1 : ℝ) = Real.sqrt 1 := h1
      _ < Real.sqrt 5 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

/-! ## §3 — Cross-Millennium relations -/

/-- **`α_PvsNP = α_Poincaré + 1/4`** (with α_Poincaré = 1): cross-Millennium
    cascade identity. -/
theorem alphaPvsNP_eq_alphaPoincare_plus_quarter :
    alphaPvsNP = alphaPoincare + 1 / 4 := by
  unfold alphaPvsNP alphaPoincare; norm_num

/-- **`α_PvsNP · α_YM = 5/2` (with α_YM = 2)**. -/
theorem alphaPvsNP_times_alphaYM : alphaPvsNP * alphaYM = 5 / 2 := by
  unfold alphaPvsNP alphaYM; norm_num

/-- **`α_PvsNP + α_RH = 11/4` (with α_RH = 3/2)**. -/
theorem alphaPvsNP_plus_alphaRH : alphaPvsNP + alphaRH = 11 / 4 := by
  unfold alphaPvsNP alphaRH; norm_num

/-! ## §4 — The substrate-cascade obstruction (load-bearing) -/

/-- **5/4 does NOT satisfy the NP-axis self-adjointness quadratic
    `16α² − 24α − 11 = 0`** — the substrate cascade output is algebraically
    incompatible with the NP-axis quadratic. Concretely:
    16·(5/4)² − 24·(5/4) − 11 = 25 − 30 − 11 = −16 ≠ 0. -/
theorem alphaPvsNP_fails_NP_quadratic :
    16 * alphaPvsNP ^ 2 - 24 * alphaPvsNP - 11 = -16 := by
  unfold alphaPvsNP; norm_num

/-! ## §5 — Honest scope marker -/

theorem AlphaPvsNPIdentities_HonestScope : True := trivial

end PrincipiaTractalis.TuringEncoding

-- Axiom checks
#print axioms PrincipiaTractalis.TuringEncoding.alphaPvsNP_pos
#print axioms PrincipiaTractalis.TuringEncoding.alphaPvsNP_gt_one
#print axioms PrincipiaTractalis.TuringEncoding.alphaPvsNP_lt_two
#print axioms PrincipiaTractalis.TuringEncoding.alphaPvsNP_sq
#print axioms PrincipiaTractalis.TuringEncoding.alphaPvsNP_ne_alphaNP
#print axioms PrincipiaTractalis.TuringEncoding.alphaPvsNP_eq_alphaPoincare_plus_quarter
#print axioms PrincipiaTractalis.TuringEncoding.alphaPvsNP_times_alphaYM
#print axioms PrincipiaTractalis.TuringEncoding.alphaPvsNP_plus_alphaRH
#print axioms PrincipiaTractalis.TuringEncoding.alphaPvsNP_fails_NP_quadratic
