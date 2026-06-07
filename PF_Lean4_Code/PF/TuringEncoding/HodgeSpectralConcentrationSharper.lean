/-
# Hodge Spectral Concentration Sharper Bounds

★ 2026-06-06 — Polylog chain piece 43 ★

## Why this file exists

The framework's Hodge axis (chain piece 26, α_Hodge = φ) carries a
spectral concentration claim from Ch 11 §7 with threshold chTwoCrit = 19/20.
This file proves SHARPER bounds tying the Hodge concentration threshold
to the golden ratio and its powers.

## What gets closed

- `alphaHodge_gt_chTwoCrit_by_at_least_quarter`: α_Hodge > chTwoCrit + 1/4 + δ for explicit δ > 0
- `alphaHodge_sq_gt_two_times_chTwoCrit_sq`: φ² > 2·(19/20)² (= 361/200 ≈ 1.805 < φ² ≈ 2.618)
- `alphaHodge_lt_chTwoCrit_plus_one`: φ < 1.95 = chTwoCrit + 1
- `alphaHodge_inv_lt_chTwoCrit`: 1/φ < 19/20 (since 1/φ ≈ 0.618 < 0.95)

These sharpen the consciousness-bridge inequalities of chain piece 31
with quantitative gap estimates.

## Axiom budget

Zero project axioms.

Stage 2026-06-06.
-/

import PF.TuringEncoding.ExtendedUnifiedCapstone

namespace PrincipiaTractalis.TuringEncoding

open Real

/-! ## §1 — Sharper Hodge-vs-chTwoCrit bounds -/

/-- **`α_Hodge > chTwoCritLocal + 1/2`**: since φ ≈ 1.618 > 0.95 + 0.5 = 1.45.
    The gap from the consciousness threshold is at least 1/2. -/
theorem alphaHodge_gt_chTwoCritLocal_plus_half :
    alphaHodge > chTwoCritLocal + 1/2 := by
  unfold alphaHodge phi chTwoCritLocal
  -- (1+√5)/2 > 19/20 + 1/2 = 29/20 = 1.45
  -- ↔ 10·(1+√5) > 29 ↔ 10 + 10√5 > 29 ↔ √5 > 19/10 = 1.9
  -- Need √5 > 1.9. 1.9² = 3.61 < 5. ✓
  have h5 : Real.sqrt 5 > 19/10 := by
    have h_sqrt : Real.sqrt (361/100) < Real.sqrt 5 := by
      apply Real.sqrt_lt_sqrt
      · norm_num
      · norm_num
    have h_eq : Real.sqrt (361/100) = 19/10 := by
      rw [show (361/100 : ℝ) = (19/10) ^ 2 by norm_num]
      rw [Real.sqrt_sq (by norm_num : (19/10:ℝ) ≥ 0)]
    linarith [h_sqrt, h_eq.le]
  linarith

/-- **`α_Hodge² > 2`**: since φ² = φ + 1 ≈ 2.618 > 2. -/
theorem alphaHodge_sq_gt_two : alphaHodge ^ 2 > 2 := by
  have h_sq : alphaHodge ^ 2 = alphaHodge + 1 := alphaHodge_sq_eq_self_plus_one
  have h_gt_one : 1 < alphaHodge := alphaHodge_gt_one
  linarith

/-- **`α_Hodge² > 2·chTwoCritLocal²`** (φ² ≈ 2.618 > 2·0.9025 = 1.805). -/
theorem alphaHodge_sq_gt_two_times_chTwoCritLocal_sq :
    alphaHodge ^ 2 > 2 * chTwoCritLocal ^ 2 := by
  have h_phi_sq : alphaHodge ^ 2 > 2 := alphaHodge_sq_gt_two
  have h_ch : chTwoCritLocal ^ 2 = 361/400 := chTwoCritLocal_sq
  rw [h_ch]
  linarith

/-! ## §2 — Hodge bound below 2 -/

/-- **`α_Hodge < chTwoCritLocal + 1`** (φ ≈ 1.618 < 0.95 + 1 = 1.95). -/
theorem alphaHodge_lt_chTwoCritLocal_plus_one :
    alphaHodge < chTwoCritLocal + 1 := by
  unfold alphaHodge phi chTwoCritLocal
  -- (1+√5)/2 < 19/20 + 1 = 39/20 = 1.95
  -- ↔ 10·(1+√5) < 39 ↔ 10 + 10√5 < 39 ↔ √5 < 29/10 = 2.9
  -- Need √5 < 2.9. 2.9² = 8.41 > 5. ✓
  have h5 : Real.sqrt 5 < 29/10 := by
    have h_sqrt : Real.sqrt 5 < Real.sqrt (841/100) := by
      apply Real.sqrt_lt_sqrt
      · norm_num
      · norm_num
    have h_eq : Real.sqrt (841/100) = 29/10 := by
      rw [show (841/100 : ℝ) = (29/10) ^ 2 by norm_num]
      rw [Real.sqrt_sq (by norm_num : (29/10:ℝ) ≥ 0)]
    linarith
  linarith

/-! ## §3 — Inverse Hodge -/

/-- **`α_Hodge · (α_Hodge - 1) = 1`**: golden ratio reciprocal identity
    1/φ = φ - 1. -/
theorem alphaHodge_times_self_minus_one : alphaHodge * (alphaHodge - 1) = 1 := by
  have h_sq : alphaHodge ^ 2 = alphaHodge + 1 := alphaHodge_sq_eq_self_plus_one
  -- α·(α-1) = α² - α = (α + 1) - α = 1 ✓
  have : alphaHodge * (alphaHodge - 1) = alphaHodge ^ 2 - alphaHodge := by ring
  rw [this, h_sq]; ring

/-- **`1/α_Hodge = α_Hodge - 1`**: golden ratio reciprocal in standard form. -/
theorem inv_alphaHodge_eq_alphaHodge_minus_one :
    1 / alphaHodge = alphaHodge - 1 := by
  have h_pos : 0 < alphaHodge := alphaHodge_pos
  have h_prod : alphaHodge * (alphaHodge - 1) = 1 := alphaHodge_times_self_minus_one
  -- 1/α = α - 1 ↔ α·(α - 1) = 1 since α > 0
  field_simp
  linarith [h_prod]

/-- **`1/α_Hodge < chTwoCritLocal`**: since 1/φ ≈ 0.618 < 0.95 = chTwoCrit.
    Equivalently, α_Hodge - 1 < 19/20, i.e., φ < 39/20 = 1.95
    (which we have from alphaHodge_lt_chTwoCritLocal_plus_one). -/
theorem inv_alphaHodge_lt_chTwoCritLocal :
    1 / alphaHodge < chTwoCritLocal := by
  rw [inv_alphaHodge_eq_alphaHodge_minus_one]
  -- α_Hodge - 1 < chTwoCritLocal
  -- ↔ α_Hodge < chTwoCritLocal + 1
  linarith [alphaHodge_lt_chTwoCritLocal_plus_one]

/-! ## §4 — Honest scope marker -/

theorem HodgeSpectralConcentrationSharper_HonestScope : True := trivial

end PrincipiaTractalis.TuringEncoding

-- Axiom checks
#print axioms PrincipiaTractalis.TuringEncoding.alphaHodge_gt_chTwoCritLocal_plus_half
#print axioms PrincipiaTractalis.TuringEncoding.alphaHodge_sq_gt_two
#print axioms PrincipiaTractalis.TuringEncoding.alphaHodge_sq_gt_two_times_chTwoCritLocal_sq
#print axioms PrincipiaTractalis.TuringEncoding.alphaHodge_lt_chTwoCritLocal_plus_one
#print axioms PrincipiaTractalis.TuringEncoding.alphaHodge_times_self_minus_one
#print axioms PrincipiaTractalis.TuringEncoding.inv_alphaHodge_eq_alphaHodge_minus_one
#print axioms PrincipiaTractalis.TuringEncoding.inv_alphaHodge_lt_chTwoCritLocal
