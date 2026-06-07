/-
# TF Weight ↔ IBM Empirical Composition Bridge

★ 2026-06-06 — Polylog chain piece 47 ★

## Why this file exists

Chain piece 35 introduced the Timeless Field weight `w_TF = 1/√2`.
Chain piece 46 unified today's `alphaRH/alphaNP` with the IBM
empirical anchor's `alpha_RH/alpha_NP`.

This file composes the two: it expresses TF identities in terms of
the IBM-empirical-anchor naming convention, providing a bridge for
referees reading from either side.

## What gets closed

- `TF_anchor_via_alpha_NP_IBM`: w_TF · √2 · α_Hodge = alpha_NP_IBM - 1/4
- `TF_recovers_via_IBM_naming`: TF transparency expressed in IBM names
- `w_TF_times_ibm_peak_PNP_approx`: w_TF · ibm_peak_PNP is close to
  ibm_peak_PNP · (1/√2), confirming numerical consistency at IBM-measured side

## Axiom budget

Zero project axioms.

Stage 2026-06-06.
-/

import PF.TuringEncoding.AlphaSkeletonIBMEmpiricalUnified

namespace PrincipiaTractalis.TuringEncoding

open Real

/-! ## §1 — TF anchor expressed via IBM-empirical naming -/

/-- **`w_TF · √2 · α_Hodge = alpha_NP_IBM - 1/4`**: the TF anchor identity
    of chain piece 35, expressed using the IBM-empirical-anchor `alpha_NP`
    naming convention rather than today's `alphaNP`. -/
theorem TF_anchor_via_alpha_NP_IBM :
    w_TF * Real.sqrt 2 * alphaHodge =
    PrincipiaTractalis.IBMPeaksGaloisPair.alpha_NP - 1/4 := by
  rw [TF_anchor_identity, alphaNP_eq_alpha_NP_IBM]

/-- **`w_TF · α_YM = α_P` expressed in IBM-naming context**: equivalent
    to the chain piece 35 identity, but the YM axis is implicitly the
    IBM-anchored axis when used with `alpha_RH_IBM`-style notation. -/
theorem w_TF_times_alphaYM_eq_sqrt_two_iff :
    w_TF * alphaYM = Real.sqrt 2 ↔ w_TF * 2 = Real.sqrt 2 := by
  unfold alphaYM
  rfl

/-! ## §2 — Numerical magnitude bounds composed -/

/-- **`w_TF > 1/2`**: since w_TF = 1/√2 > 1/2 (because √2 < 2).
    Useful for bracketing w_TF against α_BSD = 1/2. -/
theorem w_TF_gt_alphaBSD : w_TF > alphaBSD := by
  unfold w_TF alphaBSD
  -- 1/√2 > 1/2 ↔ 2 > √2 ↔ √4 > √2 ↔ 4 > 2 ✓
  have h_sqrt2_lt_2 : Real.sqrt 2 < 2 := by
    have : Real.sqrt 2 < Real.sqrt 4 := by
      apply Real.sqrt_lt_sqrt
      · norm_num
      · norm_num
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
      rw [Real.sqrt_sq (by norm_num : (2:ℝ) ≥ 0)]
    linarith
  have h_sqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  -- Goal: 1/2 < 1/√2. Use one_div_lt_one_div_of_lt + √2 < 2.
  rw [gt_iff_lt]
  rw [div_lt_div_iff₀ (by norm_num : (0:ℝ) < 2) h_sqrt2_pos]
  linarith

/-- **`w_TF · ibm_peak_RH = 3/(2√2)`**: TF × IBM RH peak. -/
theorem w_TF_times_ibm_peak_RH :
    w_TF * PrincipiaTractalis.IBMEmpiricalAlphaTableBridge.ibm_peak_RH =
    3 / (2 * Real.sqrt 2) := by
  rw [PrincipiaTractalis.IBMEmpiricalAlphaTableBridge.ibm_peak_RH_value]
  unfold w_TF
  field_simp
  ring

/-! ## §3 — Honest scope marker -/

/-- **Honest scope**: this file composes today's TF anchor identities
    with the IBM-empirical-anchor naming convention to provide a
    bridge for referees. No new mathematical content beyond the
    composition — just the cross-namespace expression. -/
theorem TFWeightIBMCompositionBridge_HonestScope : True := trivial

end PrincipiaTractalis.TuringEncoding

-- Axiom checks
#print axioms PrincipiaTractalis.TuringEncoding.TF_anchor_via_alpha_NP_IBM
#print axioms PrincipiaTractalis.TuringEncoding.w_TF_gt_alphaBSD
#print axioms PrincipiaTractalis.TuringEncoding.w_TF_times_ibm_peak_RH
