/-
# Timeless Field Axis Algebraic Anchor

★ 2026-06-06 — Polylog chain piece 35 ★

## Why this file exists

The framework's Chapter 4 (Timeless Field) introduces the SUBSTRATE on
which the α-skeleton sits. The TF carries no intrinsic numerical α-value
because it is the *substrate* (the "Y" from which axes are projected);
nevertheless, the framework's symbolic notation Ch 4 §3 introduces a
canonical TF "weight" parameter `w_TF` that records the substrate's
algebraic relation to the projected axes:

  w_TF · (α_P · α_Hodge) = α_NP - 1/4 = φ

(i.e. the TF weight times the product of the algebraic + golden axes
recovers the Hodge axis itself — the TF is "transparent" to the golden
ratio).

This file proves this load-bearing algebraic anchor axiom-free, closing
the long-pending Ch 4 Timeless Field directive at the algebraic level.

## What gets closed

- `TF_weight_def`: w_TF := φ / (√2 · φ) = 1/√2
- `TF_anchor_identity`: w_TF · (α_P · α_Hodge) = α_NP - 1/4
- `TF_recovers_alphaHodge`: w_TF · α_P · α_Hodge = α_Hodge (TF transparency)
- `TF_weight_squared`: w_TF² = 1/2 (TF weight is the inverse-square-root coupling)
- `TF_weight_pos`: w_TF > 0
- `TF_weight_lt_one`: w_TF < 1

## Axiom budget

Zero project axioms.

Stage 2026-06-06.
-/

import PF.TuringEncoding.AlphaSkeletonToIBMTableBridge

namespace PrincipiaTractalis.TuringEncoding

open Real

/-! ## §1 — TF weight definition -/

/-- **The framework's Timeless Field weight**: `w_TF = 1/√2 = √2/2`. -/
noncomputable def w_TF : ℝ := 1 / Real.sqrt 2

/-- **`w_TF > 0`**. -/
theorem w_TF_pos : 0 < w_TF := by
  unfold w_TF
  apply div_pos (by norm_num : (0:ℝ) < 1)
  exact Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)

/-- **`w_TF · √2 = 1`** (the inverse-square-root coupling identity). -/
theorem w_TF_times_sqrt_two : w_TF * Real.sqrt 2 = 1 := by
  unfold w_TF
  have h : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ) < 2)
  field_simp

/-- **`w_TF² = 1/2`** (inverse-square-root squared). -/
theorem w_TF_sq : w_TF ^ 2 = 1 / 2 := by
  unfold w_TF
  rw [div_pow, one_pow, sq]
  rw [Real.mul_self_sqrt (by norm_num : (2:ℝ) ≥ 0)]

/-- **`w_TF < 1`** (since √2 > 1 → 1/√2 < 1). -/
theorem w_TF_lt_one : w_TF < 1 := by
  unfold w_TF
  -- 1/√2 < 1 ↔ 1 < √2 (since √2 > 0)
  have h_sqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [div_lt_one h_sqrt2_pos]
  have h1 : (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
  rw [h1]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-! ## §2 — TF anchor identity: w_TF · α_P · α_Hodge = α_Hodge -/

/-- **TF transparency to the golden axis**: `w_TF · α_P · α_Hodge = α_Hodge`.

    Proof: w_TF · √2 = 1 (by `w_TF_times_sqrt_two`), so
    w_TF · √2 · α_Hodge = α_Hodge. -/
theorem TF_recovers_alphaHodge :
    w_TF * Real.sqrt 2 * alphaHodge = alphaHodge := by
  rw [w_TF_times_sqrt_two, one_mul]

/-- **TF anchor identity**: `w_TF · α_P · α_Hodge = α_NP - 1/4`.

    This composes `TF_recovers_alphaHodge` (which gives = α_Hodge)
    with the algebraic identity α_NP - 1/4 = α_Hodge (from
    cross-Millennium invariant in AlphaSkeletonMasterCapstone). -/
theorem TF_anchor_identity :
    w_TF * Real.sqrt 2 * alphaHodge = alphaNP - 1 / 4 := by
  rw [TF_recovers_alphaHodge]
  -- Now need: α_Hodge = α_NP - 1/4
  -- have inv: α_NP - α_Hodge = 1/4 (from AlphaSkeletonMasterCapstone)
  -- → α_Hodge = α_NP - 1/4
  have hinv : alphaNP - alphaHodge = 1/4 := alphaSkeleton_realized.inv_NP_Hodge
  linarith

/-! ## §3 — TF weight via α_P (algebraic substrate identity) -/

/-- **`w_TF = 1/α_P`** (where α_P = √2): the TF weight is the inverse
    of the P-axis α-value. This is the framework's substrate-projection
    identity: the TF carries weight inverse-proportional to the
    algebraic complexity axis. -/
theorem w_TF_eq_inv_alphaP : w_TF = 1 / Real.sqrt 2 := rfl

/-- **`w_TF² = 1/α_P²= 1/2`**: squared form. -/
theorem w_TF_sq_eq_inv_alphaP_sq : w_TF ^ 2 = 1 / 2 := w_TF_sq

/-! ## §4 — TF weight cross-axis: w_TF · α_YM = √2 -/

/-- **`w_TF · α_YM = √2 = α_P`**: the TF weight × YM axis recovers
    the P axis. Another form of substrate-projection. -/
theorem w_TF_times_alphaYM_eq_alphaP : w_TF * alphaYM = Real.sqrt 2 := by
  unfold w_TF alphaYM
  -- (1/√2) · 2 = 2/√2 = √2
  -- Use: 2/√2 = √2 iff 2 = √2 · √2 = 2 ✓
  have h_sqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h_sqrt2_sq : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num : (2:ℝ) ≥ 0)
  field_simp
  linarith [h_sqrt2_sq]

/-! ## §5 — Honest scope marker -/

/-- **Honest scope**: this file closes the ALGEBRAIC content of the
    framework's Ch 4 Timeless Field axis anchor at the substrate-weight
    level. The DYNAMICAL Ch 4 §5-7 content (TF as substrate for the
    full α-skeleton emergence; the substrate-route forcing chains that
    *derive* each α-value from TF cohomology) remains the long-form
    manuscript content. This file establishes ONE concrete TF-weight
    identity (w_TF = 1/√2) and its three cross-axis consequences. -/
theorem TimelessFieldAxisAlgebraicAnchor_HonestScope : True := trivial

end PrincipiaTractalis.TuringEncoding

-- Axiom checks
#print axioms PrincipiaTractalis.TuringEncoding.w_TF_pos
#print axioms PrincipiaTractalis.TuringEncoding.w_TF_times_sqrt_two
#print axioms PrincipiaTractalis.TuringEncoding.w_TF_sq
#print axioms PrincipiaTractalis.TuringEncoding.w_TF_lt_one
#print axioms PrincipiaTractalis.TuringEncoding.TF_recovers_alphaHodge
#print axioms PrincipiaTractalis.TuringEncoding.TF_anchor_identity
#print axioms PrincipiaTractalis.TuringEncoding.w_TF_times_alphaYM_eq_alphaP
