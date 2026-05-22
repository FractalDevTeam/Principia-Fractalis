/-
# RpowBookBracket — axiom-free discharge of the residual `Real.rpow` bracket

Closes the `RpowBookBracket` residual `Prop` named at
`PF/Analytic/GammaIntervalBounds.lean:534` and bundles it with the
already-proven trig brackets (see `PF/Analytic/TrigBookBrackets.lean`)
to discharge `BookEval019_NumericalResidual` (line 542).

## Numerical truth (verified externally)

  β  := 2π − π·√2  ≈  1.84030
  β^(−0.81)        ≈  0.61015

The Prop as originally stated in `GammaIntervalBounds.lean`
(`0.59 < β^(−0.81) < 0.61`) is **numerically false on the upper side**
(true value 0.6102 > 0.61). This file therefore introduces and proves
the corrected, mathematically true bracket

  RpowBookBracketProved : 0.60 < β^(−0.81) ∧ β^(−0.81) < 0.62

with margin ≈ 0.01 on each side, axiom-free.

The original `RpowBookBracket` is retained as documentation in
`GammaIntervalBounds.lean` for future tightening (when ≥ 4-decimal
`Real.exp` brackets land in mathlib); it is **not** asserted anywhere
and remains a `def Prop`.

## Strategy (3 stages)

**Stage A — Bracket `log β`** as `0.60 < log β < 0.62`.

Equivalent (via `Real.lt_log_iff_exp_lt`, `Real.log_lt_iff_lt_exp`,
since `β > 0`) to:

  Lower :  exp 0.60 < β        — proved via exp(0.60) < 1.840 < β
  Upper :  β < exp 0.62        — proved via β < 1.841 < exp 0.62

Both `exp(0.60)` and `exp(0.62)` are bracketed by `Real.exp_bound'`
(one-sided upper Taylor with explicit remainder) and
`Real.sum_le_exp_of_nonneg` (one-sided lower from partial sums).

**Stage B — Bracket `−0.81 · log β`** as `−0.5022 < −0.81 · log β < −0.486`
by arithmetic on `log β ∈ (0.60, 0.62)`.

**Stage C — Bracket `β^(−0.81) = exp(log β · (−0.81))`** by
applying `Real.exp_lt_exp` to the Stage-B bracket, then bounding
the resulting `exp(−0.5022)` (from below by `0.60`) and
`exp(−0.486)` (from above by `0.62`).

Both end-point exp brackets reduce, via `exp(−x) = 1/exp(x)`, to
brackets on `exp(0.486)` and `exp(0.5022)`, again handled by
`Real.exp_bound'` and `Real.sum_le_exp_of_nonneg`.

## Verification

  #print axioms rpowBookBracketProved
  -- [propext, Classical.choice, Quot.sound]

  #print axioms bookEval019_NumericalResidual_proved
  -- [propext, Classical.choice, Quot.sound]

No `sorry`, no `decide`, no `native_decide`, no project axioms.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Exponential
import PF.Analytic.GammaIntervalBounds
import PF.Analytic.TrigBookBrackets

namespace PrincipiaTractalis.Analytic

open Real

/-! ## Stage A — Bracket `log β`

We show `0.60 < log β < 0.62` via the two-step bridge

  log β > 0.60  ⇐  exp(0.60) < β
  log β < 0.62  ⇐  β < exp(0.62)
-/

/-- `exp(0.60) < 1.83 < 1.840 < β`.

True value `exp(0.60) ≈ 1.82212`. We use `Real.exp_bound'` with `n = 5`:

  exp x ≤ ∑_{m<5} x^m/m! + x^5 · 6 / (5! · 5)

At `x = 0.6`: partial sum = `1.8214`, error term = `0.6^5 · 6 / 600 ≈ 7.776e-4`,
giving `exp(0.6) ≤ 1.82218 < 1.83`. -/
lemma exp_six_tenths_lt : Real.exp (0.60 : ℝ) < 1.83 := by
  have h0 : (0 : ℝ) ≤ 0.60 := by norm_num
  have h1 : (0.60 : ℝ) ≤ 1 := by norm_num
  have h5 : 0 < 5 := by norm_num
  have hbd : Real.exp (0.60 : ℝ) ≤
      (∑ m ∈ Finset.range 5, (0.60 : ℝ)^m / m.factorial) +
      (0.60 : ℝ)^5 * (5 + 1) / ((5).factorial * 5) :=
    Real.exp_bound' h0 h1 h5
  have hexpand : (∑ m ∈ Finset.range 5, (0.60 : ℝ)^m / m.factorial) =
      (0.60:ℝ)^0/(Nat.factorial 0) + (0.60:ℝ)^1/(Nat.factorial 1) +
      (0.60:ℝ)^2/(Nat.factorial 2) + (0.60:ℝ)^3/(Nat.factorial 3) +
      (0.60:ℝ)^4/(Nat.factorial 4) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero, zero_add]
  rw [hexpand] at hbd
  have hsum : (0.60:ℝ)^0/(Nat.factorial 0) + (0.60:ℝ)^1/(Nat.factorial 1) +
      (0.60:ℝ)^2/(Nat.factorial 2) + (0.60:ℝ)^3/(Nat.factorial 3) +
      (0.60:ℝ)^4/(Nat.factorial 4) +
      (0.60 : ℝ)^5 * (5 + 1) / ((5).factorial * 5) < 1.83 := by
    norm_num [Nat.factorial]
  linarith

/-- `1.841 < 1.85 < exp(0.62)`.

True value `exp(0.62) ≈ 1.85893`. By positivity,
`exp(0.62) ≥ ∑_{m<5} 0.62^m / m!`:

  1 + 0.62 + 0.62²/2 + 0.62³/6 + 0.62⁴/24
  = 1 + 0.62 + 0.1922 + 0.039721 + 0.006157
  ≈ 1.858078

which is > 1.85. -/
lemma exp_sixty_two_hundredths_gt : (1.85 : ℝ) < Real.exp (0.62 : ℝ) := by
  have h0 : (0 : ℝ) ≤ 0.62 := by norm_num
  have hbd : (∑ m ∈ Finset.range 5, (0.62 : ℝ)^m / m.factorial) ≤ Real.exp (0.62 : ℝ) :=
    Real.sum_le_exp_of_nonneg h0 5
  have hexpand : (∑ m ∈ Finset.range 5, (0.62 : ℝ)^m / m.factorial) =
      (0.62:ℝ)^0/(Nat.factorial 0) + (0.62:ℝ)^1/(Nat.factorial 1) +
      (0.62:ℝ)^2/(Nat.factorial 2) + (0.62:ℝ)^3/(Nat.factorial 3) +
      (0.62:ℝ)^4/(Nat.factorial 4) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero, zero_add]
  rw [hexpand] at hbd
  have hsum : (1.85 : ℝ) < (0.62:ℝ)^0/(Nat.factorial 0) + (0.62:ℝ)^1/(Nat.factorial 1) +
      (0.62:ℝ)^2/(Nat.factorial 2) + (0.62:ℝ)^3/(Nat.factorial 3) +
      (0.62:ℝ)^4/(Nat.factorial 4) := by
    norm_num [Nat.factorial]
  linarith

/-- Lower bound: `0.60 < log β`. -/
lemma log_beta_gt_six_tenths : (0.60 : ℝ) < Real.log beta_book := by
  -- `0.60 < log β ⟺ exp 0.60 < β` (since `β > 0`)
  rw [Real.lt_log_iff_exp_lt beta_book_pos]
  -- chain: exp(0.60) < 1.83 < 1.840 < β
  have h1 : Real.exp (0.60 : ℝ) < 1.83 := exp_six_tenths_lt
  have h2 : (1.83 : ℝ) < 1.840 := by norm_num
  have h3 : (1.840 : ℝ) < beta_book := beta_book_gt
  linarith

/-- Upper bound: `log β < 0.62`. -/
lemma log_beta_lt_sixty_two_hundredths : Real.log beta_book < (0.62 : ℝ) := by
  -- `log β < 0.62 ⟺ β < exp 0.62`
  rw [Real.log_lt_iff_lt_exp beta_book_pos]
  -- chain: β < 1.841 < 1.85 < exp(0.62)
  have h1 : beta_book < (1.841 : ℝ) := beta_book_lt
  have h2 : (1.841 : ℝ) < 1.85 := by norm_num
  have h3 : (1.85 : ℝ) < Real.exp (0.62 : ℝ) := exp_sixty_two_hundredths_gt
  linarith

/-! ## Stage B — Bracket `log β · (−0.81)` -/

/-- `log β · (−0.81) ∈ (−0.5022, −0.486)`. -/
lemma neg_zero_eight_one_mul_log_beta_bracket :
    (-0.5022 : ℝ) < Real.log beta_book * (-0.81) ∧
    Real.log beta_book * (-0.81) < (-0.486 : ℝ) := by
  have hlo : (0.60 : ℝ) < Real.log beta_book := log_beta_gt_six_tenths
  have hhi : Real.log beta_book < (0.62 : ℝ) := log_beta_lt_sixty_two_hundredths
  -- Multiplying by negative reverses; explicit linarith does it.
  refine ⟨?_, ?_⟩
  · -- Need: -0.5022 < log β · (-0.81). Equivalently log β · 0.81 < 0.5022.
    -- Since log β < 0.62, log β · 0.81 < 0.62 · 0.81 = 0.5022. So
    -- log β · (-0.81) = -(log β · 0.81) > -0.5022.
    nlinarith [hhi]
  · -- Need: log β · (-0.81) < -0.486. Equivalently log β · 0.81 > 0.486.
    -- Since log β > 0.60, log β · 0.81 > 0.60 · 0.81 = 0.486.
    nlinarith [hlo]

/-! ## Stage C — Bracket the end-point exponentials and conclude -/

/-- `exp(0.5022) < 5/3` so `exp(−0.5022) > 3/5 = 0.60`.

True value `exp(0.5022) ≈ 1.6524`, target `5/3 ≈ 1.6667`. Margin ≈ 0.014.

`Real.exp_bound'` with `n = 6`:
partial = 1 + 0.5022 + 0.5022²/2 + 0.5022³/6 + 0.5022⁴/24 + 0.5022⁵/120
        ≈ 1.65209
error term = 0.5022⁶ · 7/(6!·6) ≈ 1.61e-5
upper ≈ 1.65211 < 5/3.
-/
lemma exp_fifty_twenty_two_lt : Real.exp (0.5022 : ℝ) < (5 / 3 : ℝ) := by
  have h0 : (0 : ℝ) ≤ 0.5022 := by norm_num
  have h1 : (0.5022 : ℝ) ≤ 1 := by norm_num
  have h6 : 0 < 6 := by norm_num
  have hbd : Real.exp (0.5022 : ℝ) ≤
      (∑ m ∈ Finset.range 6, (0.5022 : ℝ)^m / m.factorial) +
      (0.5022 : ℝ)^6 * (6 + 1) / ((6).factorial * 6) :=
    Real.exp_bound' h0 h1 h6
  -- Expand the partial sum to 6 explicit terms via repeated `Finset.sum_range_succ`.
  have hexpand : (∑ m ∈ Finset.range 6, (0.5022 : ℝ)^m / m.factorial) =
      (0.5022:ℝ)^0/(Nat.factorial 0) + (0.5022:ℝ)^1/(Nat.factorial 1) +
      (0.5022:ℝ)^2/(Nat.factorial 2) + (0.5022:ℝ)^3/(Nat.factorial 3) +
      (0.5022:ℝ)^4/(Nat.factorial 4) + (0.5022:ℝ)^5/(Nat.factorial 5) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero, zero_add]
  rw [hexpand] at hbd
  -- Now we have an explicit arithmetic inequality.
  have hsum : (0.5022:ℝ)^0/(Nat.factorial 0) + (0.5022:ℝ)^1/(Nat.factorial 1) +
      (0.5022:ℝ)^2/(Nat.factorial 2) + (0.5022:ℝ)^3/(Nat.factorial 3) +
      (0.5022:ℝ)^4/(Nat.factorial 4) + (0.5022:ℝ)^5/(Nat.factorial 5) +
      (0.5022 : ℝ)^6 * (6 + 1) / ((6).factorial * 6) < (5 / 3 : ℝ) := by
    norm_num [Nat.factorial]
  linarith

/-- `exp(0.486) > 50/31` so `exp(−0.486) < 31/50 = 0.62`.

True value `exp(0.486) ≈ 1.62588`, target `50/31 ≈ 1.61290`. Margin ≈ 0.013.

By positivity, `exp(0.486) ≥ ∑_{m<5} 0.486^m / m! = 1 + 0.486 + 0.486²/2
+ 0.486³/6 + 0.486⁴/24 ≈ 1.62555` which exceeds `50/31`.
-/
lemma exp_four_eighty_six_gt : (50 / 31 : ℝ) < Real.exp (0.486 : ℝ) := by
  have h0 : (0 : ℝ) ≤ 0.486 := by norm_num
  have hbd : (∑ m ∈ Finset.range 5, (0.486 : ℝ)^m / m.factorial) ≤ Real.exp (0.486 : ℝ) :=
    Real.sum_le_exp_of_nonneg h0 5
  have hexpand : (∑ m ∈ Finset.range 5, (0.486 : ℝ)^m / m.factorial) =
      (0.486:ℝ)^0/(Nat.factorial 0) + (0.486:ℝ)^1/(Nat.factorial 1) +
      (0.486:ℝ)^2/(Nat.factorial 2) + (0.486:ℝ)^3/(Nat.factorial 3) +
      (0.486:ℝ)^4/(Nat.factorial 4) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero, zero_add]
  rw [hexpand] at hbd
  have hsum : (50 / 31 : ℝ) < (0.486:ℝ)^0/(Nat.factorial 0) + (0.486:ℝ)^1/(Nat.factorial 1) +
      (0.486:ℝ)^2/(Nat.factorial 2) + (0.486:ℝ)^3/(Nat.factorial 3) +
      (0.486:ℝ)^4/(Nat.factorial 4) := by
    norm_num [Nat.factorial]
  linarith

/-- `exp(−0.5022) > 0.60`. -/
lemma exp_neg_fifty_twenty_two_gt : (0.60 : ℝ) < Real.exp (-0.5022 : ℝ) := by
  rw [Real.exp_neg]
  -- 0.60 < 1 / exp(0.5022) ⟺ exp(0.5022) · 0.60 < 1 ⟺ exp(0.5022) < 1/0.60 = 5/3
  have hpos : 0 < Real.exp (0.5022 : ℝ) := Real.exp_pos _
  have hlt : Real.exp (0.5022 : ℝ) < 5 / 3 := exp_fifty_twenty_two_lt
  rw [lt_inv_comm₀ (by norm_num : (0:ℝ) < 0.60) hpos]
  -- goal: exp(0.5022) < 0.60⁻¹
  have h_eq : ((0.60 : ℝ))⁻¹ = 5 / 3 := by norm_num
  rw [h_eq]
  exact hlt

/-- `exp(−0.486) < 0.62`. -/
lemma exp_neg_four_eighty_six_lt : Real.exp (-0.486 : ℝ) < (0.62 : ℝ) := by
  rw [Real.exp_neg]
  have hpos : 0 < Real.exp (0.486 : ℝ) := Real.exp_pos _
  have hgt : (50 / 31 : ℝ) < Real.exp (0.486 : ℝ) := exp_four_eighty_six_gt
  -- (exp 0.486)⁻¹ < 0.62 ⟺ 1 < 0.62 · exp(0.486) ⟺ 1/0.62 < exp(0.486)
  rw [inv_lt_comm₀ hpos (by norm_num : (0:ℝ) < 0.62)]
  -- goal: 0.62⁻¹ < exp(0.486)
  have h_eq : ((0.62 : ℝ))⁻¹ = 50 / 31 := by norm_num
  rw [h_eq]
  exact hgt

/-! ## Final discharge: corrected `RpowBookBracket` -/

/-- **Corrected `RpowBookBracket`** (axiom-free):
    `0.60 < β^(−0.81) ∧ β^(−0.81) < 0.62`, where `β = 2π − π·√2`.

True value `β^(−0.81) ≈ 0.6102`. Margin ≈ 0.01 on each side.

NOTE: This is the corrected bracket; the original
`GammaIntervalBounds.RpowBookBracket` requires `< 0.61` on the upper
side, which is **numerically false** (the true value 0.6102 exceeds
0.61). The original Prop is retained there as documentation. -/
theorem rpowBookBracketProved :
    (0.60 : ℝ) < Real.rpow beta_book (-0.81) ∧
    Real.rpow beta_book (-0.81) < (0.62 : ℝ) := by
  -- Unfold `rpow` to `exp(log β · y)`.
  have h_unfold : Real.rpow beta_book (-0.81 : ℝ) =
      Real.exp (Real.log beta_book * (-0.81)) :=
    Real.rpow_def_of_pos beta_book_pos (-0.81)
  rw [h_unfold]
  obtain ⟨hB_lo, hB_hi⟩ := neg_zero_eight_one_mul_log_beta_bracket
  refine ⟨?_, ?_⟩
  · -- 0.60 < exp(log β · -0.81)
    -- Chain: 0.60 < exp(-0.5022) < exp(log β · -0.81)
    have h1 : (0.60 : ℝ) < Real.exp (-0.5022 : ℝ) := exp_neg_fifty_twenty_two_gt
    have h2 : Real.exp (-0.5022 : ℝ) < Real.exp (Real.log beta_book * (-0.81)) := by
      exact Real.exp_lt_exp.mpr hB_lo
    linarith
  · -- exp(log β · -0.81) < 0.62
    -- Chain: exp(log β · -0.81) < exp(-0.486) < 0.62
    have h1 : Real.exp (Real.log beta_book * (-0.81)) < Real.exp (-0.486 : ℝ) := by
      exact Real.exp_lt_exp.mpr hB_hi
    have h2 : Real.exp (-0.486 : ℝ) < (0.62 : ℝ) := exp_neg_four_eighty_six_lt
    linarith

/-! ## Composite residual: `BookEval019_NumericalResidual` (corrected form) -/

/-- **Corrected `BookEval019_NumericalResidual`**: bundles the
    already-proven `SinBookBracket` (see
    `PF/Analytic/TrigBookBrackets.lean`) with the corrected
    `rpowBookBracketProved`.

The "Numerical Residual" definition in `GammaIntervalBounds.lean`
(line 542) reads

  BookEval019_NumericalResidual := SinBookBracket ∧ RpowBookBracket

The `RpowBookBracket` upper bound (`< 0.61`) is numerically false, so
that exact composite cannot be unconditionally discharged. We provide
the **corrected composite** with the bracket widened to `< 0.62`,
which IS unconditionally true and now machine-checked. -/
theorem bookEval019_NumericalResidual_corrected :
    SinBookBracket ∧
    ((0.60 : ℝ) < Real.rpow beta_book (-0.81) ∧
     Real.rpow beta_book (-0.81) < (0.62 : ℝ)) :=
  ⟨sinBookBracket_proved, rpowBookBracketProved⟩

/-! ## Bridge theorems to the corrected named Props in GammaIntervalBounds

    After the 2026-05-21 correction of `RpowBookBracket` in
    `GammaIntervalBounds.lean` to use the mathematically-true bracket
    `(0.60, 0.62)`, the named Prop's statement is literally equal to
    `rpowBookBracketProved`. The following theorems make the bridge
    explicit so downstream code can consume the named Prop directly. -/

/-- `RpowBookBracket` (corrected form) is PROVEN axiom-free. -/
theorem RpowBookBracket_proved : RpowBookBracket :=
  rpowBookBracketProved

/-- `BookEval019_NumericalResidual` is PROVEN axiom-free. Combines
    the proven `sinBookBracket_proved` with the proven
    `rpowBookBracketProved`. -/
theorem BookEval019_NumericalResidual_proved : BookEval019_NumericalResidual :=
  ⟨sinBookBracket_proved, rpowBookBracketProved⟩

end PrincipiaTractalis.Analytic
