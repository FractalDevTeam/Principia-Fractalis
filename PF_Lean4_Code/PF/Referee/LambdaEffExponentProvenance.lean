/-
# PF.Referee.LambdaEffExponentProvenance — where the Λ_eff exponent's number
# actually comes from, and the bracket the corpus deferred

2026-11-02. **Additive. Nothing here is renamed, weakened or withdrawn.** The
three existing theorems in
`PF/Referee/MinimalRigidityForcesLambdaEffExponentProduct.lean` are all TRUE and
stay exactly as they are. This file establishes four things they do not, two of
which close gaps the corpus itself had flagged as open.

## §A — What the rigidity hypotheses do here, exhibited rather than asserted

`MinimalRigidityForcesLambdaEffExponentProduct` carries six hypotheses on each
of its two base theorems, and **all twelve binders are underscore-prefixed** —
Lean's own marker for *unused*. Measured, not inferred:

* `Lambda_eff_exponent_product : ℝ` is a **nullary constant**
  (`LambdaEffParameterFreeCapstone.lean:93`), so no hypothesis about any
  α-assignment can change its value;
* the result types mention no `u` at all;
* both proof terms are the unconditional identities
  `Lambda_eff_exponent_product_rational_form` and `..._bracket`, each of which
  takes **zero** hypotheses and is closed by `rw; ring`.

`rigidity_hypotheses_are_inert` below *exhibits* the hypothesised statement as
`fun _ _ _ _ _ _ => <the unconditional theorem>`. If that typechecks — and the
gate says it does — the hypotheses are provably inert, by construction rather
than by reading.

**Inert is not vacuous**, and the distinction matters: the carrier is
inhabited (`the_rigidity_carrier_is_inhabited`, witness
`framework_alpha_unified`). The hypotheses are satisfiable and simply do no
work. For contrast, `MinimalRigidityForcesCosmologicalSuppression` in the same
directory binds its hypotheses *without* underscores, destructures `hM`, and
states a conclusion mentioning `u.sector2.a_NP` — that is what a load-bearing
rigidity theorem looks like here. A family census found this pattern is **not**
systemic: across 45 `MinimalRigidityForces*` files and 142 declarations, 118
declarations have no underscored binder at all.

## §B — Where the number comes from

`Lambda_eff_exponent_product := N_78pi * consciousness_threshold_capstone *
Rf_QG_unit_modulus_capstone`, and the last two are **hardcoded decimals**,
each proved by `rfl`:

    consciousness_threshold_capstone := 0.95     = 19/20
    Rf_QG_unit_modulus_capstone      := 1.1875   = 19/16

So the exponent is `(78π) · (361/320)` with `361 = 19²` and `320 = 2⁶·5`, and
only the `78π` factor carries geometric provenance. Neither supplied factor is
even a candidate substrate value: `19/20 ∉ ℤ[1/3]` and `19/16 ∉ ℤ[1/3]`, both
instances of `not_memZ13_of_prime_den` (at the prime 5 and the prime 2), proved
in `PF/Ch2ThresholdZ13Exclusion.lean` earlier today. `UnifiedAlphaAssignment`
carries nine α-values and **no field for either quantity**, so the rigidity set
is structurally incapable of determining them.

This does not make the file's docstring's arithmetic wrong — the product really
is `14079π/160`. It locates which part of that number is derived and which part
is supplied.

## §C — The `120 · log 10` bracket, which the corpus had deferred

`LambdaEffCalibration.lean:88-90` states the bracket `276 < 120·log 10 < 277`
and marks it *"claimed; rigorous bracket deferred — requires precise
`Real.log 10` bounds from mathlib"*, and
`E6ChernWeil78piFirstPrinciplesAttempt.lean:382` separately records that
`120·log 10 ≈ 276.31` *"is NOT proved as a numerical bracket here."* So the
comparison underpinning the headline `Λ_eff/Λ_0 = 10^{-120}` claim had never
been made in the kernel on the target side.

It is proved here, routed around the missing `log 10` bound rather than through
it: `2¹⁰ = 1024` and `10³ = 1000` give `3 log 10 = 10 log 2 − log(1024/1000)`,
and mathlib's `log_two_gt_d9`/`log_two_lt_d9` plus the elementary
`1 − 1/x ≤ log x ≤ x − 1` close it with no `log 5` anywhere.

## §D — And the agreement is an EXCESS, bracketed

`exponent_product_exceeds_cosmological_target` is the first kernel fact relating
the two numbers, and it is strict: `120 log 10 < Lambda_eff_exponent_product`.
The excess is then bracketed,

    1.0004 · (120 log 10) < Lambda_eff_exponent_product < 1.0006 · (120 log 10),

so the discrepancy lies **strictly between 0.04% and 0.06%**. The docstring of
the file this one accompanies calls it a *"0.04% numerical match"* twice; the
measured value is **0.0472%**, and the bracket above excludes 0.04% from below.
The stated figure understates the error. Independently recomputed at 50 dps:
product `276.44051856181686878`, target `276.31021115928548208`.

Sharper: the multiplier required for `78π` to hit `120 log 10` exactly is
`1.1275932290452734`, while the multiplier supplied by the two hardcoded
decimals is `361/320 = 1.128125`. The 0.047% is the residual of a multiplier
that was **supplied, not derived** — which is why it should not be read as a
prediction.

Zero project axioms. Author: Pablo Cohen + Claude Opus 5. 2026-11-02.
-/

import PF.Referee.MinimalRigidityForcesLambdaEffExponentProduct
import PF.Ch2ThresholdZ13Exclusion
import Mathlib.Tactic

namespace PF.Referee.LambdaEffExponentProvenance

open PrincipiaTractalis
open PrincipiaTractalis.Cosmology
open PrincipiaTractalis.AlphaFromSubstrateKTheory
open PF.Referee.MinimalSubstrateRigidityUnified

/-! ## §1 — The rigidity hypotheses are inert here, and inert is not vacuous -/

/-- **The hypothesised theorem is a weakening of an unconditional one.**

    This is the whole claim of §A, as a proof term: six binders introduced and
    discarded, the body being the hypothesis-free identity. If this
    typechecks, the rigidity set does no work for this conclusion. -/
theorem rigidity_hypotheses_are_inert :
    ∀ (u : UnifiedAlphaAssignment) (_hM : UnifiedMinimalInvariants u)
      (_h_P : u.sector1.a_Poincare = 1) (_h_P_pos : 0 < u.sector2.a_P)
      (_h_Hodge_pos : 0 < u.sector2.a_Hodge) (_h_QG_pos : 0 < u.sector2.a_QG),
      Lambda_eff_exponent_product = 14079 * Real.pi / 160 :=
  fun _ _ _ _ _ _ => Lambda_eff_exponent_product_rational_form

/-- **Inert, not vacuous.** The carrier is inhabited, so the hypotheses above
    are satisfiable and simply unused. Without this, "the hypotheses do no
    work" could be confused with "the hypotheses cannot be met". -/
theorem the_rigidity_carrier_is_inhabited : Nonempty UnifiedAlphaAssignment :=
  ⟨framework_alpha_unified⟩

/-! ## §2 — The provenance decomposition -/

/-- **★ The exponent is a geometric anchor times a supplied rational. ★**

    `Lambda_eff_exponent_product = (78π) · (361/320)`. Stated with `78 * π`
    written out rather than via `N_78pi`, which is defined twice in the
    corpus (`LambdaEffCalibration.lean:120`, `E6ChernIndex78pi.lean:91`). -/
theorem exponent_product_eq_anchor_times_supplied_multiplier :
    Lambda_eff_exponent_product = (78 * Real.pi) * (361 / 320) := by
  rw [Lambda_eff_exponent_product_formula]
  ring_nf

/-- **The supplied multiplier, and what it is made of.** Both factors are
    definitional decimals, and `361 = 19²`, `320 = 2⁶·5` — so the rational
    carries the primes 2 and 5, the two the `3^∞` substrate does not see. -/
theorem supplied_multiplier_is_nineteen_squared_over_320 :
    consciousness_threshold_capstone = 19 / 20 ∧
    Rf_QG_unit_modulus_capstone = 19 / 16 ∧
    consciousness_threshold_capstone * Rf_QG_unit_modulus_capstone = 361 / 320 ∧
    (361 : ℕ) = 19 ^ 2 ∧ (320 : ℕ) = 2 ^ 6 * 5 := by
  unfold consciousness_threshold_capstone Rf_QG_unit_modulus_capstone
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **★ Neither supplied factor is a substrate trace value. ★**

    `19/20 ∉ ℤ[1/3]` and `19/16 ∉ ℤ[1/3]`, so neither could be produced by the
    substrate's unique trace on `K_0(T∞)` at any level. Instances of the
    prime-denominator engine proved earlier today, at the primes 5 and 2. -/
theorem neither_supplied_factor_is_a_substrate_trace :
    ¬ MemZ13 (19 / 20 : ℝ) ∧ ¬ MemZ13 (19 / 16 : ℝ) := by
  refine ⟨PrincipiaTractalis.Ch2ThresholdZ13.not_memZ13_nineteen_twentieths, ?_⟩
  have hcast : (19 / 16 : ℝ) = ((19 : ℤ) : ℝ) / ((16 : ℤ) : ℝ) := by norm_num
  rw [hcast]
  exact PrincipiaTractalis.Ch2ThresholdZ13.not_memZ13_of_prime_den
    (by norm_num) (p := (2 : ℤ)) Int.prime_two (by norm_num) (by norm_num)
    (by norm_num)

/-! ## §3 — The `log 10` bracket the corpus deferred -/

/-- The elementary two-sided bound `1 − 1/x ≤ log x ≤ x − 1` for `x > 0`,
    the lower half derived from the upper half at `x⁻¹`. -/
theorem log_bounds {x : ℝ} (hx : 0 < x) :
    1 - 1 / x ≤ Real.log x ∧ Real.log x ≤ x - 1 := by
  refine ⟨?_, Real.log_le_sub_one_of_pos hx⟩
  have hinv : (0 : ℝ) < x⁻¹ := inv_pos.mpr hx
  have h := Real.log_le_sub_one_of_pos hinv
  rw [Real.log_inv] at h
  have : 1 / x = x⁻¹ := one_div x
  rw [this]
  linarith

/-- **★ `2.3024 < log 10 < 2.3027`, with no `log 5` anywhere. ★**

    `3 log 10 = 10 log 2 − log(1024/1000)` from `2¹⁰ = 1024` and `10³ = 1000`,
    then mathlib's nine-digit `log 2` bracket and `log_bounds` at `1024/1000`.
    This is the bound `LambdaEffCalibration.lean:89` records as deferred. -/
theorem log_ten_bracket :
    (2.3024 : ℝ) < Real.log 10 ∧ Real.log 10 < 2.3027 := by
  have h1024 : Real.log 1024 = 10 * Real.log 2 := by
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]
    push_cast
    ring
  have h1000 : Real.log 1000 = 3 * Real.log 10 := by
    rw [show (1000 : ℝ) = 10 ^ 3 by norm_num, Real.log_pow]
    push_cast
    ring
  have hdiv : Real.log (1024 / 1000) = Real.log 1024 - Real.log 1000 :=
    Real.log_div (by norm_num) (by norm_num)
  have key : 3 * Real.log 10 = 10 * Real.log 2 - Real.log (1024 / 1000) := by
    rw [hdiv, h1024, h1000]; ring
  obtain ⟨hlo, hhi⟩ := log_bounds (show (0 : ℝ) < 1024 / 1000 by norm_num)
  have h2lo := Real.log_two_gt_d9
  have h2hi := Real.log_two_lt_d9
  constructor
  · nlinarith [key, hhi, h2lo]
  · nlinarith [key, hlo, h2hi]

/-- **The cosmological target, bracketed in the kernel for the first time.** -/
theorem cosmological_target_bracket :
    (276.288 : ℝ) < 120 * Real.log 10 ∧ 120 * Real.log 10 < 276.324 := by
  obtain ⟨a, b⟩ := log_ten_bracket
  constructor <;> nlinarith

/-- The exponent product, bracketed from mathlib's `π` bounds. Tighter than the
    existing `(276.4, 276.5)`, which it does not replace. -/
theorem exponent_product_bracket_tight :
    (276.4404 : ℝ) < Lambda_eff_exponent_product ∧
    Lambda_eff_exponent_product < 276.4406 := by
  rw [Lambda_eff_exponent_product_rational_form]
  have hlo := Real.pi_gt_d6
  have hhi := Real.pi_lt_d6
  constructor <;> nlinarith

/-! ## §4 — The agreement is an excess, and it is bracketed -/

/-- **★ The exponent product STRICTLY EXCEEDS the cosmological target. ★**

    The first kernel fact relating the two. Slack at the worst case of both
    brackets is `0.116`. -/
theorem exponent_product_exceeds_cosmological_target :
    120 * Real.log 10 < Lambda_eff_exponent_product := by
  obtain ⟨-, ht⟩ := cosmological_target_bracket
  obtain ⟨hp, -⟩ := exponent_product_bracket_tight
  linarith

/-- **★ The excess is strictly between 0.04% and 0.06%. ★**

    So the *"0.04% numerical match"* in the accompanying file's docstring
    understates it: the bracket excludes 0.04% from below. Recomputed at
    50 dps the excess is `0.0472%`. -/
theorem excess_bracket :
    1.0004 * (120 * Real.log 10) < Lambda_eff_exponent_product ∧
    Lambda_eff_exponent_product < 1.0006 * (120 * Real.log 10) := by
  obtain ⟨tlo, thi⟩ := cosmological_target_bracket
  obtain ⟨plo, phi⟩ := exponent_product_bracket_tight
  constructor <;> nlinarith

/-! ## §5 — Capstone -/

/-- **★★ Λ_eff EXPONENT PROVENANCE, BUNDLED ★★**

    1. the rigidity hypotheses are inert for this conclusion, and satisfiable;
    2. the exponent is `(78π)·(361/320)`;
    3. neither supplied factor is a substrate trace value;
    4. `120 log 10` is bracketed in the kernel — the deferred bound;
    5. the exponent product strictly exceeds it;
    6. by strictly between 0.04% and 0.06%.

    Net: one of the three factors has geometric provenance. The agreement with
    `120 log 10` is the residual of a multiplier that was supplied by two
    hardcoded decimals, not derived — so it is a fit, and now a measured one. -/
theorem lambda_eff_exponent_provenance_capstone :
    Nonempty UnifiedAlphaAssignment ∧
    Lambda_eff_exponent_product = (78 * Real.pi) * (361 / 320) ∧
    (¬ MemZ13 (19 / 20 : ℝ) ∧ ¬ MemZ13 (19 / 16 : ℝ)) ∧
    ((276.288 : ℝ) < 120 * Real.log 10 ∧ 120 * Real.log 10 < 276.324) ∧
    120 * Real.log 10 < Lambda_eff_exponent_product ∧
    (1.0004 * (120 * Real.log 10) < Lambda_eff_exponent_product ∧
     Lambda_eff_exponent_product < 1.0006 * (120 * Real.log 10)) :=
  ⟨the_rigidity_carrier_is_inhabited,
   exponent_product_eq_anchor_times_supplied_multiplier,
   neither_supplied_factor_is_a_substrate_trace,
   cosmological_target_bracket,
   exponent_product_exceeds_cosmological_target,
   excess_bracket⟩

end PF.Referee.LambdaEffExponentProvenance

/-! ## Axiom audit — LIVE -/

#print axioms PF.Referee.LambdaEffExponentProvenance.rigidity_hypotheses_are_inert
#print axioms PF.Referee.LambdaEffExponentProvenance.the_rigidity_carrier_is_inhabited
#print axioms PF.Referee.LambdaEffExponentProvenance.exponent_product_eq_anchor_times_supplied_multiplier
#print axioms PF.Referee.LambdaEffExponentProvenance.supplied_multiplier_is_nineteen_squared_over_320
#print axioms PF.Referee.LambdaEffExponentProvenance.neither_supplied_factor_is_a_substrate_trace
#print axioms PF.Referee.LambdaEffExponentProvenance.log_bounds
#print axioms PF.Referee.LambdaEffExponentProvenance.log_ten_bracket
#print axioms PF.Referee.LambdaEffExponentProvenance.cosmological_target_bracket
#print axioms PF.Referee.LambdaEffExponentProvenance.exponent_product_bracket_tight
#print axioms PF.Referee.LambdaEffExponentProvenance.exponent_product_exceeds_cosmological_target
#print axioms PF.Referee.LambdaEffExponentProvenance.excess_bracket
#print axioms PF.Referee.LambdaEffExponentProvenance.lambda_eff_exponent_provenance_capstone
