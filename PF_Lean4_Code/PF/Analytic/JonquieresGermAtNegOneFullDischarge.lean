/-
# Jonquières Germ at `s = -1` — Path C Factoring (Sharp Open Residual)

This file MIRRORS the `s = 0` closure architecture for the value
`s = -1`, factoring `JonquieresIdentityPointGermAtHalf (-1)` to a
single, sharp, named open analytic Prop — the s = -1 analog of
`BernoulliExpHasSumAtNegLogNhdsHalf` from
`JonquieresExpansionEqualsGeomTendstoPartialAtHalfDischarge.lean`.

## Strategic position vs. `s = 0`

The `s = 0` closure (`bernoulliFnHasSumOnSomeBall_proved` in
`BernoulliFnHasSumOnSomeBallDischarge.lean`) achieves
`JonquieresIdentityPointGermAtHalf 0` UNCONDITIONALLY via the
classical analytic Bernoulli generating function identity:
`(Σ B_n v^n/n!) · (e^v − 1) = v` (analytic Cauchy product). The
per-term bridge `ζ(-m)·(log z)^m/m! = B_{m+1}·(-log z)^m/(m+1)!`
collapses the s = 0 Jonquières ζ-series to the single-derivative
Bernoulli generating function.

At `s = -1` the analogous per-term identity is:
```
ζ(-1-m)·(log z)^m/m! = -B_{m+2}·(-log z)^m·(m+1)/(m+2)!.
```

The `(m+1)` factor reflects a SECOND-LEVEL derivative structure
(differentiating the Bernoulli generating function once more in v),
and the natural target HasSum is the analytic identity for
`d/dv[v/(e^v-1)] − const`, evaluated at `v = -log z`. This is NOT
present in mathlib as a `HasSum` lift (analogous gap to the s=0
case at one higher derivative order).

This file delivers (axiom-free, no `sorry`):

1. **`jonquieresZetaTerm_neg_one_eq_bernoulli_shift`** — the per-term
   algebraic identity, mirroring
   `jonquieresZetaTerm_zero_eq_bernoulli_shift` at one higher index.
2. **`JonquieresExpansionEqualsRationalSqGermAtHalf`** — the
   polylog-eliminated germ Prop at `s = -1` (analog of
   `JonquieresExpansionEqualsGeomGermAtHalf`).
3. **`jonquieresIdentityPointGermAtHalf_neg_one_of_rationalSq_germ`** —
   UNCONDITIONAL reduction: the polylog-eliminated germ Prop ⟹
   the classical germ identity at `(s, z) = (-1, 1/2)` (analog of
   `jonquieresIdentityPointGermAtHalf_zero_of_geom_germ`).
4. **`BernoulliDerivativeExpHasSumAtNegLogNhdsHalf`** — the SHARP
   open analytic Prop at s = -1: the `HasSum` form of the
   appropriate differentiated Bernoulli generating function at
   `v = -log z`, eventually in `nhds (1/2)`. Drop-in target for
   any future formalization of the analytic Bernoulli-derivative
   identity (analog of `BernoulliExpHasSumAtNegLogNhdsHalf`).
5. **`jonquieresExpansionEqualsRationalSqGermAtHalf_of_bernoulliDeriv`**
   — REDUCTION: the analytic Bernoulli-derivative identity ⟹ the
   polylog-eliminated germ Prop.
6. **`jonquieresIdentityPointGermAtHalf_neg_one_of_bernoulliDeriv`**
   — COMPOSED capstone: analytic Bernoulli-derivative identity ⟹
   `JonquieresIdentityPointGermAtHalf (-1)`.

## What this file does NOT deliver

A LITERAL proof of `JonquieresIdentityPointGermAtHalf (-1)`. The
SHARP open residual is `BernoulliDerivativeExpHasSumAtNegLogNhdsHalf`,
the analytic-HasSum form of `d/dv[v/(e^v-1)]` (with appropriate
constant subtraction) at `v = -log z`. Discharging this requires
either:
* Termwise differentiation of the `bernoulliFn` Taylor series
  (mathlib has `HasFPowerSeriesAt.hasDerivAt` for the FIRST
  derivative at the EXPANSION point, but no lifted-HasSum lemma
  for the differentiated series at every point of the disc); or
* Direct analytic identification of
  `1/v · [v/(e^v-1) − 1 + v/2] − 1/v² · [v/(e^v-1) − 1 + v/2 − ...]`
  with the explicit closed form `log z · z / (1 − z)² + ...`.

Both routes are multi-week classical analysis tracks (analogous in
spirit to the s = 0 closure, but at one higher derivative order).

Stage L27 — Path-C factoring of `JonquieresIdentityPointGermAtHalf (-1)`
to a single sharp analytic-Bernoulli-derivative residual.
-/

import PF.Analytic.JonquieresGermAtNegOneDischarge
import PF.Analytic.PolyLogAnalyticAtHalfNegInt
import PF.Analytic.ZetaShiftBoundNegNat
import PF.Analytic.GermAtHalfDischarge
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

namespace PrincipiaTractalis.Analytic.Sheaf

open Complex Filter Topology Set
open PrincipiaTractalis.Analytic

/-! ## Step 1: the per-term algebraic bridge at `s = -1` -/

/-- **Per-term `ζ ↔ Bernoulli` identity at `s = -1`**: for every `m : ℕ` and
    every `z : ℂ`,
    ```
    ζ(-1-m) · (log z)^m / m!  =  -(m+1) · B_{m+2} · (-log z)^m / (m+2)!.
    ```
    Pure algebra + `riemannZeta_neg_nat_eq_bernoulli` at `k = m + 1`.

    Mirrors `jonquieresZetaTerm_zero_eq_bernoulli_shift` from
    `JonquieresExpansionEqualsGeomTendstoPartialAtHalfDischarge.lean`,
    shifted by one in the Bernoulli index. -/
lemma jonquieresZetaTerm_neg_one_eq_bernoulli_shift (z : ℂ) (m : ℕ) :
    riemannZeta (-1 - m) * (Complex.log z) ^ m / (m.factorial : ℂ) =
      -(((m : ℂ) + 1) * (bernoulli (m + 2) : ℂ) * (-(Complex.log z)) ^ m /
        ((m + 2).factorial : ℂ)) := by
  -- ζ(-1-m) = ζ(-(m+1)) = (-1)^(m+1) · B_{m+2}/(m+2)
  have hzeta : riemannZeta (-1 - (m : ℂ)) =
      (-1 : ℂ) ^ (m + 1) * (bernoulli (m + 2) : ℂ) / ((m : ℂ) + 2) := by
    have h0 : (-1 - (m : ℂ)) = -((m + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [h0, riemannZeta_neg_nat_eq_bernoulli]
    push_cast; ring
  rw [hzeta]
  -- (m+2)! = (m+2)(m+1) · m!
  have hfact_succ : ((m + 2).factorial : ℂ) =
      ((m : ℂ) + 2) * ((m : ℂ) + 1) * (m.factorial : ℂ) := by
    have h : (m + 2).factorial = (m + 2) * ((m + 1) * m.factorial) := by
      rw [show m + 2 = (m + 1) + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]
    have hh : ((m + 2).factorial : ℂ) = ((m + 2 : ℕ) : ℂ) *
        (((m + 1 : ℕ) : ℂ) * (m.factorial : ℂ)) := by exact_mod_cast h
    rw [hh]; push_cast; ring
  -- (-log z)^m = (-1)^m · (log z)^m
  have hneg_pow : (-(Complex.log z)) ^ m = (-1 : ℂ) ^ m * (Complex.log z) ^ m := neg_pow _ m
  rw [hneg_pow, hfact_succ]
  -- Handle factorial ≠ 0.
  have hfact_ne : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hmp1 : ((m : ℂ) + 1) ≠ 0 := by
    have h : (m + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero m
    have : ((m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast h
    push_cast at this; exact this
  have hmp2 : ((m : ℂ) + 2) ≠ 0 := by
    have h : (m + 2 : ℕ) ≠ 0 := Nat.succ_ne_zero (m + 1)
    have : ((m + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast h
    push_cast at this; exact this
  -- Algebra: LHS = ((-1)^(m+1) · B / (m+2)) · u^m / m!,
  --         RHS = -((m+1) · B · (-1)^m · u^m / ((m+2)(m+1)·m!))
  --             = ((-1)^(m+1) · B · u^m) / ((m+2)·m!)
  --         (using -1 · (-1)^m = (-1)^(m+1) and cancelling (m+1)).
  field_simp
  rw [pow_succ]
  ring

/-! ## Step 2: analyticity of `jonquieresExpansion (-1)` at `z = 1/2` -/

/-- `(1/2 : ℂ) ∈ JonquieresAnalyticDomain ∩ {z | ‖log z‖ < 2π}`.

    We have `(1/2) ∈ JonquieresAnalyticDomain` via
    `half_mem_jonquieresDomain`, and `log(1/2) = -log 2` has norm
    `log 2 < 1 < 2π`. -/
private lemma half_mem_jonquieresDomain_inter_logBall :
    (1/2 : ℂ) ∈ JonquieresAnalyticDomain ∩
      {z : ℂ | ‖Complex.log z‖ < 2 * Real.pi} := by
  refine ⟨half_mem_jonquieresDomain, ?_⟩
  -- ‖log(1/2)‖ = log 2 < 2π
  show ‖Complex.log (1/2 : ℂ)‖ < 2 * Real.pi
  have h_log_half : Complex.log (1/2 : ℂ) = -((Real.log 2 : ℝ) : ℂ) := by
    have h1 : (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) := by push_cast; ring
    rw [h1, ← Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 1/2)]
    rw [show (1/2 : ℝ) = (2 : ℝ)⁻¹ from by norm_num]
    rw [Real.log_inv]
    push_cast; ring
  rw [h_log_half]
  rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]
  have h_log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [abs_of_pos h_log_two_pos]
  have h_log_two_lt_one : Real.log 2 < 1 := by
    have h_two_lt_e : (2 : ℝ) < Real.exp 1 := by
      have := Real.exp_one_gt_d9; linarith
    have := Real.log_lt_log (by norm_num : (0 : ℝ) < 2) h_two_lt_e
    rwa [Real.log_exp] at this
  have h_pi_gt : (1 : ℝ) < 2 * Real.pi := by
    have := Real.pi_gt_three; linarith
  linarith

/-- **`jonquieresExpansion (-1)` is analytic at `1/2` UNCONDITIONALLY**.

    From `jonquieresExpansion_analyticOnNhd_neg_nat_unconditional 1`
    + membership of `1/2` in the convergence subdomain. -/
theorem jonquieresExpansion_analyticAt_half_neg_one_unconditional :
    AnalyticAt ℂ (jonquieresExpansion (-1)) (1/2 : ℂ) := by
  have h_dom := jonquieresExpansion_analyticOnNhd_neg_nat_unconditional 1
  have h_mem : (1/2 : ℂ) ∈ JonquieresAnalyticDomain ∩
      {z : ℂ | ‖Complex.log z‖ < 2 * Real.pi} :=
    half_mem_jonquieresDomain_inter_logBall
  -- AnalyticOnNhd gives AnalyticAt at each point of the set
  have h_an := h_dom (1/2 : ℂ) h_mem
  -- Adjust the argument type: -(↑1 : ℂ) = -1
  have h_cast : (-((1 : ℕ) : ℂ)) = (-1 : ℂ) := by push_cast; ring
  rw [h_cast] at h_an
  exact h_an

/-! ## Step 3: the polylog-eliminated germ Prop at `s = -1` -/

/-- **Polylog-free germ Prop at `(s, z) = (-1, 1/2)`**.

    The Jonquières expansion at `s = -1` agrees with the rational
    function `z/(1-z)^2` on a neighborhood of `1/2`. This is the
    s = -1 analog of `JonquieresExpansionEqualsGeomGermAtHalf`
    (the s = 0 polylog-free germ). The polylog has been ELIMINATED
    using its unconditional closed form `polyLog (-1) z = z/(1-z)^2`
    on `Metric.ball 0 1` (theorem `polyLog_neg_one_eq_geom_sq`). -/
def JonquieresExpansionEqualsRationalSqGermAtHalf : Prop :=
  (jonquieresExpansion (-1)) =ᶠ[nhds (1/2 : ℂ)]
    (fun z : ℂ => z / (1 - z)^2)

/-! ## Step 4: UNCONDITIONAL reduction (rational-sq germ ⟹ classical germ) -/

/-- **`polyLog (-1) =ᶠ[nhds (1/2 : ℂ)] (fun z => z/(1-z)^2)`**.

    On the open unit ball (a neighborhood of `1/2`), the polylog at
    `s = -1` equals the rational function `z/(1-z)^2` pointwise
    (theorem `polyLog_neg_one_eq_geom_sq`). -/
theorem polyLog_neg_one_eventuallyEq_rationalSq_at_half :
    (polyLog (-1)) =ᶠ[nhds (1/2 : ℂ)] (fun z : ℂ => z / (1 - z)^2) := by
  have h_unit_nhd : Metric.ball (0 : ℂ) 1 ∈ nhds (1/2 : ℂ) :=
    Metric.isOpen_ball.mem_nhds half_mem_ball_one
  filter_upwards [h_unit_nhd] with z hz
  have h_norm : ‖z‖ < 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  exact polyLog_neg_one_eq_geom_sq z h_norm

/-- **UNCONDITIONAL reduction**: the polylog-eliminated rational-sq
    germ Prop ⟹ `JonquieresIdentityPointGermAtHalf (-1)`.

    NO analyticity hypothesis required. Mirrors
    `jonquieresIdentityPointGermAtHalf_zero_of_geom_germ`. -/
theorem jonquieresIdentityPointGermAtHalf_neg_one_of_rationalSq_germ
    (h : JonquieresExpansionEqualsRationalSqGermAtHalf) :
    JonquieresIdentityPointGermAtHalf (-1) := by
  unfold JonquieresIdentityPointGermAtHalf JonquieresIdentityPointGerm
  unfold JonquieresExpansionEqualsRationalSqGermAtHalf at h
  -- polyLog (-1) =ᶠ z/(1-z)^2 (unconditional) AND jonquieresExpansion (-1) =ᶠ z/(1-z)^2
  -- Transitivity: polyLog (-1) =ᶠ z/(1-z)^2 =ᶠ jonquieresExpansion (-1).
  exact polyLog_neg_one_eventuallyEq_rationalSq_at_half.trans h.symm

/-! ## Step 4.5: Identity-theorem upgrade — frequent ⟹ germ at `s = -1` -/

/-- **`fun z => z / (1 - z)^2` is analytic at `1/2`**.

    The denominator `(1 - 1/2)^2 = 1/4 ≠ 0`, so `AnalyticAt.div`
    applies. Mirrors `rational_geom_analyticAt_half` from
    `JonquieresGermAtHalfZeroSinglePoint.lean`. -/
theorem rational_sq_analyticAt_half :
    AnalyticAt ℂ (fun z : ℂ => z / (1 - z)^2) (1/2 : ℂ) := by
  have h_num : AnalyticAt ℂ (fun z : ℂ => z) (1/2 : ℂ) := analyticAt_id
  have h_den_base : AnalyticAt ℂ (fun z : ℂ => (1 : ℂ) - z) (1/2 : ℂ) :=
    analyticAt_const.sub analyticAt_id
  have h_den : AnalyticAt ℂ (fun z : ℂ => ((1 : ℂ) - z)^2) (1/2 : ℂ) :=
    h_den_base.fun_pow 2
  have h_den_ne : (fun z : ℂ => ((1 : ℂ) - z)^2) (1/2 : ℂ) ≠ 0 := by
    show ((1 : ℂ) - 1/2)^2 ≠ 0
    norm_num
  exact h_num.fun_div h_den h_den_ne

/-- **IDENTITY-THEOREM upgrade** at `s = -1`: from the polylog-free
    FREQUENT agreement Prop `JonquieresExpansionEqualsRationalAtNegOne`,
    derive the polylog-free GERM Prop
    `JonquieresExpansionEqualsRationalSqGermAtHalf`.

    Both `fun z => z/(1-z)^2` and `jonquieresExpansion (-1)` are
    analytic at `1/2`, so by mathlib's local identity theorem
    `AnalyticAt.frequently_eq_iff_eventually_eq`, frequent agreement
    in `𝓝[≠] (1/2)` is equivalent to germ equality in `nhds (1/2)`.

    Mirrors `jonquieresExpansionEqualsGeomGermAtHalf_of_frequent` from
    `JonquieresGermAtHalfZeroSinglePoint.lean` at `s = -1`. -/
theorem jonquieresExpansionEqualsRationalSqGermAtHalf_of_frequent
    (h_freq : JonquieresExpansionEqualsRationalAtNegOne) :
    JonquieresExpansionEqualsRationalSqGermAtHalf := by
  unfold JonquieresExpansionEqualsRationalSqGermAtHalf
  unfold JonquieresExpansionEqualsRationalAtNegOne at h_freq
  -- h_freq: ∃ᶠ z in 𝓝[≠] (1/2 : ℂ), z / (1 - z)^2 = jonquieresExpansion (-1) z
  -- Goal: jonquieresExpansion (-1) =ᶠ[nhds (1/2)] (fun z => z/(1-z)^2)
  have h_sym : ∃ᶠ z in 𝓝[≠] (1/2 : ℂ),
      jonquieresExpansion (-1) z = z / (1 - z)^2 :=
    h_freq.mp (Filter.Eventually.of_forall (fun _ heq => heq.symm))
  exact (AnalyticAt.frequently_eq_iff_eventually_eq
    jonquieresExpansion_analyticAt_half_neg_one_unconditional
    rational_sq_analyticAt_half).mp h_sym

/-- **COMPOSED CAPSTONE via frequent agreement**: the polylog-free
    FREQUENT agreement Prop `JonquieresExpansionEqualsRationalAtNegOne`
    ⟹ the classical germ identity at `(s, z) = (-1, 1/2)`.

    UNCONDITIONAL. The cheapest closure path at `s = -1` to date:
    closure of `JonquieresIdentityPointGermAtHalf (-1)` requires only
    closure of `JonquieresExpansionEqualsRationalAtNegOne` (a single
    sequence/frequent-agreement constructor target). -/
theorem jonquieresIdentityPointGermAtHalf_neg_one_of_frequent
    (h_freq : JonquieresExpansionEqualsRationalAtNegOne) :
    JonquieresIdentityPointGermAtHalf (-1) :=
  jonquieresIdentityPointGermAtHalf_neg_one_of_rationalSq_germ
    (jonquieresExpansionEqualsRationalSqGermAtHalf_of_frequent h_freq)

/-! ## Step 5: the sharp open Prop — analytic Bernoulli-derivative HasSum at -log z -/

/-- **Sharp open analytic Prop at `s = -1`**: the analytic-`HasSum`
    form of the targeted Bernoulli-derivative-like identity at
    `v = -log z`, eventually in `nhds (1/2)`.

    The per-term value is exactly the s = -1 ζ-term
    (via `jonquieresZetaTerm_neg_one_eq_bernoulli_shift`), and the
    target value is `z/(1-z)^2 − jonquieresGammaTerm (-1) z`. Thus
    the HasSum content of the Prop is:
    ```
    ∀ᶠ z in nhds (1/2 : ℂ),
      HasSum (fun k : ℕ => -(↑k+1) · B_{k+2} · (-log z)^k / (k+2)!)
        (z/(1-z)^2 − jonquieresGammaTerm (-1) z).
    ```
    Mathlib has NO direct `HasSum` lift of the differentiated
    Bernoulli generating function at every point of the disc
    `|v| < 2π`; this is the analog at s = -1 of
    `BernoulliExpHasSumAtNegLogNhdsHalf`. -/
def BernoulliDerivativeExpHasSumAtNegLogNhdsHalf : Prop :=
  ∀ᶠ z in nhds (1/2 : ℂ),
    HasSum (fun k : ℕ => -(((k : ℂ) + 1) * (bernoulli (k + 2) : ℂ) *
            (-(Complex.log z))^k / ((k + 2).factorial : ℂ)))
      (z / (1 - z)^2 - jonquieresGammaTerm (-1) z)

/-! ## Step 6: REDUCTION — analytic Bernoulli-derivative ⟹ rational-sq germ -/

/-- **DISCHARGE**: the analytic Bernoulli-derivative identity at
    `v = -log z` (eventually in `nhds (1/2)`) implies the polylog-free
    rational-sq germ Prop
    `JonquieresExpansionEqualsRationalSqGermAtHalf`.

    Uses the per-term identity `jonquieresZetaTerm_neg_one_eq_bernoulli_shift`
    + `HasSum.tsum_eq` + unfolding `jonquieresExpansion`. Mirrors
    `jonquieresExpansionEqualsGeomTendstoPartialAtHalf_of_bernoulli`. -/
theorem jonquieresExpansionEqualsRationalSqGermAtHalf_of_bernoulliDeriv
    (h : BernoulliDerivativeExpHasSumAtNegLogNhdsHalf) :
    JonquieresExpansionEqualsRationalSqGermAtHalf := by
  unfold JonquieresExpansionEqualsRationalSqGermAtHalf
  unfold BernoulliDerivativeExpHasSumAtNegLogNhdsHalf at h
  filter_upwards [h] with z hHS
  -- hHS : HasSum (fun k => -(k+1)·B_{k+2}·(-log z)^k/(k+2)!)
  --              (z/(1-z)^2 - jonquieresGammaTerm (-1) z)
  -- Goal: jonquieresExpansion (-1) z = z/(1-z)^2.
  -- Step A: each summand equals jonquieresZetaTerm (-1) z k via per-term identity.
  have h_target_terms :
      HasSum (fun k : ℕ => jonquieresZetaTerm (-1) z k)
        (z / (1 - z)^2 - jonquieresGammaTerm (-1) z) := by
    refine hHS.congr_fun (fun k => ?_)
    -- Goal: -(k+1)·B_{k+2}·(-log z)^k/(k+2)! = jonquieresZetaTerm (-1) z k
    unfold jonquieresZetaTerm
    have h_cast : ((-1 : ℂ) - (k : ℂ)) = ((-1 : ℂ) - k) := by ring
    rw [h_cast]
    -- The per-term identity gives ζ(-1-k)·(log z)^k/k! = -(k+1)·B_{k+2}·(-log z)^k/(k+2)!
    rw [(jonquieresZetaTerm_neg_one_eq_bernoulli_shift z k)]
  -- Step B: tsum of jonquieresZetaTerm = z/(1-z)^2 - jonquieresGammaTerm (-1) z
  have h_tsum_value :
      jonquieresZetaSeries (-1) z = z / (1 - z)^2 - jonquieresGammaTerm (-1) z := by
    unfold jonquieresZetaSeries
    exact h_target_terms.tsum_eq
  -- Step C: unfold jonquieresExpansion (-1) z = Γ + ζ-series
  unfold jonquieresExpansion
  rw [h_tsum_value]
  ring

/-! ## Step 7: COMPOSED CAPSTONE — analytic Bernoulli-derivative ⟹ classical germ at (-1, 1/2) -/

/-- **COMPOSED CAPSTONE**: the analytic Bernoulli-derivative identity
    `BernoulliDerivativeExpHasSumAtNegLogNhdsHalf` ⟹ the classical
    Jonquières germ identity `JonquieresIdentityPointGermAtHalf (-1)`.

    Composes the discharge with the unconditional reduction
    `jonquieresIdentityPointGermAtHalf_neg_one_of_rationalSq_germ`.
    Mirrors `jonquieresIdentityPointGermAtHalf_zero_of_bernoulli`. -/
theorem jonquieresIdentityPointGermAtHalf_neg_one_of_bernoulliDeriv
    (h : BernoulliDerivativeExpHasSumAtNegLogNhdsHalf) :
    JonquieresIdentityPointGermAtHalf (-1) :=
  jonquieresIdentityPointGermAtHalf_neg_one_of_rationalSq_germ
    (jonquieresExpansionEqualsRationalSqGermAtHalf_of_bernoulliDeriv h)

end PrincipiaTractalis.Analytic.Sheaf

/-! ## Axiom audit -/

section AxiomAudit
open PrincipiaTractalis.Analytic.Sheaf
#guard_msgs(drop info) in
#print axioms jonquieresZetaTerm_neg_one_eq_bernoulli_shift
#guard_msgs(drop info) in
#print axioms jonquieresExpansion_analyticAt_half_neg_one_unconditional
#guard_msgs(drop info) in
#print axioms polyLog_neg_one_eventuallyEq_rationalSq_at_half
#guard_msgs(drop info) in
#print axioms jonquieresIdentityPointGermAtHalf_neg_one_of_rationalSq_germ
#guard_msgs(drop info) in
#print axioms jonquieresExpansionEqualsRationalSqGermAtHalf_of_bernoulliDeriv
#guard_msgs(drop info) in
#print axioms jonquieresIdentityPointGermAtHalf_neg_one_of_bernoulliDeriv
#guard_msgs(drop info) in
#print axioms rational_sq_analyticAt_half
#guard_msgs(drop info) in
#print axioms jonquieresExpansionEqualsRationalSqGermAtHalf_of_frequent
#guard_msgs(drop info) in
#print axioms jonquieresIdentityPointGermAtHalf_neg_one_of_frequent
end AxiomAudit

/-!
## Manifest

This file delivers (axiom-free, no `sorry`) the Path C factoring of
`JonquieresIdentityPointGermAtHalf (-1)`:

* `jonquieresZetaTerm_neg_one_eq_bernoulli_shift` — per-term algebraic
  bridge:
  `ζ(-1-m)·(log z)^m/m! = -(m+1)·B_{m+2}·(-log z)^m/(m+2)!`,
  axiom-free via `riemannZeta_neg_nat_eq_bernoulli` at index `m+1`.

* `jonquieresExpansion_analyticAt_half_neg_one_unconditional` —
  `jonquieresExpansion (-1)` is analytic at `1/2`, unconditionally.
  From `jonquieresExpansion_analyticOnNhd_neg_nat_unconditional 1` +
  membership of `1/2` in the convergence subdomain.

* `polyLog_neg_one_eventuallyEq_rationalSq_at_half` —
  `polyLog (-1) =ᶠ[nhds(1/2)] z/(1-z)^2`, axiom-free via
  `polyLog_neg_one_eq_geom_sq` on the open unit ball.

* `JonquieresExpansionEqualsRationalSqGermAtHalf` (def) — the
  polylog-eliminated germ Prop at `s = -1`.

* `jonquieresIdentityPointGermAtHalf_neg_one_of_rationalSq_germ` —
  UNCONDITIONAL reduction (polylog-free germ ⟹ classical germ at
  `(-1, 1/2)`).

* `BernoulliDerivativeExpHasSumAtNegLogNhdsHalf` (def) — the SHARP
  open analytic Prop at `s = -1`, the differentiated-Bernoulli
  analog of `BernoulliExpHasSumAtNegLogNhdsHalf`.

* `jonquieresExpansionEqualsRationalSqGermAtHalf_of_bernoulliDeriv`
  — REDUCTION: analytic Bernoulli-derivative identity ⟹
  polylog-free germ Prop.

* `jonquieresIdentityPointGermAtHalf_neg_one_of_bernoulliDeriv` —
  COMPOSED capstone: analytic Bernoulli-derivative identity ⟹
  classical germ identity at `(s, z) = (-1, 1/2)`.

## Honest framing

This file does NOT close `JonquieresIdentityPointGermAtHalf (-1)`.
It REDUCES the closure problem to the single sharp open analytic
Prop `BernoulliDerivativeExpHasSumAtNegLogNhdsHalf` — the analytic
`HasSum` form of the (differentiated) Bernoulli generating function
at `v = -log z`. This Prop is to `s = -1` what
`BernoulliExpHasSumAtNegLogNhdsHalf` is to `s = 0` (the latter being
fully discharged by `bernoulliExpHasSumAtNegLogNhdsHalf_proved` in
`BernoulliFnHasSumOnSomeBallDischarge.lean`).

The analog of the s = 0 discharge requires lifting the FIRST analytic
derivative of `bernoulliFn` to a `HasSum` at every `v` with
`|v| < 2π`, identifying it with the explicit closed form
`d/dv[v/(e^v − 1)] = 1/(e^v - 1) − v · e^v/(e^v - 1)²`, and combining
algebraically. Mathlib's `HasFPowerSeriesAt.hasDerivAt` provides the
derivative at the EXPANSION POINT but not the lifted-HasSum lemma at
every point of the disc. This is the classical-analysis residual that
any future s = -1 closure must address.

After this file, the s = -1 closure problem is reduced to **a single
classical analytic identity in one complex variable on a disc**, with
no Jonquières/polylog/zeta dependencies. This isolates the analytic
gap as cleanly as possible, mirroring the structure that powered the
s = 0 closure.

Stage L27 — Path-C factoring of `JonquieresIdentityPointGermAtHalf (-1)`.
-/
