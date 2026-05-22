/-
# `BernoulliCauchyCoefficientsEqualBernoulli` — Sharpest Residual Reformulation

This file packages the **REDUCTION CHAIN** for the open Prop
`BernoulliCauchyCoefficientsEqualBernoulli` from
`BernoulliExpHasSumOnBallTwoPiDischarge.lean`.

## Strategic content

The original open Prop is a Cauchy-coefficient identity:
```
(cauchyPowerSeries bernoulliFn 0 R n) (fun _ => v) = bernoulli n · v^n / n!
```

This file shows that the Cauchy-coefficient identity is **EQUIVALENT** to the
much more tractable **direct HasSum form**:
```
HasSum (fun n => (bernoulli n : ℂ) · v^n / n!) (bernoulliFn v)
```
for `v` in some open ball about `0`.

The reduction uses mathlib's
`HasFPowerSeriesAt.eq_formalMultilinearSeries` (uniqueness of formal power
series representing the same analytic function at a point) and the
`FormalMultilinearSeries.ofScalars` API. The key insight is that
**ANY** `HasSum`-form expansion of `bernoulliFn` at `0` with scalar
coefficients `c n` automatically equals the Cauchy power series at `0`
by uniqueness — so identifying the Cauchy coefficients with
`bernoulli n / n!` is equivalent to producing a direct HasSum.

This **drastically narrows** what needs to be proved: instead of
characterizing the Cauchy contour-integral formula directly, one only
needs the disc-of-convergence Taylor expansion of `v/(exp v - 1)` —
the textbook analytic content corresponding to the
formal identity `bernoulliPowerSeries · (exp - 1) = X` (which mathlib
has unconditionally as `bernoulliPowerSeries_mul_exp_sub_one`).

## What lands unconditionally

* `bernoulliScalarSeries` — the `FormalMultilinearSeries ℂ ℂ ℂ`
  built from the scalar sequence `(bernoulli n : ℂ) / n!` via
  `FormalMultilinearSeries.ofScalars`.
* `bernoulliScalarSeries_apply` — explicit evaluation
  `bernoulliScalarSeries n (fun _ => v) = (bernoulli n : ℂ) · v^n / n!`.
* `bernoulliFn_hasFPowerSeriesAt_of_hasSum` — REDUCTION direction:
  a direct HasSum on some neighbourhood ⟹ HasFPowerSeriesAt with
  `bernoulliScalarSeries`.
* `cauchyPowerSeries_eq_bernoulliScalarSeries_of_hasSum` — KEY BRIDGE:
  if the direct HasSum holds on some ball `R < 2π`, then
  `cauchyPowerSeries bernoulliFn 0 R = bernoulliScalarSeries`
  by uniqueness.
* `BernoulliFnHasSumOnSomeBall` — the SHARP repackaged residual
  (direct HasSum form, no contour integrals).
* `bernoulliCauchyCoefficientsEqualBernoulli_of_hasSumOnSomeBall` —
  the DISCHARGE THEOREM: the direct-HasSum Prop implies
  `BernoulliCauchyCoefficientsEqualBernoulli`.
* `bernoulliExpHasSumOnBallTwoPi_of_cauchyCoefficients` — the
  EXTENDED REDUCTION: `BernoulliCauchyCoefficientsEqualBernoulli` ⟹
  `BernoulliExpHasSumOnBallTwoPi` (extends the small-disc HasSum to
  the full `2π` disc via Taylor-series uniqueness; the Cauchy
  coefficients are radius-independent).

## What remains open

* `BernoulliFnHasSumOnSomeBall` — the irreducible content. This is
  the standard analytic identity "the formal Bernoulli generating
  function converges to `v/(exp v - 1)` on some disc about `0`".
  Mathlib has the formal-PS identity
  `bernoulliPowerSeries_mul_exp_sub_one` over ℚ; what's missing is a
  PowerSeries-ℚ → FormalMultilinearSeries-ℂ analytic transfer
  with convergence proved via the elementary radius bound
  `|B_n / n!|^(1/n) ~ 1/(2π)` (von Staudt–Clausen / Euler's formula).
  A direct discharge from mathlib infrastructure available right now
  would require either: (a) a Leibniz iterated-derivative product
  formula (NOT in mathlib in equality form), or (b) an analytic
  Cauchy-product theorem for FPS multiplication (NOT in mathlib in
  the form needed), or (c) a direct numerical convergence proof via
  factorial-decay estimates (multi-week project).

Stage L27 — Cauchy-coefficient ⟺ direct-HasSum equivalence;
extended reduction to the full `2π` disc.
-/

import PF.Analytic.BernoulliExpHasSumOnBallTwoPiDischarge
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness

namespace PrincipiaTractalis.Analytic.Sheaf

open Complex Filter Topology Metric Set FormalMultilinearSeries

/-! ## The Bernoulli scalar series -/

/-- The formal multilinear series with scalar coefficients
    `(bernoulli n : ℂ) / n!`. This is the analytic counterpart of
    mathlib's formal `bernoulliPowerSeries` over `ℚ`. -/
noncomputable def bernoulliScalarSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => (bernoulli n : ℂ) / (n.factorial : ℂ))

/-- Explicit evaluation: `bernoulliScalarSeries n (fun _ => v) = B_n · v^n / n!`. -/
lemma bernoulliScalarSeries_apply (n : ℕ) (v : ℂ) :
    (bernoulliScalarSeries n) (fun _ => v) = (bernoulli n : ℂ) * v ^ n / (n.factorial : ℂ) := by
  unfold bernoulliScalarSeries
  rw [FormalMultilinearSeries.ofScalars_apply_eq]
  rw [smul_eq_mul]
  ring

/-! ## The repackaged residual: direct HasSum form (no contour integrals) -/

/-- **THE SHARPEST RESIDUAL**: there exists a ball about `0` on which
    the Bernoulli generating series sums to `bernoulliFn`.

    This is the SAME mathematical content as
    `BernoulliCauchyCoefficientsEqualBernoulli` but stated in pure
    `HasSum` form — no contour integrals, no `cauchyPowerSeries`.

    Equivalently (and the standard textbook form): the formal power
    series `Σ_n (B_n / n!) v^n` converges to `v/(exp v - 1)` on a
    neighbourhood of `0`. -/
def BernoulliFnHasSumOnSomeBall : Prop :=
  ∃ R : NNReal, 0 < R ∧ (R : ℝ) < 2 * Real.pi ∧
    ∀ v : ℂ, ‖v‖ < R →
      HasSum (fun n : ℕ => (bernoulli n : ℂ) * v ^ n / (n.factorial : ℂ))
        (bernoulliFn v)

/-! ## Direct-HasSum ⟹ HasFPowerSeriesOnBall with `bernoulliScalarSeries` -/

/-- If the direct Bernoulli generating series sums to `bernoulliFn` on a
    ball, then `bernoulliFn` has `bernoulliScalarSeries` as a formal
    power series on that ball.

    This is the bridge from the "HasSum" formulation to the
    "FormalMultilinearSeries" formulation. Convergence of the HasSum
    on the open ball gives us:
    (a) the series radius is at least `R`, and
    (b) the sum equals `bernoulliFn(0 + v) = bernoulliFn v`. -/
lemma bernoulliFn_hasFPowerSeriesOnBall_of_hasSum
    {R : NNReal} (hR_pos : 0 < R) (hR_lt : (R : ℝ) < 2 * Real.pi)
    (h_sum : ∀ v : ℂ, ‖v‖ < R →
      HasSum (fun n : ℕ => (bernoulli n : ℂ) * v ^ n / (n.factorial : ℂ))
        (bernoulliFn v)) :
    HasFPowerSeriesOnBall bernoulliFn bernoulliScalarSeries 0 R := by
  -- Build the HasFPowerSeriesOnBall record via summability + the HasSum hypothesis.
  refine ⟨?_, ?_, ?_⟩
  · -- Radius bound: the series radius is at least `R`.
    -- Use `le_radius_of_summable_norm_aux` / `le_radius_of_summable`: it suffices
    -- to show that for every `r' < R`, `∑ ‖p n‖ * r'^n` is summable.
    refine ENNReal.le_of_forall_nnreal_lt (fun r' hr' ↦ ?_)
    -- `r' < R` in `ℝ≥0∞` ⟹ `(r' : ℝ) < (R : ℝ)`
    have hr'R : (r' : ℝ) < (R : ℝ) := by
      exact_mod_cast hr'
    -- The bound on `r' : ℝ`: pick a test point `v` with `‖v‖ = r'` and use the HasSum.
    -- Actually, we use `FormalMultilinearSeries.le_radius_of_summable` which needs
    -- summability of `‖p n‖ * r'^n`. We have a stronger fact: the actual scalar
    -- series `∑ |c_n| · r'^n` summable. Use the HasSum at `v` with `‖v‖ = r'` ...
    -- but we need norm-summability, not just summability. Approach: use the
    -- summability of the HasSum at `v = r'` AND the fact that for SCALAR series,
    -- norm-summability follows from summability at any sufficiently larger radius.
    -- For simplicity, use: `r' < R` ⟹ choose `r''` with `r' < r'' < R`, apply
    -- HasSum at `v` with `‖v‖ = r''` (giving summability), then use
    -- `summable_norm_mul_pow` extracting summability of `|c_n| · r''^n` and
    -- monotonicity to get `|c_n| · r'^n` norm-summable.
    -- A cleaner alternative: directly use `le_radius_of_isBigO`.
    -- The direct path: prove `r' ≤ radius` for every `r' < R` via:
    --   summable (fun n => ‖bernoulliScalarSeries n‖ * r'^n)
    -- which by `ofScalars_norm` reduces to summable (fun n => ‖c n‖ * r'^n).
    by_cases hr'0 : r' = 0
    · simp [hr'0]
    · -- Pick `r''` strictly between `r'` and `R`.
      -- Use density of ℝ.
      obtain ⟨r''_real, hr'r'', hr''R⟩ : ∃ r'' : ℝ, (r' : ℝ) < r'' ∧ r'' < (R : ℝ) :=
        exists_between hr'R
      have hr''_pos : 0 < r''_real := lt_of_le_of_lt r'.coe_nonneg hr'r''
      -- Apply HasSum at `v = r''_real : ℂ` (real on the disc, has norm r'').
      have hr''_norm_lt_R : ‖(r''_real : ℂ)‖ < R := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr''_pos]
        exact_mod_cast hr''R
      have h_summable : Summable (fun n : ℕ =>
          (bernoulli n : ℂ) * (r''_real : ℂ) ^ n / (n.factorial : ℂ)) :=
        (h_sum (r''_real : ℂ) hr''_norm_lt_R).summable
      -- Now use this to bound the radius.
      apply FormalMultilinearSeries.le_radius_of_summable_norm
      -- need Summable (fun n => ‖bernoulliScalarSeries n‖ * (r' : ℝ)^n)
      -- Bound term-by-term: ‖B_n · v^n / n!‖ at v = r''
      -- = ‖B_n / n!‖ · r''^n = ‖bernoulliScalarSeries n‖ · r''^n (using ofScalars_norm)
      -- Then since r' < r'', we have (r'/r'')^n bounded by 1, etc.
      have h_norm_eq : ∀ n : ℕ,
          ‖(bernoulli n : ℂ) * (r''_real : ℂ) ^ n / (n.factorial : ℂ)‖ =
            ‖((bernoulli n : ℂ) / (n.factorial : ℂ))‖ * r''_real ^ n := by
        intro n
        have h_rearr : (bernoulli n : ℂ) * (r''_real : ℂ) ^ n / (n.factorial : ℂ)
              = ((bernoulli n : ℂ) / (n.factorial : ℂ)) * (r''_real : ℂ) ^ n := by ring
        rw [h_rearr, norm_mul, norm_pow]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr''_pos]
      have h_summable' : Summable (fun n : ℕ =>
          ‖((bernoulli n : ℂ) / (n.factorial : ℂ))‖ * r''_real ^ n) := by
        have := h_summable.norm
        simp_rw [h_norm_eq] at this
        exact this
      -- Now bound the target by this, using (r' ≤ r'').
      refine Summable.of_nonneg_of_le
        (g := fun n : ℕ => ‖bernoulliScalarSeries n‖ * (r' : ℝ) ^ n)
        (f := fun n : ℕ => ‖((bernoulli n : ℂ) / (n.factorial : ℂ))‖ * r''_real ^ n)
        ?_ ?_ h_summable'
      · intro n
        exact mul_nonneg (norm_nonneg _) (pow_nonneg r'.coe_nonneg n)
      · intro n
        show ‖bernoulliScalarSeries n‖ * (r' : ℝ) ^ n ≤ _
        unfold bernoulliScalarSeries
        rw [FormalMultilinearSeries.ofScalars_norm_eq_mul]
        -- ‖c n‖ * ‖mkPiAlgebraFin‖ * r'^n ≤ ‖c n‖ * r''^n
        have h_mk_le : ‖ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ‖ ≤ 1 := by
          have := (ContinuousMultilinearMap.norm_mkPiAlgebraFin_le
            (𝕜 := ℂ) (A := ℂ) (n := n))
          have h_norm_one : (max 1 ‖(1 : ℂ)‖ : ℝ) = 1 := by simp
          calc ‖ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ‖
              ≤ max 1 ‖(1 : ℂ)‖ := this
            _ = 1 := h_norm_one
        calc ‖((bernoulli n : ℂ) / (n.factorial : ℂ))‖
            * ‖ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ‖ * (r' : ℝ) ^ n
            ≤ ‖((bernoulli n : ℂ) / (n.factorial : ℂ))‖ * 1 * (r' : ℝ) ^ n := by
              gcongr
          _ = ‖((bernoulli n : ℂ) / (n.factorial : ℂ))‖ * (r' : ℝ) ^ n := by ring
          _ ≤ ‖((bernoulli n : ℂ) / (n.factorial : ℂ))‖ * r''_real ^ n := by
              apply mul_le_mul_of_nonneg_left
              · exact pow_le_pow_left₀ r'.coe_nonneg (le_of_lt hr'r'') n
              · exact norm_nonneg _
  · -- 0 < R
    exact_mod_cast hR_pos
  · -- HasSum on the ball
    intro y hy
    -- y ∈ EMetric.ball 0 R ⟹ ‖y‖ < R
    have hy_norm : ‖y‖ < R := by
      rw [EMetric.mem_ball, edist_zero_right, enorm_eq_nnnorm] at hy
      exact_mod_cast hy
    have h_at_y := h_sum y hy_norm
    -- HasSum (fun n => B_n · y^n / n!) (bernoulliFn y)
    -- need: HasSum (fun n => bernoulliScalarSeries n (fun _ => y)) (bernoulliFn (0 + y))
    rw [zero_add]
    convert h_at_y using 1
    funext n
    exact bernoulliScalarSeries_apply n y

/-! ## Uniqueness bridge: `cauchyPowerSeries` agrees with `bernoulliScalarSeries` -/

/-- **KEY BRIDGE THEOREM**: if the direct HasSum holds on a ball `R < 2π`, then
    by uniqueness of formal power series representing the same analytic
    function at a point, the Cauchy power series of `bernoulliFn` at `0`
    equals `bernoulliScalarSeries`. -/
theorem cauchyPowerSeries_eq_bernoulliScalarSeries_of_hasSum
    {R : NNReal} (hR_pos : 0 < R) (hR_lt : (R : ℝ) < 2 * Real.pi)
    (h_sum : ∀ v : ℂ, ‖v‖ < R →
      HasSum (fun n : ℕ => (bernoulli n : ℂ) * v ^ n / (n.factorial : ℂ))
        (bernoulliFn v)) :
    cauchyPowerSeries bernoulliFn 0 R = bernoulliScalarSeries := by
  have h_cauchy : HasFPowerSeriesOnBall bernoulliFn
      (cauchyPowerSeries bernoulliFn 0 R) 0 R :=
    bernoulliFn_hasFPowerSeriesOnBall_of_lt_twoPi hR_pos hR_lt
  have h_scalar : HasFPowerSeriesOnBall bernoulliFn bernoulliScalarSeries 0 R :=
    bernoulliFn_hasFPowerSeriesOnBall_of_hasSum hR_pos hR_lt h_sum
  exact h_cauchy.hasFPowerSeriesAt.eq_formalMultilinearSeries h_scalar.hasFPowerSeriesAt

/-! ## DISCHARGE: direct-HasSum ⟹ Cauchy-coefficient identity -/

/-- **DISCHARGE THEOREM**: if there exists a ball about `0` on which the
    direct Bernoulli generating series sums to `bernoulliFn`, then the
    Cauchy power-series coefficients of `bernoulliFn` at `0` equal
    `bernoulli n · v^n / n!` — i.e.,
    `BernoulliCauchyCoefficientsEqualBernoulli` holds. -/
theorem bernoulliCauchyCoefficientsEqualBernoulli_of_hasSumOnSomeBall
    (h : BernoulliFnHasSumOnSomeBall) :
    BernoulliCauchyCoefficientsEqualBernoulli := by
  obtain ⟨R, hR_pos, hR_lt, h_sum⟩ := h
  refine ⟨R, hR_pos, hR_lt, ?_⟩
  intro n v _hv
  -- The cauchy series equals the bernoulli scalar series.
  have h_eq := cauchyPowerSeries_eq_bernoulliScalarSeries_of_hasSum hR_pos hR_lt h_sum
  -- Apply at `n` and evaluate at `fun _ => v`.
  have h_apply : (cauchyPowerSeries bernoulliFn 0 R n) (fun _ => v) =
      (bernoulliScalarSeries n) (fun _ => v) := by
    rw [h_eq]
  rw [h_apply, bernoulliScalarSeries_apply n v]

/-! ## Extended reduction: Cauchy coefficients ⟹ full `2π` HasSum -/

/-- **EXTENDED REDUCTION**: `BernoulliCauchyCoefficientsEqualBernoulli` ⟹
    `BernoulliExpHasSumOnBallTwoPi`.

    The Cauchy coefficients give us a `HasSum` on the small ball
    `ball 0 R` for `R < 2π`. To extend to the full `ball 0 (2π)`,
    we use:
    (1) The HasSum on `ball 0 R` provides `BernoulliFnHasSumOnSomeBall`.
    (2) `bernoulliFn_hasFPowerSeriesOnBall_of_hasSum` ⟹
        `bernoulliScalarSeries` represents `bernoulliFn` on `ball 0 R`,
        with radius `≥ R`.
    (3) At ANY larger radius `R' < 2π`, `bernoulliFn` is also represented
        by `cauchyPowerSeries bernoulliFn 0 R'`, and by uniqueness
        (`HasFPowerSeriesAt.eq_formalMultilinearSeries`), this larger
        series equals `bernoulliScalarSeries` (its radius is automatically
        ≥ R' since it represents bernoulliFn there). Hence the HasSum
        on `ball 0 R'` follows directly from `ofScalars_apply_eq`.
    (4) Apply at any `R' > ‖v‖`. -/
theorem bernoulliExpHasSumOnBallTwoPi_of_cauchyCoefficients
    (h : BernoulliCauchyCoefficientsEqualBernoulli) :
    BernoulliExpHasSumOnBallTwoPi := by
  obtain ⟨R, hR_pos, hR_lt, h_coef⟩ := h
  -- First, extract a direct HasSum on ball 0 R from h_coef:
  have h_sum_R : ∀ v : ℂ, ‖v‖ < R →
      HasSum (fun n : ℕ => (bernoulli n : ℂ) * v ^ n / (n.factorial : ℂ))
        (bernoulliFn v) := by
    intro v hv
    have h_cauchy := bernoulliFn_cauchyPowerSeries_hasSum_of_norm_lt hR_pos hR_lt hv
    -- h_cauchy: HasSum (fun n => (cauchy n) (fun _ => v)) (bernoulliFn v)
    -- Rewrite each term via h_coef:
    have h_funext : (fun n => (cauchyPowerSeries bernoulliFn 0 R n) (fun _ => v)) =
        fun n => (bernoulli n : ℂ) * v ^ n / (n.factorial : ℂ) := by
      funext n
      exact h_coef n v hv
    rw [h_funext] at h_cauchy
    exact h_cauchy
  -- Now apply the bridge: HasFPowerSeriesOnBall with bernoulliScalarSeries.
  have h_scalar_R : HasFPowerSeriesOnBall bernoulliFn bernoulliScalarSeries 0 R :=
    bernoulliFn_hasFPowerSeriesOnBall_of_hasSum hR_pos hR_lt h_sum_R
  -- Extend: for any R' < 2π with R' > 0, the SAME scalar series represents
  -- bernoulliFn on ball 0 R'. Reason: the Cauchy series at R' represents
  -- bernoulliFn on ball 0 R', and by uniqueness equals bernoulliScalarSeries.
  intro v hv
  -- v with ‖v‖ < 2π. Pick R' with ‖v‖ < R' < 2π.
  obtain ⟨R'_real, h_v_lt_R', hR'_lt_2pi⟩ : ∃ R'_real : ℝ,
      ‖v‖ < R'_real ∧ R'_real < 2 * Real.pi := exists_between hv
  have hR'_pos : 0 < R'_real := lt_of_le_of_lt (norm_nonneg v) h_v_lt_R'
  -- Lift to NNReal.
  set R' : NNReal := ⟨R'_real, le_of_lt hR'_pos⟩ with hR'_def
  have hR'_pos_nn : (0 : NNReal) < R' := by
    rw [← NNReal.coe_lt_coe]
    simpa [hR'_def] using hR'_pos
  have hR'_lt_2pi_nn : (R' : ℝ) < 2 * Real.pi := hR'_lt_2pi
  have h_v_lt_R'_nn : ‖v‖ < R' := by
    show ‖v‖ < (R' : ℝ)
    exact h_v_lt_R'
  -- Cauchy series at R' represents bernoulliFn on ball 0 R'.
  have h_cauchy_R' : HasFPowerSeriesOnBall bernoulliFn
      (cauchyPowerSeries bernoulliFn 0 R') 0 R' :=
    bernoulliFn_hasFPowerSeriesOnBall_of_lt_twoPi hR'_pos_nn hR'_lt_2pi_nn
  -- The two formal power series (cauchy R, cauchy R') BOTH represent bernoulliFn
  -- at 0 ⟹ equal by uniqueness.
  -- Similarly bernoulliScalarSeries (from R) BOTH represents bernoulliFn at 0
  -- (since h_scalar_R has it on ball 0 R, hence has HasFPowerSeriesAt at 0)
  -- and cauchy R' represents bernoulliFn at 0 (from h_cauchy_R')
  -- ⟹ equal.
  have h_scalar_at : HasFPowerSeriesAt bernoulliFn bernoulliScalarSeries 0 :=
    h_scalar_R.hasFPowerSeriesAt
  have h_cauchy_R'_at : HasFPowerSeriesAt bernoulliFn
      (cauchyPowerSeries bernoulliFn 0 R') 0 :=
    h_cauchy_R'.hasFPowerSeriesAt
  have h_eq : cauchyPowerSeries bernoulliFn 0 R' = bernoulliScalarSeries :=
    h_cauchy_R'_at.eq_formalMultilinearSeries h_scalar_at
  -- HasSum at v from cauchy R'.
  have h_at_v : HasSum
      (fun n => (cauchyPowerSeries bernoulliFn 0 R' n) (fun _ => v))
      (bernoulliFn v) :=
    bernoulliFn_cauchyPowerSeries_hasSum_of_norm_lt hR'_pos_nn hR'_lt_2pi_nn h_v_lt_R'_nn
  -- Rewrite via h_eq + bernoulliScalarSeries_apply.
  have h_funext : (fun n => (cauchyPowerSeries bernoulliFn 0 R' n) (fun _ => v)) =
      fun n => (bernoulli n : ℂ) * v ^ n / (n.factorial : ℂ) := by
    funext n
    rw [h_eq, bernoulliScalarSeries_apply]
  rw [h_funext] at h_at_v
  -- bernoulliFn v matches the RHS by case analysis on v = 0.
  have h_rhs_eq : bernoulliFn v = (if v = 0 then 1 else v / (Complex.exp v - 1)) := by
    by_cases hv0 : v = 0
    · subst hv0; simp [bernoulliFn]
    · rw [bernoulliFn_eq_of_ne_zero hv0, if_neg hv0]
  rw [← h_rhs_eq]
  exact h_at_v

end PrincipiaTractalis.Analytic.Sheaf

/-!
## Manifest

This file delivers:

* `bernoulliScalarSeries` — `FormalMultilinearSeries ℂ ℂ ℂ` from
  `(bernoulli n : ℂ) / n!` via `FormalMultilinearSeries.ofScalars`.
* `bernoulliScalarSeries_apply` — explicit evaluation.
* `bernoulliFn_hasFPowerSeriesOnBall_of_hasSum` — direct HasSum ⟹
  `HasFPowerSeriesOnBall` with the scalar series.
* `cauchyPowerSeries_eq_bernoulliScalarSeries_of_hasSum` — uniqueness
  bridge via `HasFPowerSeriesAt.eq_formalMultilinearSeries`.
* `BernoulliFnHasSumOnSomeBall` — the sharp residual in pure HasSum form.
* `bernoulliCauchyCoefficientsEqualBernoulli_of_hasSumOnSomeBall` —
  DISCHARGE: direct HasSum ⟹ Cauchy-coefficient identity.
* `bernoulliExpHasSumOnBallTwoPi_of_cauchyCoefficients` — EXTENDED
  REDUCTION: Cauchy coefficients ⟹ full `2π`-disc HasSum (via
  Taylor-series uniqueness across nested discs).

The load-bearing remaining open Prop is now `BernoulliFnHasSumOnSomeBall` —
a *direct* HasSum form with no contour integrals — corresponding
exactly to the analytic content of the formal identity
`bernoulliPowerSeries · (exp - 1) = X`.
-/

section AxiomAudit
open PrincipiaTractalis.Analytic.Sheaf
#guard_msgs(drop info) in
#print axioms bernoulliCauchyCoefficientsEqualBernoulli_of_hasSumOnSomeBall
end AxiomAudit
