/-
# PF.Analytic.XiQuadrature

★★★★★ 2026-07-25 — Hardy route milestone B4 (HARDY_SCOPING_2026-07-24 §3,
INTERVAL_SPIKE_2026-07-24): the VERIFIED-QUADRATURE layer for the
theta-integral representation of `Xi` proved in
PF.Analytic.XiThetaIntegral (r118).  Everything the final certificate
`Xi 14 < 0 < Xi 15` (milestone B5) needs beyond raw interval arithmetic
is proved here, kernel-clean: the tail bound, the series truncation, the
composite midpoint rule with the SHARP `/24` constant, and explicit
`C²` bounds for the truncated integrand.

## Goal

r118 reduced the single remaining RH bucket-1 atom to the sign of

  `Xi t = -1/(1/4 + t²) + ∫_{u>1} 2 u^{-3/4} cos((t/2) log u) · ω(u) du`.

This file supplies the four quadrature bricks:

  1. **B4a — tail brick.**  `Xi_split` cuts the integral at any
     `T ≥ 1` into `∫_{Ioc 1 T} + ∫_{Ioi T}` (with the
     interval-integral form `Xi_split_intervalIntegral` for direct
     consumption by the midpoint rule), and `Xi_tail_bound` certifies

       `|∫_{Ioi T}| ≤ (2/π) e^{-πT} / (1 - e^{-π})`   (`T ≥ 1`),

     from r118's uniform bound `Xi_theta_integrand_abs_le` plus the
     closed-form `∫_{Ioi T} e^{-πu} du = e^{-πT}/π`
     (`integral_exp_neg_pi_mul_Ioi`, via
     `integral_Ioi_of_hasDerivAt_of_tendsto'`).  HEADROOM: at `T = 8`
     the bound is `(2/π) e^{-8π}/(1-e^{-π}) ≈ 8.1·10⁻¹²`, five orders
     below the ~10⁻⁶ certificate budget.

  2. **B4b — omega truncation.**  `omegaPartial N u`
     `= ∑_{n<N} e^{-π(n+1)²u}` (a FINITE elementary sum, directly
     interval-evaluable) with the error certificate
     `omega_partial_error`:

       `|ω(u) - omegaPartial N u| ≤ e^{-π(N+1)²u} / (1 - e^{-π})`
       (`u ≥ 1`),

     by dominating the series tail `∑_{n≥N} e^{-π(n+1)²u}` with the
     crude geometric ratio `e^{-πu}` — the bound shape is deliberately
     SIMPLE for later interval evaluation.  HEADROOM: at `N = 3`,
     `u ≥ 1` the bound is `e^{-16π}/(1-e^{-π}) ≈ 1.6·10⁻²²`.

  3. **B4c — composite midpoint rule (the core).**  For any
     `f : ℝ → ℝ` given with first and second derivative witnesses on
     `uIcc a b` and `|f''| ≤ M` there:

       `midpoint_rule_error` :
         `|∫_a^b f - (b-a)·f((a+b)/2)| ≤ M (b-a)³ / 24`,
       `composite_midpoint_error` (uniform `n`-panel partition) :
         `|∫_a^b f - h ∑_{i<n} f(a + h(i+1/2))| ≤ M (b-a)³ / (24 n²)`,
         `h = (b-a)/n`.

     Proved with the SHARP constant via the order-1 Taylor pointwise
     bound `abs_sub_taylor1_le` (`|f x - f c - f'(c)(x-c)| ≤ M(x-c)²/2`,
     from FTC-2 on `f'` plus the mean-value Lipschitz bound on `f'`)
     and the symmetric cancellation `∫_a^b (x - m) dx = 0` at the
     midpoint — the `f'(m)` term integrates away, so only the
     quadratic remainder survives: `∫ M(x-m)²/2 = M(b-a)³/24`.

  4. **B4d — integrand C² bounds.**  The truncated integrand
     `g_N(u) = 2u^{-3/4} cos((t/2) log u) · omegaPartial N u` is the
     finite sum of `thetaTerm t n` over `n < N`
     (`truncated_integrand_eq`); each term gets explicit first and
     second derivatives `thetaTermD1`, `thetaTermD2`
     (`hasDerivAt_thetaTerm`, `hasDerivAt_thetaTermD1`, valid on
     `u > 0`) and the explicit closed-form second-derivative bound
     `thetaTermM t n` (`abs_thetaTermD2_le`, valid on `u ≥ 1`,
     `T`-independent):

       `|g_N''(u)| ≤ ∑_{n<N} e^{-π(n+1)²} ·
          (21/8 + (5/2)|t| + |t|²/2 + 3A + 2|t|A + 2A²)`,
       `A = π(n+1)²`  (`abs_thetaTermD2_sum_le`).

     Numerically at `|t| ≤ 15`: the `n = 0` term dominates and gives
     `M ≈ 13`; the `n ≥ 1` terms are `< 10⁻²` (the `e^{-4π}` factor
     kills them).  Every bound is a closed form in `π`, `e^{-π(n+1)²}`
     and `|t|` — exactly the objects the vendored interval engine
     evaluates.

## Brick value

B5 is now pure assembly: pick `T = 8`, `N = 3`, `n` panels with
`M(b-a)³/(24n²)` below budget, evaluate the midpoint sums by interval
arithmetic (`approx` + `decide +kernel`, one lemma per panel), and chain
`Xi_split_intervalIntegral` + `composite_midpoint_error` +
`omega_partial_error` + `Xi_tail_bound` +
`xi_sign_change_implies_on_line_zero`.  No analytic content remains —
only kernel compute.

## Axiom budget

Zero project axioms, zero sorries.  Theorems depend only on
`[propext, Classical.choice, Quot.sound]`.
-/

import PF.Analytic.XiThetaIntegral
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace PrincipiaTractalis.XiQuadrature

open Set MeasureTheory Filter
open PrincipiaTractalis.XiRealWitness
open PrincipiaTractalis.XiThetaIntegral
open scoped Real Topology

/-! ## §1 — B4a: the exponential tail integral -/

/-- Closed form for the exponential tail: `∫_{Ioi T} e^{-πu} du = e^{-πT}/π`
    (improper FTC-2 with the explicit antiderivative `-e^{-πu}/π`). -/
theorem integral_exp_neg_pi_mul_Ioi (T : ℝ) :
    ∫ u in Ioi T, Real.exp (-π * u) = Real.exp (-π * T) / π := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hderiv : ∀ x ∈ Ici T, HasDerivAt (fun u : ℝ ↦ -Real.exp (-π * u) / π)
      (Real.exp (-π * x)) x := by
    intro x _
    convert (((hasDerivAt_id' x).const_mul (-π)).exp.neg).div_const π using 1
    field_simp
  have htends : Tendsto (fun u : ℝ ↦ -Real.exp (-π * u) / π) atTop (𝓝 (-0 / π)) := by
    refine Tendsto.div_const (Tendsto.neg ?_) _
    exact Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
  have key := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
    (exp_neg_integrableOn_Ioi T hπ) htends
  rw [key]
  ring

/-- **B4a splitting lemma** — the theta integral of r118 cut at any
    `T ≥ 1`: `Xi t = -1/(1/4+t²) + (∫_{Ioc 1 T} + ∫_{Ioi T})`. -/
theorem Xi_split (t T : ℝ) (hT : 1 ≤ T) :
    Xi t = -(1 / (1 / 4 + t ^ 2))
      + ((∫ u in Ioc 1 T, 2 * u ^ (-(3 / 4) : ℝ) * Real.cos (t / 2 * Real.log u) * omega u)
        + ∫ u in Ioi T, 2 * u ^ (-(3 / 4) : ℝ) * Real.cos (t / 2 * Real.log u) * omega u) := by
  rw [Xi_eq_theta_integral t]
  congr 1
  rw [← MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      ((integrableOn_Xi_theta_integrand t).mono_set Set.Ioc_subset_Ioi_self)
      ((integrableOn_Xi_theta_integrand t).mono_set (Set.Ioi_subset_Ioi hT)),
    Set.Ioc_union_Ioi_eq_Ioi hT]

/-- `Xi_split` with the finite piece in interval-integral form
    `∫_1^T`, ready for the composite midpoint rule of §3. -/
theorem Xi_split_intervalIntegral (t T : ℝ) (hT : 1 ≤ T) :
    Xi t = -(1 / (1 / 4 + t ^ 2))
      + ((∫ u in (1 : ℝ)..T, 2 * u ^ (-(3 / 4) : ℝ) * Real.cos (t / 2 * Real.log u) * omega u)
        + ∫ u in Ioi T, 2 * u ^ (-(3 / 4) : ℝ) * Real.cos (t / 2 * Real.log u) * omega u) := by
  rw [Xi_split t T hT, intervalIntegral.integral_of_le hT]

/-- **★ B4a TAIL BRICK ★** — truncating the theta integral at `T ≥ 1`
    costs at most `(2/π) e^{-πT} / (1 - e^{-π})`, uniformly in `t`.
    At `T = 8` this is `≈ 8.1·10⁻¹²`. -/
theorem Xi_tail_bound (t T : ℝ) (hT : 1 ≤ T) :
    |∫ u in Ioi T, 2 * u ^ (-(3 / 4) : ℝ) * Real.cos (t / 2 * Real.log u) * omega u|
      ≤ 2 / π * Real.exp (-π * T) / (1 - Real.exp (-π)) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hfInt : IntegrableOn
      (fun u : ℝ ↦ 2 * u ^ (-(3 / 4) : ℝ) * Real.cos (t / 2 * Real.log u) * omega u)
      (Ioi T) :=
    (integrableOn_Xi_theta_integrand t).mono_set (Set.Ioi_subset_Ioi hT)
  have hgInt : IntegrableOn (fun u : ℝ ↦ 2 * Real.exp (-π * u) / (1 - Real.exp (-π)))
      (Ioi T) :=
    ((exp_neg_integrableOn_Ioi T hπ).const_mul 2).div_const _
  calc |∫ u in Ioi T, 2 * u ^ (-(3 / 4) : ℝ) * Real.cos (t / 2 * Real.log u) * omega u|
      ≤ ∫ u in Ioi T,
          |2 * u ^ (-(3 / 4) : ℝ) * Real.cos (t / 2 * Real.log u) * omega u| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ u in Ioi T, 2 * Real.exp (-π * u) / (1 - Real.exp (-π)) := by
        refine MeasureTheory.setIntegral_mono_on hfInt.abs hgInt measurableSet_Ioi
          fun u hu ↦ ?_
        exact Xi_theta_integrand_abs_le (hT.trans (mem_Ioi.mp hu).le) t
    _ = 2 / π * Real.exp (-π * T) / (1 - Real.exp (-π)) := by
        have hfun : (fun u : ℝ ↦ 2 * Real.exp (-π * u) / (1 - Real.exp (-π)))
            = fun u : ℝ ↦ 2 / (1 - Real.exp (-π)) * Real.exp (-π * u) := by
          funext u; ring
        rw [hfun, MeasureTheory.integral_const_mul, integral_exp_neg_pi_mul_Ioi]
        ring

/-! ## §2 — B4b: truncation of the theta series `ω` -/

/-- **`omegaPartial`** — the `N`-term partial sum of the theta tail
    `ω(u) = ∑_{n≥1} e^{-πn²u}`: a FINITE elementary sum, directly
    evaluable by the interval engine. -/
noncomputable def omegaPartial (N : ℕ) (u : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)

theorem omegaPartial_nonneg (N : ℕ) (u : ℝ) : 0 ≤ omegaPartial N u :=
  Finset.sum_nonneg fun _ _ ↦ (Real.exp_pos _).le

/-- **★ B4b OMEGA TRUNCATION ★** — for `u ≥ 1` the truncation error of
    the theta series is dominated by its first omitted term over the
    constant gap `1 - e^{-π}`:

      `|ω(u) - omegaPartial N u| ≤ e^{-π(N+1)²u} / (1 - e^{-π})`.

    (Crude geometric ratio `e^{-πu}`; already `≈ 1.6·10⁻²²` at `N = 3`,
    `u ≥ 1`.  The bound shape is kept simple for interval evaluation.) -/
theorem omega_partial_error {u : ℝ} (hu : 1 ≤ u) (N : ℕ) :
    |omega u - omegaPartial N u|
      ≤ Real.exp (-π * ((N : ℝ) + 1) ^ 2 * u) / (1 - Real.exp (-π)) := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hsum := summable_omega hu0
  have hr0 : (0 : ℝ) < Real.exp (-π * u) := Real.exp_pos _
  have hr1 : Real.exp (-π * u) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hd : (0 : ℝ) < 1 - Real.exp (-π) := by
    have h1 : Real.exp (-π) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hdu : (0 : ℝ) < 1 - Real.exp (-π * u) := by linarith
  have hexp1 : Real.exp (-π * u) ≤ Real.exp (-π) :=
    Real.exp_le_exp.mpr (by nlinarith)
  -- split off the partial sum
  have h1 : omegaPartial N u + ∑' n : ℕ, Real.exp (-π * (((n + N : ℕ) : ℝ) + 1) ^ 2 * u)
      = omega u := hsum.sum_add_tsum_nat_add N
  have htail_nonneg : (0 : ℝ) ≤ ∑' n : ℕ, Real.exp (-π * (((n + N : ℕ) : ℝ) + 1) ^ 2 * u) :=
    tsum_nonneg fun _ ↦ (Real.exp_pos _).le
  have heq : omega u - omegaPartial N u
      = ∑' n : ℕ, Real.exp (-π * (((n + N : ℕ) : ℝ) + 1) ^ 2 * u) := by linarith
  -- dominate the tail term-by-term by the geometric series
  have hterm : ∀ n : ℕ,
      Real.exp (-π * (((n + N : ℕ) : ℝ) + 1) ^ 2 * u)
        ≤ Real.exp (-π * ((N : ℝ) + 1) ^ 2 * u) * Real.exp (-π * u) ^ n := by
    intro n
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    push_cast
    have hpoly : (0 : ℝ) ≤ (n : ℝ) ^ 2 + 2 * (n : ℝ) * (N : ℝ) + (n : ℝ) := by positivity
    nlinarith [mul_nonneg (mul_nonneg hπ.le hu0.le) hpoly]
  have htailsum : Summable fun n : ℕ ↦ Real.exp (-π * (((n + N : ℕ) : ℝ) + 1) ^ 2 * u) :=
    (summable_nat_add_iff N).mpr hsum
  have hgeom : Summable
      fun n : ℕ ↦ Real.exp (-π * ((N : ℝ) + 1) ^ 2 * u) * Real.exp (-π * u) ^ n :=
    (summable_geometric_of_lt_one hr0.le hr1).mul_left _
  rw [heq, abs_of_nonneg htail_nonneg]
  calc (∑' n : ℕ, Real.exp (-π * (((n + N : ℕ) : ℝ) + 1) ^ 2 * u))
      ≤ ∑' n : ℕ, Real.exp (-π * ((N : ℝ) + 1) ^ 2 * u) * Real.exp (-π * u) ^ n :=
        htailsum.tsum_le_tsum hterm hgeom
    _ = Real.exp (-π * ((N : ℝ) + 1) ^ 2 * u) * (1 - Real.exp (-π * u))⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0.le hr1]
    _ = Real.exp (-π * ((N : ℝ) + 1) ^ 2 * u) / (1 - Real.exp (-π * u)) := by
        rw [div_eq_mul_inv]
    _ ≤ Real.exp (-π * ((N : ℝ) + 1) ^ 2 * u) / (1 - Real.exp (-π)) := by gcongr

/-! ## §3 — B4c: the composite midpoint rule with the sharp `/24` -/

/-- **Order-1 Taylor pointwise bound** — if `|f''| ≤ M` on `uIcc a b`
    then for any center `c` and point `x` in `uIcc a b`

      `|f x - f c - f'(c)(x - c)| ≤ M (x - c)² / 2`.

    Route: `f x - f c - f'(c)(x-c) = ∫_c^x (f'(s) - f'(c)) ds` (FTC-2)
    and `|f'(s) - f'(c)| ≤ M|s - c|` (mean value inequality on `f'`),
    integrated. -/
theorem abs_sub_taylor1_le {f f' f'' : ℝ → ℝ} {a b M : ℝ}
    (hf : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ uIcc a b, HasDerivAt f' (f'' x) x)
    (hM : ∀ x ∈ uIcc a b, |f'' x| ≤ M)
    {c x : ℝ} (hc : c ∈ uIcc a b) (hx : x ∈ uIcc a b) :
    |f x - f c - f' c * (x - c)| ≤ M * (x - c) ^ 2 / 2 := by
  have hsub : uIcc c x ⊆ uIcc a b := uIcc_subset_uIcc hc hx
  -- mean value inequality: `f'` is `M`-Lipschitz on `uIcc a b`
  have hlip : ∀ y ∈ uIcc a b, |f' y - f' c| ≤ M * |y - c| := by
    intro y hy
    have h := (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z hz ↦ (hf' z hz).hasDerivWithinAt)
      (fun z hz ↦ by rw [Real.norm_eq_abs]; exact hM z hz) hc hy
    rwa [Real.norm_eq_abs, Real.norm_eq_abs] at h
  -- FTC-2 on the segment from `c` to `x`
  have hcont' : ContinuousOn f' (uIcc c x) :=
    fun y hy ↦ ((hf' y (hsub hy)).continuousAt).continuousWithinAt
  have hint : IntervalIntegrable f' volume c x := hcont'.intervalIntegrable
  have hFTC : ∫ s in c..x, f' s = f x - f c :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs ↦ hf s (hsub hs)) hint
  have key : f x - f c - f' c * (x - c) = ∫ s in c..x, (f' s - f' c) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const, hFTC,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [key]
  rcases le_total c x with hcx | hxc
  · -- ascending segment: `|f'(s) - f'(c)| ≤ M (s - c)` on `Ioc c x`
    have hb : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioc c x →
        ‖f' s - f' c‖ ≤ M * (s - c) := by
      refine Filter.Eventually.of_forall fun s hs ↦ ?_
      have hsmem : s ∈ uIcc a b := hsub (by rw [uIcc_of_le hcx]; exact Ioc_subset_Icc_self hs)
      have h := hlip s hsmem
      rw [Real.norm_eq_abs]
      rwa [abs_of_nonneg (sub_nonneg.mpr hs.1.le)] at h
    have hgint : IntervalIntegrable (fun s ↦ M * (s - c)) volume c x :=
      (continuous_const.mul (continuous_id'.sub continuous_const)).intervalIntegrable _ _
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le hcx hb hgint
    have hval : ∫ s in c..x, M * (s - c) = M * (x - c) ^ 2 / 2 := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub (continuous_id'.intervalIntegrable _ _)
          intervalIntegrable_const,
        integral_id, intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [← Real.norm_eq_abs]
    exact hnorm.trans (le_of_eq hval)
  · -- descending segment: flip the orientation and use `M (c - s)` on `Ioc x c`
    rw [intervalIntegral.integral_symm x c, abs_neg]
    have hb : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioc x c →
        ‖f' s - f' c‖ ≤ M * (c - s) := by
      refine Filter.Eventually.of_forall fun s hs ↦ ?_
      have hsmem : s ∈ uIcc a b := hsub (by
        rw [uIcc_comm, uIcc_of_le hxc]
        exact Ioc_subset_Icc_self hs)
      have h := hlip s hsmem
      rw [Real.norm_eq_abs]
      rwa [abs_of_nonpos (sub_nonpos.mpr hs.2), neg_sub] at h
    have hgint : IntervalIntegrable (fun s ↦ M * (c - s)) volume x c :=
      (continuous_const.mul (continuous_const.sub continuous_id')).intervalIntegrable _ _
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le hxc hb hgint
    have hval : ∫ s in x..c, M * (c - s) = M * (x - c) ^ 2 / 2 := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub intervalIntegrable_const
          (continuous_id'.intervalIntegrable _ _),
        integral_id, intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [← Real.norm_eq_abs]
    exact hnorm.trans (le_of_eq hval)

/-- **★ B4c SINGLE-PANEL MIDPOINT RULE ★** — with the SHARP constant:

      `|∫_a^b f - (b-a) f((a+b)/2)| ≤ M (b-a)³ / 24`.

    The linear Taylor term at the midpoint integrates to zero by
    symmetry (`∫_a^b (x - m) dx = 0`), so only the quadratic remainder
    of `abs_sub_taylor1_le` survives. -/
theorem midpoint_rule_error {f f' f'' : ℝ → ℝ} {a b M : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ uIcc a b, HasDerivAt f' (f'' x) x)
    (hM : ∀ x ∈ uIcc a b, |f'' x| ≤ M) :
    |(∫ x in a..b, f x) - (b - a) * f ((a + b) / 2)| ≤ M * (b - a) ^ 3 / 24 := by
  set m : ℝ := (a + b) / 2 with hm_def
  have hm : m ∈ uIcc a b := by
    rw [uIcc_of_le hab]
    exact mem_Icc.mpr ⟨by rw [hm_def]; linarith, by rw [hm_def]; linarith⟩
  have hfc : ContinuousOn f (uIcc a b) :=
    fun y hy ↦ (hf y hy).continuousAt.continuousWithinAt
  have hfint : IntervalIntegrable f volume a b := hfc.intervalIntegrable
  have hlin_int : IntervalIntegrable (fun x ↦ f m + f' m * (x - m)) volume a b :=
    (continuous_const.add
      (continuous_const.mul (continuous_id'.sub continuous_const))).intervalIntegrable _ _
  -- the symmetric cancellation
  have hxm : ∫ x in a..b, (x - m) = 0 := by
    rw [intervalIntegral.integral_sub (continuous_id'.intervalIntegrable _ _)
        intervalIntegrable_const,
      integral_id, intervalIntegral.integral_const, smul_eq_mul, hm_def]
    ring
  have hlinval : ∫ x in a..b, (f m + f' m * (x - m)) = (b - a) * f m := by
    rw [intervalIntegral.integral_add intervalIntegrable_const
        ((continuous_const.mul (continuous_id'.sub continuous_const)).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, hxm, intervalIntegral.integral_const, smul_eq_mul]
    ring
  have key : (∫ x in a..b, f x) - (b - a) * f m
      = ∫ x in a..b, (f x - (f m + f' m * (x - m))) := by
    rw [intervalIntegral.integral_sub hfint hlin_int, hlinval]
  rw [key]
  -- integrate the quadratic remainder
  have hsq_int : ∫ x in a..b, (x - m) ^ 2 = (b - a) ^ 3 / 12 := by
    have hd : ∀ s ∈ uIcc a b, HasDerivAt (fun y : ℝ ↦ (y - m) ^ 3 / 3) ((s - m) ^ 2) s := by
      intro s _
      have h1 : HasDerivAt (fun y : ℝ ↦ y - m) 1 s := (hasDerivAt_id' s).sub_const m
      convert (h1.pow 3).div_const 3 using 1
      push_cast
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        (((continuous_id'.sub continuous_const).pow 2).intervalIntegrable _ _), hm_def]
    ring
  have hptw : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioc a b →
      ‖f s - (f m + f' m * (s - m))‖ ≤ M / 2 * (s - m) ^ 2 := by
    refine Filter.Eventually.of_forall fun s hs ↦ ?_
    have hsmem : s ∈ uIcc a b := by
      rw [uIcc_of_le hab]; exact Ioc_subset_Icc_self hs
    have h := abs_sub_taylor1_le hf hf' hM hm hsmem
    rw [Real.norm_eq_abs, sub_add_eq_sub_sub]
    linarith
  have hgint : IntervalIntegrable (fun s ↦ M / 2 * (s - m) ^ 2) volume a b :=
    (continuous_const.mul ((continuous_id'.sub continuous_const).pow 2)).intervalIntegrable _ _
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le hab hptw hgint
  rw [← Real.norm_eq_abs]
  refine hnorm.trans ?_
  rw [intervalIntegral.integral_const_mul, hsq_int]
  exact le_of_eq (by ring)

/-- **★★★★★ B4c COMPOSITE MIDPOINT RULE ★★★★★** — uniform partition of
    `[a, b]` into `n` panels of width `h = (b-a)/n`, midpoint nodes
    `a + h(i + 1/2)`:

      `|∫_a^b f - h ∑_{i<n} f(a + h(i+1/2))| ≤ M (b-a)³ / (24 n²)`.

    This is THE quadrature theorem the B5 certificate instantiates. -/
theorem composite_midpoint_error {f f' f'' : ℝ → ℝ} {a b M : ℝ} {n : ℕ}
    (hn : 0 < n) (hab : a ≤ b)
    (hf : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ uIcc a b, HasDerivAt f' (f'' x) x)
    (hM : ∀ x ∈ uIcc a b, |f'' x| ≤ M) :
    |(∫ x in a..b, f x)
        - (b - a) / n * ∑ i ∈ Finset.range n, f (a + (b - a) / n * (i + 1 / 2))|
      ≤ M * (b - a) ^ 3 / (24 * n ^ 2) := by
  have hn0 : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  set h : ℝ := (b - a) / n with hh_def
  have hh0 : 0 ≤ h := div_nonneg (by linarith) hnpos.le
  set c : ℕ → ℝ := fun i ↦ a + i * h with hc_def
  have hc0 : c 0 = a := by simp [hc_def]
  have hcn : c n = b := by
    simp only [hc_def, hh_def]
    field_simp
    ring
  have hmono : ∀ i : ℕ, c i ≤ c (i + 1) := by
    intro i
    simp only [hc_def]
    push_cast
    nlinarith [hh0]
  have hpanel_len : ∀ i : ℕ, c (i + 1) - c i = h := by
    intro i
    simp only [hc_def]
    push_cast
    ring
  have hlb : ∀ i : ℕ, a ≤ c i := by
    intro i
    simp only [hc_def]
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) i) hh0]
  have hub : ∀ i : ℕ, i ≤ n → c i ≤ b := by
    intro i hi
    rw [← hcn]
    simp only [hc_def]
    have hcast : (i : ℝ) ≤ n := by exact_mod_cast hi
    nlinarith [mul_le_mul_of_nonneg_right hcast hh0]
  have hsubset : ∀ i : ℕ, i < n → uIcc (c i) (c (i + 1)) ⊆ uIcc a b := by
    intro i hi
    rw [uIcc_of_le (hmono i), uIcc_of_le hab]
    exact Icc_subset_Icc (hlb i) (hub (i + 1) hi)
  have hfc : ContinuousOn f (uIcc a b) :=
    fun y hy ↦ (hf y hy).continuousAt.continuousWithinAt
  have hint_panel : ∀ k : ℕ, k < n → IntervalIntegrable f volume (c k) (c (k + 1)) :=
    fun k hk ↦ (hfc.mono (hsubset k hk)).intervalIntegrable
  -- per-panel single-rule error
  have hpanel : ∀ i : ℕ, i < n →
      |(∫ x in c i..c (i + 1), f x) - h * f (a + h * (i + 1 / 2))| ≤ M * h ^ 3 / 24 := by
    intro i hi
    have hsub := hsubset i hi
    have hmid : (c i + c (i + 1)) / 2 = a + h * (i + 1 / 2) := by
      simp only [hc_def]
      push_cast
      ring
    have hres := midpoint_rule_error (hmono i)
      (fun x hx ↦ hf x (hsub hx)) (fun x hx ↦ hf' x (hsub hx)) (fun x hx ↦ hM x (hsub hx))
    rw [hpanel_len i, hmid] at hres
    exact hres
  -- chain the panels
  have hsum_int : ∑ i ∈ Finset.range n, ∫ x in c i..c (i + 1), f x = ∫ x in a..b, f x := by
    have h := intervalIntegral.sum_integral_adjacent_intervals hint_panel
    rwa [hc0, hcn] at h
  have hdecomp : (∫ x in a..b, f x) - h * ∑ i ∈ Finset.range n, f (a + h * (i + 1 / 2))
      = ∑ i ∈ Finset.range n,
          ((∫ x in c i..c (i + 1), f x) - h * f (a + h * (i + 1 / 2))) := by
    rw [Finset.sum_sub_distrib, hsum_int, ← Finset.mul_sum]
  rw [hdecomp]
  calc |∑ i ∈ Finset.range n, ((∫ x in c i..c (i + 1), f x) - h * f (a + h * (i + 1 / 2)))|
      ≤ ∑ i ∈ Finset.range n,
          |(∫ x in c i..c (i + 1), f x) - h * f (a + h * (i + 1 / 2))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range n, M * h ^ 3 / 24 :=
        Finset.sum_le_sum fun i hi ↦ hpanel i (Finset.mem_range.mp hi)
    _ = n * (M * h ^ 3 / 24) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = M * (b - a) ^ 3 / (24 * n ^ 2) := by
        rw [hh_def]
        field_simp

/-! ## §4 — B4d: explicit `C²` data for the truncated integrand

    The truncated integrand `2u^{-3/4} cos((t/2) log u) · omegaPartial N u`
    is the finite sum over `n < N` of the elementary terms

      `thetaTerm t n u = 2u^{-3/4} cos((t/2) log u) e^{-π(n+1)²u}`.

    Each term is a product of three factors `P·Q·R`; we differentiate
    the product twice via the generic pointwise Leibniz lemma
    `hasDerivAt_mul3` and bound every factor on `[1, ∞)` — the
    resulting constant `thetaTermM t n` is an explicit closed form in
    `π`, `e^{-π(n+1)²}` and `|t|`, independent of the cutoff `T`. -/

/-- One theta-series term of the truncated critical-line integrand. -/
noncomputable def thetaTerm (t : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  2 * u ^ (-(3 / 4) : ℝ) * Real.cos (t / 2 * Real.log u)
    * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)

/-- Explicit first derivative of `thetaTerm t n` (valid for `u > 0`). -/
noncomputable def thetaTermD1 (t : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  -3 / 2 * u ^ (-(7 / 4) : ℝ) * Real.cos (t / 2 * Real.log u)
      * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)
    + 2 * u ^ (-(3 / 4) : ℝ) * (-(t / 2) * Real.sin (t / 2 * Real.log u) / u)
      * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)
    + 2 * u ^ (-(3 / 4) : ℝ) * Real.cos (t / 2 * Real.log u)
      * (-π * ((n : ℝ) + 1) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u))

/-- Explicit second derivative of `thetaTerm t n` (valid for `u > 0`):
    the six-term Leibniz expansion `P''QR + PQ''R + PQR'' + 2P'Q'R +
    2P'QR' + 2PQ'R'`. -/
noncomputable def thetaTermD2 (t : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  21 / 8 * u ^ (-(11 / 4) : ℝ) * Real.cos (t / 2 * Real.log u)
      * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)
    + 2 * u ^ (-(3 / 4) : ℝ)
      * ((t / 2 * Real.sin (t / 2 * Real.log u)
          - (t / 2) ^ 2 * Real.cos (t / 2 * Real.log u)) / u ^ 2)
      * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)
    + 2 * u ^ (-(3 / 4) : ℝ) * Real.cos (t / 2 * Real.log u)
      * ((π * ((n : ℝ) + 1) ^ 2) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u))
    + 2 * (-3 / 2 * u ^ (-(7 / 4) : ℝ)
      * (-(t / 2) * Real.sin (t / 2 * Real.log u) / u)
      * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u))
    + 2 * (-3 / 2 * u ^ (-(7 / 4) : ℝ) * Real.cos (t / 2 * Real.log u)
      * (-π * ((n : ℝ) + 1) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)))
    + 2 * (2 * u ^ (-(3 / 4) : ℝ)
      * (-(t / 2) * Real.sin (t / 2 * Real.log u) / u)
      * (-π * ((n : ℝ) + 1) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)))

/-- **The explicit `C²` bound constant** for `thetaTerm t n` on
    `[1, ∞)` (with `A = π(n+1)²`):

      `M(t, n) = e^{-A} (21/8 + (5/2)|t| + |t|²/2 + 3A + 2|t|A + 2A²)`.

    `T`-independent; at `|t| ≤ 15` the `n = 0` term is `≈ 13` and the
    `n ≥ 1` terms are `< 10⁻²`. -/
noncomputable def thetaTermM (t : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-π * ((n : ℝ) + 1) ^ 2) *
    (21 / 8 + 5 / 2 * |t| + |t| ^ 2 / 2 + 3 * (π * ((n : ℝ) + 1) ^ 2)
      + 2 * |t| * (π * ((n : ℝ) + 1) ^ 2) + 2 * (π * ((n : ℝ) + 1) ^ 2) ^ 2)

/-- Pointwise Leibniz rule for a triple product, packaged for reuse. -/
theorem hasDerivAt_mul3 {P Q R : ℝ → ℝ} {p q r u : ℝ}
    (hP : HasDerivAt P p u) (hQ : HasDerivAt Q q u) (hR : HasDerivAt R r u) :
    HasDerivAt (fun y ↦ P y * Q y * R y)
      (p * Q u * R u + P u * q * R u + P u * Q u * r) u := by
  have h := (hP.fun_mul hQ).fun_mul hR
  convert h using 1
  ring

private theorem hasDerivAt_P {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun y : ℝ ↦ 2 * y ^ (-(3 / 4) : ℝ)) (-3 / 2 * u ^ (-(7 / 4) : ℝ)) u := by
  have h := (Real.hasDerivAt_rpow_const (p := (-(3 / 4) : ℝ)) (Or.inl hu.ne')).const_mul
    (2 : ℝ)
  convert h using 1
  rw [show (-(3 / 4) : ℝ) - 1 = -(7 / 4) from by norm_num]
  ring

private theorem hasDerivAt_P' {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun y : ℝ ↦ -3 / 2 * y ^ (-(7 / 4) : ℝ)) (21 / 8 * u ^ (-(11 / 4) : ℝ)) u := by
  have h := (Real.hasDerivAt_rpow_const (p := (-(7 / 4) : ℝ)) (Or.inl hu.ne')).const_mul
    (-3 / 2 : ℝ)
  convert h using 1
  rw [show (-(7 / 4) : ℝ) - 1 = -(11 / 4) from by norm_num]
  ring

private theorem hasDerivAt_Q (t : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun y : ℝ ↦ Real.cos (t / 2 * Real.log y))
      (-(t / 2) * Real.sin (t / 2 * Real.log u) / u) u := by
  have hlog : HasDerivAt (fun y : ℝ ↦ t / 2 * Real.log y) (t / 2 * u⁻¹) u :=
    (Real.hasDerivAt_log hu.ne').const_mul (t / 2)
  convert hlog.cos using 1
  field_simp

private theorem hasDerivAt_Q' (t : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun y : ℝ ↦ -(t / 2) * Real.sin (t / 2 * Real.log y) / y)
      ((t / 2 * Real.sin (t / 2 * Real.log u)
        - (t / 2) ^ 2 * Real.cos (t / 2 * Real.log u)) / u ^ 2) u := by
  have hlog : HasDerivAt (fun y : ℝ ↦ t / 2 * Real.log y) (t / 2 * u⁻¹) u :=
    (Real.hasDerivAt_log hu.ne').const_mul (t / 2)
  have hnum : HasDerivAt (fun y : ℝ ↦ -(t / 2) * Real.sin (t / 2 * Real.log y))
      (-(t / 2) * (Real.cos (t / 2 * Real.log u) * (t / 2 * u⁻¹))) u :=
    hlog.sin.const_mul (-(t / 2))
  have h := hnum.div (hasDerivAt_id' u) hu.ne'
  convert h using 1
  field_simp
  ring

private theorem hasDerivAt_R (n : ℕ) (u : ℝ) :
    HasDerivAt (fun y : ℝ ↦ Real.exp (-π * ((n : ℝ) + 1) ^ 2 * y))
      (-π * ((n : ℝ) + 1) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)) u := by
  have h := ((hasDerivAt_id' u).const_mul (-π * ((n : ℝ) + 1) ^ 2)).exp
  convert h using 1
  ring

private theorem hasDerivAt_R' (n : ℕ) (u : ℝ) :
    HasDerivAt (fun y : ℝ ↦ -π * ((n : ℝ) + 1) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * y))
      ((π * ((n : ℝ) + 1) ^ 2) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)) u := by
  have h := (hasDerivAt_R n u).const_mul (-π * ((n : ℝ) + 1) ^ 2)
  convert h using 1
  ring

/-- `thetaTerm t n` has derivative `thetaTermD1 t n u` at every `u > 0`. -/
theorem hasDerivAt_thetaTerm (t : ℝ) (n : ℕ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun y : ℝ ↦ thetaTerm t n y) (thetaTermD1 t n u) u := by
  have h := hasDerivAt_mul3 (hasDerivAt_P hu) (hasDerivAt_Q t hu) (hasDerivAt_R n u)
  convert h using 1

/-- `thetaTermD1 t n` has derivative `thetaTermD2 t n u` at every `u > 0`. -/
theorem hasDerivAt_thetaTermD1 (t : ℝ) (n : ℕ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun y : ℝ ↦ thetaTermD1 t n y) (thetaTermD2 t n u) u := by
  have h1 := hasDerivAt_mul3 (hasDerivAt_P' hu) (hasDerivAt_Q t hu) (hasDerivAt_R n u)
  have h2 := hasDerivAt_mul3 (hasDerivAt_P hu) (hasDerivAt_Q' t hu) (hasDerivAt_R n u)
  have h3 := hasDerivAt_mul3 (hasDerivAt_P hu) (hasDerivAt_Q t hu) (hasDerivAt_R' n u)
  have h := (h1.add h2).add h3
  convert h using 1
  simp only [thetaTermD2]
  ring

/-- Triple-product absolute bound from factor bounds. -/
private theorem abs_triple_le {x y z bx by' bz : ℝ}
    (hx : |x| ≤ bx) (hy : |y| ≤ by') (hz : |z| ≤ bz) :
    |x * y * z| ≤ bx * by' * bz := by
  have hbx : 0 ≤ bx := (abs_nonneg x).trans hx
  have hby : 0 ≤ by' := (abs_nonneg y).trans hy
  rw [abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul hx hy (abs_nonneg y) hbx) hz (abs_nonneg z)
    (mul_nonneg hbx hby)

/-- Six-term triangle inequality in the exact shape of `thetaTermD2`. -/
private theorem abs_sum6_le {x₁ x₂ x₃ x₄ x₅ x₆ b₁ b₂ b₃ b₄ b₅ b₆ : ℝ}
    (h₁ : |x₁| ≤ b₁) (h₂ : |x₂| ≤ b₂) (h₃ : |x₃| ≤ b₃)
    (h₄ : |x₄| ≤ b₄) (h₅ : |x₅| ≤ b₅) (h₆ : |x₆| ≤ b₆) :
    |x₁ + x₂ + x₃ + 2 * x₄ + 2 * x₅ + 2 * x₆|
      ≤ b₁ + b₂ + b₃ + 2 * b₄ + 2 * b₅ + 2 * b₆ := by
  have k₄ : |2 * x₄| ≤ 2 * b₄ := by rw [abs_mul, abs_two]; linarith [abs_nonneg x₄]
  have k₅ : |2 * x₅| ≤ 2 * b₅ := by rw [abs_mul, abs_two]; linarith [abs_nonneg x₅]
  have k₆ : |2 * x₆| ≤ 2 * b₆ := by rw [abs_mul, abs_two]; linarith [abs_nonneg x₆]
  calc |x₁ + x₂ + x₃ + 2 * x₄ + 2 * x₅ + 2 * x₆|
      ≤ |x₁ + x₂ + x₃ + 2 * x₄ + 2 * x₅| + |2 * x₆| := abs_add _ _
    _ ≤ |x₁ + x₂ + x₃ + 2 * x₄| + |2 * x₅| + |2 * x₆| := by
        linarith [abs_add (x₁ + x₂ + x₃ + 2 * x₄) (2 * x₅)]
    _ ≤ |x₁ + x₂ + x₃| + |2 * x₄| + |2 * x₅| + |2 * x₆| := by
        linarith [abs_add (x₁ + x₂ + x₃) (2 * x₄)]
    _ ≤ |x₁ + x₂| + |x₃| + |2 * x₄| + |2 * x₅| + |2 * x₆| := by
        linarith [abs_add (x₁ + x₂) x₃]
    _ ≤ |x₁| + |x₂| + |x₃| + |2 * x₄| + |2 * x₅| + |2 * x₆| := by
        linarith [abs_add x₁ x₂]
    _ ≤ b₁ + b₂ + b₃ + 2 * b₄ + 2 * b₅ + 2 * b₆ := by linarith

/-- **★ B4d `C²` BOUND, single term ★** — on `[1, ∞)`:
    `|thetaTermD2 t n u| ≤ thetaTermM t n`. -/
theorem abs_thetaTermD2_le (t : ℝ) (n : ℕ) {u : ℝ} (hu : 1 ≤ u) :
    |thetaTermD2 t n u| ≤ thetaTermM t n := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hA : (0 : ℝ) < π * ((n : ℝ) + 1) ^ 2 := by positivity
  have hE : (0 : ℝ) < Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u) := Real.exp_pos _
  have hrpow_le_one : ∀ e : ℝ, e ≤ 0 → u ^ e ≤ 1 :=
    fun e he ↦ Real.rpow_le_one_of_one_le_of_nonpos hu he
  have hrpow_pos : ∀ e : ℝ, (0 : ℝ) < u ^ e := fun e ↦ Real.rpow_pos_of_pos hu0 e
  -- factor bounds
  have hP0 : |2 * u ^ (-(3 / 4) : ℝ)| ≤ 2 := by
    rw [abs_of_pos (by positivity)]
    nlinarith [hrpow_le_one (-(3 / 4) : ℝ) (by norm_num)]
  have hP1 : |-3 / 2 * u ^ (-(7 / 4) : ℝ)| ≤ 3 / 2 := by
    rw [abs_mul, show |(-3 / 2 : ℝ)| = 3 / 2 from by norm_num, abs_of_pos (hrpow_pos _)]
    nlinarith [hrpow_le_one (-(7 / 4) : ℝ) (by norm_num), hrpow_pos (-(7 / 4) : ℝ)]
  have hP2 : |21 / 8 * u ^ (-(11 / 4) : ℝ)| ≤ 21 / 8 := by
    rw [abs_of_pos (by positivity)]
    nlinarith [hrpow_le_one (-(11 / 4) : ℝ) (by norm_num)]
  have hQ0 : |Real.cos (t / 2 * Real.log u)| ≤ 1 := Real.abs_cos_le_one _
  have hsin := Real.abs_sin_le_one (t / 2 * Real.log u)
  have hcos := Real.abs_cos_le_one (t / 2 * Real.log u)
  have habs_half : |t / 2| = |t| / 2 := by rw [abs_div, abs_two]
  have hQ1 : |-(t / 2) * Real.sin (t / 2 * Real.log u) / u| ≤ |t| / 2 := by
    rw [abs_div, abs_of_pos hu0]
    refine le_trans (div_le_self (abs_nonneg _) hu) ?_
    rw [abs_mul, abs_neg, habs_half]
    nlinarith [mul_nonneg (div_nonneg (abs_nonneg t) (by norm_num : (0:ℝ) ≤ 2))
      (sub_nonneg.mpr hsin)]
  have hQ2 : |(t / 2 * Real.sin (t / 2 * Real.log u)
      - (t / 2) ^ 2 * Real.cos (t / 2 * Real.log u)) / u ^ 2|
      ≤ |t| / 2 + (|t| / 2) ^ 2 := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < u ^ 2)]
    have hu2 : (1 : ℝ) ≤ u ^ 2 := by nlinarith
    refine le_trans (div_le_self (abs_nonneg _) hu2) ?_
    rw [sub_eq_add_neg]
    refine le_trans (abs_add _ _) ?_
    rw [abs_neg, abs_mul, abs_mul, habs_half,
      show |(t / 2) ^ 2| = (|t| / 2) ^ 2 from by rw [abs_pow, habs_half]]
    nlinarith [mul_nonneg (div_nonneg (abs_nonneg t) (by norm_num : (0:ℝ) ≤ 2))
      (sub_nonneg.mpr hsin), mul_nonneg (sq_nonneg (|t| / 2)) (sub_nonneg.mpr hcos)]
  have hexp_le : Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)
      ≤ Real.exp (-π * ((n : ℝ) + 1) ^ 2) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) hA.le]
  have hR0 : |Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)|
      ≤ Real.exp (-π * ((n : ℝ) + 1) ^ 2) := by
    rw [abs_of_pos hE]; exact hexp_le
  have hR1 : |-π * ((n : ℝ) + 1) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)|
      ≤ π * ((n : ℝ) + 1) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2) := by
    rw [abs_mul, show |-π * ((n : ℝ) + 1) ^ 2| = π * ((n : ℝ) + 1) ^ 2 from by
        rw [abs_of_neg (by nlinarith : -π * ((n : ℝ) + 1) ^ 2 < 0)]; ring,
      abs_of_pos hE]
    exact mul_le_mul_of_nonneg_left hexp_le hA.le
  have hR2 : |(π * ((n : ℝ) + 1) ^ 2) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)|
      ≤ (π * ((n : ℝ) + 1) ^ 2) ^ 2 * Real.exp (-π * ((n : ℝ) + 1) ^ 2) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (π * ((n : ℝ) + 1) ^ 2) ^ 2),
      abs_of_pos hE]
    exact mul_le_mul_of_nonneg_left hexp_le (by positivity)
  -- assemble the six Leibniz terms
  have hT1 := abs_triple_le hP2 hQ0 hR0
  have hT2 := abs_triple_le hP0 hQ2 hR0
  have hT3 := abs_triple_le hP0 hQ0 hR2
  have hT4 := abs_triple_le hP1 hQ1 hR0
  have hT5 := abs_triple_le hP1 hQ0 hR1
  have hT6 := abs_triple_le hP0 hQ1 hR1
  unfold thetaTermD2 thetaTermM
  refine le_trans (abs_sum6_le hT1 hT2 hT3 hT4 hT5 hT6) (le_of_eq ?_)
  ring

/-- The truncated integrand IS the finite sum of the `thetaTerm`s. -/
theorem truncated_integrand_eq (t : ℝ) (N : ℕ) :
    (fun u : ℝ ↦ 2 * u ^ (-(3 / 4) : ℝ) * Real.cos (t / 2 * Real.log u) * omegaPartial N u)
      = fun u : ℝ ↦ ∑ n ∈ Finset.range N, thetaTerm t n u := by
  funext u
  simp only [omegaPartial, thetaTerm, Finset.mul_sum]

/-- First derivative witness for the sum of `thetaTerm`s (`u > 0`). -/
theorem hasDerivAt_thetaTerm_sum (t : ℝ) (N : ℕ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun y : ℝ ↦ ∑ n ∈ Finset.range N, thetaTerm t n y)
      (∑ n ∈ Finset.range N, thetaTermD1 t n u) u :=
  HasDerivAt.fun_sum fun n _ ↦ hasDerivAt_thetaTerm t n hu

/-- **★ B4d DERIVATIVE WITNESS ★** — the truncated integrand
    `2u^{-3/4} cos((t/2) log u) · omegaPartial N u` has derivative
    `∑_{n<N} thetaTermD1 t n u` at every `u > 0`; this is the `f'`
    hypothesis of the composite midpoint rule for B5. -/
theorem hasDerivAt_truncated_integrand (t : ℝ) (N : ℕ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt
      (fun y : ℝ ↦ 2 * y ^ (-(3 / 4) : ℝ) * Real.cos (t / 2 * Real.log y) * omegaPartial N y)
      (∑ n ∈ Finset.range N, thetaTermD1 t n u) u := by
  rw [truncated_integrand_eq t N]
  exact hasDerivAt_thetaTerm_sum t N hu

/-- Second derivative witness for the sum (`u > 0`); this is the `f''`
    hypothesis of the composite midpoint rule for B5. -/
theorem hasDerivAt_thetaTermD1_sum (t : ℝ) (N : ℕ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun y : ℝ ↦ ∑ n ∈ Finset.range N, thetaTermD1 t n y)
      (∑ n ∈ Finset.range N, thetaTermD2 t n u) u :=
  HasDerivAt.fun_sum fun n _ ↦ hasDerivAt_thetaTermD1 t n hu

/-- **★★★★★ B4d `C²` BOUND ★★★★★** — the explicit, `T`-independent
    second-derivative bound for the truncated integrand on `[1, ∞)`:
    this is the `M` hypothesis of the composite midpoint rule for B5. -/
theorem abs_thetaTermD2_sum_le (t : ℝ) (N : ℕ) {u : ℝ} (hu : 1 ≤ u) :
    |∑ n ∈ Finset.range N, thetaTermD2 t n u| ≤ ∑ n ∈ Finset.range N, thetaTermM t n :=
  (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun n _ ↦ abs_thetaTermD2_le t n hu)

end PrincipiaTractalis.XiQuadrature

-- Axiom check. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.XiQuadrature.integral_exp_neg_pi_mul_Ioi
#print axioms PrincipiaTractalis.XiQuadrature.Xi_split
#print axioms PrincipiaTractalis.XiQuadrature.Xi_split_intervalIntegral
#print axioms PrincipiaTractalis.XiQuadrature.Xi_tail_bound
#print axioms PrincipiaTractalis.XiQuadrature.omegaPartial_nonneg
#print axioms PrincipiaTractalis.XiQuadrature.omega_partial_error
#print axioms PrincipiaTractalis.XiQuadrature.abs_sub_taylor1_le
#print axioms PrincipiaTractalis.XiQuadrature.midpoint_rule_error
#print axioms PrincipiaTractalis.XiQuadrature.composite_midpoint_error
#print axioms PrincipiaTractalis.XiQuadrature.hasDerivAt_mul3
#print axioms PrincipiaTractalis.XiQuadrature.hasDerivAt_thetaTerm
#print axioms PrincipiaTractalis.XiQuadrature.hasDerivAt_thetaTermD1
#print axioms PrincipiaTractalis.XiQuadrature.abs_thetaTermD2_le
#print axioms PrincipiaTractalis.XiQuadrature.truncated_integrand_eq
#print axioms PrincipiaTractalis.XiQuadrature.hasDerivAt_thetaTerm_sum
#print axioms PrincipiaTractalis.XiQuadrature.hasDerivAt_truncated_integrand
#print axioms PrincipiaTractalis.XiQuadrature.hasDerivAt_thetaTermD1_sum
#print axioms PrincipiaTractalis.XiQuadrature.abs_thetaTermD2_sum_le
