/-
# Hankel Termwise Interchange — Fubini Step for the Polylog-Hankel Identity

The genuine analytic gap isolated by `TsumHankelAgreement.lean`:

  `∫_(Ioi 0) t^(s-1) · (Σ_n z^(n+1) · e^(-(n+1)·t)) dt`
  `= Σ_n ∫_(Ioi 0) t^(s-1) · z^(n+1) · e^(-(n+1)·t) dt`

for `0 < Re s` and `‖z‖ < 1`.

**Strategy** (mirrors `Mathlib/NumberTheory/LSeries/MellinEqDirichlet.lean`):

We apply `MeasureTheory.integral_tsum_of_summable_integral_norm`.

This is the **second atomic deliverable for axiom retirement**.

Stage L4 — Termwise interchange (Fubini on the Hankel contour).
-/

import PF.Analytic.TsumHankelAgreement
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecificLimits.Normed

namespace PrincipiaTractalis.Analytic

open Complex Filter Topology MeasureTheory Set Real

set_option maxHeartbeats 400000 in
/-! ## Per-term integrand (principal-branch Γ form) -/

/-- **Per-term polylog-Hankel integrand** on `(0,∞)`, principal-branch
    Γ form:

      `F_n(t) := t^(s-1) · (z^(n+1) · e^(-(n+1)·t))`.

    Associativity mirrors `Mathlib/NumberTheory/LSeries/MellinEqDirichlet.lean`
    where `F_n(t) = t^(s-1) · (a_n · exp(-p_n · t))` with
    `a_n = z^(n+1)`, `p_n = (n+1 : ℝ)`. -/
noncomputable def polylogHankelTerm (s z : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (s - 1) *
    (z ^ (n + 1) * (Real.exp (-(((n + 1 : ℕ) : ℝ) * t)) : ℂ))

/-! ## Bridge to the original form (geometric expansion summand) -/

/-- **Equivalence with the original form** in `TsumHankelAgreement`:
    `(t : ℂ)^(s-1) · (z^(n+1) · cexp(-((n+1):ℂ) · t))`. -/
theorem polylogHankelTerm_eq_orig (s z : ℂ) (n : ℕ) (t : ℝ) :
    polylogHankelTerm s z n t =
    (t : ℂ) ^ (s - 1) * (z ^ (n + 1) *
      Complex.exp (-((n + 1 : ℕ) : ℂ) * (t : ℂ))) := by
  unfold polylogHankelTerm
  congr 2
  -- ↑(Real.exp y) = Complex.exp ↑y, then normalize the argument cast
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-! ## Step 1: Per-term integrability -/

/-- **Continuity of `F_n`** on `Ioi 0` (needed for `aestronglyMeasurable`). -/
theorem polylogHankelTerm_continuousOn (s z : ℂ) (n : ℕ) :
    ContinuousOn (polylogHankelTerm s z n) (Ioi (0 : ℝ)) := by
  unfold polylogHankelTerm
  apply ContinuousOn.mul
  · -- t ↦ (t : ℂ)^(s-1) continuous on Ioi 0
    intro t ht
    apply ContinuousAt.continuousWithinAt
    have h_t_slit : (t : ℂ) ∈ Complex.slitPlane :=
      Complex.ofReal_mem_slitPlane.2 (Set.mem_Ioi.mp ht)
    have h_t_cont : Tendsto (fun u : ℝ => (u : ℂ)) (𝓝 t) (𝓝 (t : ℂ)) :=
      Complex.continuous_ofReal.continuousAt
    exact h_t_cont.cpow tendsto_const_nhds h_t_slit
  · -- t ↦ z^(n+1) · ((Real.exp(-(n+1)·t)) : ℂ) continuous everywhere
    apply Continuous.continuousOn
    apply Continuous.mul continuous_const
    exact Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg)

/-- **AE strong measurability** of `F_n` on `volume.restrict (Ioi 0)`. -/
theorem polylogHankelTerm_aestronglyMeasurable (s z : ℂ) (n : ℕ) :
    AEStronglyMeasurable (polylogHankelTerm s z n)
                          (volume.restrict (Ioi (0 : ℝ))) :=
  (polylogHankelTerm_continuousOn s z n).aestronglyMeasurable measurableSet_Ioi

/-- **Pointwise norm bound for `F_n`** on `Ioi 0`:

      `‖F_n(t)‖ = ‖z‖^(n+1) · t^(Re s - 1) · exp(-(n+1)·t)`. -/
theorem polylogHankelTerm_norm_eq {s z : ℂ} (n : ℕ) {t : ℝ} (ht : 0 < t) :
    ‖polylogHankelTerm s z n t‖ =
    ‖z‖ ^ (n + 1) * (t ^ (s.re - 1) * Real.exp (-(((n + 1 : ℕ) : ℝ) * t))) := by
  unfold polylogHankelTerm
  rw [norm_mul, norm_mul, norm_pow]
  rw [norm_cpow_eq_rpow_re_of_pos ht (s - 1)]
  rw [Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
  have h_sub_re : (s - 1).re = s.re - 1 := by simp
  rw [h_sub_re]
  ring

/-- **Integrability of `F_n`** on `Ioi 0` for `0 < Re s`.

    Direct via norm domination: `‖F_n(t)‖ ≤ ‖z‖^(n+1) · t^(Re s - 1) · exp(-t)`
    (since `exp(-(n+1)·t) ≤ exp(-t)` for `t > 0, n ≥ 0`), and the RHS is
    integrable (Γ-convergent, scaled by a constant). -/
theorem polylogHankelTerm_integrable {s : ℂ} (hs : 0 < s.re)
    (z : ℂ) (n : ℕ) :
    IntegrableOn (polylogHankelTerm s z n) (Ioi (0 : ℝ)) := by
  -- Use the integrable dominating function ‖z‖^(n+1) · t^(Re s - 1) · exp(-t)
  -- (the standard Γ-integrand scaled by a constant).
  have h_dom_int : IntegrableOn
      (fun t : ℝ => ‖z‖ ^ (n + 1) * (t ^ (s.re - 1) * Real.exp (-t)))
      (Ioi (0 : ℝ)) :=
    (gammaIntegrand_real_integrable hs).const_mul (‖z‖ ^ (n + 1))
  -- Apply Integrable.mono' with the dominating bound.
  refine h_dom_int.mono' (polylogHankelTerm_aestronglyMeasurable s z n) ?_
  -- Show: ‖F_n(t)‖ ≤ ‖z‖^(n+1) · (t^(Re s - 1) · exp(-t)) for a.e. t in Ioi 0
  refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
  refine Filter.Eventually.of_forall (fun t ht => ?_)
  have ht_pos : 0 < t := Set.mem_Ioi.mp ht
  -- Compute ‖F_n(t)‖
  rw [polylogHankelTerm_norm_eq n ht_pos]
  -- Now: ‖z‖^(n+1) · (t^(Re s - 1) · exp(-(n+1)·t)) ≤ ‖z‖^(n+1) · (t^(Re s - 1) · exp(-t))
  have h_z_nn : 0 ≤ ‖z‖ ^ (n + 1) := pow_nonneg (norm_nonneg _) _
  have h_t_rpow_nn : 0 ≤ t ^ (s.re - 1) := Real.rpow_nonneg ht_pos.le _
  -- exp(-(n+1)·t) ≤ exp(-t) iff -(n+1)·t ≤ -t iff t ≤ (n+1)·t
  have h_exp_le : Real.exp (-(((n + 1 : ℕ) : ℝ) * t)) ≤ Real.exp (-t) := by
    apply Real.exp_le_exp.mpr
    have hn1_ge_one : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    have : t ≤ ((n + 1 : ℕ) : ℝ) * t := by
      calc t = 1 * t := by ring
        _ ≤ ((n + 1 : ℕ) : ℝ) * t :=
          mul_le_mul_of_nonneg_right hn1_ge_one ht_pos.le
    linarith
  -- Combine
  have : t ^ (s.re - 1) * Real.exp (-(((n + 1 : ℕ) : ℝ) * t)) ≤
         t ^ (s.re - 1) * Real.exp (-t) :=
    mul_le_mul_of_nonneg_left h_exp_le h_t_rpow_nn
  have h_final : ‖z‖ ^ (n + 1) *
                  (t ^ (s.re - 1) * Real.exp (-(((n + 1 : ℕ) : ℝ) * t))) ≤
                 ‖z‖ ^ (n + 1) * (t ^ (s.re - 1) * Real.exp (-t)) :=
    mul_le_mul_of_nonneg_left this h_z_nn
  -- The bound on RHS of mono' needs `‖f a‖ ≤ g a` where `g` is the dominator.
  -- Our dominator g(t) = ‖z‖^(n+1) · (t^(Re s - 1) · exp(-t))
  -- We need: ‖F_n(t)‖ ≤ g(t). Apply transitivity if needed:
  exact h_final

/-! ## Step 2: Norm-integral evaluation -/

/-- **Closed-form for the integral of the L¹ norm of `F_n`**:

      `∫_(Ioi 0) ‖F_n(t)‖ dt = ‖z‖^(n+1) · (n+1)^(-Re s) · Γ(Re s)`. -/
theorem polylogHankelTerm_integral_norm_eq {s : ℂ} (hs : 0 < s.re) (z : ℂ) (n : ℕ) :
    ∫ t in Ioi (0 : ℝ), ‖polylogHankelTerm s z n t‖ =
    ‖z‖ ^ (n + 1) * (((n + 1 : ℕ) : ℝ) ^ (-s.re) * Real.Gamma s.re) := by
  have hn_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
  -- Pointwise norm equality on Ioi 0
  have h_pointwise : EqOn (fun t : ℝ => ‖polylogHankelTerm s z n t‖)
      (fun t : ℝ => ‖z‖ ^ (n + 1) * (t ^ (s.re - 1) *
                      Real.exp (-(((n + 1 : ℕ) : ℝ) * t))))
      (Ioi (0 : ℝ)) := by
    intro t ht
    simp only [Set.mem_Ioi] at ht
    exact polylogHankelTerm_norm_eq n ht
  rw [setIntegral_congr_fun measurableSet_Ioi h_pointwise]
  -- Pull constant ‖z‖^(n+1) out
  rw [MeasureTheory.integral_const_mul]
  -- ∫ t^(Re s - 1) · exp(-(n+1)·t) dt = (1/(n+1))^(Re s) · Γ(Re s)
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hs hn_pos]
  -- (1/(n+1))^(Re s) = (n+1)^(-Re s)
  have h_rpow : ((1 : ℝ) / ((n + 1 : ℕ) : ℝ)) ^ s.re = ((n + 1 : ℕ) : ℝ) ^ (-s.re) := by
    rw [one_div, Real.inv_rpow hn_pos.le, ← Real.rpow_neg hn_pos.le]
  rw [h_rpow]

/-! ## Step 3: Summability of the L¹ norm series -/

/-- **Summability** of `Σ_n ‖z‖^(n+1) · (n+1)^(-Re s) · Γ(Re s)`
    for `0 < Re s` and `‖z‖ < 1`. -/
theorem summable_polylogHankel_norm
    {s : ℂ} (hs : 0 < s.re) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => ‖z‖ ^ (n + 1) *
                            (((n + 1 : ℕ) : ℝ) ^ (-s.re) * Real.Gamma s.re)) := by
  -- Factor out Γ(Re s) constant
  have h_eq : (fun n : ℕ => ‖z‖ ^ (n + 1) *
                            (((n + 1 : ℕ) : ℝ) ^ (-s.re) * Real.Gamma s.re)) =
              (fun n : ℕ => (‖z‖ ^ (n + 1) *
                            ((n + 1 : ℕ) : ℝ) ^ (-s.re)) * Real.Gamma s.re) := by
    funext n; ring
  rw [h_eq]
  apply Summable.mul_right
  -- Σ ‖z‖^(n+1) · (n+1)^(-Re s) summable: bound by ‖z‖^(n+1)
  have h_geom : Summable (fun n : ℕ => ‖z‖ ^ (n + 1)) := by
    have h := summable_geometric_of_lt_one (norm_nonneg z) hz
    have : Summable (fun n : ℕ => ‖z‖ * ‖z‖ ^ n) := h.mul_left ‖z‖
    refine this.congr (fun n => ?_)
    rw [← pow_succ' ‖z‖ n]
  refine Summable.of_nonneg_of_le ?_ ?_ h_geom
  · -- Nonneg
    intro n
    have h1 : 0 ≤ ‖z‖ ^ (n + 1) := pow_nonneg (norm_nonneg _) _
    have h2 : 0 ≤ ((n + 1 : ℕ) : ℝ) ^ (-s.re) :=
      Real.rpow_nonneg (by exact_mod_cast Nat.zero_le _) _
    exact mul_nonneg h1 h2
  · -- Bound: term ≤ ‖z‖^(n+1)
    intro n
    have hn_ge_one : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    have h_neg : -s.re ≤ 0 := neg_nonpos.mpr hs.le
    have h_rpow_le_one : ((n + 1 : ℕ) : ℝ) ^ (-s.re) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hn_ge_one h_neg
    have h_zn_nn : 0 ≤ ‖z‖ ^ (n + 1) := pow_nonneg (norm_nonneg _) _
    calc ‖z‖ ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (-s.re)
        ≤ ‖z‖ ^ (n + 1) * 1 :=
          mul_le_mul_of_nonneg_left h_rpow_le_one h_zn_nn
      _ = ‖z‖ ^ (n + 1) := by ring

/-! ## Step 4: Summability of `∫ ‖F_n‖` -/

/-- **Summability of `∫_(Ioi 0) ‖F_n(t)‖ dt`** for `0 < Re s, ‖z‖ < 1`. -/
theorem summable_integral_norm_polylogHankel
    {s : ℂ} (hs : 0 < s.re) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => ∫ t in Ioi (0 : ℝ), ‖polylogHankelTerm s z n t‖) := by
  have h_eq : (fun n : ℕ => ∫ t in Ioi (0 : ℝ), ‖polylogHankelTerm s z n t‖) =
              (fun n : ℕ => ‖z‖ ^ (n + 1) *
                            (((n + 1 : ℕ) : ℝ) ^ (-s.re) * Real.Gamma s.re)) := by
    funext n
    exact polylogHankelTerm_integral_norm_eq hs z n
  rw [h_eq]
  exact summable_polylogHankel_norm hs hz

/-! ## Step 5: The Fubini interchange -/

/-- **Termwise interchange theorem** for the polylog-Hankel integrand.

    For `0 < Re s` and `‖z‖ < 1`:

      `Σ_n ∫_(Ioi 0) F_n(t) dt = ∫_(Ioi 0) Σ_n F_n(t) dt`. -/
theorem polylogHankel_tsum_integral_eq_integral_tsum
    {s : ℂ} (hs : 0 < s.re) {z : ℂ} (hz : ‖z‖ < 1) :
    ∑' n : ℕ, ∫ t in Ioi (0 : ℝ), polylogHankelTerm s z n t =
    ∫ t in Ioi (0 : ℝ), ∑' n : ℕ, polylogHankelTerm s z n t := by
  refine integral_tsum_of_summable_integral_norm
    (fun n => (polylogHankelTerm_integrable hs z n)) ?_
  exact summable_integral_norm_polylogHankel hs hz

/-! ## Step 6: Identification of the sum -/

/-- **Sum-of-terms identification**: for `‖z‖ < 1` and `t > 0`,

      `Σ_n F_n(t) = t^(s-1) · 1/(e^t/z - 1)`. -/
theorem polylogHankel_sum_eq_kernel
    {s z : ℂ} (hz : ‖z‖ < 1) (hz_ne : z ≠ 0) {t : ℝ} (ht : 0 < t) :
    ∑' n : ℕ, polylogHankelTerm s z n t =
    (t : ℂ) ^ (s - 1) * ((1 : ℂ) / (Complex.exp (t : ℂ) / z - 1)) := by
  have h_eq : ∀ n : ℕ, polylogHankelTerm s z n t =
              (t : ℂ) ^ (s - 1) *
                (z ^ (n + 1) * Complex.exp (-((n + 1 : ℕ) : ℂ) * (t : ℂ))) := by
    intro n
    exact polylogHankelTerm_eq_orig s z n t
  simp_rw [h_eq]
  rw [tsum_mul_left]
  congr 1
  exact (geom_series_polylog_kernel hz hz_ne ht).symm

/-! ## Capstone: full Fubini identity -/

/-- **Capstone**: the polylog-Hankel integrand satisfies the Fubini
    identity. For `0 < Re s`, `‖z‖ < 1`, `z ≠ 0`:

      `Σ_n ∫_(Ioi 0) F_n(t) dt = ∫_(Ioi 0) t^(s-1) · 1/(e^t/z - 1) dt`.

    This is the second atomic deliverable for axiom retirement. -/
theorem polylogHankel_termwise_interchange_capstone
    {s : ℂ} (hs : 0 < s.re) {z : ℂ} (hz : ‖z‖ < 1) (hz_ne : z ≠ 0) :
    ∑' n : ℕ, ∫ t in Ioi (0 : ℝ), polylogHankelTerm s z n t =
    ∫ t in Ioi (0 : ℝ),
      (t : ℂ) ^ (s - 1) * ((1 : ℂ) / (Complex.exp (t : ℂ) / z - 1)) := by
  rw [polylogHankel_tsum_integral_eq_integral_tsum hs hz]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro t ht
  simp only [Set.mem_Ioi] at ht
  exact polylogHankel_sum_eq_kernel hz hz_ne ht

end PrincipiaTractalis.Analytic
