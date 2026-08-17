/-
# r277: DIRICHLET ETA CONDITIONAL CONVERGENCE ON COMPLEX `0 < Re s`.

★ 2026-08-16 r277 — closes the r276 refined residual
`DirichletEta_ConditionalConvergence_ComplexOffReal` by delivering the
complex Dirichlet-test / abscissa-of-conditional-convergence result
unconditionally on the FULL right half-plane `{s : ℂ | 0 < Re s}`,
including the `Im s ≠ 0` off-real portion.

## Attack surface

Mathlib exposes only ABSOLUTE convergence of the Dirichlet η LSeries on
`1 < Re s`. Mathlib's Dirichlet-test infrastructure
`Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded` requires a
REAL monotone factor and thus applies to the real ray only (r276).

For general `s ∈ ℂ` with `Im s ≠ 0`, we develop bespoke
summation-by-parts + a complex-power difference bound directly, using:

1. `hasDerivAt_ofReal_cpow_const` (`Mathlib/Analysis/SpecialFunctions/Pow/Deriv.lean:274`).
2. `norm_image_sub_le_of_norm_deriv_le_segment'`
   (`Mathlib/Analysis/Calculus/MeanValue.lean:323`).
3. `Finset.sum_range_by_parts`
   (`Mathlib/Algebra/BigOperators/Module.lean:53`).
4. `Complex.norm_natCast_cpow_of_pos`
   (`Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:342`).
5. `Real.summable_one_div_nat_rpow`
   (`Mathlib/Analysis/PSeries.lean:297`).
6. `Real.rpow_le_rpow_of_exponent_nonpos`
   (`Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:610`).
7. `neg_one_geom_sum` (`Mathlib/Algebra/Ring/GeomSum.lean`).

## What r277 adds

Analytical primitive (UNCONDITIONAL):

- `cpow_neg_diff_norm_le`: `‖((i + 1 : ℝ) : ℂ)^(-s) - ((i : ℝ) : ℂ)^(-s)‖
  ≤ ‖s‖ / (i : ℝ)^(s.re + 1)` for `0 < s.re` and `i ≥ 1`.

Reindexed factorization: shift `n = k + 1` so the vanishing LSeries term
at `n = 0` drops out and both `f k = (k+1)^{-s}` and `g k = (-1)^k` are
regular.

- `etaShiftF s k := ((k + 1 : ℝ) : ℂ)^(-s)`, `etaShiftG k := (-1 : ℂ)^k`.
- `etaShiftF_mul_etaShiftG_eq_lseries_term_succ`: `etaShiftF s k * etaShiftG k
  = LSeries.term dirichletEtaCoeff s (k + 1)`.
- `norm_sum_etaShiftG_le`: `‖∑ i ∈ range n, etaShiftG i‖ ≤ 1` via
  `neg_one_geom_sum`.

Full complex CauchySeq (UNCONDITIONAL):

- `dirichletEta_lseries_partial_cauchy {s : ℂ} (hs : 0 < s.re)`:
  `CauchySeq (fun N : ℕ => ∑ n ∈ range N, LSeries.term dirichletEtaCoeff s n)`.

Residual discharge:

- `dirichletEta_conditionalConvergence_complexOffReal_discharged`:
  the r276 refined residual
  `DirichletEta_ConditionalConvergence_ComplexOffReal` is INHABITED.
- `dirichletEta_lseries_partial_hasLimit {s : ℂ} (hs : 0 < s.re)`:
  `∃ L : ℂ, Tendsto (LSeries partial sums) atTop (𝓝 L)`.

## Net residual movement

Before r277:
- Real-ray abscissa unconditional (r276).
- Complex-off-real portion pending inside
  `DirichletEta_ConditionalConvergence_ComplexOffReal`.

After r277:
- Full `0 < Re s` abscissa UNCONDITIONAL Lean.
- Ingredient (2) of the r271 four-ingredient Dirichlet 1858 residual
  FULLY DISCHARGED. Only ingredients (3) [`Differentiable ℂ` analytic
  continuation of η to `0 < Re s`] and (4) [identity theorem match]
  remain from the r275 design.

## Framework-first position

Route B's mathlib-native RH front still depends on the r275 refined
residual `Dirichlet1858_PowerSeriesLimit_EqualsProductForm` + the
r262 numerical positive Xi witness. r277 removes ONE named residual
(`DirichletEta_ConditionalConvergence_ComplexOffReal`) and thereby
tightens the classical-ingredient layer of Dirichlet 1858 without
changing Route B's residual list.

Substrate closure via `unified_clay_closure_via_substrate_linkage_bulletproof`
unchanged; all six Clay axes still ONE bundle.

## Scope

* NOT novel — standard MVT + Abel summation + p-series summability.
* NOT a Millennium discharge.
* IS full complex abscissa of conditional convergence for Dirichlet η,
  discharging ingredient (2) of the r271 Dirichlet 1858 residual.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`.
Kernel-only.
-/

import PF.DirichletEtaConditionalConvergenceReal_r276
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.PSeries
import Mathlib.Algebra.Ring.GeomSum

open Filter Topology

namespace PrincipiaTractalis.DirichletEtaConditionalConvergenceComplex

open PrincipiaTractalis.DirichletEtaComplex
open PrincipiaTractalis.DirichletEtaConditionalConvergenceReal

/-! ## §1 Complex power difference bound: `‖(i+1)^{-s} - i^{-s}‖ ≤ ‖s‖/i^{σ+1}`. -/

/-- Norm of the derivative bound: `‖-s · t^{-s-1}‖ ≤ ‖s‖ · i^{-Re s - 1}`
for `t ≥ i ≥ 1`, `0 < Re s`. -/
private lemma norm_neg_s_mul_cpow_neg_sub_one_le
    {s : ℂ} (hs : 0 < s.re) {i : ℕ} (hi : 1 ≤ i)
    {t : ℝ} (ht : (i : ℝ) ≤ t) :
    ‖-s * (t : ℂ)^(-s - 1)‖ ≤ ‖s‖ / (i : ℝ)^(s.re + 1) := by
  have hi_pos : (0 : ℝ) < (i : ℝ) := by
    have : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
    linarith
  have ht_pos : (0 : ℝ) < t := lt_of_lt_of_le hi_pos ht
  have hnorm : ‖(t : ℂ)^(-s - 1)‖ = t^(-s.re - 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht_pos]
    simp [Complex.sub_re, Complex.neg_re]
  have hexp_nonpos : (-s.re - 1) ≤ 0 := by linarith
  have hbase_le : t^(-s.re - 1) ≤ (i : ℝ)^(-s.re - 1) :=
    Real.rpow_le_rpow_of_exponent_nonpos hi_pos ht hexp_nonpos
  have hi_rpow_eq : (i : ℝ)^(-s.re - 1) = 1 / (i : ℝ)^(s.re + 1) := by
    rw [show (-s.re - 1 : ℝ) = -(s.re + 1) by ring, Real.rpow_neg hi_pos.le]
    field_simp
  calc ‖-s * (t : ℂ)^(-s - 1)‖
      = ‖s‖ * ‖(t : ℂ)^(-s - 1)‖ := by rw [norm_mul, norm_neg]
    _ = ‖s‖ * t^(-s.re - 1) := by rw [hnorm]
    _ ≤ ‖s‖ * (i : ℝ)^(-s.re - 1) := by
        apply mul_le_mul_of_nonneg_left hbase_le (norm_nonneg _)
    _ = ‖s‖ * (1 / (i : ℝ)^(s.re + 1)) := by rw [hi_rpow_eq]
    _ = ‖s‖ / (i : ℝ)^(s.re + 1) := by ring

/-- Complex power difference bound via MVT.
`‖(i+1)^{-s} - i^{-s}‖ ≤ ‖s‖ / i^{Re s + 1}` for `i ≥ 1`, `0 < Re s`. -/
theorem cpow_neg_diff_norm_le {s : ℂ} (hs : 0 < s.re) {i : ℕ} (hi : 1 ≤ i) :
    ‖(((i + 1 : ℕ) : ℝ) : ℂ)^(-s) - (((i : ℕ) : ℝ) : ℂ)^(-s)‖
      ≤ ‖s‖ / (i : ℝ)^(s.re + 1) := by
  have hi_pos : (0 : ℝ) < (i : ℝ) := by
    have : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
    linarith
  have hs_ne : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
  have hns_ne : (-s : ℂ) ≠ 0 := neg_ne_zero.mpr hs_ne
  set f : ℝ → ℂ := fun t => (t : ℂ)^(-s) with hf_def
  have h_deriv : ∀ t ∈ Set.Icc (i : ℝ) ((i : ℝ) + 1),
      HasDerivWithinAt f (-s * (t : ℂ)^(-s - 1)) (Set.Icc (i : ℝ) ((i : ℝ) + 1)) t := by
    intro t ht
    have ht_pos : (0 : ℝ) < t := lt_of_lt_of_le hi_pos ht.1
    have ht_ne : t ≠ 0 := ne_of_gt ht_pos
    exact (hasDerivAt_ofReal_cpow_const ht_ne hns_ne).hasDerivWithinAt
  have h_bound : ∀ t ∈ Set.Ico (i : ℝ) ((i : ℝ) + 1),
      ‖-s * (t : ℂ)^(-s - 1)‖ ≤ ‖s‖ / (i : ℝ)^(s.re + 1) := by
    intro t ht
    exact norm_neg_s_mul_cpow_neg_sub_one_le hs hi ht.1
  have h_mvt := norm_image_sub_le_of_norm_deriv_le_segment' h_deriv h_bound
    ((i : ℝ) + 1) (Set.right_mem_Icc.mpr (by linarith))
  have h_len : ((i : ℝ) + 1) - (i : ℝ) = 1 := by ring
  rw [h_len, mul_one] at h_mvt
  have hf_i1 : f ((i : ℝ) + 1) = (((i + 1 : ℕ) : ℝ) : ℂ)^(-s) := by
    simp only [hf_def]; congr 2; push_cast; ring
  have hf_i : f ((i : ℝ)) = (((i : ℕ) : ℝ) : ℂ)^(-s) := by
    simp only [hf_def]
  rw [hf_i1, hf_i] at h_mvt
  exact h_mvt

/-! ## §2 Shift-indexed factorization `f · g` for Abel summation. -/

/-- Shifted decreasing factor: `etaShiftF s k = ((k + 1 : ℝ) : ℂ)^(-s)`. -/
noncomputable def etaShiftF (s : ℂ) (k : ℕ) : ℂ := (((k + 1 : ℕ) : ℝ) : ℂ)^(-s)

/-- Shifted oscillator: `etaShiftG k = (-1 : ℂ)^k`. -/
def etaShiftG (k : ℕ) : ℂ := (-1 : ℂ)^k

/-- Bridge to LSeries.term via index shift `n = k + 1`. -/
lemma etaShiftF_mul_etaShiftG_eq_lseries_term_succ (s : ℂ) (k : ℕ) :
    etaShiftF s k * etaShiftG k = LSeries.term dirichletEtaCoeff s (k + 1) := by
  unfold etaShiftF etaShiftG
  have hk : (k + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero k
  rw [LSeries.term_of_ne_zero hk]
  unfold dirichletEtaCoeff
  rw [if_neg hk]
  -- Goal: ((k+1 : ℝ) : ℂ)^(-s) * (-1)^k = (-1)^((k+1)+1) / ((k+1 : ℕ) : ℂ)^s
  have hk_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hcast : ((k + 1 : ℕ) : ℂ) = (((k + 1 : ℕ) : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.cpow_neg]
  -- RHS: (-1)^((k+1)+1) / ((k+1 : ℝ) : ℂ)^s^(-1)⁻¹  ... just use field_simp/ring.
  have hpow : ((-1 : ℂ))^((k + 1) + 1) = (-1 : ℂ)^k := by
    have : ((-1 : ℂ))^((k + 1) + 1) = ((-1 : ℂ))^k * ((-1 : ℂ))^2 := by ring
    rw [this]; norm_num
  rw [hpow]
  have hbase_ne : (((k + 1 : ℕ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero k)
  have hbase_cpow_ne : (((k + 1 : ℕ) : ℝ) : ℂ)^s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hbase_ne)
  field_simp

/-- Partial sums of `etaShiftG` are bounded by 1. -/
lemma norm_sum_etaShiftG_le (n : ℕ) :
    ‖∑ i ∈ Finset.range n, etaShiftG i‖ ≤ 1 := by
  have h := neg_one_geom_sum (R := ℂ) (n := n)
  simp only [etaShiftG]
  rw [h]
  split_ifs
  · simp
  · simp

/-! ## §3 Summability of the difference tail. -/

/-- The comparison series `‖s‖ / (i+1)^{Re s + 1}` is summable for `Re s > 0`. -/
lemma summable_norm_s_div_rpow {s : ℂ} (hs : 0 < s.re) :
    Summable (fun i : ℕ => ‖s‖ / ((i + 1 : ℕ) : ℝ)^(s.re + 1)) := by
  have h_ps : Summable (fun i : ℕ => (1 : ℝ) / ((i + 1 : ℕ) : ℝ)^(s.re + 1)) := by
    have h1 : (1 : ℝ) < s.re + 1 := by linarith
    have := Real.summable_one_div_nat_rpow.mpr h1
    exact (summable_nat_add_iff 1).mpr this
  have h_mul : Summable (fun i : ℕ => ‖s‖ * (1 / ((i + 1 : ℕ) : ℝ)^(s.re + 1))) :=
    h_ps.mul_left ‖s‖
  convert h_mul using 1
  funext i
  rw [mul_one_div]

/-! ## §4 Absolute summability of `(etaShiftF (i+1) - etaShiftF i) * G (i+1)`. -/

/-- Summability of the differences of `etaShiftF` weighted by bounded `G`. -/
lemma summable_diff_etaShiftF_mul_partialG {s : ℂ} (hs : 0 < s.re) :
    Summable (fun i : ℕ =>
      ‖(etaShiftF s (i + 1) - etaShiftF s i) *
        (∑ j ∈ Finset.range (i + 1), etaShiftG j)‖) := by
  have h_bound_pointwise : ∀ i : ℕ,
      ‖(etaShiftF s (i + 1) - etaShiftF s i) *
        (∑ j ∈ Finset.range (i + 1), etaShiftG j)‖
        ≤ ‖s‖ / ((i + 1 : ℕ) : ℝ)^(s.re + 1) := by
    intro i
    have h_le_G : ‖∑ j ∈ Finset.range (i + 1), etaShiftG j‖ ≤ 1 :=
      norm_sum_etaShiftG_le (i + 1)
    have hi1_ge_1 : 1 ≤ i + 1 := Nat.succ_le_succ (Nat.zero_le i)
    have h_diff_le : ‖etaShiftF s (i + 1) - etaShiftF s i‖ ≤ ‖s‖ / ((i + 1 : ℕ) : ℝ)^(s.re + 1) := by
      unfold etaShiftF
      exact cpow_neg_diff_norm_le hs (i := i + 1) hi1_ge_1
    calc ‖(etaShiftF s (i + 1) - etaShiftF s i) *
            (∑ j ∈ Finset.range (i + 1), etaShiftG j)‖
        = ‖etaShiftF s (i + 1) - etaShiftF s i‖ *
            ‖∑ j ∈ Finset.range (i + 1), etaShiftG j‖ := by rw [norm_mul]
      _ ≤ (‖s‖ / ((i + 1 : ℕ) : ℝ)^(s.re + 1)) * 1 := by
          apply mul_le_mul h_diff_le h_le_G (norm_nonneg _)
          apply div_nonneg (norm_nonneg _)
          exact Real.rpow_nonneg (by positivity) _
      _ = ‖s‖ / ((i + 1 : ℕ) : ℝ)^(s.re + 1) := by ring
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) h_bound_pointwise
    (summable_norm_s_div_rpow hs)

/-! ## §5 The boundary term `etaShiftF s (n-1) · G n` tends to zero. -/

/-- The boundary product `etaShiftF s N · G (N+1)` tends to zero as `N → ∞`. -/
lemma tendsto_etaShiftF_mul_partialG_zero {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N : ℕ => etaShiftF s N *
      (∑ j ∈ Finset.range (N + 1), etaShiftG j)) atTop (𝓝 0) := by
  have h_bound : ∀ N : ℕ,
      ‖etaShiftF s N * (∑ j ∈ Finset.range (N + 1), etaShiftG j)‖
        ≤ ((N + 1 : ℕ) : ℝ)^(-s.re) := by
    intro N
    rw [norm_mul]
    have h_G : ‖∑ j ∈ Finset.range (N + 1), etaShiftG j‖ ≤ 1 :=
      norm_sum_etaShiftG_le _
    have h_F : ‖etaShiftF s N‖ = ((N + 1 : ℕ) : ℝ)^(-s.re) := by
      unfold etaShiftF
      have hN_pos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hN_pos]
      simp [Complex.neg_re]
    rw [h_F]
    have hF_nonneg : (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ)^(-s.re) :=
      Real.rpow_nonneg (by positivity) _
    calc ((N + 1 : ℕ) : ℝ)^(-s.re) * ‖∑ j ∈ Finset.range (N + 1), etaShiftG j‖
        ≤ ((N + 1 : ℕ) : ℝ)^(-s.re) * 1 := by
          apply mul_le_mul_of_nonneg_left h_G hF_nonneg
      _ = ((N + 1 : ℕ) : ℝ)^(-s.re) := by ring
  have h_tendsto : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)^(-s.re)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)) atTop atTop := by
      refine Filter.tendsto_atTop_atTop.mpr fun c => ?_
      refine ⟨Nat.ceil c, fun n hn => ?_⟩
      have h_ceil : (c : ℝ) ≤ (Nat.ceil c : ℝ) := Nat.le_ceil c
      have h_n : (Nat.ceil c : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have h_np1 : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
      linarith
    exact (tendsto_rpow_neg_atTop hs).comp h1
  exact squeeze_zero_norm h_bound h_tendsto

/-! ## §6 Abel summation gives CauchySeq of the shift-indexed sum. -/

/-- Abel summation gives CauchySeq of `∑ i ∈ range n, etaShiftF s i * etaShiftG i`. -/
lemma cauchySeq_shifted_sum {s : ℂ} (hs : 0 < s.re) :
    CauchySeq (fun n : ℕ => ∑ i ∈ Finset.range n, etaShiftF s i * etaShiftG i) := by
  -- Shift by 1 to avoid `n - 1` edge cases in sum_range_by_parts.
  rw [← cauchySeq_shift 1]
  -- Goal: CauchySeq (fun N => ∑ i ∈ range (N + 1), etaShiftF s i * etaShiftG i).
  -- Apply Finset.sum_range_by_parts pointwise.
  have h_rewrite : ∀ N : ℕ,
      (∑ i ∈ Finset.range (N + 1), etaShiftF s i * etaShiftG i)
        = etaShiftF s N * (∑ i ∈ Finset.range (N + 1), etaShiftG i)
          - ∑ i ∈ Finset.range N,
              (etaShiftF s (i + 1) - etaShiftF s i) *
                (∑ j ∈ Finset.range (i + 1), etaShiftG j) := by
    intro N
    have h := Finset.sum_range_by_parts (etaShiftF s) etaShiftG (N + 1)
    -- h uses (N + 1 - 1) and range (N + 1 - 1); simplify.
    simp only [Nat.add_sub_cancel] at h
    exact h
  have h_eq : (fun N : ℕ => ∑ i ∈ Finset.range (N + 1), etaShiftF s i * etaShiftG i)
      = fun N : ℕ =>
        etaShiftF s N * (∑ i ∈ Finset.range (N + 1), etaShiftG i)
          - ∑ i ∈ Finset.range N,
              (etaShiftF s (i + 1) - etaShiftF s i) *
                (∑ j ∈ Finset.range (i + 1), etaShiftG j) := funext h_rewrite
  rw [h_eq]
  -- Split A - B = A + (-B), use CauchySeq.add + CauchySeq.neg.
  have hA_cauchy : CauchySeq (fun N : ℕ =>
      etaShiftF s N * (∑ i ∈ Finset.range (N + 1), etaShiftG i)) :=
    (tendsto_etaShiftF_mul_partialG_zero hs).cauchySeq
  have hB_summable : Summable (fun i : ℕ =>
      (etaShiftF s (i + 1) - etaShiftF s i) *
        (∑ j ∈ Finset.range (i + 1), etaShiftG j)) :=
    (summable_diff_etaShiftF_mul_partialG hs).of_norm
  have hB_cauchy : CauchySeq (fun N : ℕ =>
      ∑ i ∈ Finset.range N,
        (etaShiftF s (i + 1) - etaShiftF s i) *
          (∑ j ∈ Finset.range (i + 1), etaShiftG j)) :=
    hB_summable.hasSum.tendsto_sum_nat.cauchySeq
  -- (A - B) = A + (-B).
  have h_sub_eq_add : (fun N : ℕ =>
      etaShiftF s N * (∑ i ∈ Finset.range (N + 1), etaShiftG i)
        - ∑ i ∈ Finset.range N,
            (etaShiftF s (i + 1) - etaShiftF s i) *
              (∑ j ∈ Finset.range (i + 1), etaShiftG j))
    = fun N : ℕ =>
      etaShiftF s N * (∑ i ∈ Finset.range (N + 1), etaShiftG i)
        + -(∑ i ∈ Finset.range N,
            (etaShiftF s (i + 1) - etaShiftF s i) *
              (∑ j ∈ Finset.range (i + 1), etaShiftG j)) := by
    funext N; rw [sub_eq_add_neg]
  rw [h_sub_eq_add]
  exact hA_cauchy.add hB_cauchy.neg

/-! ## §7 Bridge from shifted sum to LSeries partial sums. -/

/-- The complex LSeries partial sum over `range (N + 1)` equals the shifted sum. -/
lemma lseries_partialSum_succ_eq_shifted (s : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), LSeries.term dirichletEtaCoeff s n
      = ∑ i ∈ Finset.range N, etaShiftF s i * etaShiftG i := by
  induction N with
  | zero => simp [LSeries.term]
  | succ N ih =>
    rw [Finset.sum_range_succ (n := N + 1),
        Finset.sum_range_succ (f := fun i => etaShiftF s i * etaShiftG i) (n := N),
        ih, etaShiftF_mul_etaShiftG_eq_lseries_term_succ]

/-! ## §8 Full complex CauchySeq (main theorem). -/

/-- **`dirichletEta_lseries_partial_cauchy`** — UNCONDITIONAL.
`CauchySeq` of the complex LSeries partial sums for `dirichletEta`
at EVERY complex `s` with `0 < Re s`. -/
theorem dirichletEta_lseries_partial_cauchy {s : ℂ} (hs : 0 < s.re) :
    CauchySeq
      (fun N : ℕ => ∑ n ∈ Finset.range N, LSeries.term dirichletEtaCoeff s n) := by
  have h_shifted_cauchy : CauchySeq
      (fun N : ℕ => ∑ i ∈ Finset.range N, etaShiftF s i * etaShiftG i) :=
    cauchySeq_shifted_sum hs
  -- Bridge: LSeries partial over range (N+1) = shifted sum over range N.
  have h_bridge : CauchySeq
      (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), LSeries.term dirichletEtaCoeff s n) := by
    have h_eq : (fun N : ℕ => ∑ i ∈ Finset.range N, etaShiftF s i * etaShiftG i)
              = (fun N : ℕ => ∑ n ∈ Finset.range (N + 1),
                    LSeries.term dirichletEtaCoeff s n) := by
      funext N; exact (lseries_partialSum_succ_eq_shifted s N).symm
    rw [← h_eq]; exact h_shifted_cauchy
  exact (cauchySeq_shift 1).mp h_bridge

/-! ## §9 Existence of the limit. -/

/-- Existence of `L : ℂ` such that the LSeries partial sums tend to `L`. -/
theorem dirichletEta_lseries_partial_hasLimit {s : ℂ} (hs : 0 < s.re) :
    ∃ L : ℂ, Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, LSeries.term dirichletEtaCoeff s n)
      atTop (𝓝 L) :=
  cauchySeq_tendsto_of_complete (dirichletEta_lseries_partial_cauchy hs)

/-! ## §10 Residual discharge: `DirichletEta_ConditionalConvergence_ComplexOffReal`. -/

/-- **`dirichletEta_conditionalConvergence_complexOffReal_discharged`** —
UNCONDITIONAL. The r276 refined residual
`DirichletEta_ConditionalConvergence_ComplexOffReal` is INHABITED. -/
theorem dirichletEta_conditionalConvergence_complexOffReal_discharged :
    DirichletEta_ConditionalConvergence_ComplexOffReal := by
  intro s _him hs
  exact dirichletEta_lseries_partial_cauchy hs

/-! ## §11 Axiom check. -/

#print axioms
  PrincipiaTractalis.DirichletEtaConditionalConvergenceComplex.cpow_neg_diff_norm_le
#print axioms
  PrincipiaTractalis.DirichletEtaConditionalConvergenceComplex.dirichletEta_lseries_partial_cauchy
#print axioms
  PrincipiaTractalis.DirichletEtaConditionalConvergenceComplex.dirichletEta_lseries_partial_hasLimit
#print axioms
  PrincipiaTractalis.DirichletEtaConditionalConvergenceComplex.dirichletEta_conditionalConvergence_complexOffReal_discharged

end PrincipiaTractalis.DirichletEtaConditionalConvergenceComplex
