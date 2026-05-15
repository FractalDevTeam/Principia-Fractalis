/-
# Positive Definite Functionals and Cylindrical Measures
Formal definitions for the Bochner-Minlos theorem.

A functional C : S → ℂ is positive definite if for any finite set s₁,...,sₙ ∈ S
and any complex numbers z₁,...,zₙ:
  ∑ᵢⱼ zᵢ · conj(zⱼ) · C(sᵢ - sⱼ) ≥ 0

A cylindrical measure on the dual S' assigns consistent probability measures
to finite-dimensional projections.

Reference: Gel'fand-Vilenkin, Generalized Functions Vol. 4
          Principia Fractalis, Chapter 23
-/

import PF.NuclearSpaces
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Exponential

namespace PrincipiaTractalis

/-! ## Positive Definite Functionals -/

/-- A functional C : E → ℂ on a vector space is positive definite if for any
    finite collection of vectors s₁,...,sₙ and complex numbers z₁,...,zₙ,
    the Hermitian form ∑ᵢⱼ zᵢ · conj(zⱼ) · C(sᵢ - sⱼ) is a NON-NEGATIVE REAL.

    This is the standard definition (sum is real-and-nonneg, not just .re ≥ 0) —
    strengthened from the prior .re-only formulation on 2026-04-22 so that
    `pos_def_hermitian` and related properties become provable.
-/
def IsPositiveDefinite {E : Type*} [AddCommGroup E] (C : E → ℂ) : Prop :=
  ∀ (n : ℕ) (s : Fin n → E) (z : Fin n → ℂ),
    (∑ i : Fin n, ∑ j : Fin n, z i * (starRingEnd ℂ) (z j) * C (s i - s j)).im = 0 ∧
    0 ≤ (∑ i : Fin n, ∑ j : Fin n, z i * (starRingEnd ℂ) (z j) * C (s i - s j)).re

/-- Normalization condition: C(0) = 1. -/
def IsNormalized {E : Type*} [AddCommGroup E] (C : E → ℂ) : Prop :=
  C 0 = 1

/-- Continuity at 0 of a functional `C : S(ℝᵈ) → ℂ`.

    Refactored 2026-05-12: replaced the broken placeholder body
    `∀ ε > 0, ∃ k l δ, δ > 0 ∧ ∀ f : SchwartzFunction d, True → ‖C f - C 0‖ < ε`
    (which simplified to `∀ f, ‖C f - C 0‖ < ε` — overconstrained, would force
    `C` to be uniformly within ε of `C 0` everywhere, true only for `C` very
    close to constant) with mathlib's `ContinuousAt C 0`, using the genuine
    Fréchet topology on `SchwartzMap (Fin d → ℝ) ℂ`. -/
def IsContinuousAtZero {d : ℕ} (C : SchwartzFunction d → ℂ) : Prop :=
  ContinuousAt C 0

/-- A characteristic functional satisfies all Bochner-Minlos conditions. -/
@[ext]
structure CharacteristicFunctional (d : ℕ) where
  /-- The functional C : S(R^d) → ℂ -/
  toFun : SchwartzFunction d → ℂ
  /-- C(0) = 1 -/
  normalized : toFun 0 = 1
  /-- Positive definiteness -/
  positive_definite : IsPositiveDefinite toFun
  /-- Continuity at 0 -/
  continuous_at_zero : IsContinuousAtZero toFun

/-! ## Basic Properties of Positive Definite Functionals -/

/-- If C is positive definite, then C(0) ≥ 0. -/
theorem pos_def_zero_nonneg {E : Type*} [AddCommGroup E] (C : E → ℂ)
    (hpd : IsPositiveDefinite C) : 0 ≤ (C 0).re := by
  -- Use n = 1, s₀ = 0, z₀ = 1.
  -- Then ∑ᵢⱼ zᵢ · conj(zⱼ) · C(sᵢ - sⱼ) = 1 · 1 · C(0 - 0) = C(0).
  have h := (hpd 1 (fun _ => 0) (fun _ => 1)).2
  simp at h
  convert h using 1

/-- If C is positive definite, then `(C 0).im = 0` — i.e. `C 0` is real.

    Added 2026-05-13 as a standalone lemma (previously inline in
    `pos_def_hermitian` and `pos_def_normalized_bounded`). The proof
    uses `IsPositiveDefinite C` at `n = 1` with the singleton point
    `s₀ = 0` and weight `z₀ = 1`: the sum reduces to `C 0`, whose
    real-and-nonneg conclusion of `IsPositiveDefinite` includes
    `Im(C 0) = 0`. -/
theorem pos_def_zero_imaginary {E : Type*} [AddCommGroup E] (C : E → ℂ)
    (hpd : IsPositiveDefinite C) : (C 0).im = 0 := by
  have h := (hpd 1 (fun _ => 0) (fun _ => 1)).1
  simp at h
  exact h

/-- Hermitian property: If C is positive definite, then C(-s) = conj(C(s)).
    Axiom → theorem (2026-04-22): from the strengthened `IsPositiveDefinite`
    (sum is real-and-nonneg), specific z-value evaluations at n=2 force
    C(-s) = conj(C(s)). See proof for the imaginary-vanishing identities. -/
theorem pos_def_hermitian {E : Type*} [AddCommGroup E] (C : E → ℂ)
    (hpd : IsPositiveDefinite C) : ∀ s : E, C (-s) = (starRingEnd ℂ) (C s) := by
  intro s
  -- Step 1: from hpd at n=1 with z = 1, the sum equals C 0, so Im(C 0) = 0.
  have hIm0 : (C 0).im = 0 := pos_def_zero_imaginary C hpd
  -- Step 2: at n=2 with s = ![0, s], z = ![1, 1], sum = 2·C 0 + C(-s) + C s.
  have hIm_sum : (C (-s)).im + (C s).im = 0 := by
    have h := (hpd 2 ![0, s] ![1, 1]).1
    simp [Fin.sum_univ_two, sub_zero, zero_sub] at h
    linarith [hIm0, h]
  -- Step 3: at n=2 with z = ![1, Complex.I], imaginary vanishing ⟹ Re(C s) = Re(C(-s)).
  have hRe_eq : (C (-s)).re = (C s).re := by
    have h := (hpd 2 ![0, s] ![1, Complex.I]).1
    simp [Fin.sum_univ_two, sub_zero, zero_sub] at h
    have : 2 * (C 0).im - (C (-s)).re + (C s).re = 0 := by
      linarith [h]
    linarith [hIm0]
  -- Step 4: combine — C(-s) and conj(C s) have matching re and im.
  apply Complex.ext
  · rw [Complex.conj_re]; exact hRe_eq
  · rw [Complex.conj_im]; linarith

/-- If C is positive definite and normalized, then |C(s)| ≤ 1 for all s.
    Axiom → theorem (2026-04-22): apply `hpd` at n=2, s = (0, s), z = (1, -conj(C s)).
    After expanding via `pos_def_hermitian` for C(-s), the sum becomes
    1 - ‖C s‖², which must have nonneg real part — hence ‖C s‖² ≤ 1. -/
theorem pos_def_normalized_bounded {E : Type*} [AddCommGroup E] (C : E → ℂ)
    (hpd : IsPositiveDefinite C) (hn : IsNormalized C) :
    ∀ s : E, ‖C s‖ ≤ 1 := by
  intro s
  have herm := pos_def_hermitian C hpd s       -- C(-s) = conj(C s)
  have hn_re : (C 0).re = 1 := by rw [hn]; simp
  have hn_im : (C 0).im = 0 := by rw [hn]; simp
  have h := (hpd 2 ![0, s] ![1, -(starRingEnd ℂ) (C s)]).2
  simp [Fin.sum_univ_two, sub_zero, zero_sub, herm] at h
  -- After simp, h is a long arithmetic statement. Provide Re(C 0) = 1 and Im(C 0) = 0
  -- and let nlinarith find the contradiction |C s|² ≤ 1.
  have hsq : (C s).re * (C s).re + (C s).im * (C s).im ≤ 1 := by
    nlinarith [h, hn_re, hn_im]
  -- Convert re²+im² into normSq then to ‖·‖².
  have hnormSq : Complex.normSq (C s) ≤ 1 := by
    rw [Complex.normSq_apply]; linarith [hsq]
  have hNorm_sq : ‖C s‖ ^ 2 ≤ 1 := by rw [Complex.sq_norm]; exact hnormSq
  nlinarith [norm_nonneg (C s), hNorm_sq]

/-- The real part of a normalized positive-definite functional is bounded by 1.
    Direct corollary of `pos_def_normalized_bounded`: `Re(C s) ≤ |C s| ≤ 1`.

    Added 2026-05-13. Useful framing for Bochner-type modulus inequalities,
    where the difference `1 - Re C(x) ≥ 0` plays the role of a "translation
    energy" at displacement `x`. -/
theorem pos_def_normalized_re_le_one {E : Type*} [AddCommGroup E] (C : E → ℂ)
    (hpd : IsPositiveDefinite C) (hn : IsNormalized C) :
    ∀ s : E, (C s).re ≤ 1 := by
  intro s
  have h_bound : ‖C s‖ ≤ 1 := pos_def_normalized_bounded C hpd hn s
  have h_abs : |(C s).re| ≤ ‖C s‖ := Complex.abs_re_le_norm (C s)
  have h_re_le_abs : (C s).re ≤ |(C s).re| := le_abs_self _
  linarith

/-- One minus the real part of a normalized positive-definite functional
    is non-negative — equivalently, `Re(C x) ≤ Re(C 0) = 1`.

    Added 2026-05-13. The quantity `1 - Re C(x)` measures how far `C(x)`
    is from `C(0) = 1` in the real direction; it appears as the
    "translation-distance" bound in the classical Bochner modulus
    inequality `|C(s) - C(t)|² ≤ 2 · (1 - Re C(s - t))`. -/
theorem pos_def_normalized_one_sub_re_nonneg {E : Type*} [AddCommGroup E] (C : E → ℂ)
    (hpd : IsPositiveDefinite C) (hn : IsNormalized C) :
    ∀ s : E, 0 ≤ 1 - (C s).re := by
  intro s
  have := pos_def_normalized_re_le_one C hpd hn s
  linarith

/-- CLASSICAL BOCHNER MODULUS INEQUALITY (Bochner-Herglotz).

    For a normalized positive-definite functional `C : E → ℂ` on an additive
    group `E` and any two points `s, t : E`:
    `‖C s - C t‖² ≤ 2 · (1 - (C (s - t)).re)`.

    PROOF STRATEGY. Apply `IsPositiveDefinite C` at `n = 3` with points
    `(0, s, t)` and weights `(1, -α·conj(C s - C t), α·conj(C s - C t))`
    for arbitrary real `α`. The complex sum expands via `Fin.sum_univ_three`
    + `pos_def_hermitian` (`C(-x) = conj(C x)`) + `IsNormalized` (`C 0 = 1`)
    into a real polynomial of the form `1 + 2 α² D R - 2 α D` where
    `D = ‖C s - C t‖²` and `R = 1 - Re C(s-t)`. The polynomial is
    non-negative on all of `ℝ` (from PD's `.re ≥ 0` clause), so applying
    the discriminant criterion (`discrim_le_zero` in mathlib) yields
    `(2D)² ≤ 4 · (2DR) · 1`, i.e., `D² ≤ 2DR`, i.e., `D ≤ 2R`.

    Reference: Reed-Simon I §IX.2; Folland Real Analysis Chapter 4.
    Added 2026-05-14. -/
theorem pos_def_modulus_inequality {E : Type*} [AddCommGroup E] (C : E → ℂ)
    (hpd : IsPositiveDefinite C) (hn : IsNormalized C) :
    ∀ s t : E, ‖C s - C t‖^2 ≤ 2 * (1 - (C (s - t)).re) := by
  intro s t
  -- Coordinatize. Let (x, y) = C s, (u, v) = C t, (p, q) = C(s-t).
  set x : ℝ := (C s).re
  set y : ℝ := (C s).im
  set u : ℝ := (C t).re
  set v : ℝ := (C t).im
  set p : ℝ := (C (s - t)).re
  set q : ℝ := (C (s - t)).im
  -- D = ‖C s - C t‖² = (x - u)² + (y - v)²
  set D : ℝ := (x - u)^2 + (y - v)^2 with hD_def
  set R : ℝ := 1 - p with hR_def
  have hD_eq : ‖C s - C t‖^2 = D := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    show (C s - C t).re * (C s - C t).re + (C s - C t).im * (C s - C t).im = D
    simp only [Complex.sub_re, Complex.sub_im]
    show (x - u) * (x - u) + (y - v) * (y - v) = D
    rw [hD_def]; ring
  rw [hD_eq]
  -- After `set R := 1 - p` above, the goal `D ≤ 2 * (1 - (C (s-t)).re)`
  -- already folds to `D ≤ 2 * R`.
  show D ≤ 2 * R
  have hD_nonneg : 0 ≤ D := by rw [hD_def]; positivity
  -- R ≥ 0 from previous lemma
  have hR_nonneg : 0 ≤ R := by
    have := pos_def_normalized_one_sub_re_nonneg C hpd hn (s - t)
    exact this
  -- Normalization facts: C 0 = 1, so (C 0).re = 1 and (C 0).im = 0
  have hC0 : C 0 = 1 := hn
  have hC0_re : (C 0).re = 1 := by rw [hC0]; rfl
  have hC0_im : (C 0).im = 0 := by rw [hC0]; rfl
  -- Hermitian: C(-s) = conj(C s), C(-t) = conj(C t), C(t - s) = conj(C(s - t))
  have herm_s : C (-s) = (starRingEnd ℂ) (C s) := pos_def_hermitian C hpd s
  have herm_t : C (-t) = (starRingEnd ℂ) (C t) := pos_def_hermitian C hpd t
  have herm_st : C (t - s) = (starRingEnd ℂ) (C (s - t)) := by
    have h := pos_def_hermitian C hpd (s - t)
    have h' : -(s - t) = t - s := by abel
    rw [h'] at h
    exact h
  -- KEY: The polynomial bound. For every real α,
  --   0 ≤ 1 + 2 α² D R - 2 α D.
  -- Proved by instantiating hpd at n=3 with z = ![1, -α·conj(C s - C t), α·conj(C s - C t)].
  -- After expansion using normalization and hermitian, the .re of the sum reduces
  -- exactly to this polynomial.
  have key : ∀ α : ℝ, 0 ≤ 1 + 2 * α^2 * D * R - 2 * α * D := by
    intro α
    -- Define the complex weight `a = α · conj(C s - C t)`.
    -- Components: a.re = α(x - u), a.im = -α(y - v)
    set a : ℂ := (α : ℂ) * (starRingEnd ℂ) (C s - C t) with ha_def
    have ha_re : a.re = α * (x - u) := by
      rw [ha_def]
      simp only [Complex.mul_re, Complex.sub_re, Complex.conj_re, Complex.conj_im,
                 Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      show α * ((C s).re - (C t).re) = α * (x - u)
      rfl
    have ha_im : a.im = -(α * (y - v)) := by
      rw [ha_def]
      simp only [Complex.mul_im, Complex.sub_im, Complex.conj_re, Complex.conj_im,
                 Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      show α * -((C s).im - (C t).im) = -(α * (y - v))
      show α * -(y - v) = -(α * (y - v))
      ring
    -- |a|² = α² · D in real terms
    have hSq_a : a.re^2 + a.im^2 = α^2 * D := by
      rw [ha_re, ha_im, hD_def]; ring
    -- Apply PD at n=3
    have hpd_inst := (hpd 3 ![0, s, t] ![1, -a, a]).2
    have hpd_im := (hpd 3 ![0, s, t] ![1, -a, a]).1
    -- Expand the sum via Fin.sum_univ_three; unfold all Fin-3 matrix indices.
    simp only [Fin.sum_univ_three, show (![0, s, t] : Fin 3 → E) 0 = 0 from rfl,
               show (![0, s, t] : Fin 3 → E) 1 = s from rfl,
               show (![0, s, t] : Fin 3 → E) 2 = t from rfl,
               show (![(1 : ℂ), -a, a] : Fin 3 → ℂ) 0 = 1 from rfl,
               show (![(1 : ℂ), -a, a] : Fin 3 → ℂ) 1 = -a from rfl,
               show (![(1 : ℂ), -a, a] : Fin 3 → ℂ) 2 = a from rfl,
               sub_zero, zero_sub, sub_self] at hpd_inst hpd_im
    -- Use hermitian to simplify C(-s), C(-t), C(t-s)
    rw [herm_s, herm_t, herm_st, hC0] at hpd_inst
    -- Now hpd_inst is `0 ≤ Re of a long complex sum`. Reduce algebraically.
    -- After full expansion, the .re of the sum equals
    --     1 + 2(a.re² + a.im²)(1 - p) + 2·(a.re(u - x) + a.im(v - y))
    --   = 1 + 2 α² D R - 2 α D
    -- We prove this by direct computation.
    have hreduce :
        (1 * (starRingEnd ℂ) 1 * 1 + 1 * (starRingEnd ℂ) (-a) * (starRingEnd ℂ) (C s)
         + 1 * (starRingEnd ℂ) a * (starRingEnd ℂ) (C t)
         + (-a * (starRingEnd ℂ) 1 * C s + -a * (starRingEnd ℂ) (-a) * 1
            + -a * (starRingEnd ℂ) a * C (s - t))
         + (a * (starRingEnd ℂ) 1 * C t + a * (starRingEnd ℂ) (-a) * (starRingEnd ℂ) (C (s - t))
            + a * (starRingEnd ℂ) a * 1)).re
        = 1 + 2 * α^2 * D * R - 2 * α * D := by
      -- Reduce conj-of-product, mul_one, etc.
      simp only [map_one, map_neg, neg_mul, mul_neg, neg_neg, mul_one, one_mul,
                 Complex.add_re, Complex.neg_re, Complex.mul_re,
                 Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re]
      -- After simp, the goal should be a pure real-arithmetic identity in
      -- terms of a.re, a.im, x, y, u, v, p, q.
      -- Substitute the known expressions for a.re, a.im and use ring.
      rw [ha_re, ha_im]
      show _ = 1 + 2 * α^2 * D * R - 2 * α * D
      rw [hD_def, hR_def]
      ring
    -- Apply hreduce to hpd_inst
    linarith [hpd_inst.trans_eq hreduce]
  -- Now apply discriminant criterion.
  -- We have: ∀ α, 0 ≤ (2 D R) · α² + (-2 D) · α + 1.
  -- Apply discrim_le_zero: (-2D)² - 4 · (2DR) · 1 ≤ 0, i.e., 4D² - 8DR ≤ 0,
  -- i.e., D² ≤ 2DR. Since D ≥ 0, either D = 0 (≤ 2R) or D ≤ 2R.
  have hquad : ∀ α : ℝ, 0 ≤ (2 * D * R) * (α * α) + (-2 * D) * α + 1 := by
    intro α
    have := key α
    nlinarith [sq_nonneg α]
  have hdiscrim : discrim (2 * D * R) (-2 * D) 1 ≤ 0 := discrim_le_zero hquad
  -- discrim a b c = b² - 4ac, so discrim (2DR) (-2D) 1 = 4D² - 8DR
  have hdiscrim_eq : discrim (2 * D * R) (-2 * D) 1 = 4 * D^2 - 8 * D * R := by
    unfold discrim; ring
  rw [hdiscrim_eq] at hdiscrim
  -- So 4D² ≤ 8DR, i.e., D² ≤ 2DR, i.e., D(D - 2R) ≤ 0.
  -- Since D ≥ 0, D - 2R ≤ 0 (or D = 0).
  nlinarith [hD_nonneg, hR_nonneg, sq_nonneg D, sq_nonneg (D - 2 * R)]

/-- COROLLARY OF BOCHNER MODULUS INEQUALITY: continuity at 0 propagates globally.

    For a normalized positive-definite functional `C : E → ℂ` on a topological
    additive group `E`, if `C` is continuous at 0, then `C` is continuous
    everywhere. This is the standard "regularity automatic" result for
    characteristic functions.

    PROOF. Apply `pos_def_modulus_inequality` to get the pointwise bound
    `‖C t - C s‖² ≤ 2 · (1 - Re C(t - s))`. As `t → s` (in the topological
    group), `t - s → 0`, so `C(t - s) → C 0 = 1` (by continuity at 0),
    so `Re C(t - s) → 1`, so `1 - Re C(t - s) → 0`, so the bound forces
    `‖C t - C s‖ → 0`, giving `ContinuousAt C s`.

    Added 2026-05-14 (Stage 19). -/
theorem pos_def_continuous_of_continuous_at_zero
    {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    (C : E → ℂ) (hpd : IsPositiveDefinite C) (hn : IsNormalized C)
    (hc : ContinuousAt C 0) : Continuous C := by
  refine continuous_iff_continuousAt.mpr fun s => ?_
  -- We use `Metric.tendsto_nhds` on the codomain ℂ.
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  -- Get neighborhood of 0 in E where ‖C u - 1‖ < (ε/2)² · 2 = ε²/2.
  -- (We pick ε²/2 so that the modulus-inequality bound gives ‖C t - C s‖ < ε strictly.)
  rw [ContinuousAt, Metric.tendsto_nhds] at hc
  rw [hn] at hc
  have hε2 : 0 < ε^2 / 2 := by positivity
  have hc' := hc (ε^2 / 2) hε2
  -- hc' : ∀ᶠ u in 𝓝 0, dist (C u) 1 < ε²/2
  -- Translate via the topological-group continuous map `t ↦ t - s` sending s ↦ 0.
  have h_translate : Filter.Tendsto (fun t : E => t - s) (nhds s) (nhds 0) := by
    have h_cont : Continuous (fun t : E => t - s) := continuous_id.sub continuous_const
    have := h_cont.tendsto s
    simpa using this
  have hc'' : ∀ᶠ t in nhds s, dist (C (t - s)) 1 < ε^2 / 2 := h_translate hc'
  -- For each such t, the modulus inequality gives ‖C t - C s‖² ≤ ε², hence < ε strict
  -- requires a strict pass; we use the half-margin
  -- `1 - Re C(t-s) ≤ ‖C(t-s) - 1‖ < ε²/2`, then `‖C t - C s‖² ≤ ε² but we need
  -- strict. Witnessed by tightening: bound directly with strict inequality.
  filter_upwards [hc''] with t ht
  -- ht : dist (C (t - s)) 1 < ε²/2
  have hd1 : ‖C (t - s) - 1‖ < ε^2 / 2 := by
    rw [Complex.dist_eq] at ht
    exact ht
  -- 1 - Re C(t-s) ≤ ‖C(t-s) - 1‖
  have h_re_bound : 1 - (C (t - s)).re ≤ ‖C (t - s) - 1‖ := by
    have : (1 - C (t - s)).re ≤ ‖1 - C (t - s)‖ := Complex.re_le_norm _
    rw [Complex.sub_re, Complex.one_re, norm_sub_rev] at this
    exact this
  -- ‖C t - C s‖² ≤ 2 · (1 - Re C(t - s)) < 2 · (ε²/2) = ε²
  have h_mod := pos_def_modulus_inequality C hpd hn t s
  have h_sq_strict : ‖C t - C s‖^2 < ε^2 := by
    calc ‖C t - C s‖^2 ≤ 2 * (1 - (C (t - s)).re) := h_mod
      _ ≤ 2 * ‖C (t - s) - 1‖ := by linarith [h_re_bound]
      _ < 2 * (ε^2 / 2) := by linarith
      _ = ε^2 := by ring
  -- ‖C t - C s‖ < ε
  have h_norm_nonneg : 0 ≤ ‖C t - C s‖ := norm_nonneg _
  have h_eps_nonneg : 0 ≤ ε := le_of_lt hε
  have h_norm_lt : ‖C t - C s‖ < ε := by
    by_contra h_not
    push_neg at h_not
    have : ε^2 ≤ ‖C t - C s‖^2 := by
      have := mul_self_le_mul_self h_eps_nonneg h_not
      nlinarith
    linarith
  rw [Complex.dist_eq]
  exact h_norm_lt

/-- Every `CharacteristicFunctional d` has a globally continuous underlying
    functional `toFun`. Combines the structure's `continuous_at_zero` field
    with `pos_def_continuous_of_continuous_at_zero` (Stage 19) and the
    `IsTopologicalAddGroup` instance on `SchwartzMap (Fin d → ℝ) ℂ`.

    Added 2026-05-14 (Stage 20). -/
theorem CharacteristicFunctional.continuous {d : ℕ} (C : CharacteristicFunctional d) :
    Continuous C.toFun :=
  pos_def_continuous_of_continuous_at_zero C.toFun
    C.positive_definite C.normalized C.continuous_at_zero

/-- THE CHARACTERISTIC FUNCTION OF A PROBABILITY MEASURE IS POSITIVE DEFINITE.

    Mathlib provides `MeasureTheory.charFun μ : E → ℂ` as the Fourier transform
    of a measure on a real inner-product space, but not the fact that this
    function is positive-definite (a classical Bochner-direction prerequisite).
    This theorem closes that gap, connecting mathlib's `charFun` to our
    `IsPositiveDefinite` predicate.

    PROOF. For any finite collection `s : Fin n → E`, `z : Fin n → ℂ`:
    $$ \sum_{i,j} z_i \overline{z_j} \, \widehat{\mu}(s_i - s_j)
       = \int_E \left| \sum_i z_i \, e^{i \langle x, s_i \rangle} \right|^2 d\mu(x) $$
    The right side is the integral of a non-negative real function, hence
    a real non-negative complex number.

    Key steps:
    1. Real-linearity of `⟪x, ·⟫` and `Complex.exp_sub` give
       `exp(⟪x, sᵢ-sⱼ⟫·i) = exp(⟪x, sᵢ⟫·i) · conj(exp(⟪x, sⱼ⟫·i))`.
    2. Hence the double-sum integrand equals `g(x) · conj(g(x))` where
       `g(x) := ∑ᵢ zᵢ · exp(⟪x, sᵢ⟫·i)`, by the elementary identity
       `(∑aᵢ)(∑conj(bⱼ)) = ∑ᵢⱼ aᵢ·conj(bⱼ)` (`Finset.sum_mul_sum`).
    3. `g(x) · conj(g(x)) = (Complex.normSq (g x) : ℂ)` (Complex.mul_conj).
    4. Each summand is integrable on the finite measure μ:
       `exp(⟪x,t⟫·i)` is continuous and bounded by 1, hence integrable
       (`Integrable.bdd_mul` with the constant-1 integrable witness).
    5. Swap finite sum and integral (`integral_finset_sum`).

    Added 2026-05-14 (Stage 21). -/
theorem charFun_positive_definite {E : Type*}
    [SeminormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [OpensMeasurableSpace E]
    (μ : MeasureTheory.Measure E) [MeasureTheory.IsProbabilityMeasure μ] :
    IsPositiveDefinite (MeasureTheory.charFun μ) := by
  intro n s z
  -- The "Fourier mode" function
  let g : E → ℂ := fun x => ∑ i, z i * Complex.exp (((@inner ℝ E _ x (s i) : ℝ) : ℂ) * Complex.I)
  -- Pointwise: factorization of the exp factor.
  have exp_factor : ∀ (i j : Fin n) (x : E),
      Complex.exp (((@inner ℝ E _ x (s i - s j) : ℝ) : ℂ) * Complex.I)
      = Complex.exp (((@inner ℝ E _ x (s i) : ℝ) : ℂ) * Complex.I)
        * (starRingEnd ℂ) (Complex.exp (((@inner ℝ E _ x (s j) : ℝ) : ℂ) * Complex.I)) := by
    intro i j x
    -- conj(exp(↑r·I)) = exp(-(↑r·I)) via exp_conj + ring on conj
    have hconj : (starRingEnd ℂ) (Complex.exp (((@inner ℝ E _ x (s j) : ℝ) : ℂ) * Complex.I))
               = Complex.exp (-(((@inner ℝ E _ x (s j) : ℝ) : ℂ) * Complex.I)) := by
      rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
    rw [hconj, inner_sub_right, Complex.ofReal_sub, sub_mul, Complex.exp_sub,
        div_eq_mul_inv]
    congr 1
    exact (Complex.exp_neg _).symm
  -- Pointwise: the double-sum integrand equals g x * conj(g x).
  have pointwise : ∀ x : E,
      (∑ i, ∑ j, z i * (starRingEnd ℂ) (z j) *
              Complex.exp (((@inner ℝ E _ x (s i - s j) : ℝ) : ℂ) * Complex.I))
      = g x * (starRingEnd ℂ) (g x) := by
    intro x
    -- Rewrite each summand via exp_factor and regroup
    have step1 : (∑ i, ∑ j, z i * (starRingEnd ℂ) (z j) *
              Complex.exp (((@inner ℝ E _ x (s i - s j) : ℝ) : ℂ) * Complex.I))
        = ∑ i, ∑ j, (z i * Complex.exp (((@inner ℝ E _ x (s i) : ℝ) : ℂ) * Complex.I))
              * (starRingEnd ℂ) (z j * Complex.exp (((@inner ℝ E _ x (s j) : ℝ) : ℂ) * Complex.I)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [exp_factor i j x, map_mul]
      ring
    rw [step1]
    -- (∑ᵢ aᵢ) · (∑ⱼ conj(bⱼ)) = ∑ᵢⱼ aᵢ · conj(bⱼ)
    rw [← Finset.sum_mul_sum]
    show _ = g x * _
    rw [map_sum]
  -- The integrand equals (Complex.normSq (g x) : ℂ).
  have integrand_normSq : ∀ x : E,
      g x * (starRingEnd ℂ) (g x) = (Complex.normSq (g x) : ℂ) := by
    intro x
    rw [Complex.mul_conj]
  -- Each `exp(⟪x, sᵢ-sⱼ⟫·i)` is integrable: bounded continuous on finite μ.
  have exp_integrable : ∀ (i j : Fin n), MeasureTheory.Integrable
      (fun x => Complex.exp (((@inner ℝ E _ x (s i - s j) : ℝ) : ℂ) * Complex.I)) μ := by
    intro i j
    -- `(fun x => exp(⟪x, sᵢ-sⱼ⟫·i)) = (fun x => exp(...) * 1)`; apply bdd_mul.
    have heq : (fun x => Complex.exp (((@inner ℝ E _ x (s i - s j) : ℝ) : ℂ) * Complex.I))
             = (fun x => Complex.exp (((@inner ℝ E _ x (s i - s j) : ℝ) : ℂ) * Complex.I) * 1) := by
      funext x; ring
    rw [heq]
    refine MeasureTheory.Integrable.bdd_mul (MeasureTheory.integrable_const (1 : ℂ)) ?_ ?_
    · -- AEStronglyMeasurable from continuity
      apply Continuous.aestronglyMeasurable
      have h1 : Continuous (fun x : E => @inner ℝ E _ x (s i - s j)) := by
        exact continuous_inner.comp (continuous_id.prodMk continuous_const)
      exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp h1).mul continuous_const)
    · -- Bounded by 1
      refine ⟨1, fun x => ?_⟩
      rw [Complex.norm_exp]
      simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]
  -- Each `zᵢ · conj(zⱼ) · exp(⟪x, sᵢ-sⱼ⟫·i)` is integrable: constant times integrable.
  have summand_integrable : ∀ (i j : Fin n), MeasureTheory.Integrable
      (fun x => z i * (starRingEnd ℂ) (z j) *
            Complex.exp (((@inner ℝ E _ x (s i - s j) : ℝ) : ℂ) * Complex.I)) μ := by
    intro i j
    exact (exp_integrable i j).const_mul _
  -- Swap finite sum and integral: ∑ᵢⱼ ∫ = ∫ ∑ᵢⱼ.
  have swap_sum_integral :
      (∑ i, ∑ j, z i * (starRingEnd ℂ) (z j) *
              MeasureTheory.charFun μ (s i - s j))
      = ∫ x, (∑ i, ∑ j, z i * (starRingEnd ℂ) (z j) *
              Complex.exp (((@inner ℝ E _ x (s i - s j) : ℝ) : ℂ) * Complex.I)) ∂μ := by
    simp_rw [MeasureTheory.charFun_apply, ← MeasureTheory.integral_const_mul]
    -- Goal: ∑ i, ∑ j, ∫ exp_term ∂μ = ∫ ∑ i, ∑ j, exp_term ∂μ
    -- Swap inner sum and integral first
    have inner_swap : ∀ i,
        (∑ j, ∫ x, z i * (starRingEnd ℂ) (z j) *
                Complex.exp (((@inner ℝ E _ x (s i - s j) : ℝ) : ℂ) * Complex.I) ∂μ)
        = ∫ x, ∑ j, z i * (starRingEnd ℂ) (z j) *
                Complex.exp (((@inner ℝ E _ x (s i - s j) : ℝ) : ℂ) * Complex.I) ∂μ := by
      intro i
      rw [← MeasureTheory.integral_finset_sum (Finset.univ : Finset (Fin n))]
      intro j _
      exact summand_integrable i j
    simp_rw [inner_swap]
    rw [← MeasureTheory.integral_finset_sum (Finset.univ : Finset (Fin n))]
    intro i _
    exact MeasureTheory.integrable_finset_sum _ (fun j _ => summand_integrable i j)
  -- Combine: sum = ∫ (Complex.normSq (g x) : ℂ) ∂μ = ((∫ Complex.normSq (g x) ∂μ : ℝ) : ℂ)
  have sum_eq : (∑ i, ∑ j, z i * (starRingEnd ℂ) (z j) *
              MeasureTheory.charFun μ (s i - s j))
              = ((∫ x, Complex.normSq (g x) ∂μ : ℝ) : ℂ) := by
    rw [swap_sum_integral]
    simp_rw [pointwise, integrand_normSq]
    rw [integral_complex_ofReal]
  -- Conclude: .im = 0 and .re ≥ 0.
  refine ⟨?_, ?_⟩
  · rw [sum_eq, Complex.ofReal_im]
  · rw [sum_eq, Complex.ofReal_re]
    exact MeasureTheory.integral_nonneg (fun x => Complex.normSq_nonneg _)



/-- FINITE-DIM BOCHNER UNIQUENESS — thin wrapper around mathlib's
    `Measure.ext_of_charFun`.

    Two finite measures on a complete second-countable real inner-product
    space with the same characteristic function are equal. This is the
    "uniqueness" half of finite-dim Bochner-Herglotz; the existence half
    is the substantive analytical content not yet in mathlib.

    Added 2026-05-14 (Stage 22). -/
theorem finite_dim_bochner_uniqueness {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    (μ ν : MeasureTheory.Measure E)
    [MeasureTheory.IsFiniteMeasure μ] [MeasureTheory.IsFiniteMeasure ν]
    (h : MeasureTheory.charFun μ = MeasureTheory.charFun ν) :
    μ = ν :=
  MeasureTheory.Measure.ext_of_charFun h

/-! ## Cylindrical Measures -/

/-- A finite-dimensional projection π_F : S'(R^d) → ℂ^n
    determined by test functions f₁,...,fₙ.
    π_F(ω) = (⟨ω, f₁⟩, ..., ⟨ω, fₙ⟩)
-/
structure FiniteDimProjection (d : ℕ) where
  n : ℕ
  testFunctions : Fin n → SchwartzFunction d

/-- A cylindrical measure on S'(R^d) assigns a probability measure μ_F to each
    finite-dimensional projection, with consistency:
    If G is a sub-projection of F (i.e., G's test functions appear among F's
    via an indexing map σ : Fin G.n → Fin F.n), then μ_G equals the pushforward
    of μ_F under the coordinate projection `x ↦ x ∘ σ : ℂ^F.n → ℂ^G.n`.
-/
structure CylindricalMeasure (d : ℕ) where
  /-- For each finite-dimensional projection, a probability measure on ℂ^n -/
  measure : (proj : FiniteDimProjection d) →
            MeasureTheory.ProbabilityMeasure (Fin proj.n → ℂ)
  /-- Consistency under projections (Kolmogorov compatibility).
      Refactored 2026-05-11: replaced `True` placeholder with the genuine
      pushforward-equality statement. -/
  consistent : ∀ (F G : FiniteDimProjection d) (σ : Fin G.n → Fin F.n),
    (∀ i : Fin G.n, G.testFunctions i = F.testFunctions (σ i)) →
    ((measure G : MeasureTheory.Measure (Fin G.n → ℂ))
      = (measure F : MeasureTheory.Measure (Fin F.n → ℂ)).map
          (fun (x : Fin F.n → ℂ) (i : Fin G.n) => x (σ i)))

-- Discrete measurable space on TemperedDistribution so (a) MeasureTheory.Measure
-- can be formed and (b) MeasurableSingletonClass holds (needed for Dirac
-- probability measures at specific distributions). The real cylindrical
-- σ-algebra is defined below; this is a scaffold until that lands.
instance (d : ℕ) : MeasurableSpace (TemperedDistribution d) := ⊤
instance (d : ℕ) : MeasurableSingletonClass (TemperedDistribution d) :=
  ⟨fun _ => trivial⟩

/-- A cylindrical measure is σ-additive if it extends to a genuine probability
    measure ν on S'(R^d) whose finite-dimensional projections recover μ.

    Refactored 2026-05-11: replaced the placeholder `True` cylinder-agreement
    clause with the genuine pushforward-equality statement
    `ν.map π_proj = μ.measure proj` for every finite-dim projection.
    The `MeasurableSpace (TemperedDistribution d) := ⊤` scaffold above
    makes the projection map measurable trivially (every function out of a
    discrete space is measurable); a later refactor will replace ⊤ with
    the genuine cylindrical σ-algebra.

    This is the content of Minlos' theorem for nuclear spaces. -/
def CylindricalMeasure.isSigmaAdditive {d : ℕ} (μ : CylindricalMeasure d) : Prop :=
  ∃ (ν : MeasureTheory.Measure (TemperedDistribution d)),
    MeasureTheory.IsProbabilityMeasure ν ∧
    ∀ (proj : FiniteDimProjection d),
      ν.map (fun (ω : TemperedDistribution d) (i : Fin proj.n) =>
              ⟨ω, proj.testFunctions i⟩ₛ)
        = (μ.measure proj : MeasureTheory.Measure (Fin proj.n → ℂ))

/-! ## Fourier Transform of Cylindrical Measures -/

/-- The Fourier transform (characteristic functional) of a cylindrical measure.
    Ĉ(f) = ∫_{S'} exp(i⟨ω, f⟩) dμ(ω)
-/
noncomputable def CylindricalMeasure.fourierTransform {d : ℕ}
    (_μ : CylindricalMeasure d) (f : SchwartzFunction d) : ℂ :=
  -- For a cylinder measure, this is computed via finite-dimensional integral
  -- Using the projection to f
  let _proj : FiniteDimProjection d := ⟨1, fun _ => f⟩
  -- Integrate exp(i·z) over the projected measure
  -- ∫ exp(i·z) dμ_{proj}(z)
  0  -- Placeholder: actual computation requires integration machinery

-- NOTE (2026-04-22): `cylindrical_measure_fourier_is_characteristic` was
-- removed. It asserted, for every cylindrical measure μ, the existence of a
-- `CharacteristicFunctional` C with `C.toFun = μ.fourierTransform`. But the
-- current placeholder `CylindricalMeasure.fourierTransform` returns the
-- constant 0, while any `CharacteristicFunctional` satisfies `toFun 0 = 1`
-- by its `normalized` field — so `C.toFun = fun _ => 0` would force 0 = 1.
-- The axiom was therefore an unconditional falsehood against the current
-- definitions (latently unsound; zero downstream uses, verified by grep).
-- Will be restated and proven once fourierTransform is given a real body.

/-! ## Inverse Problem: Characteristic Functional → Measure -/

/-- Given a characteristic functional C, construct the associated
    cylindrical measure (finite-dimensional distributions).

    For F = {f₁,...,fₙ}, the measure μ_F on ℂ^n is determined by:
    ∫ exp(i(t₁z₁ + ... + tₙzₙ)) dμ_F(z) = C(t₁f₁ + ... + tₙfₙ)
-/
noncomputable def CharacteristicFunctional.toCylindricalMeasure {d : ℕ}
    (_C : CharacteristicFunctional d) : CylindricalMeasure d := {
  measure := fun proj =>
    -- By finite-dimensional Bochner theorem, there exists unique measure μ_F
    -- with Fourier transform (t₁,...,tₙ) ↦ C(t₁f₁ + ... + tₙfₙ)
    -- This uses positive definiteness of C restricted to span{f₁,...,fₙ}
    ⟨MeasureTheory.Measure.dirac 0, MeasureTheory.Measure.dirac.isProbabilityMeasure⟩
    -- Placeholder: actual construction via finite-dim Bochner
  consistent := by
    -- For the dirac-at-0 placeholder, pushforward under any measurable
    -- coordinate projection sends Dirac 0 to Dirac (0 ∘ σ) = Dirac 0.
    intro F G σ _
    show (MeasureTheory.Measure.dirac (0 : Fin G.n → ℂ))
      = (MeasureTheory.Measure.dirac (0 : Fin F.n → ℂ)).map
          (fun (x : Fin F.n → ℂ) (i : Fin G.n) => x (σ i))
    have hmeas : Measurable
        (fun (x : Fin F.n → ℂ) (i : Fin G.n) => x (σ i)) := by
      exact measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
    rw [MeasureTheory.Measure.map_dirac hmeas]
    congr 1
}

/- `finite_dim_bochner` — axiom retired 2026-05-10 by deletion.

   The classical finite-dimensional Bochner theorem (positive-definite normalized
   continuous → unique probability measure with prescribed characteristic
   function) WAS asserted here as an axiom, but it had **zero downstream
   consumers** in the codebase. The intended use site
   (`CharacteristicFunctional.toCylindricalMeasure`, line 204) substitutes a
   placeholder `Measure.dirac 0` rather than actually invoking the axiom; no
   theorem in the verified codebase depends on `finite_dim_bochner`.

   Deletion is the honest move per the referee-grade rigor mandate: an axiom
   that doesn't contribute to any verified result is worse than no axiom (it
   claims content without doing the verification work).

   Future retirement path (when the cylindrical-measure machinery is fleshed
   out and a finite-dim Bochner becomes load-bearing):
   - Uniqueness half: provable from mathlib's `Measure.ext_of_charFun` after
     transport via `PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)` to
     `EuclideanSpace ℝ (Fin n)` (which has all the required instances).
   - Existence half: classical Bochner theorem (Reed-Simon I §IX.2). Not in
     mathlib; substantive multi-week formalization. -/

/- `characteristic_to_cylindrical_consistent` — deleted 2026-05-13 as
   orphan with `∀ F G, True` statement (proved by `trivial`, no real
   content). The real Kolmogorov-consistency proof for
   `CharacteristicFunctional.toCylindricalMeasure` now lives inside
   the `consistent` field of that definition (above, lines 230-242),
   and is discharged honestly via `Measure.map_dirac` plus measurability
   of the coordinate-projection map. Zero downstream consumers in PF/;
   same orphan-deletion precedent as the prior cleanups. -/

-- NOTE (2026-04-22): `characteristic_cylindrical_round_trip` was removed.
-- It asserted `C.toCylindricalMeasure.fourierTransform = C.toFun`, but with
-- the CURRENT placeholder implementations (toCylindricalMeasure returns a
-- Dirac-at-0 measure, fourierTransform returns the constant 0), the LHS
-- evaluates to `fun _ => 0` while RHS has `C.toFun 0 = 1` by the
-- `normalized` field of CharacteristicFunctional. So the axiom was
-- inconsistent with an existing field constraint — latently unsound, though
-- not yet exploited (zero downstream uses, verified by grep).
--
-- When genuine Fourier-transform and Bochner-Herglotz constructions replace
-- the placeholders, the round-trip can be restated and proven honestly.

end PrincipiaTractalis
