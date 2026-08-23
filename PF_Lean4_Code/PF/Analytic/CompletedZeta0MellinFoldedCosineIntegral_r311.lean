/-
# r311: `mellin F q = tail + conj tail`, hence `Re(mellin F q) = 2 · tail.re`
#      via `mellin_comp_inv` + `hf_modif_FE` + tail conjugation + split at 1
#      + chain-closer `4/901 < tail.re → Xi_Positive_At_15`

★ 2026-08-22 r311 — fold and split landing. Structural collapse of the r309
target `(mellin f_modif ⟨1/4, 15/2⟩).re` onto TWICE the real part of the
single tail integral `∫ y in Ioi 1, y^(q-1) • F y`. Real-integrand cosine
form (evenKernel unfolding + polar expansion of `y^(q-1)`) deferred to r312.

## Mission

Deliver the exact one-sided real integral for the Xi_Positive_At_15 discharge.
NO numerical approximation. Mathlib normalizations control; exponents must
emerge from the identities, not be forced.

## Route

Let `F := (hurwitzEvenFEPair 0).f_modif`, `q := ⟨1/4, 15/2⟩`. r309 gave
`Xi_Positive_At_15 ↔ 8/901 < (mellin F q).re`. r310 proved
`(mellin F q).im = 0`. r311 replaces `(mellin F q).re` with an explicit
real-integral form.

**Step 1** (§2, `(0, 1) → (1, ∞) fold at general exponent`):
Apply mathlib's `mellin_comp_inv (fun t => G t⁻¹) s = mellin G (-s)` to the
`(Ioi 1)`-indicator of `F`. The LHS integrates on `Ioo 0 1` with `F(t⁻¹)`;
substituting `F(t⁻¹) = t^(1/2) · F(t)` from `WeakFEPair.hf_modif_FE` at the
self-dual `hurwitzEvenFEPair 0` (`ε = 1`, `k = 1/2`, `g_modif = f_modif`)
and combining `t^(s-1) · t^(1/2) = t^(s - 1/2)` via `Complex.cpow_add` +
`Complex.ofReal_cpow`. Setting `q_L := s + 1/2` (so `s = q_L - 1/2`) gives

    `∫ t in Ioo 0 1, (t : ℂ)^(q_L - 1) • F(t)
       = ∫ y in Ioi 1, (y : ℂ)^((k - q_L) - 1) • F(y)`.

At `q_L = q` with `k - q = q̄ = ⟨1/4, -15/2⟩`, this becomes `V = U'`
(head integral = tail integral at conjugate exponent).

**Step 2** (§3, tail conjugation): `U' = conj U`. Push conjugation through
the integrand on `Ioi 1` using `Complex.cpow_conj` (arg `(y : ℂ) = 0 ≠ π`
for `y > 1`) + `Complex.conj_ofReal` (since `F(y) = evenKernel 0 y - 1` is
real on `Ioi 1`) + `MeasureTheory.integral_conj`.

**Step 3** (§4, split `mellin` at 1): `mellin F q = V + U` via
`setIntegral_union` on `Ioc 0 1` disjoint-union `Ioi 1 = Ioi 0`.

**Step 4** (§5, combining): `mellin F q = conj U + U = 2 · U.re` (as ℂ).
The complex sum `conj U + U` has zero imaginary part (matching r310) and
its real part is `2 · U.re`.

**Step 5** (§6-§7, real-integrand extraction on `Ioi 1`): Unfold
`F(x) = evenKernel 0 x - 1` for `x > 1` (from `WeakFEPair.f_modif`'s `Ioi 1`
branch), and extract `Re((x : ℂ)^(q-1)) = x^(-3/4) · cos((15/2) log x)`
for `x > 0` at `q = ⟨1/4, 15/2⟩` via `Complex.cpow` polar form. Use
`MeasureTheory.integral_re` to move `.re` through the integral.

## Final identity (`re_mellin_F_at_q_eq_two_re_tail`)

  `(mellin ((hurwitzEvenFEPair 0).f_modif) ⟨1/4, 15/2⟩).re
     = 2 * (∫ y in Ioi 1, (y : ℂ)^(q - 1) • F y).re`.

The tail integral is still stated as a **complex** integral. The real-integrand
form (`= 2 · ∫₁^∞ (evenKernel 0 x - 1) · x^(-3/4) · cos((15/2) log x) dx`) is
r312; separated because the polar decomposition of `(y : ℂ)^(q - 1)` plus the
`integral_re` swap plus the `evenKernel 0 y - 1` unfolding on `Ioi 1` is
independent mechanical work.

## Chain-closer (r311 form)

  `Xi_Positive_At_15_from_re_tail_lower_bound :
     4/901 < (∫ y in Ioi 1, (y : ℂ)^(q - 1) • F y).re
       → Xi_Positive_At_15`.

The `4/901` (vs r309's `8/901`) is the factor-of-2 absorbed from
`(mellin F q).re = 2 · tail.re`; matches Pabs's chain-closer specification
exactly on the "at minimum forward-use chain-closer" bar. r312 will strengthen
the LHS to the explicit cosine integral form.

## Framework-first status

NOT a numerical discharge. Structural fold: three complex-integral identities
(head-tail substitution, tail conjugation, split at 1) combine to produce the
first-time real-integral representation of the Xi_Positive_At_15 discharge
target. The exponent `-3/4` and the phase `(15/2) log x` emerge from
mathlib's Mellin convention (`(t : ℂ)^(s - 1)`) applied at
`s = q = ⟨1/4, 15/2⟩`; the factor of 2 emerges from `U + conj U = 2 U.re`.
No hidden normalization.

Book anchors: Ch 20 § 20.4 (RH via Fractal Resonance), Ch 34A § 34A.5.
Paper `principia_fractalis_alpha_skeleton_2026-07-13.pdf` § 6.
-/

import PF.Analytic.CompletedZeta0MellinRealAtCritical15_r310
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace PrincipiaTractalis.CompletedZeta0MellinFoldedCosineIntegral

open Complex MeasureTheory Set Real
open HurwitzZeta
open PrincipiaTractalis.CompletedZeta0MellinReduction
open PrincipiaTractalis.CompletedZeta0MellinRealAtCritical15

/-! ## §1 Notation shorthands. -/

/-- `F` = the modified theta kernel of `hurwitzEvenFEPair 0`. -/
private noncomputable abbrev F : ℝ → ℂ := (hurwitzEvenFEPair 0).f_modif

/-- `q` = the discharge target Mellin exponent. -/
private noncomputable abbrev q : ℂ := ⟨(1 : ℝ)/4, (15 : ℝ)/2⟩

/-- `qBar` = the conjugate, arising as `k - q` at `k = 1/2`. -/
private noncomputable abbrev qBar : ℂ := ⟨(1 : ℝ)/4, -((15 : ℝ)/2)⟩

/-! ## §2 The (0, 1) → (1, ∞) fold via `mellin_comp_inv` + `hf_modif_FE`. -/

/-- **`f_modif_inv_apply`** — evaluating `F(t⁻¹)` uses `WeakFEPair.hf_modif_FE`
at the self-dual `hurwitzEvenFEPair 0` (where `g_modif = f_modif` because
`(hurwitzEvenFEPair 0).symm = hurwitzEvenFEPair 0` and `symm.f_modif = g_modif`
by definition of `WeakFEPair.symm`):

  `F(t⁻¹) = (t^(1/2) : ℂ) • F(t)` for `t > 0`.

Uses `ε = 1`, `k = 1/2` for `hurwitzEvenFEPair 0`. -/
theorem f_modif_inv_apply {t : ℝ} (ht : 0 < t) :
    F t⁻¹ = ((t^((1 : ℝ)/2) : ℝ) : ℂ) • F t := by
  have h := (hurwitzEvenFEPair 0).hf_modif_FE t ht
  -- h : (hurwitzEvenFEPair 0).f_modif (1/t)
  --       = ((hurwitzEvenFEPair 0).ε * ↑(t^(hurwitzEvenFEPair 0).k)) •
  --           (hurwitzEvenFEPair 0).g_modif t
  -- (hurwitzEvenFEPair 0).ε = 1, .k = 1/2. And g_modif is defined via P.symm.f_modif structure
  -- Actually, WeakFEPair.g_modif is a separate defn — but for self-dual case, evaluates equal
  -- Because g_modif uses P.g = ofReal ∘ cosKernel 0 = ofReal ∘ evenKernel 0 = P.f
  -- and P.f₀ = P.g₀ = 1, P.ε = P.ε⁻¹ = 1.
  -- So g_modif = f_modif pointwise for hurwitzEvenFEPair 0.
  rw [show (1 : ℝ)/t = t⁻¹ from one_div t] at h
  -- Now: F t⁻¹ = ((hurwitzEvenFEPair 0).ε * ↑(t^(hurwitzEvenFEPair 0).k)) • g_modif t
  show (hurwitzEvenFEPair 0).f_modif t⁻¹ = _
  rw [h]
  -- Show the coefficient simplifies and g_modif t = F t.
  have hε : (hurwitzEvenFEPair 0).ε = 1 := rfl
  have hk : (hurwitzEvenFEPair 0).k = (1 : ℝ)/2 := rfl
  rw [hε, hk, one_mul]
  -- Now goal: ((t^(1/2) : ℝ) : ℂ) • (hurwitzEvenFEPair 0).g_modif t
  --          = ((t^(1/2) : ℝ) : ℂ) • F t
  congr 1
  -- Show g_modif t = F t = f_modif t.
  -- g_modif = (Ioi 1).indicator (fun x => P.g x - P.g₀)
  --         + (Ioo 0 1).indicator (fun x => P.g x - (P.ε⁻¹ * ↑(x^(-P.k))) • P.f₀)
  -- For hurwitzEvenFEPair 0: P.g = ofReal ∘ cosKernel 0, P.g₀ = 1, P.f₀ = 1, P.ε⁻¹ = 1.
  -- And cosKernel 0 = evenKernel 0 via `evenKernel_eq_cosKernel_of_zero`.
  simp only [WeakFEPair.g_modif, WeakFEPair.f_modif, Pi.add_apply, hurwitzEvenFEPair]
  by_cases h1 : t ∈ Ioi 1
  · by_cases h2 : t ∈ Ioo 0 1
    · exact absurd (mem_Ioo.mp h2).2 (not_lt.mpr (le_of_lt (mem_Ioi.mp h1)))
    · simp [Set.indicator_of_mem h1, Set.indicator_of_notMem h2, add_zero,
        Function.comp_apply, evenKernel_eq_cosKernel_of_zero]
  · by_cases h2 : t ∈ Ioo 0 1
    · simp [Set.indicator_of_notMem h1, Set.indicator_of_mem h2, zero_add,
        Function.comp_apply, inv_one, evenKernel_eq_cosKernel_of_zero]
    · simp only [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, add_zero]

/-- **`half_mellin_fold`** — the general-exponent half-Mellin fold at
`hurwitzEvenFEPair 0`: for any `q_L : ℂ`,

  `∫ t in Ioo 0 1, (t : ℂ)^(q_L - 1) • F(t) dt
     = ∫ y in Ioi 1, (y : ℂ)^(((1 : ℝ)/2 : ℂ) - q_L - 1) • F(y) dy`.

Proof strategy: apply `mellin_comp_inv` to `G := (Ioi 1).indicator F` at
exponent `s := q_L - 1/2`, which gives
`∫ t in Ioo 0 1, t^(s-1) • F(t⁻¹) dt = ∫ y in Ioi 1, y^(-s-1) • F y dy`.
Substitute `F(t⁻¹) = (t^(1/2) : ℂ) • F(t)` from `f_modif_inv_apply` on the
LHS; combine `t^(s-1) · t^(1/2) = t^(s - 1/2) = t^(q_L - 1)` via
`Complex.cpow_add` + `Complex.ofReal_cpow`. On the RHS,
`-s - 1 = -(q_L - 1/2) - 1 = (1/2 - q_L) - 1 = (k - q_L) - 1`. -/
theorem half_mellin_fold (q_L : ℂ) :
    (∫ t in Ioo (0 : ℝ) 1, (t : ℂ)^(q_L - 1) • F t)
      = ∫ y in Ioi (1 : ℝ), (y : ℂ)^((((1 : ℝ)/2 : ℝ) : ℂ) - q_L - 1) • F y := by
  -- Step 1: Set G = (Ioi 1).indicator F, s = q_L - 1/2.
  set s : ℂ := q_L - (((1 : ℝ)/2 : ℝ) : ℂ) with hs_def
  set G : ℝ → ℂ := (Ioi (1 : ℝ)).indicator F with hG_def
  -- Step 2: mellin_comp_inv at G, s.
  have h_inv : mellin (fun t => G t⁻¹) s = mellin G (-s) := mellin_comp_inv G s
  -- Step 3: Simplify both sides of h_inv.
  -- LHS: mellin (fun t => G t⁻¹) s = ∫ t in Ioi 0, (t : ℂ)^(s-1) • G(t⁻¹) dt
  --    G(t⁻¹) = F(t⁻¹) if t⁻¹ ∈ Ioi 1 (i.e., 0 < t < 1), else 0.
  -- RHS: mellin G (-s) = ∫ y in Ioi 0, y^(-s-1) • G(y) dy
  --    G(y) = F(y) if y ∈ Ioi 1, else 0.
  unfold mellin at h_inv
  -- Rewrite both sides using indicator support.
  have hLHS :
      (∫ t in Ioi (0 : ℝ), (t : ℂ)^(s-1) • G t⁻¹)
        = ∫ t in Ioo (0 : ℝ) 1, (t : ℂ)^(s-1) • F t⁻¹ := by
    rw [← integral_indicator (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ))),
        ← integral_indicator (measurableSet_Ioo : MeasurableSet (Ioo (0 : ℝ) 1))]
    congr 1
    funext t
    by_cases ht0 : t ∈ Ioi (0 : ℝ)
    · by_cases ht1 : t ∈ Ioo (0 : ℝ) 1
      · -- t ∈ (0, 1): t⁻¹ > 1, so G(t⁻¹) = F(t⁻¹)
        rw [Set.indicator_of_mem ht0, Set.indicator_of_mem ht1]
        show _ = (t : ℂ)^(s-1) • F t⁻¹
        congr 1
        rw [hG_def]
        rw [Set.indicator_of_mem]
        exact (one_lt_inv₀ ht0).mpr ht1.2
      · -- t ∈ (0, ∞) \ (0, 1) = [1, ∞): t⁻¹ ≤ 1, so G(t⁻¹) = 0
        rw [Set.indicator_of_mem ht0, Set.indicator_of_notMem ht1]
        have ht_ge : (1 : ℝ) ≤ t := by
          rcases lt_or_ge t 1 with h | h
          · exact absurd (mem_Ioo.mpr ⟨ht0, h⟩) ht1
          · exact h
        rw [hG_def, Set.indicator_of_notMem]
        · simp
        · rw [mem_Ioi, not_lt]
          exact inv_le_one_of_one_le₀ ht_ge
    · -- ¬ t ∈ Ioi 0: t ≤ 0
      have ht_not_Ioo : t ∉ Ioo (0 : ℝ) 1 := fun h => ht0 (Ioo_subset_Ioi_self h)
      rw [Set.indicator_of_notMem ht0, Set.indicator_of_notMem ht_not_Ioo]
  have hRHS :
      (∫ y in Ioi (0 : ℝ), (y : ℂ)^(-s - 1) • G y)
        = ∫ y in Ioi (1 : ℝ), (y : ℂ)^(-s - 1) • F y := by
    rw [← integral_indicator (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ))),
        ← integral_indicator (measurableSet_Ioi : MeasurableSet (Ioi (1 : ℝ)))]
    congr 1
    funext y
    by_cases hy0 : y ∈ Ioi (0 : ℝ)
    · by_cases hy1 : y ∈ Ioi (1 : ℝ)
      · rw [Set.indicator_of_mem hy0, Set.indicator_of_mem hy1]
        rw [hG_def, Set.indicator_of_mem hy1]
      · rw [Set.indicator_of_mem hy0, Set.indicator_of_notMem hy1]
        rw [hG_def, Set.indicator_of_notMem hy1]
        simp
    · have hy_not_Ioi1 : y ∉ Ioi (1 : ℝ) := fun h => hy0 (Ioi_subset_Ioi zero_le_one h)
      rw [Set.indicator_of_notMem hy0, Set.indicator_of_notMem hy_not_Ioi1]
  -- Substitute:
  rw [hLHS] at h_inv
  rw [hRHS] at h_inv
  -- h_inv : ∫ t in Ioo 0 1, (t : ℂ)^(s-1) • F(t⁻¹) = ∫ y in Ioi 1, y^(-s-1) • F y
  -- Now substitute F(t⁻¹) = (t^(1/2) : ℝ) • F(t) via f_modif_inv_apply.
  have hLHS_sub :
      (∫ t in Ioo (0 : ℝ) 1, (t : ℂ)^(s-1) • F t⁻¹)
        = ∫ t in Ioo (0 : ℝ) 1, (t : ℂ)^(q_L - 1) • F t := by
    refine setIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
    have ht_pos : (0 : ℝ) < t := ht.1
    have ht_ne : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht_pos.ne'
    rw [f_modif_inv_apply ht_pos, smul_smul]
    congr 1
    -- Goal: (t : ℂ)^(s-1) * ((t^(1/2) : ℝ) : ℂ) = (t : ℂ)^(q_L - 1)
    rw [Complex.ofReal_cpow ht_pos.le]
    -- Now: (t : ℂ)^(s-1) * (t : ℂ)^((1/2 : ℝ) : ℂ) = (t : ℂ)^(q_L - 1)
    rw [← Complex.cpow_add _ _ ht_ne]
    congr 1
    -- Goal: s - 1 + ((1/2 : ℝ) : ℂ) = q_L - 1
    rw [hs_def]
    ring
  rw [hLHS_sub] at h_inv
  -- Now rewrite RHS: -s - 1 = (1/2 : ℂ) - q_L - 1
  have hRHS_exp : -s - 1 = (((1 : ℝ)/2 : ℝ) : ℂ) - q_L - 1 := by
    rw [hs_def]; ring
  rw [hRHS_exp] at h_inv
  exact h_inv

/-- **`half_mellin_fold_at_critical_15`** — specialization to `q_L = q = ⟨1/4, 15/2⟩`:

  `∫ t in Ioo 0 1, (t : ℂ)^(q - 1) • F(t) dt = ∫ y in Ioi 1, (y : ℂ)^(qBar - 1) • F(y) dy`.

Since `(1/2 : ℝ) : ℂ - q = qBar` via `half_sub_critical_15_half_eq_neg_critical_15_half`
from r310. -/
theorem half_mellin_fold_at_critical_15 :
    (∫ t in Ioo (0 : ℝ) 1, (t : ℂ)^(q - 1) • F t)
      = ∫ y in Ioi (1 : ℝ), (y : ℂ)^(qBar - 1) • F y := by
  have h := half_mellin_fold q
  -- h : ∫ t in Ioo 0 1, (t : ℂ)^(q - 1) • F t
  --      = ∫ y in Ioi 1, (y : ℂ)^((1/2 : ℂ) - q - 1) • F y
  -- Show: ((1/2 : ℝ) : ℂ) - q = qBar via half_sub_critical_15_half_eq_neg_critical_15_half
  rw [h]
  congr 1
  funext y
  congr 2
  -- Goal: ((1/2 : ℝ) : ℂ) - q - 1 = qBar - 1
  rw [show (((1 : ℝ)/2 : ℝ) : ℂ) - q = qBar from
    half_sub_critical_15_half_eq_neg_critical_15_half]

/-! ## §3 Tail conjugation: `U' = conj U`. -/

/-- **`f_modif_ioi_one_im_eq_zero`** — `F` has zero imaginary part on `Ioi 1`
(consequence of `f_modif_hurwitzEvenFEPair_zero_im_eq_zero` from r310). -/
theorem f_modif_ioi_one_im_eq_zero (x : ℝ) (_hx : x ∈ Ioi (1 : ℝ)) :
    (F x).im = 0 :=
  f_modif_hurwitzEvenFEPair_zero_im_eq_zero x

/-- **`tail_conj_symmetric`** — for any `s : ℂ`,

  `∫ y in Ioi 1, (y : ℂ)^(conj s - 1) • F y = conj (∫ y in Ioi 1, (y : ℂ)^(s - 1) • F y)`.

Same technique as `mellin_conj_of_im_zero` from r310, restricted to `Ioi 1`. -/
theorem tail_conj_symmetric (s : ℂ) :
    (∫ y in Ioi (1 : ℝ), (y : ℂ)^(starRingEnd ℂ s - 1) • F y)
      = starRingEnd ℂ (∫ y in Ioi (1 : ℝ), (y : ℂ)^(s - 1) • F y) := by
  rw [← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
  have hy_pos : (0 : ℝ) < y := lt_trans zero_lt_one hy
  have hy_arg : (y : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hy_pos.le]
    exact Real.pi_pos.ne
  have h_cpow : (y : ℂ) ^ (starRingEnd ℂ s - 1) = starRingEnd ℂ ((y : ℂ) ^ (s - 1)) := by
    have hstar : starRingEnd ℂ s - 1 = starRingEnd ℂ (s - 1) := by
      rw [map_sub, map_one]
    rw [hstar, Complex.cpow_conj _ _ hy_arg, Complex.conj_ofReal]
  have h_F : starRingEnd ℂ (F y) = F y := by
    apply Complex.ext
    · rfl
    · rw [Complex.conj_im, f_modif_ioi_one_im_eq_zero y hy, neg_zero]
  rw [smul_eq_mul, smul_eq_mul, h_cpow, map_mul, h_F]

/-- **`tail_at_qBar_eq_conj_tail_at_q`** — specialization: `U' = conj U`. -/
theorem tail_at_qBar_eq_conj_tail_at_q :
    (∫ y in Ioi (1 : ℝ), (y : ℂ)^(qBar - 1) • F y)
      = starRingEnd ℂ (∫ y in Ioi (1 : ℝ), (y : ℂ)^(q - 1) • F y) := by
  have h_conj_q : starRingEnd ℂ q = qBar := by
    apply Complex.ext
    · rfl
    · rfl
  rw [← h_conj_q]
  exact tail_conj_symmetric q

/-! ## §4 The fold: `V = conj U`. -/

/-- **`head_eq_conj_tail_at_critical_15`** — combining §2 and §3:

  `∫ t in Ioo 0 1, (t : ℂ)^(q - 1) • F(t) dt = conj (∫ y in Ioi 1, (y : ℂ)^(q - 1) • F(y) dy)`. -/
theorem head_eq_conj_tail_at_critical_15 :
    (∫ t in Ioo (0 : ℝ) 1, (t : ℂ)^(q - 1) • F t)
      = starRingEnd ℂ (∫ y in Ioi (1 : ℝ), (y : ℂ)^(q - 1) • F y) := by
  rw [half_mellin_fold_at_critical_15, tail_at_qBar_eq_conj_tail_at_q]

/-! ## §5 Split `mellin` at 1. -/

/-- **`mellin_F_at_q_split_at_one`** — `mellin F q = V + U` via disjoint
union `Ioc 0 1 ⊔ Ioi 1 = Ioi 0` and `Ioc 0 1` ≡ `Ioo 0 1` (a.e.). Uses
`MellinConvergent` for `hurwitzEvenFEPair 0` at every `s` (from
`WeakFEPair.toStrongFEPair.hasMellin`) to get integrability. -/
theorem mellin_F_at_q_split_at_one :
    mellin F q
      = (∫ t in Ioo (0 : ℝ) 1, (t : ℂ)^(q - 1) • F t)
        + ∫ y in Ioi (1 : ℝ), (y : ℂ)^(q - 1) • F y := by
  have h_conv : MellinConvergent F q :=
    ((hurwitzEvenFEPair 0).toStrongFEPair.hasMellin q).1
  -- h_conv : IntegrableOn (fun t => (t : ℂ)^(q-1) • F t) (Ioi 0)
  unfold mellin
  rw [show Ioi (0 : ℝ) = Ioc (0 : ℝ) 1 ∪ Ioi 1 from (Ioc_union_Ioi_eq_Ioi zero_le_one).symm,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (h_conv.mono_set Ioc_subset_Ioi_self)
        (h_conv.mono_set (fun x (hx : x ∈ Ioi (1 : ℝ)) => mem_Ioi.mpr (zero_lt_one.trans hx))),
      integral_Ioc_eq_integral_Ioo]

/-! ## §6 Combining §4 and §5: `mellin F q = tail + conj tail` = `2 · tail.re` (as ℂ). -/

/-- **`mellin_F_at_q_eq_tail_plus_conj_tail`** — combining `head + tail = mellin`
(§5) with `head = conj tail` (§4):

  `mellin F q = (∫ y in Ioi 1, y^(q-1) • F y) + conj (∫ y in Ioi 1, y^(q-1) • F y)`. -/
theorem mellin_F_at_q_eq_tail_plus_conj_tail :
    mellin F q
      = (∫ y in Ioi (1 : ℝ), (y : ℂ)^(q - 1) • F y)
        + starRingEnd ℂ (∫ y in Ioi (1 : ℝ), (y : ℂ)^(q - 1) • F y) := by
  rw [mellin_F_at_q_split_at_one, head_eq_conj_tail_at_critical_15, add_comm]

/-- **`re_mellin_F_at_q_eq_two_re_tail`** — the real part of the Mellin at `q`
equals `2 · tail.re`:

  `(mellin F q).re = 2 * (∫ y in Ioi 1, y^(q - 1) • F y).re`.

From `mellin_F_at_q_eq_tail_plus_conj_tail` and `z.re + (conj z).re = 2 * z.re`. -/
theorem re_mellin_F_at_q_eq_two_re_tail :
    (mellin F q).re
      = 2 * (∫ y in Ioi (1 : ℝ), (y : ℂ)^(q - 1) • F y).re := by
  rw [mellin_F_at_q_eq_tail_plus_conj_tail, Complex.add_re, Complex.conj_re]
  ring

/-! ## §7 Chain-closer via the complex-integral tail. -/

/-- **`Xi_Positive_At_15_from_re_tail_lower_bound`** — chain-closer using the
complex-integral form of the tail:

  `4/901 < (∫ y in Ioi 1, (y : ℂ)^(q - 1) • F y).re → Xi_Positive_At_15`.

Combines `re_mellin_F_at_q_eq_two_re_tail` (r311 §6) with r309's
`Xi_Positive_At_15_from_re_mellin_lower_bound`. The `4/901` (vs r309's
`8/901`) is exactly the factor-of-2 absorbed from `re = 2 · tail.re`. -/
theorem Xi_Positive_At_15_from_re_tail_lower_bound
    {a : ℝ} (ha : (4 : ℝ)/901 < a)
    (h : a ≤ (∫ y in Ioi (1 : ℝ), (y : ℂ)^(q - 1) • F y).re) :
    PrincipiaTractalis.UnifiedClayClosureViaRouteBSpecificXiAndFullPinning.Xi_Positive_At_15 := by
  refine Xi_Positive_At_15_from_re_mellin_lower_bound (a := 2 * a) ?_ ?_
  · linarith
  · rw [re_mellin_F_at_q_eq_two_re_tail]
    linarith

/-! ## §8 Axiom checks. -/

#print axioms
  PrincipiaTractalis.CompletedZeta0MellinFoldedCosineIntegral.f_modif_inv_apply
#print axioms
  PrincipiaTractalis.CompletedZeta0MellinFoldedCosineIntegral.half_mellin_fold
#print axioms
  PrincipiaTractalis.CompletedZeta0MellinFoldedCosineIntegral.half_mellin_fold_at_critical_15
#print axioms
  PrincipiaTractalis.CompletedZeta0MellinFoldedCosineIntegral.f_modif_ioi_one_im_eq_zero
#print axioms
  PrincipiaTractalis.CompletedZeta0MellinFoldedCosineIntegral.tail_conj_symmetric
#print axioms
  PrincipiaTractalis.CompletedZeta0MellinFoldedCosineIntegral.tail_at_qBar_eq_conj_tail_at_q
#print axioms
  PrincipiaTractalis.CompletedZeta0MellinFoldedCosineIntegral.head_eq_conj_tail_at_critical_15
#print axioms
  PrincipiaTractalis.CompletedZeta0MellinFoldedCosineIntegral.mellin_F_at_q_split_at_one
#print axioms
  PrincipiaTractalis.CompletedZeta0MellinFoldedCosineIntegral.mellin_F_at_q_eq_tail_plus_conj_tail
#print axioms
  PrincipiaTractalis.CompletedZeta0MellinFoldedCosineIntegral.re_mellin_F_at_q_eq_two_re_tail
#print axioms
  PrincipiaTractalis.CompletedZeta0MellinFoldedCosineIntegral.Xi_Positive_At_15_from_re_tail_lower_bound

end PrincipiaTractalis.CompletedZeta0MellinFoldedCosineIntegral
