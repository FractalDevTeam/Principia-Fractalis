/-
# r310: `mellin (f_modif) ⟨1/4, 15/2⟩` IS REAL — imaginary part vanishes
#      via `WeakFEPair.functional_equation₀` + Mellin conjugation

★ 2026-08-22 r310 — first analytic-content step past the r309 normalization
collapse. Combines two facts about `mellin ((hurwitzEvenFEPair 0).f_modif)`
at the specific point `q = ⟨1/4, 15/2⟩`:

- FE-symmetry (from `WeakFEPair.functional_equation₀` at the self-dual
  pair `hurwitzEvenFEPair 0` with `ε = 1`, `k = 1/2`):
      `Λ₀ ⟨1/4, -15/2⟩ = Λ₀ ⟨1/4, 15/2⟩`,
  because `k - q = 1/2 - ⟨1/4, 15/2⟩ = ⟨1/4, -15/2⟩ = conj q`.

- Mellin conjugation (from the fact that `f_modif` for `hurwitzEvenFEPair 0`
  is real-valued in ℂ):
      `mellin f_modif (conj q) = conj (mellin f_modif q)`,
  proved by pushing conjugation through the integrand:
  `conj((t : ℂ)^(q-1) · f_modif t) = (t : ℂ)^(conj q - 1) · f_modif t`
  for `t > 0`, using `Complex.cpow_conj` (arg (t : ℂ) = 0 ≠ π) and
  `Complex.conj_ofReal` for the real-valued `f_modif`, then applying
  `integral_conj`.

Combining: `mellin f_modif q = mellin f_modif (conj q) = conj (mellin f_modif q)`,
hence `(mellin f_modif q).im = 0`.

## What r310 delivers

- `f_modif_hurwitzEvenFEPair_zero_im_eq_zero` :
    `∀ x, ((hurwitzEvenFEPair 0).f_modif x).im = 0` — pointwise realness
  of the modified theta kernel `f_modif` for the Hurwitz FE-pair at `a = 0`.

- `mellin_conj_of_im_zero` :
    `mellin f (conj s) = conj (mellin f s)` for any `f : ℝ → ℂ` with
    `(f x).im = 0` on `Ioi 0`. Kernel-clean; no integrability hypothesis
    needed (uses `LinearIsometry.integral_comp_comm`).

- `half_sub_critical_15_half_eq_neg_critical_15_half` :
    `((1/2 : ℝ) : ℂ) - ⟨1/4, 15/2⟩ = ⟨1/4, -15/2⟩` — the FE argument
    `k - q` at `k = 1/2`, `q = ⟨1/4, 15/2⟩`. Complex-arithmetic identity.

- `hurwitzEvenFEPair_zero_Λ₀_symmetry_at_critical_15` :
    `(hurwitzEvenFEPair 0).Λ₀ ⟨1/4, -15/2⟩ = (hurwitzEvenFEPair 0).Λ₀ ⟨1/4, 15/2⟩` —
    the FE identity at the critical point.

- `mellin_f_modif_at_critical_15_conj_eq` :
    `mellin f_modif ⟨1/4, -15/2⟩ = conj (mellin f_modif ⟨1/4, 15/2⟩)` —
    conjugation identity specialized to the critical point.

- `mellin_f_modif_at_critical_15_im_eq_zero` :
    `(mellin ((hurwitzEvenFEPair 0).f_modif) ⟨1/4, 15/2⟩).im = 0` —
    the CORE realness result.

- `mellin_f_modif_at_critical_15_eq_ofReal_re` :
    `mellin f_modif ⟨1/4, 15/2⟩ = ((mellin f_modif ⟨1/4, 15/2⟩).re : ℂ)` —
    the mellin as an `ofReal` cast of its real part, exhibiting that the
    full complex value is a real number embedded in ℂ.

## Framework-first status

Pure structural landing. NOT a numerical discharge. Provides the realness
invariant that r311 will consume to fold the (0, 1) half of the Mellin
integral into the [1, ∞) half via `x ↦ 1/x` and expose the cosine-integrand
representation
`Re(mellin f_modif q) = 2 ∫₁^∞ (evenKernel 0 x - 1) · x^(-3/4) · cos((15/2) log x) dx`.

## Framework-first dependency-reduction ledger

**Before r310** (r309 state): `Xi_Positive_At_15 ↔ 8/901 < (mellin f_modif ⟨1/4, 15/2⟩).re`.
The `.re` was extracted from a genuinely complex quantity; nothing said
that the `.im` was zero.

**After r310**: same reformulation as r309, but now companion-fact that
`(mellin f_modif ⟨1/4, 15/2⟩).im = 0`, so the target real number for
numerical bounding is the full complex value viewed as a real. This
unlocks: (a) the `x ↦ 1/x` fold for r311 (whose conjugate-pairing at
`q + conj q = 1/2 = k` folds the (0, 1) half onto (1, ∞)), and
(b) certified numerical bounds via real-integral machinery.

Book anchors: Ch 20 § 20.4 (RH via Fractal Resonance), Ch 34A § 34A.5.
Paper `principia_fractalis_alpha_skeleton_2026-07-13.pdf` § 6.
-/

import PF.Analytic.CompletedZeta0MellinReduction_r309
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace PrincipiaTractalis.CompletedZeta0MellinRealAtCritical15

open Complex MeasureTheory Set
open HurwitzZeta
open PrincipiaTractalis.CompletedZeta0MellinReduction

/-! ## §1 Arithmetic: `((1/2 : ℝ) : ℂ) - ⟨1/4, 15/2⟩ = ⟨1/4, -15/2⟩`. -/

/-- **`half_sub_critical_15_half_eq_neg_critical_15_half`** — the FE argument
`k - q` at `k = 1/2`, `q = ⟨1/4, 15/2⟩`. -/
theorem half_sub_critical_15_half_eq_neg_critical_15_half :
    (((1 : ℝ)/2 : ℝ) : ℂ) - ((⟨(1 : ℝ)/4, (15 : ℝ)/2⟩ : ℂ))
      = ((⟨(1 : ℝ)/4, -((15 : ℝ)/2)⟩ : ℂ)) := by
  apply Complex.ext
  · simp; ring
  · simp

/-! ## §2 Pointwise realness of `f_modif` for `hurwitzEvenFEPair 0`. -/

/-- **`f_modif_hurwitzEvenFEPair_zero_im_eq_zero`** — for every `x : ℝ`,
`((hurwitzEvenFEPair 0).f_modif x).im = 0`.

Direct from the definition of `WeakFEPair.f_modif` as a sum of indicators
of `Ioi 1` and `Ioo 0 1` applied to expressions built from `ofReal`
values (namely `evenKernel 0 x`, real constants `1`, `ε = 1`, `g₀ = 1`,
and the real power `x^(-1/2)`). Case-split on `x`'s membership in
each indicator's set. -/
theorem f_modif_hurwitzEvenFEPair_zero_im_eq_zero (x : ℝ) :
    ((hurwitzEvenFEPair 0).f_modif x).im = 0 := by
  simp only [WeakFEPair.f_modif, Pi.add_apply, Set.indicator]
  -- Split into the four disjoint cases: x ∈ Ioi 1, x ∈ Ioo 0 1, both, or neither.
  by_cases h1 : x ∈ Ioi 1
  · by_cases h2 : x ∈ Ioo 0 1
    · exact absurd (mem_Ioo.mp h2).2 (not_lt.mpr (le_of_lt (mem_Ioi.mp h1)))
    · simp only [if_pos h1, if_neg h2, add_zero]
      -- goal: ((hurwitzEvenFEPair 0).f x - (hurwitzEvenFEPair 0).f₀).im = 0
      show (((evenKernel 0 x : ℝ) : ℂ) - (if (0 : UnitAddCircle) = 0 then 1 else 0)).im = 0
      simp [Complex.sub_im, Complex.ofReal_im]
  · by_cases h2 : x ∈ Ioo 0 1
    · simp only [if_neg h1, if_pos h2, zero_add]
      -- goal: ((hurwitzEvenFEPair 0).f x - ((hurwitzEvenFEPair 0).ε *
      --        ↑(x^(-(hurwitzEvenFEPair 0).k))) • (hurwitzEvenFEPair 0).g₀).im = 0
      show (((evenKernel 0 x : ℝ) : ℂ)
              - ((1 : ℂ) * ((x^(-((1 : ℝ)/2)) : ℝ) : ℂ)) • (1 : ℂ)).im = 0
      simp [Complex.sub_im, Complex.ofReal_im, smul_eq_mul]
    · simp only [if_neg h1, if_neg h2, add_zero, Complex.zero_im]

/-! ## §3 Mellin conjugation for ℂ-valued functions with zero imaginary part. -/

/-- **`mellin_conj_of_im_zero`** — for any `f : ℝ → ℂ` such that `(f x).im = 0`
on `Ioi 0`, the Mellin transform satisfies
`mellin f (conj s) = conj (mellin f s)`.

Push conjugation through the integrand: for `t > 0`,
- `(t : ℂ)^(conj s - 1) = conj ((t : ℂ)^(s - 1))` via `Complex.cpow_conj`
  (arg (t : ℂ) = 0 ≠ π for `t > 0`) plus `Complex.conj_ofReal`.
- `conj (f t) = f t` since `(f t).im = 0`.

Then apply `MeasureTheory.integral_conj` on the restricted measure. -/
theorem mellin_conj_of_im_zero
    {f : ℝ → ℂ} (hf : ∀ x ∈ Ioi (0 : ℝ), (f x).im = 0) (s : ℂ) :
    mellin f (starRingEnd ℂ s) = starRingEnd ℂ (mellin f s) := by
  unfold mellin
  rw [← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  have ht_pos : (0 : ℝ) < t := ht
  have ht_arg : (t : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg ht_pos.le]
    exact Real.pi_pos.ne
  have h_cpow : (t : ℂ) ^ (starRingEnd ℂ s - 1) = starRingEnd ℂ ((t : ℂ) ^ (s - 1)) := by
    have hstar : starRingEnd ℂ s - 1 = starRingEnd ℂ (s - 1) := by
      rw [map_sub, map_one]
    rw [hstar, Complex.cpow_conj _ _ ht_arg, Complex.conj_ofReal]
  have h_f : starRingEnd ℂ (f t) = f t := by
    apply Complex.ext
    · rfl
    · rw [Complex.conj_im, hf t ht, neg_zero]
  rw [smul_eq_mul, smul_eq_mul, h_cpow, map_mul, h_f]

/-! ## §4 FE symmetry at the critical point. -/

/-- **`hurwitzEvenFEPair_zero_Λ₀_symmetry_at_critical_15`** —
`(hurwitzEvenFEPair 0).Λ₀ ⟨1/4, -15/2⟩ = (hurwitzEvenFEPair 0).Λ₀ ⟨1/4, 15/2⟩`.

Direct application of `WeakFEPair.functional_equation₀` at
`s = ⟨1/4, 15/2⟩`, using `(hurwitzEvenFEPair 0).ε = 1`,
`(hurwitzEvenFEPair 0).k = 1/2`, self-duality
`(hurwitzEvenFEPair 0).symm = hurwitzEvenFEPair 0`, and the arithmetic
`k - q = ⟨1/4, -15/2⟩`. -/
theorem hurwitzEvenFEPair_zero_Λ₀_symmetry_at_critical_15 :
    (hurwitzEvenFEPair 0).Λ₀ ((⟨(1 : ℝ)/4, -((15 : ℝ)/2)⟩ : ℂ))
      = (hurwitzEvenFEPair 0).Λ₀ ((⟨(1 : ℝ)/4, (15 : ℝ)/2⟩ : ℂ)) := by
  have hFE := (hurwitzEvenFEPair 0).functional_equation₀
                ((⟨(1 : ℝ)/4, (15 : ℝ)/2⟩ : ℂ))
  rw [hurwitzEvenFEPair_zero_symm] at hFE
  -- hFE : (hurwitzEvenFEPair 0).Λ₀ ((hurwitzEvenFEPair 0).k - ⟨1/4, 15/2⟩)
  --         = (hurwitzEvenFEPair 0).ε • (hurwitzEvenFEPair 0).Λ₀ ⟨1/4, 15/2⟩
  -- (hurwitzEvenFEPair 0).k = 1/2, .ε = 1
  show (hurwitzEvenFEPair 0).Λ₀ _ = _
  rw [show (((⟨(1 : ℝ)/4, -((15 : ℝ)/2)⟩ : ℂ))
            : ℂ) = (((1 : ℝ)/2 : ℝ) : ℂ) - ((⟨(1 : ℝ)/4, (15 : ℝ)/2⟩ : ℂ)) from
       (half_sub_critical_15_half_eq_neg_critical_15_half).symm]
  convert hFE using 1
  simp [hurwitzEvenFEPair]

/-! ## §5 Mellin conjugation identity at the critical point. -/

/-- **`mellin_f_modif_at_critical_15_conj_eq`** —
`mellin ((hurwitzEvenFEPair 0).f_modif) ⟨1/4, -15/2⟩
  = conj (mellin ((hurwitzEvenFEPair 0).f_modif) ⟨1/4, 15/2⟩)`.

From `mellin_conj_of_im_zero` applied with `f = (hurwitzEvenFEPair 0).f_modif`
(real-valued by `f_modif_hurwitzEvenFEPair_zero_im_eq_zero`) and
`s = ⟨1/4, 15/2⟩`, using that `conj ⟨1/4, 15/2⟩ = ⟨1/4, -15/2⟩`. -/
theorem mellin_f_modif_at_critical_15_conj_eq :
    mellin ((hurwitzEvenFEPair 0).f_modif) ((⟨(1 : ℝ)/4, -((15 : ℝ)/2)⟩ : ℂ))
      = starRingEnd ℂ
          (mellin ((hurwitzEvenFEPair 0).f_modif) ((⟨(1 : ℝ)/4, (15 : ℝ)/2⟩ : ℂ))) := by
  have h_conj_q :
      starRingEnd ℂ ((⟨(1 : ℝ)/4, (15 : ℝ)/2⟩ : ℂ)) = ((⟨(1 : ℝ)/4, -((15 : ℝ)/2)⟩ : ℂ)) := by
    apply Complex.ext
    · rfl
    · rfl
  rw [← h_conj_q]
  exact mellin_conj_of_im_zero
    (fun x hx => f_modif_hurwitzEvenFEPair_zero_im_eq_zero x)
    ((⟨(1 : ℝ)/4, (15 : ℝ)/2⟩ : ℂ))

/-! ## §6 Realness: `(mellin f_modif ⟨1/4, 15/2⟩).im = 0`. -/

/-- **`mellin_f_modif_at_critical_15_im_eq_zero`** — the CORE realness result:
`(mellin ((hurwitzEvenFEPair 0).f_modif) ⟨1/4, 15/2⟩).im = 0`.

Combining §4 (FE symmetry: `Λ₀ ⟨1/4, -15/2⟩ = Λ₀ ⟨1/4, 15/2⟩`) and
§5 (conjugation: `Λ₀ ⟨1/4, -15/2⟩ = conj (Λ₀ ⟨1/4, 15/2⟩)`), we get
`Λ₀ ⟨1/4, 15/2⟩ = conj (Λ₀ ⟨1/4, 15/2⟩)`, i.e., `Λ₀ ⟨1/4, 15/2⟩` has
zero imaginary part. Unfolding `Λ₀ = mellin f_modif` finishes. -/
theorem mellin_f_modif_at_critical_15_im_eq_zero :
    (mellin ((hurwitzEvenFEPair 0).f_modif)
        ((⟨(1 : ℝ)/4, (15 : ℝ)/2⟩ : ℂ))).im = 0 := by
  have h_FE :
      mellin ((hurwitzEvenFEPair 0).f_modif) ((⟨(1 : ℝ)/4, -((15 : ℝ)/2)⟩ : ℂ))
        = mellin ((hurwitzEvenFEPair 0).f_modif) ((⟨(1 : ℝ)/4, (15 : ℝ)/2⟩ : ℂ)) :=
    hurwitzEvenFEPair_zero_Λ₀_symmetry_at_critical_15
  have h_conj :
      mellin ((hurwitzEvenFEPair 0).f_modif) ((⟨(1 : ℝ)/4, -((15 : ℝ)/2)⟩ : ℂ))
        = starRingEnd ℂ
            (mellin ((hurwitzEvenFEPair 0).f_modif) ((⟨(1 : ℝ)/4, (15 : ℝ)/2⟩ : ℂ))) :=
    mellin_f_modif_at_critical_15_conj_eq
  have h_selfconj :
      starRingEnd ℂ
          (mellin ((hurwitzEvenFEPair 0).f_modif) ((⟨(1 : ℝ)/4, (15 : ℝ)/2⟩ : ℂ)))
        = mellin ((hurwitzEvenFEPair 0).f_modif) ((⟨(1 : ℝ)/4, (15 : ℝ)/2⟩ : ℂ)) := by
    rw [← h_conj, h_FE]
  -- conj z = z ↔ z.im = 0
  have := Complex.conj_eq_iff_im.mp h_selfconj
  exact this

/-! ## §7 Restatement: mellin at critical 15 IS an `ofReal` cast. -/

/-- **`mellin_f_modif_at_critical_15_eq_ofReal_re`** — the mellin equals the
`ofReal` cast of its real part:
`mellin f_modif ⟨1/4, 15/2⟩ = ((mellin f_modif ⟨1/4, 15/2⟩).re : ℂ)`.

Immediate from `.im = 0` via `Complex.ext`. This exhibits the full
complex Mellin value as a real number lifted into ℂ, ready for
real-integral manipulation. -/
theorem mellin_f_modif_at_critical_15_eq_ofReal_re :
    mellin ((hurwitzEvenFEPair 0).f_modif) ((⟨(1 : ℝ)/4, (15 : ℝ)/2⟩ : ℂ))
      = (((mellin ((hurwitzEvenFEPair 0).f_modif)
            ((⟨(1 : ℝ)/4, (15 : ℝ)/2⟩ : ℂ))).re : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [Complex.ofReal_re]
  · rw [Complex.ofReal_im, mellin_f_modif_at_critical_15_im_eq_zero]

/-! ## §8 Axiom checks. -/

#print axioms
  PrincipiaTractalis.CompletedZeta0MellinRealAtCritical15.half_sub_critical_15_half_eq_neg_critical_15_half
#print axioms
  PrincipiaTractalis.CompletedZeta0MellinRealAtCritical15.f_modif_hurwitzEvenFEPair_zero_im_eq_zero
#print axioms
  PrincipiaTractalis.CompletedZeta0MellinRealAtCritical15.mellin_conj_of_im_zero
#print axioms
  PrincipiaTractalis.CompletedZeta0MellinRealAtCritical15.hurwitzEvenFEPair_zero_Λ₀_symmetry_at_critical_15
#print axioms
  PrincipiaTractalis.CompletedZeta0MellinRealAtCritical15.mellin_f_modif_at_critical_15_conj_eq
#print axioms
  PrincipiaTractalis.CompletedZeta0MellinRealAtCritical15.mellin_f_modif_at_critical_15_im_eq_zero
#print axioms
  PrincipiaTractalis.CompletedZeta0MellinRealAtCritical15.mellin_f_modif_at_critical_15_eq_ofReal_re

end PrincipiaTractalis.CompletedZeta0MellinRealAtCritical15
