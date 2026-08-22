/-
# r309: `completedRiemannZeta₀ → mellin(f_modif)` normalization collapse
#      + threshold conversion `4/901 → 8/901`

★ 2026-08-21 r309 — normalization-collapse landing. Unfolds mathlib's
definitional chain

    `completedRiemannZeta₀ s
       = completedHurwitzZetaEven₀ 0 s
       = (hurwitzEvenFEPair 0).Λ₀ (s / 2) / 2
       = mellin ((hurwitzEvenFEPair 0).f_modif) (s / 2) / 2`

at `s = ⟨1/2, 15⟩` (using r305 `critical_15_half_eq` for the division
computation `s/2 = ⟨1/4, 15/2⟩`), and converts the r308 threshold
`4/901 < (completedRiemannZeta₀ ⟨1/2, 15⟩).re` to
`8/901 < (mellin(f_modif) ⟨1/4, 15/2⟩).re` via
`(z/2).re = z.re/2` and `linarith`.

## Framework-first mathematical status

Pure normalization collapse. All identities used are mathlib
definitional unfolds plus complex-arithmetic normalizations:

- `completedRiemannZeta₀ = completedHurwitzZetaEven₀ 0`   — `def` unfold.
- `completedHurwitzZetaEven₀ a s = (hurwitzEvenFEPair a).Λ₀ (s/2) / 2` — `def` unfold.
- `WeakFEPair.Λ₀ = mellin P.f_modif` — `def` unfold.
- `⟨1/2, 15⟩ / 2 = ⟨1/4, 15/2⟩` — r305 `critical_15_half_eq`.

## What r309 delivers

- `completedRiemannZeta0_at_critical_15_via_mellin :
    completedRiemannZeta₀ ⟨1/2, 15⟩
      = mellin ((hurwitzEvenFEPair 0).f_modif) ⟨1/4, 15/2⟩ / 2` —
  the exact corpus-native reduction to a Mellin transform of the
  modified theta kernel `f_modif`.

- `re_completedZeta0_at_critical_15_eq_re_mellin_half :
    (completedRiemannZeta₀ ⟨1/2, 15⟩).re
      = (mellin ((hurwitzEvenFEPair 0).f_modif) ⟨1/4, 15/2⟩).re / 2` —
  real-part extraction (from `(z/2).re = z.re/2` via mathlib's
  `Complex.div_re` on a real denominator).

- `xi_15_eq_re_mellin_half_minus_correction :
    Xi 15 = (mellin ((hurwitzEvenFEPair 0).f_modif) ⟨1/4, 15/2⟩).re / 2 - 4/901` —
  substituting into r308.

- `Xi_Positive_At_15_iff_re_mellin_gt_8_over_901 :
    Xi_Positive_At_15 ↔
      8/901 < (mellin ((hurwitzEvenFEPair 0).f_modif) ⟨1/4, 15/2⟩).re` —
  the residual restated on the Mellin transform's real part, with the
  factor-of-2 normalization absorbed into the threshold (r308 was
  `4/901 < (completedRiemannZeta₀).re`; r309 is
  `8/901 < (mellin f_modif).re`).

- `Xi_Positive_At_15_from_re_mellin_lower_bound :
    ∀ {a : ℝ}, 8/901 < a →
      a ≤ (mellin ((hurwitzEvenFEPair 0).f_modif) ⟨1/4, 15/2⟩).re →
      Xi_Positive_At_15` — CHAIN-CLOSER on the Mellin threshold.

## Framework-first dependency-reduction ledger

**Before r309** (r308 state): `Xi_Positive_At_15 ↔ 4/901 <
(completedRiemannZeta₀ ⟨1/2, 15⟩).re`. The entire function
`completedRiemannZeta₀` was still opaque relative to the theta kernel
attack.

**After r309**: `Xi_Positive_At_15 ↔ 8/901 < (mellin(f_modif)
⟨1/4, 15/2⟩).re`. The Mellin transform is directly the attack surface;
`f_modif` is explicit piecewise (mathlib's `WeakFEPair.f_modif`):
above `x = 1`, `f_modif x = evenKernel 0 x - 1`; below `x = 1`,
`f_modif x = evenKernel 0 x - x^(-1/2)`.

**Remaining** for r310+:
- r310: eliminate the `(0, 1)` half of the Mellin integral by
  `x ↦ 1/x` substitution using `evenKernel_functional_equation`,
  producing a single integral over `x ∈ [1, ∞)`. At the critical
  Mellin parameter `q = ⟨1/4, 15/2⟩`, the weight `k = 1/2` puts
  `q + conj q = k`, turning paired halves into conjugates and
  producing:
    `Re(mellin(f_modif) q) = 2 ∫₁^∞ (evenKernel 0 x - 1) · x^(-3/4)
                                  · cos((15/2) log x) dx`.
- r311: certified numerical lower bound
  `4/901 < ∫₁^∞ (evenKernel 0 x - 1) · x^(-3/4) · cos((15/2) log x) dx`
  via truncation of the theta series `evenKernel 0 x - 1 = 2 ∑_{n≥1}
  exp(-π n² x)` with certified tail bounds.

## Numerical target check

r308 target: `4/901 ≈ 0.00444` < `Re(completedRiemannZeta₀)`.
r309 target: `8/901 ≈ 0.00888` < `Re(mellin(f_modif))`.

Rough estimate: `(mellin(f_modif) ⟨1/4, 15/2⟩).re ~ 2 · 10⁻²` (twice
the completedRiemannZeta₀ estimate), consistent with the factor of 2.

Book anchors: Ch 20 § 20.4 (RH via Fractal Resonance), Ch 34A § 34A.5.
Paper `principia_fractalis_alpha_skeleton_2026-07-13.pdf` § 6.
-/

import PF.Analytic.Xi15CompletedZeta0Reduction_r308
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven

namespace PrincipiaTractalis.CompletedZeta0MellinReduction

open Complex
open HurwitzZeta
open PrincipiaTractalis.XiRealWitness
open PrincipiaTractalis.UnifiedClayClosureViaRouteBSpecificXiAndFullPinning
open PrincipiaTractalis.Xi15CompletedZeta0Reduction
open PrincipiaTractalis.GammaRAtCritical15

/-! ## §1 Definitional unfolding: `completedRiemannZeta₀ → mellin(f_modif) / 2`. -/

/-- **`completedRiemannZeta0_at_critical_15_via_mellin`** —
the corpus-native reduction:

  `completedRiemannZeta₀ ⟨1/2, 15⟩
     = mellin ((hurwitzEvenFEPair 0).f_modif) ⟨1/4, 15/2⟩ / 2`.

Chain of definitional unfolds:

  `completedRiemannZeta₀ s = completedHurwitzZetaEven₀ 0 s`  (rfl)
  `completedHurwitzZetaEven₀ 0 s = (hurwitzEvenFEPair 0).Λ₀ (s / 2) / 2`  (def)
  `WeakFEPair.Λ₀ = mellin P.f_modif`  (def)

plus `⟨1/2, 15⟩ / 2 = ⟨1/4, 15/2⟩` (r305 `critical_15_half_eq`). -/
theorem completedRiemannZeta0_at_critical_15_via_mellin :
    completedRiemannZeta₀ ((⟨(1 : ℝ)/2, (15 : ℝ)⟩ : ℂ))
      = mellin ((hurwitzEvenFEPair 0).f_modif)
          ((⟨(1 : ℝ)/4, (15 : ℝ)/2⟩ : ℂ)) / 2 := by
  show ((hurwitzEvenFEPair 0).Λ₀ ((⟨(1 : ℝ)/2, (15 : ℝ)⟩ : ℂ) / 2)) / 2 = _
  rw [critical_15_half_eq]
  rfl

/-! ## §2 Real-part extraction: `.re / 2`. -/

/-- **`re_completedZeta0_at_critical_15_eq_re_mellin_half`** —

  `(completedRiemannZeta₀ ⟨1/2, 15⟩).re
     = (mellin ((hurwitzEvenFEPair 0).f_modif) ⟨1/4, 15/2⟩).re / 2`.

From `completedRiemannZeta0_at_critical_15_via_mellin` and
`(z / 2 : ℂ).re = z.re / 2` (Complex division by a real). -/
theorem re_completedZeta0_at_critical_15_eq_re_mellin_half :
    (completedRiemannZeta₀ ((⟨(1 : ℝ)/2, (15 : ℝ)⟩ : ℂ))).re
      = (mellin ((hurwitzEvenFEPair 0).f_modif)
          ((⟨(1 : ℝ)/4, (15 : ℝ)/2⟩ : ℂ))).re / 2 := by
  rw [completedRiemannZeta0_at_critical_15_via_mellin]
  simp [Complex.div_re, Complex.normSq]

/-! ## §3 Xi(15) as `re(mellin) / 2 - 4/901`. -/

/-- **`xi_15_eq_re_mellin_half_minus_correction`** —

  `Xi 15 = (mellin ((hurwitzEvenFEPair 0).f_modif) ⟨1/4, 15/2⟩).re / 2 - 4/901`.

From r308 `xi_15_eq_re_completedZeta0_minus_correction` and
r309 §2. -/
theorem xi_15_eq_re_mellin_half_minus_correction :
    Xi 15
      = (mellin ((hurwitzEvenFEPair 0).f_modif)
          ((⟨(1 : ℝ)/4, (15 : ℝ)/2⟩ : ℂ))).re / 2 - (4 : ℝ)/901 := by
  rw [xi_15_eq_re_completedZeta0_minus_correction,
      re_completedZeta0_at_critical_15_eq_re_mellin_half]

/-! ## §4 Threshold conversion: `4/901 → 8/901` (factor-of-2 absorption). -/

/-- **`Xi_Positive_At_15_iff_re_mellin_gt_8_over_901`** —
the r308 threshold `4/901 < Re(completedRiemannZeta₀)` converts to
`8/901 < Re(mellin(f_modif))` via the factor-of-2 normalization:

  `Xi_Positive_At_15 ↔
     8/901 < (mellin ((hurwitzEvenFEPair 0).f_modif) ⟨1/4, 15/2⟩).re`.

From `Xi_Positive_At_15_iff_re_completedZeta0_gt_correction` (r308) +
`re_completedZeta0_at_critical_15_eq_re_mellin_half` (r309 §2) +
`linarith` for the threshold arithmetic. -/
theorem Xi_Positive_At_15_iff_re_mellin_gt_8_over_901 :
    Xi_Positive_At_15 ↔
      (8 : ℝ)/901
        < (mellin ((hurwitzEvenFEPair 0).f_modif)
            ((⟨(1 : ℝ)/4, (15 : ℝ)/2⟩ : ℂ))).re := by
  rw [Xi_Positive_At_15_iff_re_completedZeta0_gt_correction,
      re_completedZeta0_at_critical_15_eq_re_mellin_half]
  constructor
  · intro h; linarith
  · intro h; linarith

/-! ## §5 THE MELLIN-THRESHOLD CHAIN-CLOSER. -/

/-- **★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★ (r309) Xi_Positive_At_15 CHAIN-CLOSER (Mellin route) ★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★★** —
any certified lower bound on `(mellin ((hurwitzEvenFEPair 0).f_modif)
⟨1/4, 15/2⟩).re` strictly greater than `8/901 ≈ 0.00888` discharges
the aggregate's Xi witness residual via the corpus-native Mellin
route.

r310+ certified numerical enclosure work terminates the discharge by
producing such an `a` via the theta-Mellin integral representation
of the modified kernel `f_modif`. -/
theorem Xi_Positive_At_15_from_re_mellin_lower_bound
    {a : ℝ} (ha : (8 : ℝ)/901 < a)
    (h : a ≤ (mellin ((hurwitzEvenFEPair 0).f_modif)
              ((⟨(1 : ℝ)/4, (15 : ℝ)/2⟩ : ℂ))).re) :
    Xi_Positive_At_15 :=
  Xi_Positive_At_15_iff_re_mellin_gt_8_over_901.mpr (lt_of_lt_of_le ha h)

/-! ## §6 Axiom checks. -/

#print axioms
  PrincipiaTractalis.CompletedZeta0MellinReduction.completedRiemannZeta0_at_critical_15_via_mellin
#print axioms
  PrincipiaTractalis.CompletedZeta0MellinReduction.re_completedZeta0_at_critical_15_eq_re_mellin_half
#print axioms
  PrincipiaTractalis.CompletedZeta0MellinReduction.xi_15_eq_re_mellin_half_minus_correction
#print axioms
  PrincipiaTractalis.CompletedZeta0MellinReduction.Xi_Positive_At_15_iff_re_mellin_gt_8_over_901
#print axioms
  PrincipiaTractalis.CompletedZeta0MellinReduction.Xi_Positive_At_15_from_re_mellin_lower_bound

end PrincipiaTractalis.CompletedZeta0MellinReduction
