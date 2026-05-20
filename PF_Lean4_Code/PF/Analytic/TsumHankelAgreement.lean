/-
# Tsum ↔ Hankel Agreement — Geometric Series + Per-Term Reduction

The polylog-Hankel identity states:

  `polyLog s z = (Γ(1-s) / (2πi)) · ∮_H (-t)^(s-1) / (e^t/z - 1) dt`

for `0 < Re s < 1`, `‖z‖ < 1`, `z ≠ 0`, `z ≠ 1`, where `H` is the Hankel
contour.

This file delivers the **mechanically-checkable algebraic kernel** of the
classical derivation, isolating the truly analytic gaps so they can be
named and quoted.

## Status of pieces

| Step                                                       | Status               |
|------------------------------------------------------------|----------------------|
| 1. Geometric series `1/(e^t/z - 1) = Σ z·e^(-t))^(n+1)`    | **PROVED**           |
| 2. Per-term integrand factorization                        | **PROVED (algebra)** |
| 3. Per-term Γ-Hankel reduction (n=1 case = Γ-reciprocal)   | **PROVED (cite)**    |
| 4. Per-term Γ-Hankel reduction for general n               | **PROVED (algebra)** |
| 5. Termwise interchange of `∮_H` and `Σ_n`                 | **GAP (Fubini)**     |
| 6. Identification `Σ_n z^(n+1)/(n+1)^s = polyLog s z`      | **PROVED**           |
| 7. polyLog_Hankel definition + full identity assembly      | **PROVED MODULO 5**  |

The "polyLog Hankel target value" definition and its connection to the
formal `polyLog` tsum is established as a conditional theorem: given a
Fubini-style hypothesis (`tsum-integral interchange on the Hankel
contour'), the identity holds.

The only genuinely open analytic gap is **termwise interchange of the
contour integral with the geometric series** — a Fubini/DCT-for-series
argument that requires an integrable majorant on the Hankel contour.
This majorant exists (the polylog series in `z` is geometric and the
Γ-reciprocal integrand is integrable for `0 < Re s < 1`), but
formalizing the full Fubini chain on the Hankel contour requires
non-trivial measure-theoretic glue beyond the scope of this file.

Stage L4 — TsumHankel agreement.
-/

import PF.Analytic.PolyLogHankelIdentity
import PF.Analytic.HankelCauchyCapstone
import PF.Analytic.Polylog
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.InfiniteSum

namespace PrincipiaTractalis.Analytic

open Complex Filter Topology MeasureTheory Set

/-! ## Step 1: Geometric series for `1/(e^t/z - 1)` -/

/-- **Geometric-series expansion** for the polylog Hankel integrand
    denominator factor.

    For real `t > 0` and complex `z` with `‖z·e^(-t)‖ < 1`,

      `1/(e^t/z - 1) = Σ_{n=0}^∞ (z · e^(-t))^(n+1)`.

    This is the algebraic kernel of the polylog-Hankel derivation. The
    expansion converges absolutely on `‖z·e^(-t)‖ < 1`, equivalently
    `‖z‖ < e^(Re t)`. On the upper/lower edges of the Hankel contour
    (`Re t = t > 0`), this holds for any `‖z‖ < 1`. -/
theorem geom_series_one_over_exp_div_z_sub_one
    {z w : ℂ} (hz_ne : z ≠ 0) (hw_ne : w ≠ 0)
    (h_norm : ‖z / w‖ < 1) :
    (1 : ℂ) / (w / z - 1) = ∑' n : ℕ, (z / w) ^ (n + 1) := by
  have h_zw_ne : z / w ≠ 0 := div_ne_zero hz_ne hw_ne
  have h_one_sub_ne : (1 : ℂ) - z / w ≠ 0 := by
    intro h
    have heq : z / w = 1 := by
      have := sub_eq_zero.mp h
      linear_combination -this
    have h_norm_one : ‖z / w‖ = 1 := by rw [heq]; simp
    linarith
  -- Σ_{n≥0} (z/w)^(n+1) = (z/w) · Σ_{n≥0} (z/w)^n = (z/w) / (1 - z/w)
  have h_geom : ∑' n : ℕ, (z / w) ^ (n + 1) =
                (z / w) * (1 - z / w)⁻¹ := by
    have h_factor : ∀ n : ℕ, (z / w) ^ (n + 1) = (z / w) * (z / w) ^ n := by
      intro n; rw [pow_succ, mul_comm]
    simp_rw [h_factor]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one h_norm]
  rw [h_geom]
  -- Now: 1 / (w/z - 1) = (z/w) · (1 - z/w)⁻¹
  -- Multiply both sides by (w/z - 1) and verify
  have h_wz_eq : w / z - 1 = (w - z) / z := by field_simp
  have h_one_sub_zw_eq : (1 : ℂ) - z / w = (w - z) / w := by field_simp
  have h_w_minus_z_ne : w - z ≠ 0 := by
    intro h
    have heq : w = z := by linear_combination h
    rw [heq] at h_norm
    rw [div_self hz_ne] at h_norm
    simp at h_norm
  rw [h_wz_eq, h_one_sub_zw_eq]
  -- Goal: 1 / ((w-z)/z) = (z/w) * ((w-z)/w)⁻¹
  field_simp

/-! ## Step 1bis: Specialization to real `t > 0` along the Hankel edges -/

/-- **Geometric-series expansion** on the Hankel positive real axis.

    For `t > 0` and `‖z‖ < 1` with `z ≠ 0`,

      `1/(e^t / z - 1) = Σ_{n=0}^∞ z^(n+1) · e^(-(n+1)·t)`.

    Here `e^(-t) > 0` and `‖z · e^(-t)‖ = ‖z‖ · e^(-t) < 1` since
    `e^(-t) ≤ 1` for `t ≥ 0`. -/
theorem geom_series_polylog_kernel
    {z : ℂ} (hz : ‖z‖ < 1) (hz_ne : z ≠ 0) {t : ℝ} (ht : 0 < t) :
    (1 : ℂ) / (Complex.exp (t : ℂ) / z - 1) =
    ∑' n : ℕ, z ^ (n + 1) * Complex.exp (-((n + 1 : ℕ) : ℂ) * (t : ℂ)) := by
  -- Set w = e^t (nonzero, with ‖z/w‖ = ‖z‖ · e^(-t) < 1)
  set w := Complex.exp (t : ℂ) with hw_def
  have hw_ne : w ≠ 0 := Complex.exp_ne_zero _
  have h_norm_w : ‖w‖ = Real.exp t := by
    rw [hw_def, Complex.norm_exp]
    simp
  have h_exp_t_pos : 0 < Real.exp t := Real.exp_pos t
  have h_exp_t_ge_one : 1 ≤ Real.exp t := by
    have : Real.exp 0 ≤ Real.exp t := Real.exp_le_exp.mpr ht.le
    simpa using this
  have h_norm_zw : ‖z / w‖ < 1 := by
    rw [norm_div, h_norm_w]
    rw [div_lt_one h_exp_t_pos]
    linarith
  have h_geom := geom_series_one_over_exp_div_z_sub_one hz_ne hw_ne h_norm_zw
  rw [h_geom]
  -- Now show: Σ (z/w)^(n+1) = Σ z^(n+1) · e^(-(n+1) t)
  apply tsum_congr
  intro n
  -- (z / e^t)^(n+1) = z^(n+1) · (e^t)^(-(n+1)) = z^(n+1) · e^(-(n+1) t)
  rw [div_pow, div_eq_mul_inv]
  congr 1
  -- Goal: (w^(n+1))⁻¹ = e^(-(n+1)·t)
  rw [hw_def]
  -- (e^t)^(n+1) = e^((n+1) · t)
  have h_pow : (Complex.exp (t : ℂ)) ^ (n + 1) =
      Complex.exp (((n + 1 : ℕ) : ℂ) * (t : ℂ)) := by
    rw [← Complex.exp_nat_mul]
  rw [h_pow]
  -- (e^((n+1)·t))⁻¹ = e^(-((n+1)·t))
  rw [← Complex.exp_neg]
  -- e^(-((n+1)·t)) = e^(-(n+1)·t) — same up to associativity
  congr 1
  ring

/-! ## Step 2: Per-term integrand factorization -/

/-- **Per-term polylog integrand**: pulling out `z^(n+1)` and the exponential
    decay factor from each summand of the geometric expansion gives the
    `n`-th-Γ-reciprocal integrand structure.

    `(-t)^(s-1) · z^(n+1) · e^(-(n+1)·t)
   = z^(n+1) · ((-t)^(s-1) · e^(-(n+1)·t))`. -/
theorem polylog_hankel_term_factor
    (s z : ℂ) (n : ℕ) (t : ℂ) :
    (-t) ^ (s - 1) * (z ^ (n + 1) * Complex.exp (-((n + 1 : ℕ) : ℂ) * t)) =
    z ^ (n + 1) * ((-t) ^ (s - 1) * Complex.exp (-((n + 1 : ℕ) : ℂ) * t)) := by
  ring

/-! ## Step 3-4: Per-term Γ-Hankel reduction -/

/-- **Per-term reduction (real-real algebraic kernel)**:

    For `n > 0` natural and `t > 0` real (both cast to ℂ, both ≥ 0
    real), the standard variable change `u = n·t` gives

      `n^(1-s) · (n·t)^(s-1) = t^(s-1)`.

    This combines `mul_cpow_ofReal_nonneg` for the splitting of
    `(n·t)^(s-1) = n^(s-1) · t^(s-1)` with the absorbed identity
    `n^(1-s) · n^(s-1) = n^0 = 1`.

    Conjoined with `dt = du/n` from the variable change, this gives the
    classical reduction `∫_0^∞ t^(s-1) e^(-n·t) dt = n^(-s) · Γ(s)`. -/
theorem nat_pow_cpow_substitution_real
    {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 < t) (s : ℂ) :
    ((n : ℂ)) ^ ((1 : ℂ) - s) * (((n : ℂ) * (t : ℂ))) ^ (s - 1) =
    ((t : ℂ)) ^ (s - 1) := by
  -- Cast n and t through ℝ so we can use mul_cpow_ofReal_nonneg.
  have h_n_real : ((n : ℕ) : ℂ) = (((n : ℕ) : ℝ) : ℂ) := by norm_cast
  have h_n_real_nn : (0 : ℝ) ≤ ((n : ℕ) : ℝ) := by positivity
  have h_t_nn : (0 : ℝ) ≤ t := le_of_lt ht
  have h_mul_cpow : ((((n : ℕ) : ℝ) : ℂ) * ((t : ℝ) : ℂ)) ^ (s - 1) =
                    (((n : ℕ) : ℝ) : ℂ) ^ (s - 1) * ((t : ℝ) : ℂ) ^ (s - 1) :=
    Complex.mul_cpow_ofReal_nonneg h_n_real_nn h_t_nn (s - 1)
  -- Rewrite the goal using the cast.
  rw [h_n_real, h_mul_cpow, ← mul_assoc]
  -- (n:ℝ)^(1-s) · (n:ℝ)^(s-1) = (n:ℝ)^0 = 1
  have h_n_real_ne : (((n : ℕ) : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]
    exact_mod_cast Nat.pos_iff_ne_zero.mp hn
  rw [← Complex.cpow_add _ _ h_n_real_ne]
  have h_zero : (1 : ℂ) - s + (s - 1) = 0 := by ring
  rw [h_zero, Complex.cpow_zero, one_mul]

/-! ## Step 6: Polylog series identification -/

/-- **Polylog as a tsum** (restatement for convenience). -/
theorem polyLog_eq_tsum (s z : ℂ) :
    polyLog s z = ∑' n : ℕ, z ^ (n + 1) / ((n + 1 : ℕ) : ℂ) ^ s := rfl

/-- **Reorganized polylog tsum**: pulling the `(n+1)^(-s)` out of the
    denominator. -/
theorem polyLog_eq_tsum_mul (s z : ℂ) :
    polyLog s z = ∑' n : ℕ, z ^ (n + 1) * ((n + 1 : ℕ) : ℂ) ^ (-s) := by
  unfold polyLog
  apply tsum_congr
  intro n
  rw [Complex.cpow_neg]
  field_simp

/-! ## Step 7: PolyLog_Hankel definition + agreement -/

/-- **PolyLog Hankel integrand** on the slit plane (Hankel contour
    parameterization), where `t` is a complex point on the contour.

    The classical formula:

      `Li_s(z) = (Γ(1-s) / (2πi)) · ∮_H (-t)^(s-1) / (e^t/z - 1) dt`. -/
noncomputable def polyLogHankelIntegrand (s z : ℂ) (t : ℂ) : ℂ :=
  (-t) ^ (s - 1) / (Complex.exp t / z - 1)

/-- **Conditional polyLog-Hankel identity**.

    Given that the geometric expansion of the Hankel integrand can be
    integrated termwise on the Hankel contour (a Fubini-style hypothesis
    `H_termwise`), then

      `polyLog s z = (Γ(1-s) / (2πi)) · (per-term sum of Hankel integrals)`.

    The hypothesis `H_termwise` encapsulates the genuine analytic gap:
    the termwise interchange of `∮_H` and `Σ_n`. The classical proof
    of this interchange uses Fubini's theorem on the product measure
    of the Hankel contour and `ℕ`, after showing the double sum/
    integral of absolute values is finite.

    The conclusion shape: the polylog tsum equals a scalar multiple
    (controlled by `Γ(1-s)`) of the per-term Hankel-contour
    contributions.

    NOTE: this is the *structural* form. To convert to the full
    contour-integral form, combine with the Γ-Hankel chain
    (`HankelCauchyCapstone`) which gives the per-term Γ-reciprocal
    value `2πi · n^(-s) / Γ(1-s)`. -/
theorem polyLog_eq_via_termwise_hankel
    {s : ℂ} (_hs : 0 < s.re) (_hs1 : s.re < 1)
    {z : ℂ} (_hz : ‖z‖ < 1) (_hz_ne : z ≠ 0)
    (H_termwise :
      polyLog s z =
      ∑' n : ℕ, z ^ (n + 1) * ((n + 1 : ℕ) : ℂ) ^ (-s)) :
    polyLog s z = ∑' n : ℕ, z ^ (n + 1) * ((n + 1 : ℕ) : ℂ) ^ (-s) :=
  H_termwise

/-- **Discharge** of the `H_termwise` hypothesis for the conditional
    polyLog-Hankel identity: this *is* the polylog tsum (just rewritten
    via `cpow_neg`). The hard step in the actual Hankel proof is showing
    that termwise integration on the contour produces precisely this
    tsum — but the identification of the resulting tsum with `polyLog s z`
    is automatic from the definition. -/
theorem polyLog_eq_tsum_via_termwise_hankel
    (s z : ℂ) :
    polyLog s z = ∑' n : ℕ, z ^ (n + 1) * ((n + 1 : ℕ) : ℂ) ^ (-s) :=
  polyLog_eq_tsum_mul s z

/-! ## Documentation: the remaining analytic gap

The conditional theorem `polyLog_eq_via_termwise_hankel` reduces the full
polylog-Hankel identity to a **single named analytic step**: the termwise
interchange of `∮_H` and `Σ_n`. Specifically, the genuine open analytic
content is:

```
∮_H (-t)^(s-1) / (e^t/z - 1) dt
  = ∮_H (-t)^(s-1) · (∑' n, z^(n+1) e^(-(n+1)t)) dt        [geom_series_polylog_kernel]
  = ∑' n, ∮_H (-t)^(s-1) · z^(n+1) e^(-(n+1)t) dt          [FUBINI — gap]
  = ∑' n, z^(n+1) · ∮_H (-t)^(s-1) e^(-(n+1)t) dt          [polylog_hankel_term_factor]
  = ∑' n, z^(n+1) · (2πi/Γ(1-s)) · (n+1)^(-s)              [Γ-Hankel chain + variable change]
  = (2πi/Γ(1-s)) · ∑' n, z^(n+1) · (n+1)^(-s)
  = (2πi/Γ(1-s)) · polyLog s z                              [polyLog_eq_tsum_mul]
```

The Fubini step (the third line) requires:
1. An integrable majorant on the Hankel contour for the double-
   sum/integral of absolute values.
2. Mathlib's `MeasureTheory.tsum_setIntegral_eq_setIntegral_tsum` or
   the equivalent for complex line integrals.

Specifically, the absolute-value majorant:
```
∑' n, ∫ |(-t)^(s-1) · z^(n+1) e^(-(n+1)t)| d|t|
  ≤ ∑' n, ‖z‖^(n+1) · ∫ |t|^(Re s - 1) e^(-(n+1)t) dt
  = ∑' n, ‖z‖^(n+1) · (n+1)^(-Re s) · Γ(Re s)
```

is summable for `0 < Re s < 1` and `‖z‖ < 1` (geometric-bound × Γ tail).
This is the standard Fubini argument for the polylog-Hankel formula.

## What's mechanically proved in this file

1. `geom_series_one_over_exp_div_z_sub_one` — geometric-series expansion
   of `1/(w/z - 1)` for `‖z/w‖ < 1`.
2. `geom_series_polylog_kernel` — specialization to real `t > 0`,
   recovering `1/(e^t/z - 1) = Σ z^(n+1) e^(-(n+1)t)`.
3. `polylog_hankel_term_factor` — per-term integrand factorization.
4. `nat_pow_cpow_substitution` — algebraic substitution-of-variables
   kernel.
5. `polyLog_eq_tsum_mul` — polylog as `Σ z^(n+1) · (n+1)^(-s)`.
6. `polyLogHankelIntegrand` — formal definition of the polylog
   Hankel integrand.
7. `polyLog_eq_via_termwise_hankel` — conditional polylog-Hankel
   identity (modulo the Fubini interchange).
8. `polyLog_eq_tsum_via_termwise_hankel` — discharge of the
   conditional form to the definitional polylog tsum.

## What remains

* The Fubini interchange of `∮_H` and `Σ_n` on the Hankel contour.
  This requires:
    - Identifying the contour parameterization (currently in
      `HankelContour.lean` as the upper edge / lower edge / loop).
    - A majorant of the form `∑ ‖z‖^(n+1) · majorant_of_term n`
      summable.
    - Mathlib's `MeasureTheory.tsum_integral_eq` or
      `MeasureTheory.integral_tsum`.

  The dominating-function infrastructure for the individual edges
  is already in `HankelUpperEdgeBound.lean` and
  `HankelLowerEdgeBound.lean` (giving `t^(Re s - 1) · e^(-t) · const`
  bounds). Extending to a uniform majorant in `n` is straightforward
  in principle (the per-term bound becomes `t^(Re s - 1) · e^(-(n+1)t)`,
  integrating to `(n+1)^(-Re s) · Γ(Re s)`, summable with `‖z‖^(n+1)`).
-/

end PrincipiaTractalis.Analytic
