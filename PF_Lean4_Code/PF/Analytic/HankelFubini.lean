/-
# Hankel-Polylog Fubini Step — Termwise Integral / Tsum Interchange

This file exposes the **Fubini-step deliverable** for the polylog–Hankel
identity as standalone, top-level theorems. The substantive proofs live
in `PF.Analytic.HankelTermwiseInterchange`; this module re-states the
final results under a `HankelFubini` namespace so that downstream code
can import a focused module containing exactly the interchange capstone
without pulling in the entire per-term Γ-Hankel chain.

## Mathematical content

For `0 < Re s`, `‖z‖ < 1`, `z ≠ 0`:

  `Σ_{n=0}^∞ ∫_(0,∞) (-t)^(s-1) · z^(n+1) · e^(-(n+1)·t) dt`
    `= ∫_(0,∞) (-t)^(s-1) · (Σ_{n=0}^∞ z^(n+1) · e^(-(n+1)·t)) dt`

with the right-hand side simplifying further to the kernel form

  `∫_(0,∞) (-t)^(s-1) · (1 / (e^t / z - 1)) dt`.

## Proof strategy

The proof uses `MeasureTheory.integral_tsum_of_summable_integral_norm`
(Mathlib's standard Fubini–Tonelli for term-by-term integration of a
series of integrable functions). The hypotheses are:

1. **Per-term integrability** (Step 1): `F_n(t) = t^(s-1)·z^(n+1)·e^(-(n+1)t)`
   is integrable on `(0,∞)` for `0 < Re s`. Proved via the norm bound
   `‖F_n(t)‖ ≤ ‖z‖^(n+1) · t^(Re s - 1) · e^(-t)`, dominated by the
   standard Γ integrand.

2. **Per-term norm integral closed form** (Step 2):
   `∫_(0,∞) ‖F_n(t)‖ dt = ‖z‖^(n+1) · (n+1)^(-Re s) · Γ(Re s)`
   via `Real.integral_rpow_mul_exp_neg_mul_Ioi`.

3. **Summability of the L¹ norm series** (Step 3):
   `Σ_n ‖z‖^(n+1) · (n+1)^(-Re s) · Γ(Re s)` converges for
   `0 < Re s` and `‖z‖ < 1`. The geometric factor `‖z‖^(n+1)` is
   already summable; multiplying by `(n+1)^(-Re s) ≤ 1` preserves
   summability.

All steps are axiom-free (depend only on standard mathlib).

## Status

- `HankelFubini.tsum_integral_eq_integral_tsum` — termwise interchange.
- `HankelFubini.integrand_integrable_per_term` — per-term integrability.
- `HankelFubini.summable_integral_norm` — summable majorant condition.
- `HankelFubini.capstone` — capstone reducing the right-hand side to the
  closed kernel form `(t : ℂ)^(s-1) · 1 / (e^t / z - 1)`.

Stage L4 — Hankel-polylog Fubini step (axiom-retirement deliverable #2).
-/

import PF.Analytic.HankelTermwiseInterchange

namespace PrincipiaTractalis.Analytic
namespace HankelFubini

open Complex Filter Topology MeasureTheory Set Real

/-! ## Per-term integrand (re-export) -/

/-- **Per-term polylog-Hankel integrand**:
    `F_n(t) := t^(s-1) · z^(n+1) · e^(-(n+1)·t)`. -/
noncomputable abbrev integrand (s z : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  polylogHankelTerm s z n t

/-! ## Step 1: per-term integrability -/

/-- **Per-term integrability**: `F_n` is integrable on `(0,∞)` for `0 < Re s`. -/
theorem integrand_integrable_per_term {s : ℂ} (hs : 0 < s.re) (z : ℂ) (n : ℕ) :
    IntegrableOn (integrand s z n) (Ioi (0 : ℝ)) :=
  polylogHankelTerm_integrable hs z n

/-! ## Step 2: per-term norm-integral closed form -/

/-- **Closed form for the per-term L¹ norm integral**:
    `∫_(0,∞) ‖F_n(t)‖ dt = ‖z‖^(n+1) · (n+1)^(-Re s) · Γ(Re s)`. -/
theorem integral_norm_per_term {s : ℂ} (hs : 0 < s.re) (z : ℂ) (n : ℕ) :
    ∫ t in Ioi (0 : ℝ), ‖integrand s z n t‖ =
    ‖z‖ ^ (n + 1) * (((n + 1 : ℕ) : ℝ) ^ (-s.re) * Real.Gamma s.re) :=
  polylogHankelTerm_integral_norm_eq hs z n

/-! ## Step 3: summability of the L¹ norm series (the dominating majorant) -/

/-- **Summable majorant**: the series `Σ_n ∫ ‖F_n(t)‖ dt` converges
    for `0 < Re s` and `‖z‖ < 1`. -/
theorem summable_integral_norm
    {s : ℂ} (hs : 0 < s.re) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => ∫ t in Ioi (0 : ℝ), ‖integrand s z n t‖) :=
  summable_integral_norm_polylogHankel hs hz

/-! ## Step 4: the Fubini interchange -/

/-- **Termwise tsum/integral interchange** — the primary deliverable.

    For `0 < Re s` and `‖z‖ < 1`:

      `Σ_n ∫_(0,∞) F_n(t) dt = ∫_(0,∞) Σ_n F_n(t) dt`.

    Proved by applying `MeasureTheory.integral_tsum_of_summable_integral_norm`
    to the per-term integrability of `F_n` and the summable majorant
    `‖z‖^(n+1) · (n+1)^(-Re s) · Γ(Re s)`. -/
theorem tsum_integral_eq_integral_tsum
    {s : ℂ} (hs : 0 < s.re) {z : ℂ} (hz : ‖z‖ < 1) :
    ∑' n : ℕ, ∫ t in Ioi (0 : ℝ), integrand s z n t =
    ∫ t in Ioi (0 : ℝ), ∑' n : ℕ, integrand s z n t :=
  polylogHankel_tsum_integral_eq_integral_tsum hs hz

/-! ## Step 5: identification with the kernel form (capstone) -/

/-- **Capstone**: the tsum-of-integrals equals the integral against the
    Hankel kernel `1 / (e^t / z - 1)`.

    For `0 < Re s`, `‖z‖ < 1`, `z ≠ 0`:

      `Σ_n ∫_(0,∞) F_n(t) dt = ∫_(0,∞) t^(s-1) · 1/(e^t/z - 1) dt`. -/
theorem capstone
    {s : ℂ} (hs : 0 < s.re) {z : ℂ} (hz : ‖z‖ < 1) (hz_ne : z ≠ 0) :
    ∑' n : ℕ, ∫ t in Ioi (0 : ℝ), integrand s z n t =
    ∫ t in Ioi (0 : ℝ),
      (t : ℂ) ^ (s - 1) * ((1 : ℂ) / (Complex.exp (t : ℂ) / z - 1)) :=
  polylogHankel_termwise_interchange_capstone hs hz hz_ne

end HankelFubini
end PrincipiaTractalis.Analytic
