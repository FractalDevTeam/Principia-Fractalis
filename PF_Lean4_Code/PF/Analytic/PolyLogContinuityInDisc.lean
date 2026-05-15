/-
# Polylog Continuity for `|z| < 1`

The continuity transfer for `polyLog s z` in `s ∈ ℂ` for fixed `z` in
the disc of convergence `|z| < 1`, via mathlib's `continuousOn_tsum`
(Weierstrass M-test).

For our target `z_book` with `|z_book| = 1`, this does NOT directly
apply — see the documentation in `PolyLogContinuity.lean` for the
analytic-continuation path.

Stage L4 — Polylog continuity in disc of convergence.
-/

import PF.Analytic.PolyLogContinuity
import Mathlib.Analysis.Normed.Group.FunctionSeries

namespace PrincipiaTractalis.Analytic

open Complex

/-! ## Summability of the geometric-shifted series -/

/-- **Summability of `n ↦ ‖z‖^(n+1)`** for `‖z‖ < 1`. -/
theorem summable_norm_pow_succ (z : ℂ) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => ‖z‖^(n+1)) := by
  have h_geom : Summable (fun n : ℕ => ‖z‖^n) :=
    summable_geometric_of_lt_one (norm_nonneg z) hz
  have : Summable (fun n : ℕ => ‖z‖ * ‖z‖^n) := h_geom.mul_left ‖z‖
  refine this.congr ?_
  intro n
  rw [pow_succ, mul_comm]

/-! ## Continuity of polylog on the half-plane for `|z| < 1` -/

/-- **★ Polylog continuity for `|z| < 1` on the half-plane `Re s ≥ 0`**:

      `ContinuousOn (fun s => polyLog s z) {s | 0 ≤ s.re}`.

    Direct application of `continuousOn_tsum` (Weierstrass M-test).
    Uses:
    * `continuous_polyLog_term` for termwise continuity.
    * `norm_polyLog_term_le` (from `PF.Analytic.Polylog`) for the bound.
    * `summable_norm_pow_succ` for the summable dominating series. -/
theorem polyLog_continuousOn_of_norm_lt_one
    (z : ℂ) (hz : ‖z‖ < 1) :
    ContinuousOn (fun s : ℂ => polyLog s z) {s : ℂ | 0 ≤ s.re} := by
  unfold polyLog
  refine continuousOn_tsum ?_ (summable_norm_pow_succ z hz) ?_
  · intro n
    exact (continuous_polyLog_term z n).continuousOn
  · intro n s hs
    exact norm_polyLog_term_le hs n

/-! ## Pointwise continuity on `Re s > 0` -/

/-- **Openness of the half-plane `Re s > 0`**. -/
theorem isOpen_re_pos : IsOpen {s : ℂ | 0 < s.re} :=
  isOpen_lt continuous_const Complex.continuous_re

/-- **Pointwise continuity** at each `s` with `Re s > 0`, for `|z| < 1`.

    The set `{s | 0 ≤ s.re}` is a neighborhood of `s` when `0 < s.re`
    (via the strictly open `{s | 0 < s.re}` contained in it). -/
theorem continuousAt_polyLog_of_norm_lt_one
    (z : ℂ) (hz : ‖z‖ < 1) {s : ℂ} (hs : 0 < s.re) :
    ContinuousAt (fun s : ℂ => polyLog s z) s := by
  have h_continuousOn := polyLog_continuousOn_of_norm_lt_one z hz
  have h_nhds : {w : ℂ | 0 ≤ w.re} ∈ nhds s :=
    Filter.mem_of_superset (isOpen_re_pos.mem_nhds hs)
      (fun w hw => show 0 ≤ w.re from le_of_lt hw)
  exact (h_continuousOn s hs.le).continuousAt h_nhds

/-! ## Documentation for `|z| = 1` case

For `z_book` with `‖z_book‖ = 1`, the disc-of-convergence argument
above does not apply: the bound `‖z‖^(n+1)` is not summable (it's `1`
for `‖z‖ = 1`). Polylog continuity at z_book requires:

1. **Conditional-convergence handling**: the series converges only
   conditionally (Dirichlet test, for `Re s > 0, z ≠ 1`).
2. **Analytic continuation**: via Hankel-route representation (the
   17-module chain provides the underlying Γ-reciprocal formula).
3. **Continuity transfer**: from the Hankel representation's
   continuity (provable from Γ-continuity + the proven DCT) to polyLog.

The polylog Hankel identity:
  `polyLog s z = (Γ(1-s) / 2πi) · ∮_H (-t)^(s-1) / (e^t/z - 1) dt`

follows from the proven Γ-reciprocal Hankel formula via geometric-
series expansion and termwise integration. This is the remaining
substantive analytic deliverable.
-/

end PrincipiaTractalis.Analytic
