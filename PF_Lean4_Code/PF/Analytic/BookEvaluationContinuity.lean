/-
# Continuity of `bookEvaluation` — Monodromy-Shift Component

The analytic-content piece for the s_star IVT framework: continuity of
the **monodromy-shift component** of `bookEvaluation s`.

By definition `polyLogSheet (-1) s z_book = polyLog s z_book +
polyLogMonodromyShift (-1) s z_book`. This file establishes:

* Continuity of `s ↦ (Complex.log z_book)^(s − 1)` on `ℂ` (assuming
  `log z_book ≠ 0`).
* Continuity of `s ↦ Complex.Gamma s` on the half-plane `Re s > 0`.
* Continuity of `s ↦ polyLogMonodromyShift (-1) s z_book` on the
  half-plane `Re s > 0`.

The full continuity of `bookEvaluation` further requires continuity of
`s ↦ polyLog s z_book`, the formal-series component. For `|z_book| = 1`
the series converges only conditionally; the natural continuity comes
from the **Hankel representation** (now mechanized in the 17-module
chain). Bridging the Hankel representation to the formal series is the
remaining open analytic content for completing `bookEvaluation`'s
continuity.

Stage L4 — `bookEvaluation` continuity foundation.
-/

import PF.Analytic.SStarBridge
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

namespace PrincipiaTractalis.Analytic

open Complex

/-! ## Continuity of `s ↦ z₀^(s − 1)` for nonzero base -/

/-- **Continuity of `s ↦ z₀^(s − 1)`** for fixed nonzero base `z₀ ∈ ℂ`.

    Proof: `z₀^w = exp(w · log z₀)` for `z₀ ≠ 0`, a composition of
    continuous functions. -/
theorem continuous_const_cpow {z₀ : ℂ} (hz : z₀ ≠ 0) :
    Continuous (fun s : ℂ => z₀ ^ (s - 1)) := by
  have h_rewrite : (fun s : ℂ => z₀ ^ (s - 1)) =
                   fun s : ℂ => Complex.exp ((s - 1) * Complex.log z₀) := by
    funext s
    rw [Complex.cpow_def_of_ne_zero hz, mul_comm]
  rw [h_rewrite]
  apply Complex.continuous_exp.comp
  exact (continuous_id.sub continuous_const).mul continuous_const

/-! ## Continuity of `Complex.Gamma` on `Re s > 0` -/

/-- **`Γ(s) ≠ 0` for `Re s > 0`**.

    Uses `Complex.Gamma_ne_zero` with the hypothesis `s ≠ -m` for all
    `m : ℕ`, which holds since `Re(-m) ≤ 0 < Re s`. -/
theorem Gamma_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    Complex.Gamma s ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro m h_eq
  have : s.re = -(m : ℝ) := by
    rw [h_eq]; simp
  have : s.re ≤ 0 := by rw [this]; exact neg_nonpos.mpr (Nat.cast_nonneg m)
  linarith

/-- **Continuity of `Complex.Gamma`** at any `s` with `Re s > 0`.

    For `Re s > 0`, `Γ` has no poles, hence is differentiable and
    continuous. Uses `Complex.differentiableAt_Gamma`. -/
theorem continuousAt_Gamma_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    ContinuousAt Complex.Gamma s := by
  have h_diff : DifferentiableAt ℂ Complex.Gamma s := by
    apply Complex.differentiableAt_Gamma
    intro n h_eq
    have h_re : s.re = -(n : ℝ) := by rw [h_eq]; simp
    have : s.re ≤ 0 := by rw [h_re]; exact neg_nonpos.mpr (Nat.cast_nonneg n)
    linarith
  exact h_diff.continuousAt

/-! ## Continuity of `polyLogMonodromyShift (-1) (·) z_book` -/

/-- **Continuity of the `(-1)`-monodromy shift** at `s` with `Re s > 0`,
    assuming `log z_book ≠ 0` (which holds since `z_book ≠ 1`).

    `polyLogMonodromyShift (-1) s z_book =
       2πi · (-1) · (log z_book)^(s−1) / Γ(s)`.

    Each factor is continuous in `s` for `Re s > 0`. -/
theorem continuousAt_polyLogMonodromyShift_book
    (h_log_ne : Complex.log z_book ≠ 0)
    {s : ℂ} (hs : 0 < s.re) :
    ContinuousAt (fun s : ℂ => polyLogMonodromyShift (-1) s z_book) s := by
  unfold polyLogMonodromyShift
  apply ContinuousAt.div
  · apply ContinuousAt.mul continuousAt_const
    exact (continuous_const_cpow h_log_ne).continuousAt
  · exact continuousAt_Gamma_of_re_pos hs
  · exact Gamma_ne_zero_of_re_pos hs

/-! ## Conditional `bookEvaluation` continuity

The full continuity of `bookEvaluation` on `(0, 1)` follows by
combining the monodromy-shift continuity (proven above) with:

1. Continuity of `Complex.re ∘ Complex.ofReal` (immediate).
2. Continuity of `s ↦ polyLog s z_book` on the relevant domain
   (the open analytic content).

For `|z_book| = 1, z_book ≠ 1`, the polylog series `Σ z^n / n^s`
converges only conditionally for `0 < Re s ≤ 1` (Dirichlet test). The
function `s ↦ polyLog s z_book` is continuous via analytic
continuation, which the 17-module Hankel-route chain provides:

```
polyLog s z = (Γ(1-s) / (2πi)) · ∮_H (-t)^(s-1) / (e^t/z - 1) dt
```

The Hankel integral is continuous in `s`, and `Γ(1-s)/(2πi)` is
continuous away from poles. Together they give the polylog
continuity needed.

Bridging the formal `tsum` definition in `PF.Analytic.Polylog` to the
Hankel representation is the remaining open piece — one would need to
prove that the formal `tsum` agrees with the Hankel integral on the
appropriate domain, then transfer continuity through the equality.

With the monodromy-shift continuity now established axiom-clean, the
analytic skeleton of `bookEvaluation`'s continuity is in place.
-/

/-- **Conditional `bookEvaluation` continuity**: given continuity of
    `s ↦ polyLog s z_book` at `s_re_complex` (and the log non-vanishing
    hypothesis), `bookEvaluation` is continuous at `s_re`. -/
theorem continuousAt_bookEvaluation
    (h_log_ne : Complex.log z_book ≠ 0)
    {s_re : ℝ} (hs : 0 < s_re)
    (h_polyLog_cont : ContinuousAt (fun s : ℂ => polyLog s z_book) (s_re : ℂ)) :
    ContinuousAt bookEvaluation s_re := by
  unfold bookEvaluation polyLogSheet
  -- bookEvaluation s = Re (polyLog (s : ℂ) z_book +
  --                       polyLogMonodromyShift (-1) (s : ℂ) z_book)
  -- Take ContinuousAt of each piece, then compose with Complex.re ∘ ofReal.
  have h_cast : ContinuousAt (fun s : ℝ => ((s : ℝ) : ℂ)) s_re :=
    Complex.continuous_ofReal.continuousAt
  have h_mono : ContinuousAt
      (fun s : ℂ => polyLogMonodromyShift (-1) s z_book) (s_re : ℂ) :=
    continuousAt_polyLogMonodromyShift_book h_log_ne
      (by show 0 < ((s_re : ℂ)).re; simp; exact hs)
  have h_sum : ContinuousAt
      (fun s : ℂ => polyLog s z_book + polyLogMonodromyShift (-1) s z_book)
      (s_re : ℂ) :=
    h_polyLog_cont.add h_mono
  have h_comp : ContinuousAt
      (fun s : ℝ => polyLog ((s : ℂ)) z_book +
                    polyLogMonodromyShift (-1) ((s : ℂ)) z_book) s_re :=
    h_sum.comp h_cast
  exact Complex.continuous_re.continuousAt.comp h_comp

end PrincipiaTractalis.Analytic
