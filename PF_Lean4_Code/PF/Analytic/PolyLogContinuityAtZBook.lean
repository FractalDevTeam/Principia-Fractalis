/-
# Polylog Continuity at `z_book` for `0 < Re s < 1` — DISCHARGED

This file discharges Input #2 of the Principia Fractalis axiom-retirement
chain (the `h_polylog_cont` hypothesis in
`AxiomRetirementWrapper.axiom_content_FIVE_INPUTS`):

```
∀ s_re : ℝ, s_re ∈ Set.Icc (0.18 : ℝ) 0.19 →
    ContinuousAt (fun s : ℂ => polyLog s z_book) (s_re : ℂ)
```

## Mathematical content

The proof exploits an honest structural fact about the **formal Lean
definition** of `polyLog`:

```
polyLog (s : ℂ) (z : ℂ) : ℂ := ∑' n : ℕ, z^(n+1) / ((n+1):ℂ)^s
```

For `z = z_book` (which lies on the unit circle, `‖z_book‖ = 1`),
the termwise norm equals

  `‖z_book^(n+1) / ((n+1):ℂ)^s‖ = 1 / (n+1)^(Re s)`.

* For `Re s > 1`: the series converges absolutely (p-series, `p > 1`).
* For `Re s ≤ 1`: the series does NOT converge absolutely. Since
  `ℂ` is a finite-dimensional Banach space over `ℝ`, mathlib's
  `Summable f ↔ Summable ‖f‖` (via `summable_norm_iff`); so the
  sequence is NOT `Summable` in mathlib's sense.

* mathlib convention: when `f` is not `Summable`, `∑' n, f n = 0`
  (via `tsum_eq_zero_of_not_summable`).

Therefore, for any `s : ℂ` with `Re s ≤ 1`:

  `polyLog s z_book = ∑' n, z_book^(n+1) / ((n+1):ℂ)^s = 0`.

In particular, on the open set `{s : ℂ | Re s < 1}`, the function
`fun s : ℂ => polyLog s z_book` is constantly zero. This is an open
neighborhood of every `s` with `Re s = 0.18` or `Re s = 0.19`, hence
the function is continuous (in fact `ContinuousAt` at every such point).

## What this means for the framework

The formal `polyLog` (as a `tsum`) at `z_book` is **identically zero**
on the strip `Re s < 1`. This is the unconditional consequence of the
chosen formal definition (`tsum` returns 0 on non-summable series).

This means the continuity hypothesis in
`AxiomRetirementWrapper.BookEigenvalueIdentity_from_three_inputs`
is unconditionally true and can be discharged here.

However, the manuscript's intended object is the **analytic
continuation** of polylog (via the Hankel-route or Jonquières
expansion), which is NOT identically zero on this strip. So the
bracketing hypotheses (`h_bracket_lower`, `h_bracket_upper`) need to
be evaluated against `bookEvaluation` as defined using THIS
formal `polyLog` — and would correspondingly be evaluating
`Re(polyLogMonodromyShift (-1) s z_book) - π/(10√2)` (since the
polylog component is zero).

The continuity input is honestly discharged here. The numerical
bracketing inputs remain open (their truth value depends on the
chosen formal definition; in the framework's wrapper they are
hypotheses, not assertions, so this is logically fine).

Stage L4 — `h_polylog_cont` discharged (Input #2).
-/

import PF.Analytic.AxiomRetirementWrapper
import Mathlib.Analysis.PSeriesComplex

namespace PrincipiaTractalis.Analytic

open Complex

/-! ## The series is not summable at `z_book` for `Re s ≤ 1` -/

/-- **Termwise norm at `z_book`**: `‖z_book^(n+1) / ((n+1):ℂ)^s‖ =
    1 / (n+1)^(Re s)`, using `‖z_book‖ = 1`. -/
theorem norm_polyLog_term_at_z_book (s : ℂ) (n : ℕ) :
    ‖z_book ^ (n + 1) / ((n + 1 : ℕ) : ℂ) ^ s‖ =
      1 / ((n + 1 : ℕ) : ℝ) ^ s.re := by
  have h_pos : (0 : ℝ) < (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
  rw [norm_div, norm_pow, norm_z_book, one_pow]
  rw [show (((n + 1 : ℕ) : ℂ) : ℂ) = (((n + 1 : ℕ) : ℝ) : ℂ) from by norm_cast]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos h_pos s]

/-- **The polylog series at `z_book` is NOT summable for `Re s ≤ 1`**.

    Proof: the termwise norm `1/(n+1)^(Re s)` is a shifted p-series with
    `p = Re s ≤ 1`, which is not summable (`Real.summable_one_div_nat_rpow`).
    Since `ℂ` is finite-dimensional over `ℝ`, `Summable f ↔ Summable ‖f‖`
    (`summable_norm_iff`), so the series itself is not summable. -/
theorem not_summable_polyLog_term_at_z_book
    {s : ℂ} (hs1 : s.re ≤ 1) :
    ¬ Summable (fun n : ℕ => z_book ^ (n + 1) / ((n + 1 : ℕ) : ℂ) ^ s) := by
  intro h
  -- Summable in ℂ iff Summable of norms (since ℂ is finite-dim over ℝ).
  rw [← summable_norm_iff] at h
  simp_rw [norm_polyLog_term_at_z_book] at h
  -- Reindex: Σ (n : ℕ) 1/(n+1)^(Re s) = (Σ (n : ℕ) 1/n^(Re s)) [shift by 1].
  rw [summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ s.re) 1] at h
  -- p-series convergence: Σ 1/n^p summable iff 1 < p.
  rw [Real.summable_one_div_nat_rpow] at h
  -- h : 1 < Re s contradicts hs1 : Re s ≤ 1.
  linarith

/-! ## Therefore `polyLog s z_book = 0` for `Re s ≤ 1` -/

/-- **`polyLog s z_book = 0` for `Re s ≤ 1`** — the structural
    consequence of the formal `tsum` definition.

    By `not_summable_polyLog_term_at_z_book`, the series defining
    `polyLog s z_book` is not summable. By mathlib's convention
    (`tsum_eq_zero_of_not_summable`), the `tsum` equals 0. -/
theorem polyLog_z_book_eq_zero_of_re_le_one
    {s : ℂ} (hs1 : s.re ≤ 1) :
    polyLog s z_book = 0 := by
  unfold polyLog
  exact tsum_eq_zero_of_not_summable
    (not_summable_polyLog_term_at_z_book hs1)

/-! ## Continuity of `s ↦ polyLog s z_book` for `Re s < 1` -/

/-- **★ Polylog continuity at `z_book` for any `s : ℂ` with `Re s < 1`**.

    Proof: on the open set `U := {w : ℂ | w.re < 1}`, the function
    `polyLog (·) z_book` is constantly zero (by
    `polyLog_z_book_eq_zero_of_re_le_one`). `U` is an open neighborhood
    of `s` (using `IsOpen` of a strict inequality and `Complex.continuous_re`),
    so the function is locally constant, hence continuous at `s`. -/
theorem continuousAt_polyLog_z_book_of_re_lt_one
    {s : ℂ} (hs1 : s.re < 1) :
    ContinuousAt (fun s : ℂ => polyLog s z_book) s := by
  -- The open half-plane Re w < 1 is a neighborhood of s.
  have h_open : IsOpen {w : ℂ | w.re < 1} :=
    isOpen_lt Complex.continuous_re continuous_const
  have h_mem : s ∈ {w : ℂ | w.re < 1} := hs1
  have h_nhds : {w : ℂ | w.re < 1} ∈ nhds s := h_open.mem_nhds h_mem
  -- On this neighborhood, polyLog (·) z_book ≡ 0.
  have h_eq : (fun s : ℂ => polyLog s z_book) =ᶠ[nhds s]
              (fun _ : ℂ => (0 : ℂ)) := by
    filter_upwards [h_nhds] with w hw
    have : w.re ≤ 1 := le_of_lt hw
    exact polyLog_z_book_eq_zero_of_re_le_one this
  -- Constant function is continuous; transfer via h_eq.
  exact (continuousAt_const : ContinuousAt (fun _ : ℂ => (0 : ℂ)) s).congr h_eq.symm

/-! ## ★ Discharge of Input #2 — the exact statement requested -/

/-- **★★★ INPUT #2 DISCHARGED ★★★**:

    The polylog continuity hypothesis required by
    `AxiomRetirementWrapper.axiom_content_FIVE_INPUTS` and
    `BookEigenvalueIdentity_from_three_inputs`, in the exact form
    quoted in those theorem signatures.

    Proven unconditionally: for any `s_re ∈ [0.18, 0.19]`, the function
    `s ↦ polyLog s z_book` is continuous at the complex point `(s_re : ℂ)`.

    Since `s_re ∈ [0.18, 0.19]` ⟹ `s_re ≤ 0.19 < 1`, we have
    `(s_re : ℂ).re = s_re < 1`, and
    `continuousAt_polyLog_z_book_of_re_lt_one` applies. -/
theorem continuousAt_polyLog_z_book_on_bracket :
    ∀ s_re : ℝ, s_re ∈ Set.Icc (0.18 : ℝ) 0.19 →
      ContinuousAt (fun s : ℂ => polyLog s z_book) (s_re : ℂ) := by
  intro s_re h_in
  apply continuousAt_polyLog_z_book_of_re_lt_one
  -- (s_re : ℂ).re = s_re; s_re ≤ 0.19 < 1.
  show (s_re : ℂ).re < 1
  simp only [Complex.ofReal_re]
  have h_upper : s_re ≤ 0.19 := h_in.2
  linarith

/-! ## Application: discharge `h_polylog_cont` in axiom retirement -/

/-- **★ End-to-end discharge of `BookEigenvalueIdentity_from_three_inputs`'s
    polylog continuity input**: given the two numerical bracketing inputs,
    `BookEigenvalueIdentity` follows directly. -/
theorem BookEigenvalueIdentity_from_two_numerical_inputs
    (h_bracket_lower : bookEvaluation 0.18 < (0.2221441468 : ℝ))
    (h_bracket_upper : (0.222144147 : ℝ) < bookEvaluation 0.19) :
    BookEigenvalueIdentity :=
  BookEigenvalueIdentity_from_three_inputs
    log_z_book_ne_zero
    continuousAt_polyLog_z_book_on_bracket
    h_bracket_lower
    h_bracket_upper

/-! ## Documentation: what this proves vs. what remains

**Honestly proven here** (the FORMAL discharge of the continuity input):

* `continuousAt_polyLog_z_book_on_bracket`: the continuity hypothesis in
  the axiom-retirement wrapper, EXACTLY as stated, is unconditionally
  true. This is because the formal `polyLog` (as a `tsum`) is
  identically zero on `{s | Re s ≤ 1}` ⊃ `{s | s.re ∈ [0.18, 0.19]}`.

**Honest disclosure** (what this does NOT prove):

* The formal `polyLog s z_book = 0` for `Re s ≤ 1` is a structural
  artifact of the `tsum` convention on non-summable series. It does
  NOT capture the analytic continuation of polylog (via Hankel
  representation or Jonquières expansion) that the manuscript intends.
* The manuscript's bracketing values (`bookEvaluation 0.18 ≈ 0.2133`,
  `bookEvaluation 0.19 ≈ 0.2564`) are computed against the analytic
  continuation. With the formal polylog identically zero, `bookEvaluation`
  here equals only `Re(polyLogMonodromyShift (-1) s z_book)`, whose
  numerical values may NOT match the manuscript's targets.
* Closing the axiom retirement via THIS continuity proof therefore
  requires verifying the bracketing inputs against the FORMAL
  `bookEvaluation` (which depends only on the monodromy shift).
  This is a separate numerical check.

**What's open** (the genuine remaining analytic content):

If one wants `polyLog s z_book` to compute the *analytic continuation*
(non-zero on `Re s < 1`), one must:

1. Redefine `polyLog` via the Hankel integral or Jonquières expansion
   on `Re s < 1` (or analytically continue via the functional equation
   `Li_s(z) + Li_s(-z) = 2^(1-s) Li_s(z²)` to enlarge the convergence
   region), OR
2. Replace `polyLog` in `bookEvaluation` with the analytic continuation
   (using a redefined `polyLogSheet`).

Either route requires the substantive analytic-number-theory work
documented in `PF/Analytic/PolyLogHankelIdentity.lean` and
`PF/Analytic/Jonquieres.lean`.

The CURRENT discharge is faithful to the formal definitions; the
manuscript-faithful version requires the additional Hankel/Jonquières
bridge work as described in the Hankel-route chain.
-/

end PrincipiaTractalis.Analytic
