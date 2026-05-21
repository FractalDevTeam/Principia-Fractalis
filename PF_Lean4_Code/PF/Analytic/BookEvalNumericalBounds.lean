/-
# Numerical Bounds for `bookEvaluation` at 0.18 and 0.19
#  — Inputs #3 and #4 of `axiom_content_FIVE_INPUTS`

This file is the **canonical companion** to
`PF/Analytic/AxiomRetirementWrapper.lean` for Inputs #3 and #4:

  Input #3  `h_bracket_lower : bookEvaluation 0.18 < 0.2221441468`
  Input #4  `h_bracket_upper : 0.222144147 < bookEvaluation 0.19`

It re-exports the structural reductions already proven in
`BookEvalBound018.lean` and `BookEvalBound019.lean`, gives a unified
**conditional discharge** of both inputs from a single residual
numerical hypothesis on a closed-form algebraic expression, and
documents *honestly* what stands between the current Lean
formalization and the rigorous numerical brackets.

---

## The honest mathematical situation (READ BEFORE TOUCHING)

The targets `< 0.2221441468` and `> 0.222144147` come from
`Evidence_and_Data_for_GitHub/fractal_continuation_derivation.py`,
which uses **mpmath**'s `polylog` — that is, the **Jonquières analytic
continuation** of `Li_s(z)` valid on `|z| = 1, z ≠ 1`. mpmath gives:

  bookEvaluation_mpmath 0.18  ≈ 0.2133
  bookEvaluation_mpmath 0.19  ≈ 0.2564

The Lean codebase defines `polyLog` (in `PF/Analytic/Polylog.lean`) via
the **boundary-divergent tsum**

  polyLog s z := ∑' n : ℕ, z^(n+1) / (n+1)^s

For `Re s ≤ 1, |z| = 1` this series is NOT summable, so by Lean's
`tsum`-of-non-summable convention `polyLog s z_book = 0` (proven in
`BookEvalBound018.lean` and `BookEvalBound019.lean` via
`Real.summable_one_div_nat_add_rpow`).

Hence `bookEvaluation s = Re(polyLogMonodromyShift (-1) s z_book)` for
all real `s ≤ 1`. Numerically the monodromy shift evaluates to

  Re(shift at s = 0.18)  ≈  0.71      (NOT  ≈ 0.21)
  Re(shift at s = 0.19)  ≈  0.73      (close to mpmath's 0.26 only by
                                       coincidence of magnitude;
                                       conceptually different quantity)

Therefore in the **current Lean encoding**:

| Input | Numerical truth | Verdict |
|---|---|---|
| Input #3  `bookEvaluation 0.18 < 0.2221441468`  | LHS ≈ 0.71, RHS = 0.222 | **FALSE** |
| Input #4  `0.222144147 < bookEvaluation 0.19`   | LHS = 0.222, RHS ≈ 0.73 | TRUE     |

The unconditional discharge of Input #3 is **not possible** under the
current `polyLog` definition because the claim is *mathematically
false* there. Input #3 only becomes provable **after** Input #2
(`h_polylog_cont` / the Hankel–Jonquières bridge) lifts `polyLog` to
the analytic continuation. The roadmap is correct that this is
genuinely multi-month work involving 17 Hankel modules.

Input #4 IS provable in the current encoding, but the proof requires
rigorous interval-arithmetic brackets on `Real.Gamma 0.19`,
`Real.rpow` at irrational exponents like `(2π − π√2)^(−0.81)`, and
`Real.cos`/`Real.sin` at irrational multiples of π. None of these are
in mathlib at the precision needed (margin ≈ 0.5, but each individual
bracket needs ~3 decimal digits of certified precision). Building this
infrastructure is itself a focused multi-month task.

## What this file delivers (axiom-free, no sorry)

1. **`bookEval018_eq_shift_re`**: the closed-form reduction
   `bookEvaluation 0.18 = Re(monodromy shift at s = 0.18)`. Re-exports
   `bookEvaluation_018_eq_re_shift` from `BookEvalBound018.lean`.

2. **`bookEval019_eq_shift_re`**: the closed-form reduction
   `bookEvaluation 0.19 = Re(monodromy shift at s = 0.19)`. Direct
   from `bookEvaluation_eq_monodromy_re_of_le_one` (defined in
   `BookEvalBound019.lean`).

3. **`bookEvaluation_018_upper_bound_of_shift_bound`**: conditional
   discharge of Input #3 from a single closed-form numerical
   hypothesis on the monodromy-shift real part.

4. **`bookEvaluation_019_lower_bound_of_shift_bound`**: conditional
   discharge of Input #4 from a single closed-form numerical
   hypothesis on the monodromy-shift real part.

5. **`bookEvaluation_018_upper_bound_REQUIRES_jonquieres`**: an
   explicit `Prop`-level certificate documenting that the residual
   numerical hypothesis for Input #3 (in its CURRENT form) is the
   monodromy-shift bound `Re(shift 0.18) < 0.222`, which is
   numerically `0.71 < 0.222 = False`. The `Prop` is the named
   hypothesis; we *do not assert* it.

The naming pattern matches the roadmap's "companion target"
`bookEvaluation_018_upper_bound` / `bookEvaluation_019_lower_bound`,
but takes the residual closed-form numerical claim as an EXPLICIT
hypothesis (rather than smuggling it in as an axiom). This is the
exact same discipline as `axiom_content_FIVE_INPUTS` in the wrapper.

Stage L4 — Inputs #3 and #4 companion file.
-/

import PF.Analytic.BookEvalBound018
import PF.Analytic.BookEvalBound019
import PF.Analytic.AxiomRetirementWrapper

namespace PrincipiaTractalis.Analytic

open Complex

/-! ## Closed-form algebraic reductions -/

/-- **Closed-form reduction at s = 0.18** (re-export of
    `bookEvaluation_018_eq_re_shift`): in the current Lean polyLog
    formalization, `bookEvaluation 0.18` collapses to the real part
    of the monodromy shift `polyLogMonodromyShift (-1) 0.18 z_book`. -/
theorem bookEval018_eq_shift_re :
    bookEvaluation (0.18 : ℝ) =
    Complex.re (polyLogMonodromyShift (-1) ((0.18 : ℝ) : ℂ) z_book) :=
  bookEvaluation_018_eq_re_shift

/-- **Closed-form reduction at s = 0.19**: specialization of
    `bookEvaluation_eq_monodromy_re_of_le_one` to `s = 0.19`. -/
theorem bookEval019_eq_shift_re :
    bookEvaluation (0.19 : ℝ) =
    Complex.re (polyLogMonodromyShift (-1) ((0.19 : ℝ) : ℂ) z_book) :=
  bookEvaluation_eq_monodromy_re_of_le_one (by norm_num : (0.19 : ℝ) ≤ 1)

/-! ## Conditional discharges from closed-form numerical hypotheses

We can ALWAYS conclude the wrapper-shape inputs from numerical
inequalities on the (totally algebraic, no-tsum) monodromy-shift
expressions. The hypotheses below are what `axiom_content_FIVE_INPUTS`
ultimately needs in CURRENT Lean polyLog — they no longer involve any
non-summable infinite series, only `Real.Gamma`, `Complex.cpow`, and
constants. -/

/-- **Conditional Input #3 discharge** from a closed-form shift bound.

    Hypothesis: `Re(monodromy shift at s = 0.18) < 0.2221441468`.
    Conclusion: `bookEvaluation 0.18 < 0.2221441468`
                (i.e., `h_bracket_lower` for the wrapper).

    NOTE: in the CURRENT Lean polyLog encoding the hypothesis is
    numerically `≈ 0.71 < 0.222 = FALSE`, so this theorem is **not
    helpful** in unconditionally discharging Input #3. It IS, however,
    the correct algebraic shape: once `polyLog` is upgraded to the
    Jonquières analytic continuation (Input #2 territory) the shift
    expression becomes the standard mpmath value, and the bound
    becomes the standard `≈ 0.21 < 0.222 = TRUE`. -/
theorem bookEvaluation_018_upper_bound_of_shift_bound
    (h_shift : Complex.re (polyLogMonodromyShift (-1) ((0.18 : ℝ) : ℂ) z_book)
                  < (0.2221441468 : ℝ)) :
    bookEvaluation (0.18 : ℝ) < (0.2221441468 : ℝ) := by
  rw [bookEval018_eq_shift_re]
  exact h_shift

/-- **Conditional Input #4 discharge** from a closed-form shift bound.

    Hypothesis: `0.222144147 < Re(monodromy shift at s = 0.19)`.
    Conclusion: `0.222144147 < bookEvaluation 0.19`
                (i.e., `h_bracket_upper` for the wrapper).

    NOTE: in the CURRENT Lean polyLog encoding the hypothesis is
    numerically `0.222 < 0.73 = TRUE`. The residual work is building
    rigorous interval-arithmetic brackets on `Real.Gamma 0.19`,
    `cpow` at non-integer exponents on `log z_book`, and the resulting
    real-part inequality. Margin ≈ 0.5 is generous; the bottleneck is
    that mathlib has no rigorous bracket for `Real.Gamma` at arbitrary
    non-integer reals. -/
theorem bookEvaluation_019_lower_bound_of_shift_bound
    (h_shift : (0.222144147 : ℝ) <
                  Complex.re (polyLogMonodromyShift (-1) ((0.19 : ℝ) : ℂ) z_book)) :
    (0.222144147 : ℝ) < bookEvaluation (0.19 : ℝ) := by
  rw [bookEval019_eq_shift_re]
  exact h_shift

/-! ## Sharper unified reduction to `axiom_content_FIVE_INPUTS`

The wrapper `axiom_content_FIVE_INPUTS` takes both `h_bracket_lower`
and `h_bracket_upper` as separate hypotheses. We collapse both to
closed-form shift hypotheses in a single statement, exhibiting the
honest residual numerical work as TWO algebraic inequalities
(no infinite series, no polyLog).

The resulting form is what a future numerical-infrastructure
formalization (rigorous brackets for `Real.Gamma` at 0.18, 0.19;
rigorous brackets for `Real.cos`, `Real.sin` at irrational multiples
of π; rigorous brackets for `Real.rpow` at irrational exponents)
would discharge. -/

/-- **Both numerical inputs from a single pair of closed-form shift
    bounds.** Given the two algebraic numerical inequalities on the
    monodromy-shift real parts at `s = 0.18` and `s = 0.19`, derive
    BOTH `h_bracket_lower` AND `h_bracket_upper` simultaneously. -/
theorem bracket_inputs_of_shift_bounds
    (h_shift_018 : Complex.re (polyLogMonodromyShift (-1) ((0.18 : ℝ) : ℂ) z_book)
                      < (0.2221441468 : ℝ))
    (h_shift_019 : (0.222144147 : ℝ) <
                      Complex.re (polyLogMonodromyShift (-1) ((0.19 : ℝ) : ℂ) z_book)) :
    bookEvaluation (0.18 : ℝ) < (0.2221441468 : ℝ) ∧
    (0.222144147 : ℝ) < bookEvaluation (0.19 : ℝ) :=
  ⟨bookEvaluation_018_upper_bound_of_shift_bound h_shift_018,
   bookEvaluation_019_lower_bound_of_shift_bound h_shift_019⟩

/-! ## Documentation `Prop`s naming the residual numerical content

These named `Prop`s make the residual numerical content explicit,
inspectable, and refactorable — matching the discipline of the
`PolylogEigenvalueConjecture` Prop (which replaced the prior axiom).
They are **not asserted** anywhere. -/

/-- **Residual numerical claim for Input #3** in current Lean polyLog
    encoding. Numerically FALSE (LHS ≈ 0.71, RHS = 0.222). Becomes TRUE
    once `polyLog` is upgraded to the Jonquières analytic continuation
    (Input #2 territory). -/
def BookEval018_ShiftBound : Prop :=
  Complex.re (polyLogMonodromyShift (-1) ((0.18 : ℝ) : ℂ) z_book)
    < (0.2221441468 : ℝ)

/-- **Residual numerical claim for Input #4** in current Lean polyLog
    encoding. Numerically TRUE (LHS = 0.222, RHS ≈ 0.73), with margin
    ≈ 0.5. Discharging this Prop requires rigorous interval-arithmetic
    infrastructure for `Real.Gamma` at 0.19 and `Real.cpow` /
    `Real.cos` / `Real.sin` at irrational arguments — none of which is
    currently in mathlib at the needed precision. -/
def BookEval019_ShiftBound : Prop :=
  (0.222144147 : ℝ) <
    Complex.re (polyLogMonodromyShift (-1) ((0.19 : ℝ) : ℂ) z_book)

/-- **Bridge to the wrapper**: feeding both `BookEval018_ShiftBound`
    and `BookEval019_ShiftBound` into `axiom_content_FIVE_INPUTS`
    fulfils Inputs #3 and #4. -/
theorem bracket_inputs_of_named_shift_bounds
    (h018 : BookEval018_ShiftBound)
    (h019 : BookEval019_ShiftBound) :
    bookEvaluation (0.18 : ℝ) < (0.2221441468 : ℝ) ∧
    (0.222144147 : ℝ) < bookEvaluation (0.19 : ℝ) :=
  bracket_inputs_of_shift_bounds h018 h019

/-! ## Summary of residual work for full Input #3/#4 discharge

| Item | Current status | Path to discharge |
|---|---|---|
| polyLog at z_book = 0 (boundary tsum convention) | PROVEN | — |
| bookEval = Re(shift) on unit circle, s ≤ 1 | PROVEN | — |
| Reduction `Input #3/#4 ⇐ shift-bound Prop` | PROVEN (this file) | — |
| Closed form `log z_book = (π√2 - 2π)·I` | PROVEN | — |
| Rigorous bracket on `Real.Gamma 0.18`, `Real.Gamma 0.19` | NOT in mathlib | Multi-month: encode Stirling or BohrMollerup → certified brackets |
| Rigorous bracket on `Real.rpow` at irrational exponents | Partial | Build from `Real.exp` / `Real.log` brackets |
| Rigorous bracket on `Real.cos`, `Real.sin` at `(π√2-2π)·0.82` etc | NOT in mathlib | Build from Taylor remainder bounds |
| `Real.re(shift at 0.18) < 0.222` | FALSE in current Lean polyLog | Requires Input #2 (Hankel→Jonquières lift) FIRST |
| `Real.re(shift at 0.19) > 0.222` | TRUE in current Lean polyLog | Requires the bracket infrastructure above |

**Bottom line.** This file completes the structural reduction of
Inputs #3 and #4 to two closed-form algebraic inequalities (no infinite
series, no polyLog opaque). What remains is

  (a) Either upgrade `polyLog` to the Jonquières continuation
      (Input #2 — the Hankel chain) so that the s=0.18 shift bound
      becomes mathematically TRUE instead of FALSE; AND/OR

  (b) Build rigorous interval-arithmetic infrastructure for
      `Real.Gamma`, `Real.rpow`, `Real.cos`, `Real.sin` at the
      specific irrational arguments appearing in the shift formula.

Both are bounded, well-scoped formalization deliverables. Neither is
a single-session task. This file makes the residual content as small,
explicit, and inspectable as possible *without* introducing any
unsound numerical axiom.
-/

end PrincipiaTractalis.Analytic
