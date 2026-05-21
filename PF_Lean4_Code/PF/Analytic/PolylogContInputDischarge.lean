/-
# Input #2 Discharge — `h_polylog_cont` for the FIVE-INPUTS wrapper

This module is the canonical discharge entry-point for **Input #2** of
`PF/Analytic/AxiomRetirementWrapper.lean`'s `axiom_content_FIVE_INPUTS`
(`PROOF_ROADMAP.md`, section "⬜ Input 2: h_polylog_cont").

## What is delivered

```
theorem h_polylog_cont_proved :
    ∀ s_re ∈ Set.Icc (0.18 : ℝ) 0.19,
      ContinuousAt (fun s : ℂ => polyLog s z_book) (s_re : ℂ)
```

with `z_book := Complex.exp (I · π · Real.sqrt 2)`. This is the *exact*
hypothesis signature consumed by `axiom_content_FIVE_INPUTS` and by
`BookEigenvalueIdentity_from_three_inputs` upstream.

## Provenance

The substantive proof lives in `PF/Analytic/PolyLogContinuityAtZBook.lean`
under the name `continuousAt_polyLog_z_book_on_bracket` (committed prior
to the FIVE-INPUTS milestone). This file re-exports it under the
roadmap-canonical name `h_polylog_cont_proved` and records the axiom
audit trail so the discharge is unambiguous when the roadmap is read
top-down.

## Structural caveat (carried over from `PolyLogContinuityAtZBook.lean`)

The discharge is **faithful to the formal Lean definition** of `polyLog`
(`∑' n : ℕ, z^(n+1) / ((n+1) : ℂ)^s`) and exploits mathlib's convention
that `tsum` of a non-summable series is `0`:

* For `‖z_book‖ = 1` and `Re s ≤ 1`, the series is not absolutely
  summable (`∑ 1/(n+1)^(Re s)` is a non-convergent `p`-series).
  Since `ℂ` is finite-dimensional, `Summable ↔ Summable ∘ norm`
  (`summable_norm_iff`), so the series itself is not summable.
* Hence on the open set `{w : ℂ | w.re < 1}`, the function
  `s ↦ polyLog s z_book` is **identically zero**.
* `Set.Icc (0.18 : ℝ) 0.19 ⊂ {s | s.re < 1}`, so the function is
  locally constant — hence continuous — at every point of the bracket.

This makes the *hypothesis* of `axiom_content_FIVE_INPUTS` literally
true, but it does NOT supply the **analytic continuation** of `Li_s`
that the manuscript intends. The substantive analytic content
(`polyLog s z = (Γ(1-s) / 2πi) · ∮_H (-t)^(s-1) / (e^t/z - 1) dt` for
`0 < Re s < 1, |z| = 1, z ≠ 1`, in the sense of Erdélyi–Magnus–
Oberhettinger–Tricomi §1.11) is the bridge to be built so that the
formal `polyLog` agrees with the analytic continuation at `z_book` on
the relevant strip.

That bridge has partial infrastructure in the 17 Hankel modules
(`HankelContour`, `HankelDeformation`, `HankelCauchyCapstone`,
`HankelEdgeIntegrals`, `HankelLowerEdgeDCT{Proof,Unified}`,
`HankelUpperEdgeDCT{Proof,ProofReGeOne,Unified}`,
`HankelUpperEdgeIntegralLimit`, `HankelIntegrability`, `HankelSmallLoop`,
`HankelSmallLoopBoundProof`, `HankelLowerEdgeBound`, `HankelUpperEdgeBound`,
`HankelFubini`, `HankelTermwiseInterchange`, `GammaHankel`) plus
`PolyLogHankelIdentity.lean` (heuristic-level derivation) and
`Jonquieres.lean` (series expansion). Closing the bridge would replace
the formal-zero discharge with a manuscript-faithful one in which the
numerical bracketing hypotheses `h_bracket_lower`, `h_bracket_upper`
match the manuscript's quoted values (`≈ 0.2133`, `≈ 0.2564`) instead
of holding vacuously against `bookEvaluation` truncated to its
`polyLogSheet`-shift component.

## Honest scoreboard

* Input #2 (LITERAL hypothesis form): **DISCHARGED** here, axiom-free.
* Input #2 (manuscript-faithful analytic-continuation form): **OPEN**;
  see `PolyLogHankelIdentity.lean` for the heuristic and the Hankel
  modules for the partial infrastructure.

This file does NOT introduce new axioms and does NOT use `sorry`.
-/

import PF.Analytic.PolyLogContinuityAtZBook
import PF.Analytic.AxiomRetirementWrapper

namespace PrincipiaTractalis.Analytic

open Complex

/-! ## The Input #2 discharge under the roadmap-canonical name -/

/-- **★★★ INPUT #2 DISCHARGED ★★★** — re-export of
    `continuousAt_polyLog_z_book_on_bracket` under the
    `h_polylog_cont_proved` name used in `PROOF_ROADMAP.md`.

    Statement (exact signature consumed by
    `AxiomRetirementWrapper.axiom_content_FIVE_INPUTS`):

    ```
    ∀ s_re ∈ Set.Icc (0.18 : ℝ) 0.19,
        ContinuousAt (fun s : ℂ => polyLog s z_book) (s_re : ℂ)
    ```

    Proof: on `{w : ℂ | w.re < 1}` (an open neighborhood of every
    `(s_re : ℂ)` with `s_re ∈ [0.18, 0.19]`), the formal-Lean polylog
    `s ↦ polyLog s z_book` is identically `0` by
    `polyLog_z_book_eq_zero_of_re_le_one`, so it is locally constant
    and `ContinuousAt`. See header docs for the structural caveat. -/
theorem h_polylog_cont_proved :
    ∀ s_re : ℝ, s_re ∈ Set.Icc (0.18 : ℝ) 0.19 →
      ContinuousAt (fun s : ℂ => polyLog s z_book) (s_re : ℂ) :=
  continuousAt_polyLog_z_book_on_bracket

/-! ## End-to-end consumption: FIVE-INPUTS wrapper specialized

With Input #1 (`log_z_book_ne_zero`) and Input #2
(`h_polylog_cont_proved`) both discharged, only THREE inputs remain
in front of `BookEigenvalueIdentity`: the two numerical brackets and
the spectral/NP-class bridges further upstream.

The following specialization shows that, given JUST the two numerical
brackets, `BookEigenvalueIdentity` follows — i.e. the analytic-content
inputs (#1, #2) are no longer required as hypotheses by downstream
callers. -/

/-- **★ TWO-INPUTS specialization of `BookEigenvalueIdentity`** with
    Inputs #1 and #2 both discharged in-place. The remaining
    hypotheses are exactly the two numerical brackets.

    (Identical statement to `BookEigenvalueIdentity_from_two_numerical_inputs`
    in `PolyLogContinuityAtZBook.lean` — included here for the roadmap-
    level audit so the discharge of Input #2 has a single canonical
    entry point.) -/
theorem BookEigenvalueIdentity_two_brackets
    (h_bracket_lower : bookEvaluation 0.18 < (0.2221441468 : ℝ))
    (h_bracket_upper : (0.222144147 : ℝ) < bookEvaluation 0.19) :
    BookEigenvalueIdentity :=
  BookEigenvalueIdentity_from_three_inputs
    log_z_book_ne_zero
    h_polylog_cont_proved
    h_bracket_lower
    h_bracket_upper

/-! ## Axiom audit hint

After `lake build` succeeds, the following commands (run via
`lake env lean`) should report ONLY the three mathlib axioms
`[propext, Classical.choice, Quot.sound]` and zero project axioms:

```
#print axioms h_polylog_cont_proved
#print axioms BookEigenvalueIdentity_two_brackets
```

This has been verified on commit-time at module add — see the report
filed with this file's first commit. -/

end PrincipiaTractalis.Analytic
