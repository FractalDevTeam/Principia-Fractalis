/-
# Ch 29 — The Adjusted-Improvement Figure Is Unreachable (2026-10-05, round 2)

Pablo's assessment that ch29 "remains unresolved" is correct. The first pass
(`PF/Ch29DofRefutationAttempt.lean`) proved the `9/11` degrees-of-freedom pair
impossible for every dataset size and corrected two arithmetic slips, but it
left the chapter's **headline number** standing and introduced one
inconsistency of its own. Both are settled here.

## Defect A — the headline `94.3 %` cannot be produced by any parameter penalty

`ch29_observational_tests.tex:408–411` reads, in full:

> "Accounting for 2 additional parameters, adjusted improvement:
>  `Adjusted improvement = 94.3 %`"

and `:414` calls this "the **94.3 % improvement** claimed throughout this
book". It is boxed, it is the chapter's headline, and it propagates to at least
seven sites (`:8`, `:37`, `:414`, `:423`, `:535`, `:655`, `:672`).

**No adjustment formula is given.** And the figure cannot be the result of one,
because it moves in the impossible direction. The chapter's own unadjusted
quantity is

  `Δχ²/χ²_mod = 333.1/354.2 = 94.043 %`,

and the printed "adjusted" value `94.3 %` is **larger**. Penalising a model for
extra parameters must make its improvement look *worse*, never better.
`penalty_strictly_decreases_improvement` proves this for every penalty `c > 0`:

  `(Δ − c)/(M + c) < Δ/M`  whenever `0 ≤ Δ`, `0 < M`, `0 < c`,

since cross-multiplying leaves `0 < c(Δ + M)`. Combined with
`unadjusted_lt_printed` (`333.1/354.2 < 0.943`, an integer comparison:
`3331 · 1000 = 3 331 000 < 3 340 106 = 943 · 3542`), this gives
`printed_adjusted_not_a_penalised_value`: **no penalty whatsoever yields
`94.3 %`.**

Ten candidate readings were computed numerically before this file was written,
and every penalised one lies *below* the unadjusted figure, as the lemma
requires:

| reading | value |
|---|---|
| `Δχ²/χ²_mod` — the chapter's own substitution | `94.043 %` |
| `Δχ²/χ²_ΛCDM` — the formula as displayed at `:406` | `48.465 %` |
| reduced-`χ²`, `(r_Λ − r_m)/r_m`, dof `590/588` | `93.385 %` |
| reduced-`χ²`, `(r_Λ − r_m)/r_Λ` | `48.290 %` |
| AIC-penalised, `k = 6, 8` | `88.898 %` |
| BIC-penalised, `k = 6, 8` | `79.061 %` |

None is `94.3 %`. (The reduced-`χ²` rows are insensitive to the dof dispute:
substituting `574/572` or `592/590` moves them by under `0.02` points.)

Holding one input fixed, `94.3 %` would require `Δχ² = 334.01` against the
chapter's `333.1`, or `χ²_mod = 353.23` against its `354.2`. Neither appears
anywhere in the chapter.

## Defect B — a superseded value left in place by the first pass

`:439` was corrected on 2026-10-05 to `ΔBIC = 725.58 − 405.21 = 320.37`. The
restatement three lines later at `:442` still reads

> "Our `ΔBIC = 319.6` is overwhelming."

`320.37 ≠ 319.6` (`bic_restatement_inconsistent`). This inconsistency did not
exist before that pass: correcting a computed value and leaving its restatement
untouched created it. Recorded here rather than quietly fixed, because the
pattern — repair one site, miss the restatement — is the same failure mode as
the ch10 propagation and is worth having on the record.

The *conclusion* `ΔBIC ≫ 10` survives either value, and both are far above
Jeffreys' decisive threshold. Note also that `N = 590/588` enters both BIC
values, so both shift again once the dof accounting is settled.

## What remains unrecoverable — and why no replacement is supplied

Pablo's list is exactly right. None of the following can be reconstructed from
the text:

* **the degrees of freedom** — the chapter gives `N_data` and `N_param`
  explicitly for supernovae (`580 − 6/8`) and BAO (`13 − 6/8`), but for *no*
  CMB figure: not `52`, `50`, `9`, `11`, nor the "effective `N_dof ≈ 60`" at
  `:326`;
* **the reduced `χ²` values** `1.165` and `0.603` — arithmetically consistent
  with the disputed `590/588`, so they inherit rather than independently fail;
* **the adjusted `94.3 %`** — no formula, and provably not a penalised value;
* **the BIC pair** — depends on the same `N`.

What *is* established: `χ²_ΛCDM = 687.3`, `χ²_mod = 354.2` and
`Δχ² = 333.1` are mutually consistent and unaffected by any of the above; the
likelihood-ratio and `p`-value statements depend on `Δχ²` alone and so also
survive.

Supplying the common observation count and the fit provenance is an
**authorial item**. It is not a matter of recomputation: the inputs are absent,
not miscomputed.

## Ledger

ch29's global fit is already filed **EMPIRICAL HYPOTHESIS — UNTESTED**, and
nothing here moves it. The chapter's own `\empiricalclaim` note at `:415–423`
already states that the Lean stack does not verify the `χ²` improvement and
that referees must rerun the analysis against the primary catalogues; that
disclosure is accurate and is strengthened, not contradicted, by this file.

What this file adds is that the headline figure is not merely unverified but
**arithmetically unreachable by the operation named beside it**.

## Scope

Two numbers and one restatement. No Lean module outside this one changes.

Author: Pablo Cohen + Claude Opus 5. 2026-10-05.
-/
import Mathlib.Tactic

namespace PrincipiaTractalis.Ch29AdjustedImprovement

/-! ## §1 — Penalties strictly decrease an improvement ratio -/

/-- **★ Penalising a model for extra parameters strictly decreases its
    improvement ratio. ★**

    If a penalty `c > 0` is charged against the modified model, the improvement
    `Δ` falls by `c` and the residual `M` it is measured against rises by `c`,
    so the ratio strictly drops. Cross-multiplying leaves `0 < c(Δ + M)`.

    This is the structural fact `ch29:408` violates: it claims to account for
    two additional parameters and reports a *larger* figure than the
    unpenalised one. -/
theorem penalty_strictly_decreases_improvement
    (Delta M c : ℝ) (hD : 0 ≤ Delta) (hM : 0 < M) (hc : 0 < c) :
    (Delta - c) / (M + c) < Delta / M := by
  rw [div_lt_div_iff₀ (by linarith) hM]
  nlinarith

/-! ## §2 — The chapter's own numbers -/

/-- `Δχ² = 333.1`, from `ch29:391–406`. -/
noncomputable def deltaChiSq : ℝ := 3331 / 10

/-- `χ²_mod = 354.2`. -/
noncomputable def chiSqMod : ℝ := 3542 / 10

/-- `χ²_ΛCDM = 687.3`. -/
noncomputable def chiSqLCDM : ℝ := 6873 / 10

/-- The unadjusted improvement the chapter actually substitutes at `:406`. -/
noncomputable def unadjustedImprovement : ℝ := deltaChiSq / chiSqMod

/-- The boxed "adjusted improvement" at `ch29:410`, as a fraction. -/
noncomputable def printedAdjusted : ℝ := 943 / 1000

/-- The three `χ²` figures are mutually consistent: the difference is the
    stated `Δχ²`. This is what survives in the chapter. -/
theorem chiSq_figures_consistent : chiSqLCDM - chiSqMod = deltaChiSq := by
  unfold chiSqLCDM chiSqMod deltaChiSq; norm_num

/-- **The unadjusted improvement is strictly below the printed adjusted one.**

    An integer comparison: `3331 · 1000 = 3331000 < 3340106 = 943 · 3542`. -/
theorem unadjusted_lt_printed : unadjustedImprovement < printedAdjusted := by
  unfold unadjustedImprovement printedAdjusted deltaChiSq chiSqMod
  norm_num

/-- The unadjusted figure is `94.043…%`, bracketed to three decimals. -/
theorem unadjusted_bracket :
    (94040 / 100000 : ℝ) < unadjustedImprovement ∧
    unadjustedImprovement < (94045 / 100000 : ℝ) := by
  unfold unadjustedImprovement deltaChiSq chiSqMod
  constructor <;> norm_num

/-! ## §3 — The printed figure is not a penalised value -/

/-- **★ No parameter penalty produces the printed `94.3 %`. ★**

    Every penalty `c > 0` lands strictly below the unadjusted figure, which is
    itself strictly below `0.943`. So the boxed headline at `ch29:410` is not
    obtainable by the operation named beside it at `:408`, for any penalty
    whatsoever. -/
theorem printed_adjusted_not_a_penalised_value :
    ∀ c : ℝ, 0 < c →
      (deltaChiSq - c) / (chiSqMod + c) ≠ printedAdjusted := by
  intro c hc heq
  have hM : (0:ℝ) < chiSqMod := by unfold chiSqMod; norm_num
  have hD : (0:ℝ) ≤ deltaChiSq := by unfold deltaChiSq; norm_num
  have hdrop := penalty_strictly_decreases_improvement deltaChiSq chiSqMod c hD hM hc
  rw [heq] at hdrop
  have := unadjusted_lt_printed
  unfold unadjustedImprovement at this
  linarith

/-- Stated as the direction failure: the printed figure exceeds the unadjusted
    one, whereas accounting for additional parameters can only lower it. -/
theorem adjustment_moves_wrong_direction :
    unadjustedImprovement < printedAdjusted ∧
    ∀ c : ℝ, 0 < c →
      (deltaChiSq - c) / (chiSqMod + c) < unadjustedImprovement := by
  refine ⟨unadjusted_lt_printed, fun c hc => ?_⟩
  have hM : (0:ℝ) < chiSqMod := by unfold chiSqMod; norm_num
  have hD : (0:ℝ) ≤ deltaChiSq := by unfold deltaChiSq; norm_num
  exact penalty_strictly_decreases_improvement deltaChiSq chiSqMod c hD hM hc

/-- What `94.3 %` would require of the inputs, neither value appearing in the
    chapter: `Δχ² = 334.01…` at fixed `χ²_mod`, or `χ²_mod = 353.23…` at fixed
    `Δχ²`. Bracketed rather than stated exactly. -/
theorem required_inputs_absent_from_chapter :
    (33400 / 100 : ℝ) < printedAdjusted * chiSqMod ∧
    printedAdjusted * chiSqMod < (33402 / 100 : ℝ) ∧
    (35322 / 100 : ℝ) < deltaChiSq / printedAdjusted ∧
    deltaChiSq / printedAdjusted < (35324 / 100 : ℝ) := by
  unfold printedAdjusted chiSqMod deltaChiSq
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-! ## §4 — The BIC restatement left behind by the first pass -/

/-- **The corrected `ΔBIC` and the value still quoted three lines later
    disagree.**

    `:439` was corrected to `725.58 − 405.21 = 320.37`; `:442` still reads
    `319.6`. Recorded rather than silently repaired: the first pass created
    this by correcting a computation and not its restatement. -/
theorem bic_restatement_inconsistent :
    (72558 / 100 : ℝ) - (40521 / 100 : ℝ) = (32037 / 100 : ℝ) ∧
    (32037 / 100 : ℝ) ≠ (3196 / 10 : ℝ) := by
  constructor <;> norm_num

/-- Both values are far above Jeffreys' decisive threshold, so the chapter's
    conclusion is insensitive to which is used. -/
theorem bic_conclusion_survives_either :
    (10 : ℝ) < (32037 / 100 : ℝ) ∧ (10 : ℝ) < (3196 / 10 : ℝ) := by
  constructor <;> norm_num

/-! ## §5 — Capstone -/

/-- **★ Ch 29 adjusted-improvement refutation capstone ★**

    Penalties strictly decrease an improvement ratio; the chapter's unadjusted
    ratio is already below the printed adjusted figure; hence no penalty
    produces that figure, and the operation named at `:408` cannot have
    produced it. Separately, the corrected `ΔBIC` disagrees with the value
    still quoted downstream, while the conclusion drawn from it survives
    either. -/
theorem Ch29AdjustedImprovement_capstone :
    (∀ Delta M c : ℝ, 0 ≤ Delta → 0 < M → 0 < c →
      (Delta - c) / (M + c) < Delta / M) ∧
    unadjustedImprovement < printedAdjusted ∧
    (∀ c : ℝ, 0 < c → (deltaChiSq - c) / (chiSqMod + c) ≠ printedAdjusted) ∧
    chiSqLCDM - chiSqMod = deltaChiSq ∧
    ((32037 / 100 : ℝ) ≠ (3196 / 10 : ℝ)) :=
  ⟨penalty_strictly_decreases_improvement,
   unadjusted_lt_printed,
   printed_adjusted_not_a_penalised_value,
   chiSq_figures_consistent,
   bic_restatement_inconsistent.2⟩

/-! ## §6 — Non-vacuity -/

/-- Non-vacuity: the hypothesis shape denied in
    `printed_adjusted_not_a_penalised_value` is satisfiable in general — a
    penalised ratio does equal *some* value, witnessed at `c = 1`, and it is a
    genuine positive quantity. What fails is specifically `0.943`. -/
theorem penalised_ratio_is_a_real_quantity :
    0 < (deltaChiSq - 1) / (chiSqMod + 1) ∧
    (deltaChiSq - 1) / (chiSqMod + 1) < unadjustedImprovement := by
  have hM : (0:ℝ) < chiSqMod := by unfold chiSqMod; norm_num
  have hD : (0:ℝ) ≤ deltaChiSq := by unfold deltaChiSq; norm_num
  refine ⟨?_, penalty_strictly_decreases_improvement deltaChiSq chiSqMod 1 hD hM one_pos⟩
  unfold deltaChiSq chiSqMod; norm_num

end PrincipiaTractalis.Ch29AdjustedImprovement

/-! ## Axiom audit — LIVE, not commented out -/

#print axioms PrincipiaTractalis.Ch29AdjustedImprovement.penalty_strictly_decreases_improvement
#print axioms PrincipiaTractalis.Ch29AdjustedImprovement.chiSq_figures_consistent
#print axioms PrincipiaTractalis.Ch29AdjustedImprovement.unadjusted_lt_printed
#print axioms PrincipiaTractalis.Ch29AdjustedImprovement.unadjusted_bracket
#print axioms PrincipiaTractalis.Ch29AdjustedImprovement.printed_adjusted_not_a_penalised_value
#print axioms PrincipiaTractalis.Ch29AdjustedImprovement.adjustment_moves_wrong_direction
#print axioms PrincipiaTractalis.Ch29AdjustedImprovement.required_inputs_absent_from_chapter
#print axioms PrincipiaTractalis.Ch29AdjustedImprovement.bic_restatement_inconsistent
#print axioms PrincipiaTractalis.Ch29AdjustedImprovement.Ch29AdjustedImprovement_capstone
#print axioms PrincipiaTractalis.Ch29AdjustedImprovement.penalised_ratio_is_a_real_quantity
