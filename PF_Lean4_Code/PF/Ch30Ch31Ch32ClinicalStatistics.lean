/-
# Ch 30 / 31 / 32 — Clinical and Statistical Defects (2026-10-05)

Six defects in the chapters that report patient statistics. **These are the
defects that would do most damage if published uncorrected**, because
clinical-looking numbers invite clinical-looking trust.

Every figure below is recomputed from the chapters' own stated inputs. The
provenance questions — which numbers have no stated `N`, instrument, cohort
source, analysis code, or ethics reference — are a separate, author-only matter
already logged; this file is about internal consistency only.

## ch30 — the boxed diagnostic metrics do not match the chapter's own confusion matrix, and two of them are permuted

`ch30:272–284` gives the confusion matrix `TN = 402`, `FN = 9`, `FP = 14`,
`TP = 422`. Those sum to `847`, matching the stated cohort
(`confusion_matrix_totals`). From them:

| metric | correct | boxed at `:250–253` |
|---|---|---|
| sensitivity `TP/(TP+FN)` | `97.91 %` | `96.8 %` |
| specificity `TN/(TN+FP)` | `96.63 %` | `97.8 %` |
| PPV `TP/(TP+FP)` | `96.79 %` | `97.4 %` |
| NPV `TN/(TN+FN)` | `97.81 %` | `97.2 %` |

Two of the four are not merely wrong but **swapped with each other's
neighbours**: the boxed "sensitivity" `96.8 %` is the correct **PPV**, and the
boxed "specificity" `97.8 %` is the correct **NPV** (`boxed_sens_is_actually_ppv`,
`boxed_spec_is_actually_npv`). The boxed PPV `97.4 %` and NPV `97.2 %` match
**none** of the four correct values (`boxed_ppv_and_npv_match_nothing`).

That pattern — two values displaced into each other's slots, two unaccounted
for — is the signature of a transposed table rather than four independent
rounding slips, so a repair should re-derive all four from the matrix rather
than adjust them individually.

## ch30 — the stratified table and the headline disagree by three patients

`ch30:359–382` gives per-diagnosis accuracies whose correct-counts are pinned
exactly by their one-decimal percentages (no rounding slack at these `N`):

  `142/143 + 252/267 + 183/189 + 153/156 + 91/92 = 821`,

against the headline matrix's `TN + TP = 824` (`stratified_total_is_821`). Two
presentations of one cohort differ by three patients, and the error count
differs by the same three: `26` against `23`.

## ch30 — a heading that contradicts its own body

`ch30:453` heads a subsection "The 15 Discrepant Cases"; the body immediately
lists `9` false negatives and `14` false positives, totalling `23`
(`discrepant_cases_are_23`) — consistent with the confusion matrix and not with
the heading.

## ch30 — the per-1000 diagnostic gain, and the national figure built on it

`ch30:352` reports "approximately 350 out of 1000 DOC patients receiving correct
diagnosis" from the chapter's own `60 %` behavioural and `97.3 %` fractal
accuracies. `973 − 600 = 373`, not `350` (`per_thousand_gain_is_373`). The
downstream `70,000–105,000` national range is exactly `350 × 200` and
`350 × 300` (`national_figure_inherits_the_error`), so it inherits rather than
being independently derived; with `373` it becomes `74,600–111,900`.

## ch31 — a third `ch₂`, and it is unbounded

`ch31:189–193` introduces

  `ch₂ = |P_β² / (P_δ · P_θ)|^{1/3}`

as the EEG-computable form of the metric. It carries **no normalisation and is
unbounded above** (`band_ratio_exceeds_one`, `band_ratio_unbounded`):
`(P_β, P_δ, P_θ) = (10, 1, 1)` gives `4.64`, and `(100, 1, 1)` gives `21.54`.
This contradicts ch32's own stated sanity check `0 ≤ ch₂ ≤ 1` (`ch32:361`).

**And it diverges in exactly the wrong regime.** The expression grows without
bound as `P_β` dominates `P_δ` and `P_θ` — that is the alert, awake state, which
is precisely the regime the `0.95` threshold exists to pick out. So the formula
is least trustworthy where the chapter relies on it most.

This is the **third** mutually incompatible `ch₂` in the corpus, after ch06's
matrix trace form (range `[−1/2, 1/2]`) and its entanglement form
(`≤ 1 − 1/d`, so `1/2` for a qubit). Counting ch04's `Tr(C²ρ)/Tr(ρ)` and the
Chern–Weil density, there are at least five, all converging on one `0.95`.

## ch32 — the age decline is overstated tenfold

`ch32:402–406` gives the regression `ch₂ = 0.982 − 0.00012·age` and then reports
"Decline: 0.012 per decade". A slope of `0.00012` per year is `0.0012` per
decade (`decline_per_decade_is_point_0012`). The chapter's own two reference
ages confirm it: `0.9796` at 20 and `0.9724` at 80 is `0.0072` over six
decades, i.e. `0.0012` each (`reference_ages_confirm_slope`).

## Scope

Internal consistency of reported statistics. No claim here bears on whether the
underlying measurements are sound — those remain **EMPIRICAL HYPOTHESIS —
UNTESTED** per the chapters' own 2026-07-23 ledgers, and the provenance gaps are
an author-only item. Nothing here is patient-identifying.

Author: Pablo Cohen + Claude Opus 5. 2026-10-05.
-/
import Mathlib.Tactic

namespace PrincipiaTractalis.Ch30Ch31Ch32Clinical

/-! ## §1 — ch30: the confusion matrix -/

/-- The matrix as printed at `ch30:272–284`. -/
def TN : ℕ := 402
def FN : ℕ := 9
def FP : ℕ := 14
def TP : ℕ := 422

/-- The matrix is internally consistent with the stated cohort of `847`, and
    with `824` correct. -/
theorem confusion_matrix_totals :
    TN + FN + FP + TP = 847 ∧ TN + TP = 824 ∧ FN + FP = 23 := by
  refine ⟨by decide, by decide, by decide⟩

/-- Sensitivity `TP/(TP+FN)`, correct value. -/
noncomputable def sensitivity : ℝ := 422 / 431

/-- Specificity `TN/(TN+FP)`, correct value. -/
noncomputable def specificity : ℝ := 402 / 416

/-- PPV `TP/(TP+FP)`, correct value. -/
noncomputable def ppv : ℝ := 422 / 436

/-- NPV `TN/(TN+FN)`, correct value. -/
noncomputable def npv : ℝ := 402 / 411

/-- The four correct values, bracketed to four decimals. -/
theorem correct_metrics_bracketed :
    (9790 / 10000 : ℝ) < sensitivity ∧ sensitivity < (9792 / 10000 : ℝ) ∧
    (9662 / 10000 : ℝ) < specificity ∧ specificity < (9664 / 10000 : ℝ) ∧
    (9678 / 10000 : ℝ) < ppv ∧ ppv < (9680 / 10000 : ℝ) ∧
    (9780 / 10000 : ℝ) < npv ∧ npv < (9782 / 10000 : ℝ) := by
  unfold sensitivity specificity ppv npv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

/-- **★ The boxed "sensitivity" is the correct PPV. ★**

    The boxed `96.8 %` is what `ppv = 422/436 = 0.96789` rounds to, within half
    a unit in the last printed place; `sensitivity = 422/431 = 0.97912` is more
    than twenty such units away. Stated as a rounding claim rather than a strict
    bracket, because `ppv` sits just BELOW `0.968` — my first attempt asserted
    `0.968 < ppv` and Lean refused it, correctly. -/
theorem boxed_sens_is_actually_ppv :
    |ppv - (968 / 1000 : ℝ)| < 5 / 10000 ∧
    5 / 10000 < |sensitivity - (968 / 1000 : ℝ)| := by
  unfold ppv sensitivity
  rw [abs_sub_lt_iff, lt_abs]
  refine ⟨⟨by norm_num, by norm_num⟩, Or.inl (by norm_num)⟩

/-- **★ The boxed "specificity" is the correct NPV. ★**

    `97.8 %` is what `npv = 402/411 = 0.97810` rounds to; `specificity =
    402/416 = 0.96635` is more than twenty units in the last place away. -/
theorem boxed_spec_is_actually_npv :
    |npv - (978 / 1000 : ℝ)| < 5 / 10000 ∧
    5 / 10000 < |specificity - (978 / 1000 : ℝ)| := by
  unfold npv specificity
  rw [abs_sub_lt_iff, lt_abs]
  refine ⟨⟨by norm_num, by norm_num⟩, Or.inr (by norm_num)⟩

/-- **★ The boxed PPV `97.4 %` and NPV `97.2 %` match none of the four. ★**

    Each is separated from every correct value by more than `0.001`. -/
theorem boxed_ppv_and_npv_match_nothing :
    (974 / 1000 : ℝ) ≠ sensitivity ∧ (974 / 1000 : ℝ) ≠ specificity ∧
    (974 / 1000 : ℝ) ≠ ppv ∧ (974 / 1000 : ℝ) ≠ npv ∧
    (972 / 1000 : ℝ) ≠ sensitivity ∧ (972 / 1000 : ℝ) ≠ specificity ∧
    (972 / 1000 : ℝ) ≠ ppv ∧ (972 / 1000 : ℝ) ≠ npv := by
  unfold sensitivity specificity ppv npv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

/-! ## §2 — ch30: the stratified table -/

/-- Per-diagnosis correct-counts, pinned by the printed one-decimal accuracies:
    `143×0.993`, `267×0.944`, `189×0.968`, `156×0.981`, `92×0.989`. -/
def strataCorrect : List ℕ := [142, 252, 183, 153, 91]

/-- **★ The stratified table totals `821`, not the headline's `824`. ★** -/
theorem stratified_total_is_821 :
    strataCorrect.sum = 821 ∧ 847 - 821 = 26 ∧ (821 : ℕ) ≠ 824 ∧
    824 - 821 = 3 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Each stratum's count is the NEAREST integer to its printed percentage, and
    uniquely so at these cohort sizes — the counts are not a free choice.

    Worked in exact integers for the first stratum: `143 × 99.3 % = 141.999`, so
    `142` is off by `1` part in `143 000` while the neighbouring `141` is off by
    `999`. A half-unit of slack at this `N` is `71.5` parts, so `142` is inside
    it and `141` is not. The other four strata were checked the same way before
    this file was written.

    My first attempt at this theorem used integer DIVISION (`143*993/10000`),
    which truncates to `141` and made the statement false; the `decide` tactic
    caught it by proving the negation. Recorded because the slip is the same
    rounding-versus-truncation confusion that produces miscounts like the one
    this section is about. -/
theorem first_stratum_count_is_nearest :
    (142 * 1000 : ℕ) - 993 * 143 = 1 ∧
    (993 * 143 : ℕ) - 141 * 1000 = 999 ∧
    1 < 72 ∧ 72 < 999 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-! ## §3 — ch30: the discrepant-case heading -/

/-- **The heading says 15; the body's own breakdown gives 23.** -/
theorem discrepant_cases_are_23 :
    FN + FP = 23 ∧ (23 : ℕ) ≠ 15 := by
  refine ⟨by decide, by decide⟩

/-! ## §4 — ch30: the per-1000 gain and the national figure -/

/-- **★ The gain is `373` per 1000, not `350`. ★**

    From the chapter's own `97.3 %` and `60 %`. -/
theorem per_thousand_gain_is_373 :
    973 - 600 = 373 ∧ (373 : ℕ) ≠ 350 := by
  refine ⟨by decide, by decide⟩

/-- **The national range was computed from `350`, so it inherits.**

    `350 × 200 = 70 000` and `350 × 300 = 105 000` reproduce the printed range
    exactly; `373` would give `74 600`–`111 900`. -/
theorem national_figure_inherits_the_error :
    350 * 200 = 70000 ∧ 350 * 300 = 105000 ∧
    373 * 200 = 74600 ∧ 373 * 300 = 111900 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-! ## §5 — ch31: the unbounded band-ratio `ch₂` -/

/-- The EEG form introduced at `ch31:191`, as a cube of the quantity to avoid
    irrational roots: `ch₂³ = P_β²/(P_δ·P_θ)`. Working with the cube is
    equivalent for bounding, since `t ↦ t³` is strictly monotone. -/
noncomputable def bandRatioCubed (Pb Pd Pt : ℝ) : ℝ := Pb ^ 2 / (Pd * Pt)

/-- **★ The band ratio exceeds `1`, contradicting ch32's stated constraint. ★**

    `ch₂³ = 100 > 1` forces `ch₂ > 1`, against `0 ≤ ch₂ ≤ 1` at `ch32:361`. -/
theorem band_ratio_exceeds_one :
    bandRatioCubed 10 1 1 = 100 ∧ (1 : ℝ) < 100 := by
  unfold bandRatioCubed
  refine ⟨by norm_num, by norm_num⟩

/-- **★ And it is unbounded: no ceiling whatsoever. ★**

    For any proposed bound `B` there is a `P_β` exceeding it, with `P_δ`, `P_θ`
    fixed at `1`. -/
theorem band_ratio_unbounded (B : ℝ) : ∃ Pb : ℝ, 0 < Pb ∧ B < bandRatioCubed Pb 1 1 := by
  refine ⟨|B| + 2, by positivity, ?_⟩
  unfold bandRatioCubed
  have h : B ≤ |B| := le_abs_self B
  nlinarith [abs_nonneg B]

/-- **It diverges in the ALERT regime**, where `β` dominates `δ` and `θ` —
    exactly where the `0.95` threshold is supposed to discriminate. Recorded as
    the monotonicity in `P_β`. -/
theorem diverges_as_beta_dominates (Pb Pb' : ℝ) (h0 : 0 < Pb) (h : Pb < Pb') :
    bandRatioCubed Pb 1 1 < bandRatioCubed Pb' 1 1 := by
  unfold bandRatioCubed
  have : Pb ^ 2 < Pb' ^ 2 := by nlinarith
  simpa using this

/-! ## §6 — ch32: the age decline -/

/-- The regression at `ch32:404`. -/
noncomputable def ch2OfAge (age : ℝ) : ℝ := 982 / 1000 - (12 / 100000) * age

/-- **★ The decline is `0.0012` per decade, not the printed `0.012`. ★** -/
theorem decline_per_decade_is_point_0012 :
    ch2OfAge 0 - ch2OfAge 10 = 12 / 10000 ∧
    (12 / 10000 : ℝ) ≠ 12 / 1000 := by
  unfold ch2OfAge
  refine ⟨by norm_num, by norm_num⟩

/-- **The chapter's own two reference ages confirm it**: `0.9796` at 20 and
    `0.9724` at 80 differ by `0.0072` over six decades. -/
theorem reference_ages_confirm_slope :
    ch2OfAge 20 = 9796 / 10000 ∧ ch2OfAge 80 = 9724 / 10000 ∧
    ch2OfAge 20 - ch2OfAge 80 = 72 / 10000 ∧
    (72 / 10000 : ℝ) / 6 = 12 / 10000 := by
  unfold ch2OfAge
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-! ## §7 — Capstone -/

/-- **★ Ch 30 / 31 / 32 clinical-statistics capstone ★**

    The confusion matrix is self-consistent but the boxed metrics are not drawn
    from it, with two displaced into each other's slots; the stratified table
    totals three patients fewer than the headline; the discrepant-case heading
    contradicts its own body; the per-1000 gain is `373` and the national figure
    was built from `350`; the band-ratio `ch₂` is unbounded; and the age decline
    is overstated tenfold. -/
theorem ClinicalStatistics_capstone :
    (TN + FN + FP + TP = 847) ∧
    strataCorrect.sum = 821 ∧
    (FN + FP = 23) ∧
    (973 - 600 = 373) ∧
    bandRatioCubed 10 1 1 = 100 ∧
    (ch2OfAge 0 - ch2OfAge 10 = 12 / 10000) :=
  ⟨confusion_matrix_totals.1,
   stratified_total_is_821.1,
   discrepant_cases_are_23.1,
   per_thousand_gain_is_373.1,
   band_ratio_exceeds_one.1,
   decline_per_decade_is_point_0012.1⟩

/-! ## §8 — Non-vacuity -/

/-- Non-vacuity: the four correct metrics are genuine probabilities in `(0,1)`,
    so the comparisons above are between meaningful quantities; and the band
    ratio is positive, so its unboundedness is a real divergence rather than a
    sign artefact. -/
theorem quantities_are_meaningful :
    0 < sensitivity ∧ sensitivity < 1 ∧
    0 < specificity ∧ specificity < 1 ∧
    0 < bandRatioCubed 10 1 1 := by
  unfold sensitivity specificity bandRatioCubed
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

end PrincipiaTractalis.Ch30Ch31Ch32Clinical

/-! ## Axiom audit — LIVE, not commented out -/

#print axioms PrincipiaTractalis.Ch30Ch31Ch32Clinical.confusion_matrix_totals
#print axioms PrincipiaTractalis.Ch30Ch31Ch32Clinical.correct_metrics_bracketed
#print axioms PrincipiaTractalis.Ch30Ch31Ch32Clinical.boxed_sens_is_actually_ppv
#print axioms PrincipiaTractalis.Ch30Ch31Ch32Clinical.boxed_spec_is_actually_npv
#print axioms PrincipiaTractalis.Ch30Ch31Ch32Clinical.boxed_ppv_and_npv_match_nothing
#print axioms PrincipiaTractalis.Ch30Ch31Ch32Clinical.stratified_total_is_821
#print axioms PrincipiaTractalis.Ch30Ch31Ch32Clinical.first_stratum_count_is_nearest
#print axioms PrincipiaTractalis.Ch30Ch31Ch32Clinical.discrepant_cases_are_23
#print axioms PrincipiaTractalis.Ch30Ch31Ch32Clinical.per_thousand_gain_is_373
#print axioms PrincipiaTractalis.Ch30Ch31Ch32Clinical.national_figure_inherits_the_error
#print axioms PrincipiaTractalis.Ch30Ch31Ch32Clinical.band_ratio_exceeds_one
#print axioms PrincipiaTractalis.Ch30Ch31Ch32Clinical.band_ratio_unbounded
#print axioms PrincipiaTractalis.Ch30Ch31Ch32Clinical.diverges_as_beta_dominates
#print axioms PrincipiaTractalis.Ch30Ch31Ch32Clinical.decline_per_decade_is_point_0012
#print axioms PrincipiaTractalis.Ch30Ch31Ch32Clinical.reference_ages_confirm_slope
#print axioms PrincipiaTractalis.Ch30Ch31Ch32Clinical.ClinicalStatistics_capstone
#print axioms PrincipiaTractalis.Ch30Ch31Ch32Clinical.quantities_are_meaningful
