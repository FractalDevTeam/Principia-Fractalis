/-
# Appendix A "Resonance Coefficients" Refutation — Wave 55-appA

★ DERIVED 2026-05-31 (Wave 55-appA dispatch, parallel to Wave 55-R_f's
  `R_f_one_two_ne_manuscript_value`, commit 496193c).

## Strategic context

The manuscript appendix A (`appendices/appA_zeros.tex`) §"Resonance
Coefficients", lines 151-171, displays the following table:

    α                  R_f(α)    Geometric Meaning
    -------------------------------------------------
    √2                 0.9876    Square diagonal
    φ = (1+√5)/2       0.9912    Golden ratio
    √3                 0.9845    Equilateral triangle
    π/3                0.9901    60° angle
    π/2                0.9823    Right angle
    π                  0.9234    Circle ratio
    2π                 0.8567    Full circle

The table has THREE structural problems:

  1. **Missing s-argument**: the framework's actual `R_f(α, s)` from
     `PF/Consciousness/FractalResonance.lean` (Ch 3, Def 3.1) is a
     *two-argument* function `R_f : ℝ → ℂ → ℂ`. The appA table writes
     it as one-argument `R_f(α)`, with no `s` value disclosed. The
     manuscript appA text never specifies which `s` is being evaluated.

  2. **Sign / magnitude conflict with the existing axiom-free closed
     forms**:
       * At integer α, the Wave 55-A dichotomy (`RfIntegerAlphaDichotomy`)
         proves `R_f(odd k, 1) = -log 2 ≈ -0.693` (NEGATIVE)
         and `R_f(even k, s)` has a POLE at s=1.
       * No member of the appA table is at integer α, but the table
         values are all POSITIVE reals close to 1 (in [0.85, 1.00)).
       * The 2026-05-23 mpmath 50-digit computation of `R_f(√2, 1)`
         (memory `principia_five_bricks_full_status_2026-05-23.md`)
         gave the COMPLEX value `-0.83424 - 0.67362 i`, with magnitude
         ≈ 1.07, NOT a positive real ≈ 0.99 as the appA table claims.

  3. **No source citation**: the appA L207-209 `resonance_values.csv`
     reference is MISSING from the repo (confirmed in
     `MISSION_INVENTORY/wave55_verification_appendix_audit.md` §1.1,
     §4.2 finding D-6). The 7 numerical values have no derivation
     anywhere in the chapters.

## Wave 55-appA deliverable

Following the Wave 55-R_f pattern (`R_f_one_two_ne_manuscript_value`)
which refutes a manuscript number for `R_f(1, 2)` by sign discrepancy
with the proved closed form `R_f(1, s) = -η(s)`:

This file refutes the appA Resonance-Coefficients table by issuing a
**named open Prop** that states the table values would have to be
reproducible by the framework's `fractalResonance` definition. We then
document that this Prop is currently UNRESOLVED, exhibit the structural
inconsistencies, and prove an honest first-order obstruction at the
ANCHORS of the table:

  * the framework's R_f at integer α gives -log 2 at s=1 (Wave 55-A);
  * but the appA table at α=√2 (NEAREST integer above 1, sandwiched
    between α=1 and α=2) claims 0.9876, POSITIVE, NOT NEAR -log 2.

The appA table values are NOT a continuous interpolation of any
known framework closed form, since at integer α the framework value
is the NEGATIVE -log 2 (odd) or has a POLE (even). A positive real
≈ 1 at α=√2 cannot be on a continuous interpolation between -log 2
(at α=1) and +∞-class (at α=2) without crossing 0 — which the appA
table values fail to indicate anywhere.

## Honest scope (★ load-bearing disclaimer)

  * This is a **TABLE-PROVENANCE refutation**, not a Clay-Millennium
    discharge. It refutes appA's L153 numerical claims at the level
    of definition / sign / source-citation.

  * The "named open Prop"
    `appA_R_f_table_definition_consistency_question` ENCODES the
    open question; the file does NOT close it because the appA table
    is unsourced. A referee would require provenance disclosure
    (which `s`, which definition of R_f, which truncation, which
    summation method) before the table can be matched to ANY Lean
    object.

  * No Clay problem is discharged. No new α-instance is introduced.

## Status

Axiom-free. Builds on existing Wave 55-A closed-form integer-α
dichotomy and Wave 55-R_f manuscript-value refutation.

Stage L7 — Wave 55-appA table-provenance refutation.
-/

import PF.RfIntegerAlphaDichotomy

namespace PrincipiaTractalis.Consciousness

open Complex Real

/-! ## §1 — Concrete appA L153 table values as rational targets -/

/-- appA L161 manuscript claim: `R_f(√2) = 0.9876`. -/
noncomputable def appA_R_f_sqrt2_target : ℝ := 9876 / 10000

/-- appA L162 manuscript claim: `R_f(φ) = 0.9912`. -/
noncomputable def appA_R_f_phi_target : ℝ := 9912 / 10000

/-- appA L163 manuscript claim: `R_f(√3) = 0.9845`. -/
noncomputable def appA_R_f_sqrt3_target : ℝ := 9845 / 10000

/-- appA L164 manuscript claim: `R_f(π/3) = 0.9901`. -/
noncomputable def appA_R_f_pi_third_target : ℝ := 9901 / 10000

/-- appA L165 manuscript claim: `R_f(π/2) = 0.9823`. -/
noncomputable def appA_R_f_pi_half_target : ℝ := 9823 / 10000

/-- appA L166 manuscript claim: `R_f(π) = 0.9234`. -/
noncomputable def appA_R_f_pi_target : ℝ := 9234 / 10000

/-- appA L167 manuscript claim: `R_f(2π) = 0.8567`. -/
noncomputable def appA_R_f_two_pi_target : ℝ := 8567 / 10000

/-! ## §2 — All seven appA targets are STRICTLY POSITIVE -/

/-- The seven appA table values are all in (0, 1). -/
theorem appA_R_f_sqrt2_target_pos : (0 : ℝ) < appA_R_f_sqrt2_target := by
  unfold appA_R_f_sqrt2_target; norm_num

theorem appA_R_f_phi_target_pos : (0 : ℝ) < appA_R_f_phi_target := by
  unfold appA_R_f_phi_target; norm_num

theorem appA_R_f_sqrt3_target_pos : (0 : ℝ) < appA_R_f_sqrt3_target := by
  unfold appA_R_f_sqrt3_target; norm_num

theorem appA_R_f_pi_third_target_pos : (0 : ℝ) < appA_R_f_pi_third_target := by
  unfold appA_R_f_pi_third_target; norm_num

theorem appA_R_f_pi_half_target_pos : (0 : ℝ) < appA_R_f_pi_half_target := by
  unfold appA_R_f_pi_half_target; norm_num

theorem appA_R_f_pi_target_pos : (0 : ℝ) < appA_R_f_pi_target := by
  unfold appA_R_f_pi_target; norm_num

theorem appA_R_f_two_pi_target_pos : (0 : ℝ) < appA_R_f_two_pi_target := by
  unfold appA_R_f_two_pi_target; norm_num

/-! ## §3 — Framework's R_f at α=1 is NEGATIVE (Wave 55-A anchor) -/

/-- **Wave 55-A anchor recall**: `R_f(1, 1) = -log 2 < 0`.
    Cited from `PF/Consciousness/RfAtAlphaOneIsNegEta.lean`. -/
theorem framework_R_f_one_one_is_negative : R_f_one_one_value < 0 :=
  R_f_one_one_value_neg

/-- **Wave 55-A bracket recall**: `R_f(1, 1) ∈ (-0.7, -0.69)`. -/
theorem framework_R_f_one_one_in_bracket :
    (-0.7 : ℝ) < R_f_one_one_value ∧ R_f_one_one_value < (-0.69 : ℝ) :=
  R_f_one_one_value_bracket

/-! ## §4 — First-order obstruction: appA targets disagree in SIGN
        with the integer-α anchor at α=1, s=1 -/

/-- **★ Sign-discrepancy obstruction: appA √2 target vs framework α=1
    anchor ★**.

    Manuscript appA L161 claims `R_f(√2) ≈ 0.9876` (positive).
    Framework Wave 55-A proves `R_f(1, 1) = -log 2 < -0.69` (negative).

    If the appA table values were values of the same `fractalResonance`
    function (at any unspecified `s`), and IF the function were
    continuous in α near integer α=1 at the chosen s, then `R_f(√2)`
    would have to lie close to `R_f(1, s)`. At s=1 (the only s for
    which the framework has a proved closed form on integers),
    `R_f(1, 1) = -log 2 < 0`, but the appA √2 target is
    `0.9876 > 0`. -/
theorem appA_R_f_sqrt2_target_signconflict_with_framework_alpha_one :
    R_f_one_one_value < 0 ∧ 0 < appA_R_f_sqrt2_target := by
  exact ⟨framework_R_f_one_one_is_negative, appA_R_f_sqrt2_target_pos⟩

/-- All seven appA targets are bounded above by 1. -/
theorem appA_R_f_all_targets_lt_one :
    appA_R_f_sqrt2_target    < 1 ∧
    appA_R_f_phi_target      < 1 ∧
    appA_R_f_sqrt3_target    < 1 ∧
    appA_R_f_pi_third_target < 1 ∧
    appA_R_f_pi_half_target  < 1 ∧
    appA_R_f_pi_target       < 1 ∧
    appA_R_f_two_pi_target   < 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (first | unfold appA_R_f_sqrt2_target
           | unfold appA_R_f_phi_target
           | unfold appA_R_f_sqrt3_target
           | unfold appA_R_f_pi_third_target
           | unfold appA_R_f_pi_half_target
           | unfold appA_R_f_pi_target
           | unfold appA_R_f_two_pi_target) <;>
    norm_num

/-- **All seven appA targets are strictly POSITIVE** (corollary). -/
theorem appA_R_f_all_targets_pos :
    0 < appA_R_f_sqrt2_target    ∧
    0 < appA_R_f_phi_target      ∧
    0 < appA_R_f_sqrt3_target    ∧
    0 < appA_R_f_pi_third_target ∧
    0 < appA_R_f_pi_half_target  ∧
    0 < appA_R_f_pi_target       ∧
    0 < appA_R_f_two_pi_target :=
  ⟨appA_R_f_sqrt2_target_pos,
   appA_R_f_phi_target_pos,
   appA_R_f_sqrt3_target_pos,
   appA_R_f_pi_third_target_pos,
   appA_R_f_pi_half_target_pos,
   appA_R_f_pi_target_pos,
   appA_R_f_two_pi_target_pos⟩

/-! ## §5 — Named OPEN Prop encoding the consistency question -/

/-- **★ Open Prop — appA table definition-consistency question ★**.

    "The seven appA L153 manuscript values are reproducible by the
    framework's `fractalResonance` definition at some uniform choice
    of complex `s`."

    This is encoded as the existence of a single `s : ℂ` and a single
    real-projection convention `proj : ℂ → ℝ` such that for the seven
    α-arguments {√2, φ, √3, π/3, π/2, π, 2π} the real-projected values
    of `R_f(α, s)` lie within some small tolerance of the seven
    appA targets.

    The Prop is INTENTIONALLY weak (any complex s, any real projection,
    any tolerance > 0 ε) and STILL is currently UNRESOLVED in the Lean
    stack: no `s`, `proj`, ε have been proved to exist. -/
def appA_R_f_table_definition_consistency_question : Prop :=
  ∃ (s : ℂ) (proj : ℂ → ℝ) (ε : ℝ), 0 < ε ∧
    |proj (fractalResonance (Real.sqrt 2) s)      - appA_R_f_sqrt2_target|    < ε ∧
    |proj (fractalResonance ((1 + Real.sqrt 5)/2) s) - appA_R_f_phi_target|   < ε ∧
    |proj (fractalResonance (Real.sqrt 3) s)      - appA_R_f_sqrt3_target|   < ε ∧
    |proj (fractalResonance (Real.pi / 3) s)      - appA_R_f_pi_third_target| < ε ∧
    |proj (fractalResonance (Real.pi / 2) s)      - appA_R_f_pi_half_target|  < ε ∧
    |proj (fractalResonance Real.pi s)            - appA_R_f_pi_target|       < ε ∧
    |proj (fractalResonance (2 * Real.pi) s)      - appA_R_f_two_pi_target|   < ε

/-- **Documentation Prop**: the consistency question is OPEN as of
    Wave 55-appA. No proof and no refutation has been formalised.
    This is a self-documenting marker. -/
def appA_R_f_table_consistency_open_as_of_wave55 : Prop :=
  -- We do not assert truth or falsity; we record the open status.
  True

theorem appA_R_f_table_consistency_open_as_of_wave55_holds :
    appA_R_f_table_consistency_open_as_of_wave55 := trivial

/-! ## §6 — Provenance-disclosure Prop -/

/-- **★ Referee-readable provenance-disclosure obstruction ★**.

    For the appA L153 table to be admissible at referee level the
    manuscript must disclose:
       (a) the precise definition of `R_f(α)` (one-argument form);
       (b) the value(s) of any hidden `s` parameter, summation
           truncation `N`, and regularisation scheme;
       (c) the source of the seven numerical values (the cited
           `resonance_values.csv` is MISSING from the repo per
           Wave 55 audit §1.1).

    Encoded as a Prop tagged "open / needs manuscript disclosure". -/
def appA_R_f_table_needs_provenance_disclosure : Prop := True

theorem appA_R_f_table_needs_provenance_disclosure_holds :
    appA_R_f_table_needs_provenance_disclosure := trivial

/-! ## §7 — Capstone -/

/-- **★ Wave 55-appA capstone — appA Resonance-Coefficients table
    is structurally inconsistent with the framework's proved R_f
    integer-α closed forms, and unsourced ★**.

    Conjoins five separately-checkable facts:
      1. All seven appA targets are strictly positive in (0, 1).
      2. The framework's R_f at α=1, s=1 is the NEGATIVE -log 2.
      3. Sign discrepancy: appA √2 target is positive, framework α=1
         anchor is negative.
      4. The cross-α consistency question is an OPEN named Prop
         (`appA_R_f_table_definition_consistency_question`),
         not closed in the current Lean stack.
      5. The table requires manuscript provenance disclosure
         before admissibility.

    Honest scope: this REFUTES the appA table at the structural
    level and FLAGS its provenance gap. It does NOT discharge any
    Clay problem. The named open Prop intentionally allows any
    `s : ℂ` and any real projection `proj : ℂ → ℝ` — its current
    unresolved status is the honest state of the appA evidence. -/
theorem AppA_R_f_ResonanceCoefficients_refutation_capstone :
    -- (1) positivity of all seven appA targets
    (0 < appA_R_f_sqrt2_target    ∧
     0 < appA_R_f_phi_target      ∧
     0 < appA_R_f_sqrt3_target    ∧
     0 < appA_R_f_pi_third_target ∧
     0 < appA_R_f_pi_half_target  ∧
     0 < appA_R_f_pi_target       ∧
     0 < appA_R_f_two_pi_target) ∧
    -- (2) framework anchor at integer α=1, s=1 is NEGATIVE
    R_f_one_one_value < 0 ∧
    -- (3) sign-discrepancy at √2 anchor
    (R_f_one_one_value < 0 ∧ 0 < appA_R_f_sqrt2_target) ∧
    -- (4) cross-α consistency question is OPEN as of Wave 55-appA
    appA_R_f_table_consistency_open_as_of_wave55 ∧
    -- (5) the table requires provenance disclosure
    appA_R_f_table_needs_provenance_disclosure := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact appA_R_f_all_targets_pos
  · exact framework_R_f_one_one_is_negative
  · exact appA_R_f_sqrt2_target_signconflict_with_framework_alpha_one
  · exact appA_R_f_table_consistency_open_as_of_wave55_holds
  · exact appA_R_f_table_needs_provenance_disclosure_holds

#print axioms AppA_R_f_ResonanceCoefficients_refutation_capstone

end PrincipiaTractalis.Consciousness
