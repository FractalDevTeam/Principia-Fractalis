/-
# Principia Fractalis — α-Affine Target-Anchored Score
  (formerly "Consciousness Quantification via the Second Chern Character")

**Semantic status (Phase B, 2026-09-14) per
`codex/CH2_SEMANTIC_DISAMBIGUATION_LEDGER_2026-09-14.md`.**

This file formalizes the manuscript's **α-affine target-anchored
score** `alphaAffineScore(α) := 0.95 + (α − √2)/10`, a real-valued
affine function of one real parameter α. The historical file name
"ChernCharacter.lean" and its top-level identifier `ch_2` implied
identification with the second Chern character of Chern–Weil theory.
That identification is not established by anything in this file.

**Precise statement of what is and is not in this file:**

- IS: an affine function `alphaAffineScore : ℝ → ℝ` (S1 in the
  ledger), plus evaluations at the eight canonical Millennium
  α-values, plus monotonicity and a threshold-iff.
- IS NOT: a construction of the second Chern character
  `(1/8π²) Tr(F ∧ F)` (ledger S7). No bundle, connection, or
  curvature data appears here.
- IS NOT: a linear entropy `1 − Tr(ρ²)` (ledger S3). That object
  lives in `PF/Consciousness/Ch2PhiBridgeDischarge.lean`.
- IS NOT: a proof of consciousness. The predicate
  `alphaAffineScore α ≥ 0.95` is a numerical inequality between
  a real-valued affine expression and a postulated threshold; it
  does not establish any conscious-state property of any physical
  system.

**The value `0.95` is a definitional input**, not a derivation. The
target-anchored intercept is what makes `alphaAffineScore(√2) = 0.95`
hold algebraically. See `ch06_consciousness.tex:188–198` remark
2026-07-01 for the manuscript's honest-scope acknowledgement that
0.95 is a phenomenological anchor.

Canonical names introduced in this file:
- `alphaAffineScore` — canonical re-export of
  `PrincipiaTractalis.MillenniumSix.alphaAffineScore`.
- `alphaAffineScoreThreshold95` — canonical re-export of
  `PrincipiaTractalis.consciousnessThreshold95` (the postulated
  19/20 constant).
- Canonical-name evaluation theorems `alphaAffineScore_at_alpha_*`
  (evaluations of the definition at the eight canonical α-values;
  NOT derivations).
- Canonical `alphaAffineScore_slope`, `alphaAffineScore_strict_mono`,
  `alphaAffineScore_mono`, `alphaAffineScore_threshold_iff`.

Old identifiers (`ch_2`, `consciousness_threshold`, and every
`ch_2_at_alpha_*` theorem) are retained as `@[deprecated]`
compatibility aliases; downstream code continues to build.

## Status

ZERO project axioms. All theorems here reduce, by pure arithmetic,
to the affine form `alphaAffineScore(α) = 0.95 + (α − √2)/10`.
-/

import PF.MillenniumSixReductions
import PF.IntervalArithmetic
import PF.ChernWeil

namespace PrincipiaTractalis.Consciousness

open PrincipiaTractalis
open PrincipiaTractalis.MillenniumSix

/-! ## Canonical: α-affine target-anchored score

We reuse the canonical `alphaAffineScore` already defined in
`PF.MillenniumSixReductions`:

    `alphaAffineScore (α : ℝ) : ℝ := 0.95 + (α − √2) / 10`

Semantic class: S1 in the ledger. This is a target-anchored affine
function, not a Chern–Weil form.
-/

/-- **Postulated 19/20 threshold** (re-export of
    `PrincipiaTractalis.consciousnessThreshold95`).

    This is the crystallization value `0.95`, a phenomenological
    anchor per `ch06_consciousness.tex:188–198` remark 2026-07-01,
    not a first-principles derived value. -/
noncomputable def alphaAffineScoreThreshold95 : ℝ :=
  PrincipiaTractalis.consciousnessThreshold95

@[simp] theorem alphaAffineScoreThreshold95_val :
    alphaAffineScoreThreshold95 = 0.95 := rfl

/-- Deprecated alias for `alphaAffineScoreThreshold95`. -/
@[deprecated alphaAffineScoreThreshold95 (since := "2026-09-14")]
def consciousness_threshold : ℝ := 0.95

@[simp] theorem consciousness_threshold_val :
    consciousness_threshold = 0.95 := rfl

/-- **`alphaAffineScore` as a function of the resonance parameter α**:
    `alphaAffineScore(α) := 0.95 + (α − √2)/10`.
    Re-export of `MillenniumSix.alphaAffineScore` for isolated reading
    of this file. -/
noncomputable def alphaAffineScore (α : ℝ) : ℝ :=
  MillenniumSix.alphaAffineScore α

@[simp] theorem alphaAffineScore_def (α : ℝ) :
    alphaAffineScore α = 0.95 + (α - Real.sqrt 2) / 10 := rfl

/-- Deprecated alias for `alphaAffineScore`. The old name `ch_2`
    misleadingly implied identification with the second Chern
    character; this Lean binding is a target-anchored affine function.
    Retained for downstream compatibility. -/
@[deprecated alphaAffineScore (since := "2026-09-14")]
noncomputable def ch_2 (α : ℝ) : ℝ := alphaAffineScore α

@[simp] theorem ch_2_def (α : ℝ) :
    ch_2 α = 0.95 + (α - Real.sqrt 2) / 10 := rfl

/-! ## P-class anchor: `alphaAffineScore(√2) = 0.95` exactly

**This is EVALUATION of the target-anchored definition at its anchor,
not a derivation of the 0.95 threshold.** The value 0.95 was placed
in the definition; extracting it back is algebraic tautology. -/

/-- **α-affine score at the P-class anchor**: evaluation, not
    derivation. -/
theorem alphaAffineScore_at_alpha_P_eq_threshold :
    alphaAffineScore (Real.sqrt 2) = 0.95 := by
  unfold alphaAffineScore MillenniumSix.alphaAffineScore
  ring

/-- Deprecated alias for `alphaAffineScore_at_alpha_P_eq_threshold`. -/
@[deprecated alphaAffineScore_at_alpha_P_eq_threshold (since := "2026-09-14")]
theorem ch_2_at_alpha_P_eq_threshold :
    ch_2 (Real.sqrt 2) = 0.95 :=
  alphaAffineScore_at_alpha_P_eq_threshold

/-- **P-class via the canonical enum**:
    `alphaAffineScore(alpha_value .P) = 0.95`. -/
theorem alphaAffineScore_at_alpha_value_P :
    alphaAffineScore (MillenniumSix.alpha_value .P) = 0.95 := by
  rw [show MillenniumSix.alpha_value .P = Real.sqrt 2 from
        MillenniumSix.alpha_value_P]
  exact alphaAffineScore_at_alpha_P_eq_threshold

/-- Deprecated alias for `alphaAffineScore_at_alpha_value_P`. -/
@[deprecated alphaAffineScore_at_alpha_value_P (since := "2026-09-14")]
theorem ch_2_at_alpha_value_P :
    ch_2 (MillenniumSix.alpha_value .P) = 0.95 :=
  alphaAffineScore_at_alpha_value_P

/-! ## NP-class: `alphaAffineScore(φ + 1/4) > 0.95` -/

/-- **α-affine score at α_NP = φ + 1/4** is strictly above the P-anchor
    intercept. Follows from `φ + 1/4 > √2` and the affine form. -/
theorem alphaAffineScore_at_alpha_NP_gt_threshold :
    (0.95 : ℝ) < alphaAffineScore (phi + 1/4) := by
  unfold alphaAffineScore MillenniumSix.alphaAffineScore
  have h : Real.sqrt 2 < phi + 1/4 := phi_plus_quarter_gt_sqrt2
  linarith

/-- Deprecated alias. -/
@[deprecated alphaAffineScore_at_alpha_NP_gt_threshold (since := "2026-09-14")]
theorem ch_2_at_alpha_NP_gt_threshold :
    (0.95 : ℝ) < ch_2 (phi + 1/4) :=
  alphaAffineScore_at_alpha_NP_gt_threshold

/-- **NP-class via the canonical enum**. -/
theorem alphaAffineScore_at_alpha_value_NP_gt_threshold :
    (0.95 : ℝ) < alphaAffineScore (MillenniumSix.alpha_value .NP) := by
  simp only [MillenniumSix.alpha_value_NP]
  exact alphaAffineScore_at_alpha_NP_gt_threshold

/-- Deprecated alias. -/
@[deprecated alphaAffineScore_at_alpha_value_NP_gt_threshold (since := "2026-09-14")]
theorem ch_2_at_alpha_value_NP_gt_threshold :
    (0.95 : ℝ) < ch_2 (MillenniumSix.alpha_value .NP) :=
  alphaAffineScore_at_alpha_value_NP_gt_threshold

/-- **NP-class closed form**:
    `alphaAffineScore(φ + 1/4) = 0.95 + ((φ + 1/4) − √2)/10`. -/
theorem alphaAffineScore_at_alpha_NP_closed_form :
    alphaAffineScore (phi + 1/4) = 0.95 + (phi + 1/4 - Real.sqrt 2) / 10 := by
  unfold alphaAffineScore MillenniumSix.alphaAffineScore
  rfl

/-- Deprecated alias. -/
@[deprecated alphaAffineScore_at_alpha_NP_closed_form (since := "2026-09-14")]
theorem ch_2_at_alpha_NP_closed_form :
    ch_2 (phi + 1/4) = 0.95 + (phi + 1/4 - Real.sqrt 2) / 10 :=
  alphaAffineScore_at_alpha_NP_closed_form

/-! ## Monotonicity: `alphaAffineScore` is strictly increasing in α -/

/-- **Affine slope**: the slope of `alphaAffineScore` in α is `1/10`. -/
theorem alphaAffineScore_slope (α β : ℝ) :
    alphaAffineScore β - alphaAffineScore α = (β - α) / 10 := by
  unfold alphaAffineScore MillenniumSix.alphaAffineScore
  ring

/-- Deprecated alias. -/
@[deprecated alphaAffineScore_slope (since := "2026-09-14")]
theorem ch_2_slope (α β : ℝ) :
    ch_2 β - ch_2 α = (β - α) / 10 :=
  alphaAffineScore_slope α β

/-- **`alphaAffineScore` is strictly monotone**: globally on ℝ.
    Pure algebra from the affine form with positive slope 1/10. -/
theorem alphaAffineScore_strict_mono : StrictMono alphaAffineScore := by
  intro α β hαβ
  have h : alphaAffineScore β - alphaAffineScore α = (β - α) / 10 :=
    alphaAffineScore_slope α β
  have hpos : 0 < (β - α) / 10 := by
    have : 0 < β - α := sub_pos.mpr hαβ
    linarith
  linarith

/-- Deprecated alias. -/
@[deprecated alphaAffineScore_strict_mono (since := "2026-09-14")]
theorem ch_2_strict_mono : StrictMono ch_2 :=
  alphaAffineScore_strict_mono

/-- **`alphaAffineScore` is monotone (non-strict)**. -/
theorem alphaAffineScore_mono : Monotone alphaAffineScore :=
  alphaAffineScore_strict_mono.monotone

/-- Deprecated alias. -/
@[deprecated alphaAffineScore_mono (since := "2026-09-14")]
theorem ch_2_mono : Monotone ch_2 := alphaAffineScore_mono

/-! ## The threshold criterion (iff form)

**Nomenclature note.** The historical name `ch_2_threshold_iff` and
its "crystallization" phrasing suggested a physical phase transition.
The Lean content is purely algebraic: `0.95 ≤ affine(α) ↔ √2 ≤ α`,
where affine is target-anchored so that its intercept is 0.95 at
α = √2. No physical claim is proved. -/

/-- **Affine-threshold iff α ≥ √2**:
    `0.95 ≤ alphaAffineScore α ↔ √2 ≤ α`. Purely algebraic
    consequence of the affine form. -/
theorem alphaAffineScore_threshold_iff (α : ℝ) :
    (0.95 : ℝ) ≤ alphaAffineScore α ↔ Real.sqrt 2 ≤ α := by
  unfold alphaAffineScore MillenniumSix.alphaAffineScore
  constructor
  · intro h
    have h10 : (0 : ℝ) ≤ (α - Real.sqrt 2) / 10 := by linarith
    have : (0 : ℝ) ≤ α - Real.sqrt 2 := by linarith
    linarith
  · intro h
    have : (0 : ℝ) ≤ α - Real.sqrt 2 := by linarith
    have h10 : (0 : ℝ) ≤ (α - Real.sqrt 2) / 10 := by linarith
    linarith

/-- Deprecated alias for `alphaAffineScore_threshold_iff`. -/
@[deprecated alphaAffineScore_threshold_iff (since := "2026-09-14")]
theorem ch_2_threshold_iff (α : ℝ) :
    (0.95 : ℝ) ≤ ch_2 α ↔ Real.sqrt 2 ≤ α :=
  alphaAffineScore_threshold_iff α

/-- **Strict affine-threshold iff α > √2**. -/
theorem alphaAffineScore_strict_threshold_iff (α : ℝ) :
    (0.95 : ℝ) < alphaAffineScore α ↔ Real.sqrt 2 < α := by
  unfold alphaAffineScore MillenniumSix.alphaAffineScore
  constructor
  · intro h
    have : (0 : ℝ) < α - Real.sqrt 2 := by linarith
    linarith
  · intro h
    have : (0 : ℝ) < α - Real.sqrt 2 := by linarith
    have h10 : (0 : ℝ) < (α - Real.sqrt 2) / 10 := by linarith
    linarith

/-- Deprecated alias. -/
@[deprecated alphaAffineScore_strict_threshold_iff (since := "2026-09-14")]
theorem ch_2_strict_threshold_iff (α : ℝ) :
    (0.95 : ℝ) < ch_2 α ↔ Real.sqrt 2 < α :=
  alphaAffineScore_strict_threshold_iff α

/-! ## Evaluations at the 8 canonical α-values

Under the target-anchored affine form `alphaAffineScore(α) = 0.95 + (α − √2)/10`,
each evaluation below is algebraic substitution — none is a derivation
of consciousness, a physical prediction, or a Chern–Weil computation.

  * Poincaré (α=1):    `alphaAffineScore = 0.95 − (√2−1)/10 < 0.95`
  * P     (α=√2):       `alphaAffineScore = 0.95`
  * RH    (α=3/2):      `alphaAffineScore = 0.95 + (3/2−√2)/10 > 0.95`
  * Hodge (α=φ):        `alphaAffineScore = 0.95 + (φ−√2)/10 > 0.95`
  * NP    (α=φ+1/4):    `alphaAffineScore = 0.95 + (φ+1/4−√2)/10 > 0.95`
  * YM    (α=2):        `alphaAffineScore = 0.95 + (2−√2)/10 > 0.95`
  * BSD   (α=3π/4):     `alphaAffineScore = 0.95 + (3π/4−√2)/10 > 0.95`
  * NS    (α=3π/2):     `alphaAffineScore = 0.95 + (3π/2−√2)/10 > 0.95`
-/

/-- **Poincaré-class** (α = 1): closed form. -/
theorem alphaAffineScore_at_alpha_Poincare :
    alphaAffineScore (MillenniumSix.alpha_value .Poincare) =
      0.95 + (1 - Real.sqrt 2) / 10 := by
  simp [MillenniumSix.alpha_value_Poincare, alphaAffineScore_def]

/-- Deprecated alias. -/
@[deprecated alphaAffineScore_at_alpha_Poincare (since := "2026-09-14")]
theorem ch_2_at_alpha_Poincare :
    ch_2 (MillenniumSix.alpha_value .Poincare) =
      0.95 + (1 - Real.sqrt 2) / 10 :=
  alphaAffineScore_at_alpha_Poincare

/-- **Poincaré-class evaluation lies below the 0.95 anchor** since
    `1 < √2`. Purely algebraic; no physical meaning attached. -/
theorem alphaAffineScore_at_alpha_Poincare_lt_threshold :
    alphaAffineScore (MillenniumSix.alpha_value .Poincare) < (0.95 : ℝ) := by
  rw [show MillenniumSix.alpha_value .Poincare = (1 : ℝ) from
        MillenniumSix.alpha_value_Poincare]
  unfold alphaAffineScore MillenniumSix.alphaAffineScore
  have h_lb : (1.4142135623 : ℝ) ≤ Real.sqrt 2 :=
    sqrt2_in_interval_10digit.1
  linarith

/-- Deprecated alias. -/
@[deprecated alphaAffineScore_at_alpha_Poincare_lt_threshold (since := "2026-09-14")]
theorem ch_2_at_alpha_Poincare_lt_threshold :
    ch_2 (MillenniumSix.alpha_value .Poincare) < (0.95 : ℝ) :=
  alphaAffineScore_at_alpha_Poincare_lt_threshold

/-- **RH-class** (α = 3/2): closed form. -/
theorem alphaAffineScore_at_alpha_RH :
    alphaAffineScore (MillenniumSix.alpha_value .RH) =
      0.95 + (3/2 - Real.sqrt 2) / 10 := by
  simp [MillenniumSix.alpha_value_RH, alphaAffineScore_def]

/-- Deprecated alias. -/
@[deprecated alphaAffineScore_at_alpha_RH (since := "2026-09-14")]
theorem ch_2_at_alpha_RH :
    ch_2 (MillenniumSix.alpha_value .RH) =
      0.95 + (3/2 - Real.sqrt 2) / 10 :=
  alphaAffineScore_at_alpha_RH

/-- **RH-class strict inequality**: 3/2 > √2 ⟹ evaluation > 0.95. -/
theorem alphaAffineScore_at_alpha_RH_gt_threshold :
    (0.95 : ℝ) < alphaAffineScore (MillenniumSix.alpha_value .RH) := by
  rw [show MillenniumSix.alpha_value .RH = (3 : ℝ)/2 from
        MillenniumSix.alpha_value_RH]
  rw [alphaAffineScore_strict_threshold_iff]
  have h_ub : Real.sqrt 2 ≤ 1.4142135624 :=
    sqrt2_in_interval_10digit.2
  linarith

/-- Deprecated alias. -/
@[deprecated alphaAffineScore_at_alpha_RH_gt_threshold (since := "2026-09-14")]
theorem ch_2_at_alpha_RH_gt_threshold :
    (0.95 : ℝ) < ch_2 (MillenniumSix.alpha_value .RH) :=
  alphaAffineScore_at_alpha_RH_gt_threshold

/-- **Hodge-class** (α = φ): closed form. -/
theorem alphaAffineScore_at_alpha_Hodge :
    alphaAffineScore (MillenniumSix.alpha_value .Hodge) =
      0.95 + (phi - Real.sqrt 2) / 10 := by
  simp [MillenniumSix.alpha_value_Hodge, alphaAffineScore_def]

/-- Deprecated alias. -/
@[deprecated alphaAffineScore_at_alpha_Hodge (since := "2026-09-14")]
theorem ch_2_at_alpha_Hodge :
    ch_2 (MillenniumSix.alpha_value .Hodge) =
      0.95 + (phi - Real.sqrt 2) / 10 :=
  alphaAffineScore_at_alpha_Hodge

/-- **Hodge-class strict inequality**: φ > √2 ⟹ evaluation > 0.95. -/
theorem alphaAffineScore_at_alpha_Hodge_gt_threshold :
    (0.95 : ℝ) < alphaAffineScore (MillenniumSix.alpha_value .Hodge) := by
  rw [show MillenniumSix.alpha_value .Hodge = phi from
        MillenniumSix.alpha_value_Hodge]
  rw [alphaAffineScore_strict_threshold_iff]
  have h_phi_lb : (1.6180339887 : ℝ) ≤ phi :=
    phi_in_interval_10digit.1
  have h_sqrt2_ub : Real.sqrt 2 ≤ (1.4142135624 : ℝ) :=
    sqrt2_in_interval_10digit.2
  linarith

/-- Deprecated alias. -/
@[deprecated alphaAffineScore_at_alpha_Hodge_gt_threshold (since := "2026-09-14")]
theorem ch_2_at_alpha_Hodge_gt_threshold :
    (0.95 : ℝ) < ch_2 (MillenniumSix.alpha_value .Hodge) :=
  alphaAffineScore_at_alpha_Hodge_gt_threshold

/-- **NP-class** (α = φ + 1/4): closed form. -/
theorem alphaAffineScore_at_alpha_NP_full :
    alphaAffineScore (MillenniumSix.alpha_value .NP) =
      0.95 + (phi + 1/4 - Real.sqrt 2) / 10 := by
  simp [MillenniumSix.alpha_value_NP, alphaAffineScore_def]

/-- Deprecated alias. -/
@[deprecated alphaAffineScore_at_alpha_NP_full (since := "2026-09-14")]
theorem ch_2_at_alpha_NP_full :
    ch_2 (MillenniumSix.alpha_value .NP) =
      0.95 + (phi + 1/4 - Real.sqrt 2) / 10 :=
  alphaAffineScore_at_alpha_NP_full

/-- **YM-class** (α = 2): closed form. -/
theorem alphaAffineScore_at_alpha_YM :
    alphaAffineScore (MillenniumSix.alpha_value .YM) =
      0.95 + (2 - Real.sqrt 2) / 10 := by
  simp [MillenniumSix.alpha_value_YM, alphaAffineScore_def]

/-- Deprecated alias. -/
@[deprecated alphaAffineScore_at_alpha_YM (since := "2026-09-14")]
theorem ch_2_at_alpha_YM :
    ch_2 (MillenniumSix.alpha_value .YM) =
      0.95 + (2 - Real.sqrt 2) / 10 :=
  alphaAffineScore_at_alpha_YM

/-- **YM-class strict inequality**: 2 > √2 ⟹ evaluation > 0.95. -/
theorem alphaAffineScore_at_alpha_YM_gt_threshold :
    (0.95 : ℝ) < alphaAffineScore (MillenniumSix.alpha_value .YM) := by
  rw [show MillenniumSix.alpha_value .YM = (2 : ℝ) from
        MillenniumSix.alpha_value_YM]
  rw [alphaAffineScore_strict_threshold_iff]
  have h_ub : Real.sqrt 2 ≤ 1.4142135624 :=
    sqrt2_in_interval_10digit.2
  linarith

/-- Deprecated alias. -/
@[deprecated alphaAffineScore_at_alpha_YM_gt_threshold (since := "2026-09-14")]
theorem ch_2_at_alpha_YM_gt_threshold :
    (0.95 : ℝ) < ch_2 (MillenniumSix.alpha_value .YM) :=
  alphaAffineScore_at_alpha_YM_gt_threshold

/-- **BSD-class** (α = 3π/4): closed form. -/
theorem alphaAffineScore_at_alpha_BSD :
    alphaAffineScore (MillenniumSix.alpha_value .BSD) =
      0.95 + (3 * Real.pi / 4 - Real.sqrt 2) / 10 := by
  simp [MillenniumSix.alpha_value_BSD, alphaAffineScore_def]

/-- Deprecated alias. -/
@[deprecated alphaAffineScore_at_alpha_BSD (since := "2026-09-14")]
theorem ch_2_at_alpha_BSD :
    ch_2 (MillenniumSix.alpha_value .BSD) =
      0.95 + (3 * Real.pi / 4 - Real.sqrt 2) / 10 :=
  alphaAffineScore_at_alpha_BSD

/-- **BSD-class strict inequality**: 3π/4 > √2 since π > 4√2/3. -/
theorem alphaAffineScore_at_alpha_BSD_gt_threshold :
    (0.95 : ℝ) < alphaAffineScore (MillenniumSix.alpha_value .BSD) := by
  rw [show MillenniumSix.alpha_value .BSD = 3 * Real.pi / 4 from
        MillenniumSix.alpha_value_BSD]
  rw [alphaAffineScore_strict_threshold_iff]
  have h_sqrt2_ub : Real.sqrt 2 ≤ 1.4142135624 :=
    sqrt2_in_interval_10digit.2
  have h_pi_lb : (3.14159265358979323846 : ℝ) < Real.pi :=
    Real.pi_gt_d20
  linarith

/-- Deprecated alias. -/
@[deprecated alphaAffineScore_at_alpha_BSD_gt_threshold (since := "2026-09-14")]
theorem ch_2_at_alpha_BSD_gt_threshold :
    (0.95 : ℝ) < ch_2 (MillenniumSix.alpha_value .BSD) :=
  alphaAffineScore_at_alpha_BSD_gt_threshold

/-- **NS-class** (α = 3π/2): closed form. -/
theorem alphaAffineScore_at_alpha_NS :
    alphaAffineScore (MillenniumSix.alpha_value .NS) =
      0.95 + (3 * Real.pi / 2 - Real.sqrt 2) / 10 := by
  simp [MillenniumSix.alpha_value_NS, alphaAffineScore_def]

/-- Deprecated alias. -/
@[deprecated alphaAffineScore_at_alpha_NS (since := "2026-09-14")]
theorem ch_2_at_alpha_NS :
    ch_2 (MillenniumSix.alpha_value .NS) =
      0.95 + (3 * Real.pi / 2 - Real.sqrt 2) / 10 :=
  alphaAffineScore_at_alpha_NS

/-- **NS-class strict inequality**: 3π/2 > √2 since π > 2√2/3. -/
theorem alphaAffineScore_at_alpha_NS_gt_threshold :
    (0.95 : ℝ) < alphaAffineScore (MillenniumSix.alpha_value .NS) := by
  rw [show MillenniumSix.alpha_value .NS = 3 * Real.pi / 2 from
        MillenniumSix.alpha_value_NS]
  rw [alphaAffineScore_strict_threshold_iff]
  have h_sqrt2_ub : Real.sqrt 2 ≤ 1.4142135624 :=
    sqrt2_in_interval_10digit.2
  have h_pi_lb : (3.14159265358979323846 : ℝ) < Real.pi :=
    Real.pi_gt_d20
  linarith

/-- Deprecated alias. -/
@[deprecated alphaAffineScore_at_alpha_NS_gt_threshold (since := "2026-09-14")]
theorem ch_2_at_alpha_NS_gt_threshold :
    (0.95 : ℝ) < ch_2 (MillenniumSix.alpha_value .NS) :=
  alphaAffineScore_at_alpha_NS_gt_threshold

/-! ## Seven-of-eight above-anchor evaluations

Under the target-anchored affine form, exactly ONE of the eight
canonical α-values (Poincaré, α = 1) evaluates BELOW 0.95; the other
SEVEN evaluate at or above 0.95. This is a fact about the affine
function's behavior, not a physical prediction.
-/

/-- **Seven-class above-anchor bundle**: every canonical Millennium
    class except Poincaré evaluates above the 0.95 anchor under the
    target-anchored affine form. -/
theorem alphaAffineScore_seven_classes_above_anchor :
    alphaAffineScore (MillenniumSix.alpha_value .P) = 0.95 ∧
    (0.95 : ℝ) < alphaAffineScore (MillenniumSix.alpha_value .RH) ∧
    (0.95 : ℝ) < alphaAffineScore (MillenniumSix.alpha_value .Hodge) ∧
    (0.95 : ℝ) < alphaAffineScore (MillenniumSix.alpha_value .NP) ∧
    (0.95 : ℝ) < alphaAffineScore (MillenniumSix.alpha_value .YM) ∧
    (0.95 : ℝ) < alphaAffineScore (MillenniumSix.alpha_value .BSD) ∧
    (0.95 : ℝ) < alphaAffineScore (MillenniumSix.alpha_value .NS) :=
  ⟨alphaAffineScore_at_alpha_value_P,
   alphaAffineScore_at_alpha_RH_gt_threshold,
   alphaAffineScore_at_alpha_Hodge_gt_threshold,
   alphaAffineScore_at_alpha_value_NP_gt_threshold,
   alphaAffineScore_at_alpha_YM_gt_threshold,
   alphaAffineScore_at_alpha_BSD_gt_threshold,
   alphaAffineScore_at_alpha_NS_gt_threshold⟩

/-- Deprecated alias for `alphaAffineScore_seven_classes_above_anchor`.
    The old name `seven_classes_crystallize` implied a physical
    crystallization result; the actual content is an evaluation of a
    real-valued affine function at seven points. -/
@[deprecated alphaAffineScore_seven_classes_above_anchor (since := "2026-09-14")]
theorem seven_classes_crystallize :
    ch_2 (MillenniumSix.alpha_value .P) = 0.95 ∧
    (0.95 : ℝ) < ch_2 (MillenniumSix.alpha_value .RH) ∧
    (0.95 : ℝ) < ch_2 (MillenniumSix.alpha_value .Hodge) ∧
    (0.95 : ℝ) < ch_2 (MillenniumSix.alpha_value .NP) ∧
    (0.95 : ℝ) < ch_2 (MillenniumSix.alpha_value .YM) ∧
    (0.95 : ℝ) < ch_2 (MillenniumSix.alpha_value .BSD) ∧
    (0.95 : ℝ) < ch_2 (MillenniumSix.alpha_value .NS) :=
  alphaAffineScore_seven_classes_above_anchor

/-! ## Capstone bundle -/

/-- **α-affine capstone bundle**: the load-bearing algebraic facts
    about the target-anchored affine function `alphaAffineScore`.

    **This bundle asserts no physical, consciousness, or Chern–Weil
    content.** It states:
      1. `alphaAffineScore` is strictly monotone in α (slope 1/10).
      2. `0.95 ≤ alphaAffineScore α ↔ √2 ≤ α` (target-anchored iff).
      3. `alphaAffineScore(√2) = 0.95` (evaluation at the P anchor).
      4. `alphaAffineScore(φ + 1/4) > 0.95` (evaluation at α_NP).
      5. Seven of eight canonical Millennium α-values evaluate
         above the anchor; only Poincaré (α = 1) evaluates below. -/
theorem alphaAffineScore_capstone :
    StrictMono alphaAffineScore ∧
    (∀ α : ℝ, (0.95 : ℝ) ≤ alphaAffineScore α ↔ Real.sqrt 2 ≤ α) ∧
    alphaAffineScore (Real.sqrt 2) = 0.95 ∧
    (0.95 : ℝ) < alphaAffineScore (phi + 1/4) ∧
    (alphaAffineScore (MillenniumSix.alpha_value .P) = 0.95 ∧
     (0.95 : ℝ) < alphaAffineScore (MillenniumSix.alpha_value .RH) ∧
     (0.95 : ℝ) < alphaAffineScore (MillenniumSix.alpha_value .Hodge) ∧
     (0.95 : ℝ) < alphaAffineScore (MillenniumSix.alpha_value .NP) ∧
     (0.95 : ℝ) < alphaAffineScore (MillenniumSix.alpha_value .YM) ∧
     (0.95 : ℝ) < alphaAffineScore (MillenniumSix.alpha_value .BSD) ∧
     (0.95 : ℝ) < alphaAffineScore (MillenniumSix.alpha_value .NS)) :=
  ⟨alphaAffineScore_strict_mono,
   alphaAffineScore_threshold_iff,
   alphaAffineScore_at_alpha_P_eq_threshold,
   alphaAffineScore_at_alpha_NP_gt_threshold,
   alphaAffineScore_seven_classes_above_anchor⟩

/-- Deprecated alias for `alphaAffineScore_capstone`. The old name
    `consciousness_quantification_capstone` implied a proof of
    consciousness quantification; the actual content is algebraic. -/
@[deprecated alphaAffineScore_capstone (since := "2026-09-14")]
theorem consciousness_quantification_capstone :
    StrictMono ch_2 ∧
    (∀ α : ℝ, (0.95 : ℝ) ≤ ch_2 α ↔ Real.sqrt 2 ≤ α) ∧
    ch_2 (Real.sqrt 2) = 0.95 ∧
    (0.95 : ℝ) < ch_2 (phi + 1/4) ∧
    (ch_2 (MillenniumSix.alpha_value .P) = 0.95 ∧
     (0.95 : ℝ) < ch_2 (MillenniumSix.alpha_value .RH) ∧
     (0.95 : ℝ) < ch_2 (MillenniumSix.alpha_value .Hodge) ∧
     (0.95 : ℝ) < ch_2 (MillenniumSix.alpha_value .NP) ∧
     (0.95 : ℝ) < ch_2 (MillenniumSix.alpha_value .YM) ∧
     (0.95 : ℝ) < ch_2 (MillenniumSix.alpha_value .BSD) ∧
     (0.95 : ℝ) < ch_2 (MillenniumSix.alpha_value .NS)) :=
  alphaAffineScore_capstone

end PrincipiaTractalis.Consciousness
