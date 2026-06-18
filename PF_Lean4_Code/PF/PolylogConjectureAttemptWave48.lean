/-
# PolylogEigenvalueConjecture — Wave 48 Attack via Rigidity Reduction

★ 2026-06-18 — Wave 48 ★

## Goal of this file

Continues the Wave 47 reduction program. Wave 47 reduced
`PolylogEigenvalueConjecture` to `EmpiricalAlphaIdentificationHypothesis`
(two equalities pinning `alpha_of_class` at ClassP and ClassNP). Wave 48
reduces FURTHER to a single **rigidity** statement: `alpha_of_class`
restricted to `{ClassP, ClassNP}` is the UNIQUE map into ℝ satisfying the
polylog algebraic conditions plus positivity.

## What this file adds

  1. `polylog_admissible_pair (x y : ℝ) : Prop` — the algebraic
     conditions defining "admissible" `(alpha_of_class ClassP,
     alpha_of_class ClassNP)` pairs: `x² = 2 ∧ x > 0 ∧ 16y² − 24y − 11 = 0
     ∧ y > 0`.

  2. `polylog_admissible_pair_is_unique` — the ONLY admissible pair
     in ℝ × ℝ is `(√2, φ+1/4)`. Proven from `Real.sqrt_eq_iff_sq_eq`
     (positive square root uniqueness) and the framework's
     `alpha_NP_quadratic` together with positive-root uniqueness of
     `16y² − 24y − 11 = 0` (the unique positive root being `φ + 1/4`).

  3. `polylog_conjecture_iff_admissible_pair` —
     `PolylogEigenvalueConjecture` is equivalent to the statement
     "`(alpha_of_class ClassP, alpha_of_class ClassNP)` is an
     admissible pair." This is a definitional name-bridge.

  4. `polylog_conjecture_iff_canonical_pair_pin` — composing (2) and (3),
     `PolylogEigenvalueConjecture` is EQUIVALENT to the canonical-pair
     pin `alpha_of_class ClassP = √2 ∧ alpha_of_class ClassNP = φ + 1/4`.
     This is the rigidity result: the polylog conjecture's "algebraic
     conditions plus positivity" content is EXHAUSTED by the
     canonical-pair pin — there is no algebraic slack remaining.

## Wave 48 honest scope

This file does NOT discharge `PolylogEigenvalueConjecture`
unconditionally (the Wave 41B no-go forbids it).

It DOES sharpen the conjecture's reformulation: the algebraic content
is RIGID (single admissible pair). Hence Wave 47's
`EmpiricalAlphaIdentificationHypothesis` is the LITERAL canonical
form, not one option among many — any hypothesis discharging polylog
must imply exactly `alpha_of_class ClassP = √2 ∧ alpha_of_class
ClassNP = φ + 1/4`.

This rigidity result is one more BRICK in the polylog reduction
program: each brick narrows the gap between the opaque
`alpha_of_class` and the framework's substrate constants.

## Axiom budget

Zero project axioms, zero sorries. All theorems below depend only on
`[propext, Classical.choice, Quot.sound]`.
-/

import PF.PolylogConjectureAttemptWave47
import PF.TuringEncoding.AlphaCanonical

namespace PrincipiaTractalis.PolylogConjectureAttemptWave48

open TuringEncoding
open PrincipiaTractalis.PolylogConjectureAttemptWave47

/-! ## §1 — Admissible pair predicate -/

/-- **`polylog_admissible_pair x y`** — the algebraic conditions
    defining an "admissible" `(x, y)` pair for `(alpha_of_class ClassP,
    alpha_of_class ClassNP)`:

      `x² = 2 ∧ x > 0 ∧ 16·y² − 24·y − 11 = 0 ∧ y > 0`.

    These are exactly the four clauses of `PolylogEigenvalueConjecture`,
    abstracted from the specific `alpha_of_class` arguments. -/
def polylog_admissible_pair (x y : ℝ) : Prop :=
  x ^ 2 = 2 ∧ 0 < x ∧
  16 * y ^ 2 - 24 * y - 11 = 0 ∧ 0 < y

/-! ## §2 — The canonical pair `(√2, φ + 1/4)` is admissible -/

/-- **`canonical_pair_is_admissible`** — `(√2, φ + 1/4)` is an
    admissible pair. Direct consequence of the framework's unconditional
    `alpha_P_sq`, `alpha_P_pos`, `alpha_NP_quadratic`, `alpha_NP_pos`
    theorems. -/
theorem canonical_pair_is_admissible :
    polylog_admissible_pair (Real.sqrt 2) (phi + 1/4) :=
  ⟨alpha_P_sq, alpha_P_pos, alpha_NP_quadratic, alpha_NP_pos⟩

/-! ## §3 — Uniqueness of the admissible pair -/

/-- **`polylog_admissible_pair_is_unique`** — the ONLY admissible pair
    in ℝ × ℝ is `(√2, φ + 1/4)`.

    Proof: `x² = 2 ∧ x > 0` forces `x = √2` (unique positive square root
    of 2). `16y² − 24y − 11 = 0 ∧ y > 0` forces `y = φ + 1/4` (the unique
    positive root of the NP-quadratic, since the discriminant `576 + 704
    = 1280 = 256·5` gives roots `(24 ± 16·√5)/32 = (3 ± 2√5)/4`, and the
    positive root is `(3 + 2√5)/4 = φ + 1/4`). -/
theorem polylog_admissible_pair_is_unique
    (x y : ℝ) (h : polylog_admissible_pair x y) :
    x = Real.sqrt 2 ∧ y = phi + 1/4 := by
  obtain ⟨h_xsq, h_xpos, h_yquad, h_ypos⟩ := h
  refine ⟨?_, ?_⟩
  · -- x = √2: x > 0 and x² = 2 → x = √2
    have h_sqrt_sq : Real.sqrt (x ^ 2) = x := Real.sqrt_sq (le_of_lt h_xpos)
    rw [← h_sqrt_sq, h_xsq]
  · -- y = φ + 1/4: 16y² - 24y - 11 = 0 and y > 0 → y = φ + 1/4
    -- The two roots are (3 ± 2√5)/4; positive root is (3 + 2√5)/4 = φ + 1/4.
    -- y - (3 - 2√5)/4 and y - (3 + 2√5)/4 are the two factors.
    have h_sqrt5_pos : 0 < Real.sqrt 5 :=
      Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0)
    have h_sqrt5_sq : Real.sqrt 5 ^ 2 = 5 :=
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
    -- factor 16y² - 24y - 11 = 16(y - (3-2√5)/4)(y - (3+2√5)/4)
    -- compute: 16·((3-2√5)/4)·((3+2√5)/4) = 16·(9 - 20)/16 = -11 ✓
    -- 16·((3-2√5)/4 + (3+2√5)/4) = 16·(6/4) = 24 ✓
    -- So 16y² - 24y - 11 = 16(y - (3-2√5)/4)(y - (3+2√5)/4).
    have h_y_minus_minus_root : 16 * (y - (3 - 2 * Real.sqrt 5)/4) *
                                  (y - (3 + 2 * Real.sqrt 5)/4) = 0 := by
      nlinarith [h_yquad, h_sqrt5_sq]
    -- product is zero, so one factor is zero
    have h_y_root_or : y - (3 - 2 * Real.sqrt 5)/4 = 0 ∨
                       y - (3 + 2 * Real.sqrt 5)/4 = 0 := by
      rcases mul_eq_zero.mp h_y_minus_minus_root with h1 | h2
      · rcases mul_eq_zero.mp h1 with h0 | h0
        · -- 16 = 0 impossible
          exfalso; linarith [h0]
        · left; exact h0
      · right; exact h2
    -- exclude the negative root (3 - 2√5)/4
    -- (3 - 2√5)/4 < 0 since 2√5 > 4 (√5 > 2)
    have h_sqrt5_gt_two : 2 < Real.sqrt 5 := by
      nlinarith [h_sqrt5_sq, h_sqrt5_pos]
    have h_neg_root_neg : (3 - 2 * Real.sqrt 5)/4 < 0 := by
      have : 2 * Real.sqrt 5 > 4 := by linarith
      linarith
    rcases h_y_root_or with h_neg | h_pos
    · -- y = (3 - 2√5)/4 < 0 contradicts y > 0
      exfalso
      have h_y_eq : y = (3 - 2 * Real.sqrt 5)/4 := by linarith
      rw [h_y_eq] at h_ypos
      linarith
    · -- y = (3 + 2√5)/4 = φ + 1/4
      have h_y_eq : y = (3 + 2 * Real.sqrt 5)/4 := by linarith
      unfold phi
      rw [h_y_eq]
      ring

/-! ## §4 — Polylog conjecture iff admissible pair -/

/-- **`polylog_conjecture_iff_admissible_pair`** — definitional
    name-bridge: `PolylogEigenvalueConjecture` is equivalent to
    `polylog_admissible_pair (alpha_of_class ClassP) (alpha_of_class ClassNP)`. -/
theorem polylog_conjecture_iff_admissible_pair :
    PolylogEigenvalueConjecture ↔
    polylog_admissible_pair (alpha_of_class ClassP) (alpha_of_class ClassNP) := by
  unfold PolylogEigenvalueConjecture polylog_admissible_pair
  constructor
  · rintro ⟨⟨h_xsq, h_xpos⟩, h_yquad, h_ypos⟩
    exact ⟨h_xsq, h_xpos, h_yquad, h_ypos⟩
  · rintro ⟨h_xsq, h_xpos, h_yquad, h_ypos⟩
    exact ⟨⟨h_xsq, h_xpos⟩, h_yquad, h_ypos⟩

/-! ## §5 — Rigidity capstone -/

/-- **★ (W48) RIGIDITY CAPSTONE ★** — `PolylogEigenvalueConjecture` is
    EQUIVALENT to the canonical-pair pin `alpha_of_class ClassP = √2 ∧
    alpha_of_class ClassNP = φ + 1/4`.

    The forward direction COMPOSES `polylog_conjecture_iff_admissible_pair`
    with `polylog_admissible_pair_is_unique`. The backward direction
    is Wave 47's `wave47_polylog_discharge_under_empirical_pin`.

    Rigidity content: the polylog conjecture's algebraic-plus-positivity
    content has NO ALGEBRAIC SLACK — the canonical pair `(√2, φ + 1/4)`
    is the unique admissible value pair. Hence the
    `EmpiricalAlphaIdentificationHypothesis` form (Wave 47) is the
    canonical form, not one option among many. -/
theorem polylog_conjecture_iff_canonical_pair_pin :
    PolylogEigenvalueConjecture ↔
    (alpha_of_class ClassP = Real.sqrt 2 ∧
     alpha_of_class ClassNP = phi + 1/4) := by
  rw [polylog_conjecture_iff_admissible_pair]
  constructor
  · intro h
    have := polylog_admissible_pair_is_unique _ _ h
    exact this
  · rintro ⟨hP, hNP⟩
    rw [hP, hNP]
    exact canonical_pair_is_admissible

/-! ## §6 — Sharper Wave 48 capstone -/

/-- **★★ (W48) SINGLE-CITATION RIGIDITY CAPSTONE ★★** — the polylog
    conjecture's algebraic content is rigidly the canonical pair, and
    this rigidity is equivalent to the empirical-pin form of Wave 47.

    Three-way equivalence:
      (i)  `PolylogEigenvalueConjecture`
      (ii) `EmpiricalAlphaIdentificationHypothesis`
      (iii) `polylog_admissible_pair (alpha_of_class ClassP) (alpha_of_class ClassNP)`

    All three are mutually equivalent. -/
theorem polylog_wave48_rigidity_capstone :
    (PolylogEigenvalueConjecture ↔ EmpiricalAlphaIdentificationHypothesis) ∧
    (PolylogEigenvalueConjecture ↔
     polylog_admissible_pair (alpha_of_class ClassP) (alpha_of_class ClassNP)) ∧
    (EmpiricalAlphaIdentificationHypothesis ↔
     polylog_admissible_pair (alpha_of_class ClassP) (alpha_of_class ClassNP)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (PrincipiaTractalis.PolylogConjectureAttemptWave47.empirical_pin_iff_polylog_conjecture).symm
  · exact polylog_conjecture_iff_admissible_pair
  · constructor
    · intro h
      have h_poly : PolylogEigenvalueConjecture :=
        (PrincipiaTractalis.PolylogConjectureAttemptWave47.empirical_pin_iff_polylog_conjecture).mp h
      exact polylog_conjecture_iff_admissible_pair.mp h_poly
    · intro h
      have h_poly : PolylogEigenvalueConjecture :=
        polylog_conjecture_iff_admissible_pair.mpr h
      exact (PrincipiaTractalis.PolylogConjectureAttemptWave47.empirical_pin_iff_polylog_conjecture).mpr h_poly

end PrincipiaTractalis.PolylogConjectureAttemptWave48

-- Axiom check. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.PolylogConjectureAttemptWave48.canonical_pair_is_admissible
#print axioms PrincipiaTractalis.PolylogConjectureAttemptWave48.polylog_admissible_pair_is_unique
#print axioms PrincipiaTractalis.PolylogConjectureAttemptWave48.polylog_conjecture_iff_admissible_pair
#print axioms PrincipiaTractalis.PolylogConjectureAttemptWave48.polylog_conjecture_iff_canonical_pair_pin
#print axioms PrincipiaTractalis.PolylogConjectureAttemptWave48.polylog_wave48_rigidity_capstone
