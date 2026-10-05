/-
# Ch 26 Vacuum-Energy Refutation (2026-10-05)

Two numerical defects in `ch26_cosmological_constant.tex`, both verified
independently in Python before being proved here.

## Defect A — the displayed derivation does not produce its own boxed number

The proof of the QFT vacuum-energy proposition displays

  `ρ_vac ∼ (10¹⁹ × 1.6×10⁻¹⁰)⁴ / [(197×10⁻¹³)⁴ · 64π²] ∼ 10⁹¹ g/cm³`

Evaluated exactly as written this is `6.889 × 10⁷⁶`, not `10⁹¹` — short by a
factor of `1.45 × 10¹⁴`.

Two independent errors produce that gap:

1. **Wrong power of `ħc`.** An energy density is `Λ⁴/(ħc)³`: dimensionally
   `E⁴ / (E³L³) = E/L³`. The displayed expression cubes nothing — it raises
   `ħc` to the FOURTH power, giving `E⁰/L⁴`, which is not an energy density at
   all.
2. **Mixed units.** The numerator converts GeV to joules (`× 1.6×10⁻¹⁰`) while
   the denominator leaves `197 MeV·fm` in MeV·cm. The two factors are not in
   the same unit system.

**The boxed value is nevertheless right.** Done correctly —
`ρ = Λ⁴/[(ħc)³ · 64π²] · (g/GeV)` with `ħc = 1.9733×10⁻¹⁴ GeV·cm` — the
Planck-scale density is `3.673 × 10⁹⁰ g/cm³`, i.e. `∼10⁹¹`. So this is a
defective *derivation* of a sound *result*, which is the more insidious case:
the conclusion survives, the proof does not support it.

## Defect B — `ρ_SUSY` is wrong by forty-two orders, and the chapter refutes itself

The SUSY subsection states

  `ρ_SUSY ∼ (1 TeV)⁴ ∼ 10⁻¹⁶ g/cm³`,  "Still 13 orders of magnitude too large!"

The same formula the chapter calibrates at the Planck scale gives
`3.673 × 10²⁶ g/cm³` at 1 TeV — larger than the quoted figure by
`3.7 × 10⁴²`. And the true discrepancy against observation is about **56**
orders of magnitude, not 13.

**The decisive argument is internal.** It needs no external datum, only the
chapter's own boxed figure and the `Λ⁴` scaling the chapter itself uses:

  `Λ_Planck / Λ_TeV = 10¹⁹ / 10³ = 10¹⁶`
  density scales as the fourth power, so `(10¹⁶)⁴ = 10⁶⁴`
  therefore  `discrepancy_SUSY = 10¹²⁰ / 10⁶⁴ = 10⁵⁶`

The chapter's own boxed `10¹²⁰` forces `10⁵⁶`. Its stated `13` is inconsistent
with a number it boxes two pages earlier. Likewise its own `10⁹¹` forces
`ρ_SUSY ∼ 10²⁷ g/cm³`, not `10⁻¹⁶`.

For what it is worth externally, `∼56` orders is also the standard literature
figure for TeV-scale SUSY breaking (commonly quoted as "about 60"), so the
correction moves the chapter INTO agreement with the known result rather than
away from it. That is unusual among the defects found in this corpus and worth
noting.

## What this file proves (axiom-free)

1. `printedVacuumExpr_lt` / `printedVacuumExpr_gt` — the displayed expression
   lies strictly between `10⁷⁵` and `10⁷⁸`. Strategy: the expression is
   `K / (C · 64π²)` with `K, C` explicit positive rationals, so bounding `π²`
   two-sidedly (`Real.pi_gt_d6`, `Real.pi_lt_d6`) brackets it.
2. `printedVacuumExpr_ne_boxed` — hence it is not `10⁹¹`.
3. `planck_to_TeV_density_ratio` — the `Λ⁴` scaling factor between the two
   cutoffs is exactly `10⁶⁴`.
4. `susy_density_forced_by_chapter` — the chapter's own `10⁹¹` forces
   `ρ_SUSY ∼ 10²⁷`, and `10²⁷ ≠ 10⁻¹⁶`.
5. `susy_discrepancy_forced_by_chapter` — the chapter's own `10¹²⁰` forces a
   discrepancy of `10⁵⁶`, and `10¹³ ≠ 10⁵⁶`.

## Scope

Both defects are arithmetic. Neither touches the chapter's physics programme,
and no rigor-ledger label elsewhere moves. Defect A leaves the boxed result
standing and removes a broken proof of it; defect B replaces a wrong number
with the one the chapter's own figures imply.

Author: Pablo Cohen + Claude Opus 5. 2026-10-05.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

namespace PrincipiaTractalis.Ch26Refutation

/-! ## §1 — Defect A: the displayed expression -/

/-- The vacuum-energy expression exactly as displayed in the chapter's proof:
    `(10¹⁹ × 1.6×10⁻¹⁰)⁴ / [(197×10⁻¹³)⁴ · 64π²]`. -/
noncomputable def printedVacuumExpr : ℝ :=
  (10 ^ 19 * (16 / 10 ^ 11)) ^ 4 / ((197 / 10 ^ 13) ^ 4 * (64 * Real.pi ^ 2))

/-- The chapter's boxed Planck-scale density, `10⁹¹ g/cm³`. -/
noncomputable def boxedPlanckDensity : ℝ := 10 ^ 91

private theorem pi_sq_lower : (9.8596 : ℝ) < Real.pi ^ 2 := by
  have h : (3.14 : ℝ) < Real.pi := by linarith [Real.pi_gt_d6]
  nlinarith [h, Real.pi_pos]

private theorem pi_sq_upper : Real.pi ^ 2 < (9.9225 : ℝ) := by
  have h : Real.pi < (3.15 : ℝ) := by linarith [Real.pi_lt_d6]
  nlinarith [h, Real.pi_pos]

private theorem printed_den_pos :
    (0 : ℝ) < (197 / 10 ^ 13 : ℝ) ^ 4 * (64 * Real.pi ^ 2) := by
  have := Real.pi_pos
  positivity

/-- **(1a)** The displayed expression is below `10⁷⁸`. -/
theorem printedVacuumExpr_lt : printedVacuumExpr < (10 : ℝ) ^ 78 := by
  unfold printedVacuumExpr
  rw [div_lt_iff₀ printed_den_pos]
  nlinarith [pi_sq_lower]

/-- **(1b)** The displayed expression is above `10⁷⁵`. -/
theorem printedVacuumExpr_gt : (10 : ℝ) ^ 75 < printedVacuumExpr := by
  unfold printedVacuumExpr
  rw [lt_div_iff₀ printed_den_pos]
  nlinarith [pi_sq_upper]

/-- **(2)** Hence the displayed expression is not the boxed `10⁹¹`. It is short
    by more than thirteen orders of magnitude, so the proof as printed does not
    establish the proposition it precedes. -/
theorem printedVacuumExpr_ne_boxed : printedVacuumExpr ≠ boxedPlanckDensity := by
  intro h
  have hlt := printedVacuumExpr_lt
  rw [h] at hlt
  unfold boxedPlanckDensity at hlt
  norm_num at hlt

/-! ## §2 — Defect B: the chapter's own figures force the SUSY numbers -/

/-- **(3)** The `Λ⁴` scaling factor between the Planck and TeV cutoffs, using
    the chapter's own cutoff values `10¹⁹` GeV and `10³` GeV. -/
theorem planck_to_TeV_density_ratio :
    (((10 : ℝ) ^ 19 / 10 ^ 3) ^ 4) = (10 : ℝ) ^ 64 := by
  norm_num

/-- **(4)** The chapter's own boxed `10⁹¹ g/cm³` at the Planck cutoff forces
    `ρ_SUSY ∼ 10²⁷ g/cm³` at the TeV cutoff — not the stated `10⁻¹⁶`. -/
theorem susy_density_forced_by_chapter :
    boxedPlanckDensity / (((10 : ℝ) ^ 19 / 10 ^ 3) ^ 4) = (10 : ℝ) ^ 27 ∧
    (10 : ℝ) ^ 27 ≠ 1 / 10 ^ 16 := by
  refine ⟨?_, by norm_num⟩
  unfold boxedPlanckDensity
  rw [planck_to_TeV_density_ratio]
  norm_num

/-- **(5)** The chapter's own boxed discrepancy `10¹²⁰` at the Planck cutoff
    forces a SUSY discrepancy of `10⁵⁶`, not the stated thirteen orders.

    This is the decisive statement: it uses no external datum, only a figure
    the chapter boxes itself and the fourth-power scaling the chapter itself
    applies. The chapter contradicts its own arithmetic. -/
theorem susy_discrepancy_forced_by_chapter :
    (10 : ℝ) ^ 120 / (((10 : ℝ) ^ 19 / 10 ^ 3) ^ 4) = (10 : ℝ) ^ 56 ∧
    (10 : ℝ) ^ 13 ≠ (10 : ℝ) ^ 56 := by
  refine ⟨?_, by norm_num⟩
  rw [planck_to_TeV_density_ratio]
  norm_num

/-! ## §3 — Capstone -/

/-- **★ Ch 26 vacuum-energy refutation capstone ★**

    Defect A: the displayed derivation lies strictly between `10⁷⁵` and `10⁷⁸`
    and so is not the boxed `10⁹¹` it claims to produce — though the boxed
    value is itself correct.

    Defect B: the chapter's own boxed figures force `ρ_SUSY ∼ 10²⁷ g/cm³` and a
    discrepancy of `10⁵⁶`, refuting the stated `10⁻¹⁶` and "13 orders". -/
theorem Ch26VacuumEnergyRefutation_capstone :
    ((10 : ℝ) ^ 75 < printedVacuumExpr ∧ printedVacuumExpr < (10 : ℝ) ^ 78) ∧
    printedVacuumExpr ≠ boxedPlanckDensity ∧
    (boxedPlanckDensity / (((10 : ℝ) ^ 19 / 10 ^ 3) ^ 4) = (10 : ℝ) ^ 27 ∧
      (10 : ℝ) ^ 27 ≠ 1 / 10 ^ 16) ∧
    ((10 : ℝ) ^ 120 / (((10 : ℝ) ^ 19 / 10 ^ 3) ^ 4) = (10 : ℝ) ^ 56 ∧
      (10 : ℝ) ^ 13 ≠ (10 : ℝ) ^ 56) :=
  ⟨⟨printedVacuumExpr_gt, printedVacuumExpr_lt⟩,
   printedVacuumExpr_ne_boxed,
   susy_density_forced_by_chapter,
   susy_discrepancy_forced_by_chapter⟩

/-! ## §4 — Non-vacuity -/

/-- Non-vacuity: the displayed expression is strictly positive, so the brackets
    above are not brackets on zero. -/
theorem printedVacuumExpr_pos : 0 < printedVacuumExpr := by
  unfold printedVacuumExpr
  have := Real.pi_pos
  positivity

end PrincipiaTractalis.Ch26Refutation

/-! ## Axiom audit — LIVE, not commented out -/

#print axioms PrincipiaTractalis.Ch26Refutation.printedVacuumExpr_lt
#print axioms PrincipiaTractalis.Ch26Refutation.printedVacuumExpr_gt
#print axioms PrincipiaTractalis.Ch26Refutation.printedVacuumExpr_ne_boxed
#print axioms PrincipiaTractalis.Ch26Refutation.susy_density_forced_by_chapter
#print axioms PrincipiaTractalis.Ch26Refutation.susy_discrepancy_forced_by_chapter
#print axioms PrincipiaTractalis.Ch26Refutation.Ch26VacuumEnergyRefutation_capstone
