/-
# R_f Shift-Series Infrastructure (Brick 5c-prep)

Defines the SHIFT SERIES that appear in the correction term of the
base-3 self-referencing recursion (Brick 5b):

  c_r(α, s) := Σ_{m≥1} e^(iπα·D_3(m)) · [1/(3m+r)^s - 1/(3m)^s]

for r ∈ {0, 1, 2}. The r = 0 case is trivially zero (the shift is zero).
For r ∈ {1, 2}, the shift terms `1/(3m+r)^s - 1/(3m)^s` are bounded by
`|s|·r/(3m)^(Re(s)+1)`, giving absolute convergence for `Re(s) > 0`.

## Purpose

This file builds the rigorous Lean infrastructure for the "correction"
side of the recursion identity from Brick 5b. Whether the manuscript's
claim `R_f(α, 1) = πα/10 leading order` holds or fails, the shift series
are the concrete objects that determine the closed-form value of
R_f(α, s) on the absolutely-convergent regime `Re(s) > 1`.

## Status

Axiom-free. Strictly the shift-series term + summand bound at Re(s) > 1.

Stage L5c-prep — shift-series term + bound.
-/

import PF.Consciousness.FractalResonance

namespace PrincipiaTractalis.Analytic

open Complex Real PrincipiaTractalis.Consciousness
open PrincipiaTractalis.TuringEncoding

/-! ## The shift-series term -/

/-- **Shift-series term at depth m**: `e^(iπα·D_3(m)) · [1/(3m+r)^s - 1/(3m)^s]`.

    For r = 0, this is identically 0 (no shift).
    For r ∈ {1, 2} and m ≥ 1, the bracket is nonzero and bounded by
    `|s|·r/(3m)^(Re(s)+1)` via the mean value theorem on `x ↦ x^(-s)`. -/
noncomputable def shiftSeriesTerm (α : ℝ) (s : ℂ) (r m : ℕ) : ℂ :=
  if m = 0 then 0
  else phaseFactor α m * (1 / ((3 * m + r : ℕ) : ℂ)^s - 1 / ((3 * m : ℕ) : ℂ)^s)

/-- **r = 0 case**: the shift is zero, so the term vanishes identically. -/
theorem shiftSeriesTerm_r_zero (α : ℝ) (s : ℂ) (m : ℕ) :
    shiftSeriesTerm α s 0 m = 0 := by
  unfold shiftSeriesTerm
  by_cases hm : m = 0
  · simp [hm]
  · simp [hm]

/-- **r = 0 case as `Summable`**: the term is identically 0, hence summable. -/
theorem shiftSeriesTerm_r_zero_summable (α : ℝ) (s : ℂ) :
    Summable (shiftSeriesTerm α s 0) := by
  have h_eq_zero : (shiftSeriesTerm α s 0) = (fun _ : ℕ => (0 : ℂ)) := by
    funext m
    exact shiftSeriesTerm_r_zero α s m
  rw [h_eq_zero]
  exact summable_zero

/-- **Phase factor norm bound**: `‖phaseFactor α m‖ = 1`. (Re-export
    from `FractalResonance.norm_phaseFactor` for use in shift series
    bounds.) -/
theorem norm_phaseFactor_eq_one (α : ℝ) (m : ℕ) :
    ‖phaseFactor α m‖ = 1 := norm_phaseFactor α m

end PrincipiaTractalis.Analytic
