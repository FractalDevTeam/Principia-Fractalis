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

/-! ## Brick B: shift-series r ∈ {1,2} bound + summability

    For r ∈ {1, 2} and m ≥ 1, the bracket `1/(3m+r)^s - 1/(3m)^s`
    is bounded by triangle inequality:

      `|1/(3m+r)^s - 1/(3m)^s| ≤ 1/(3m+r)^(Re s) + 1/(3m)^(Re s)
                              ≤ 2/(3m)^(Re s)`.

    Combined with `‖phaseFactor α m‖ = 1`:

      `‖shiftSeriesTerm α s r m‖ ≤ 2/(3m)^(Re s)`.

    For `Re(s) > 1`, this is summable by comparison with
    `mathlib.Complex.summable_one_div_nat_cpow`. -/

/-- **Triangle-inequality bound on a single shift-series term** for `r ∈ {1,2}`,
    `m ≥ 1`, `0 < Re(s)`. -/
theorem norm_shiftSeriesTerm_le_triangle
    (α : ℝ) (s : ℂ) (r m : ℕ) (hm : m ≠ 0) :
    ‖shiftSeriesTerm α s r m‖ ≤
      ‖(1 : ℂ) / ((3 * m + r : ℕ) : ℂ)^s‖ + ‖(1 : ℂ) / ((3 * m : ℕ) : ℂ)^s‖ := by
  unfold shiftSeriesTerm
  rw [if_neg hm]
  -- ‖phaseFactor · (a - b)‖ = ‖phaseFactor‖ · ‖a - b‖ = 1 · ‖a - b‖
  rw [norm_mul, norm_phaseFactor]
  rw [one_mul]
  -- ‖a - b‖ ≤ ‖a‖ + ‖b‖ via triangle inequality
  exact norm_sub_le _ _

/-- **Summability of the shift-series for any `r` at `Re(s) > 1`**.

    Triangle bound gives `‖shiftSeriesTerm α s r m‖ ≤ ‖1/(3m+r)^s‖ + ‖1/(3m)^s‖`.
    Both terms summable in m via mathlib's `Complex.summable_one_div_nat_cpow`. -/
theorem shiftSeriesTerm_summable_of_re_gt_one
    (α : ℝ) {s : ℂ} (hs : 1 < s.re) (r : ℕ) :
    Summable (shiftSeriesTerm α s r) := by
  set_option maxHeartbeats 800000 in
  -- Use Complex.summable_one_div_nat_cpow for the m = 3*· and 3*·+r families.
  have h_zeta_summable :
      Summable (fun m : ℕ => (1 : ℂ) / (m : ℂ)^s) :=
    (Complex.summable_one_div_nat_cpow (p := s)).mpr hs
  -- Compose: m ↦ 3*m is an injection, so (3*m) form is summable. Similarly (3*m+r).
  -- Direct route: bound ‖shiftSeriesTerm α s r m‖ ≤ ‖1 / (m : ℂ)^s‖ · C for some C.
  -- We need ‖1/(3m)^s‖ ≤ ‖1/m^s‖ which requires (3m)^(Re s) ≥ m^(Re s) i.e. Re s > 0.
  -- The simplest path: use the index n ↦ 3*n and 3*n+r as injections.
  apply Summable.of_norm_bounded (g := fun m : ℕ => 2 * ‖(1 : ℂ) / (m : ℂ)^s‖)
  · exact (h_zeta_summable.norm).mul_left 2
  intro m
  by_cases hm : m = 0
  · simp [shiftSeriesTerm, hm]
  · -- m ≥ 1: triangle bound + monotonicity in the integer base
    have h_tri := norm_shiftSeriesTerm_le_triangle α s r m hm
    have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
    have h_3m_pos : 0 < 3 * m := by omega
    have h_3m_plus_r_pos : 0 < 3 * m + r := by omega
    -- Convert all norms to real expressions via Complex.norm_natCast_cpow_of_pos.
    have h_re_pos : 0 < s.re := lt_trans zero_lt_one hs
    have h_n_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
    have h_3n_pos : (0 : ℝ) < (3 * m : ℝ) := by exact_mod_cast h_3m_pos
    have h_3nr_pos : (0 : ℝ) < (3 * m + r : ℝ) := by exact_mod_cast h_3m_plus_r_pos
    have h_norm_3m :
        ‖(1 : ℂ) / ((3 * m : ℕ) : ℂ)^s‖ = 1 / (3 * m : ℝ)^s.re := by
      rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos h_3m_pos]
      norm_cast
    have h_norm_3mr :
        ‖(1 : ℂ) / ((3 * m + r : ℕ) : ℂ)^s‖ = 1 / (3 * m + r : ℝ)^s.re := by
      rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos h_3m_plus_r_pos]
      norm_cast
    have h_norm_m :
        ‖(1 : ℂ) / ((m : ℕ) : ℂ)^s‖ = 1 / (m : ℝ)^s.re := by
      rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hm_pos]
    rw [h_norm_3m, h_norm_3mr] at h_tri
    rw [h_norm_m]
    -- Monotonicity: 1/(3m)^(Re s) ≤ 1/m^(Re s) since 3m ≥ m and Re s > 0.
    have h_3m_ge : (m : ℝ) ≤ (3 * m : ℝ) := by
      push_cast; linarith
    have h_3mr_ge : (m : ℝ) ≤ (3 * m + r : ℝ) := by
      push_cast; have : (0:ℝ) ≤ (r:ℝ) := Nat.cast_nonneg r; linarith
    have h_pow_3m : (m : ℝ)^s.re ≤ (3 * m : ℝ)^s.re :=
      Real.rpow_le_rpow h_n_pos.le h_3m_ge h_re_pos.le
    have h_pow_3mr : (m : ℝ)^s.re ≤ (3 * m + r : ℝ)^s.re :=
      Real.rpow_le_rpow h_n_pos.le h_3mr_ge h_re_pos.le
    have h_pow_m_pos : (0 : ℝ) < (m : ℝ)^s.re := Real.rpow_pos_of_pos h_n_pos _
    have h_div_3m : 1 / (3 * m : ℝ)^s.re ≤ 1 / (m : ℝ)^s.re :=
      one_div_le_one_div_of_le h_pow_m_pos h_pow_3m
    have h_div_3mr : 1 / (3 * m + r : ℝ)^s.re ≤ 1 / (m : ℝ)^s.re :=
      one_div_le_one_div_of_le h_pow_m_pos h_pow_3mr
    -- ‖shiftSeriesTerm‖ ≤ 1/(3m+r)^Re s + 1/(3m)^Re s (from h_tri)
    --                   ≤ 1/m^Re s + 1/m^Re s              (from h_div_*)
    --                   = 2 · (1/m^Re s)
    linarith [h_tri, h_div_3m, h_div_3mr]

end PrincipiaTractalis.Analytic
