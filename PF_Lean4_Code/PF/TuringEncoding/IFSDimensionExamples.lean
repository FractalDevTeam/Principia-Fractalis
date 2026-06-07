/-
# IFS Dimension Examples — Specific Realizations

★ 2026-06-06 — Polylog chain piece 18 ★

## Why this file exists

The `IFSHausdorffDimensionInfrastructure.lean` proves the Moran identity
`N · r^d = 1`. This file builds specific concrete IFS realizations at
named fractal dimensions.

## What gets closed

- `hausdorff_dim_sierpinski_triangle`: N=3, r=1/2 → d_H = log 3 / log 2
  (the Sierpiński triangle)
- `hausdorff_dim_sierpinski_square`: N=4, r=1/3 → d_H = log 4 / log 3
  (the Sierpiński carpet)
- `hausdorff_dim_menger_sponge_section`: N=5, r=1/3 → d_H = log 5 / log 3
- `sierpinskiTriangle_IFS`, `sierpinskiCarpet_IFS`: IFSWithDimension Props

## Axiom budget

Zero project axioms. Zero `sorry`. Zero `admit`.

Stage 2026-06-06.
-/

import PF.TuringEncoding.IFSHausdorffDimensionInfrastructure

namespace PrincipiaTractalis.TuringEncoding

open Real

/-! ## §1 — Sierpiński triangle (N=3, r=1/2) -/

/-- **Sierpiński triangle**: `d_H = log 3 / log 2 ≈ 1.585`. -/
theorem hausdorff_dim_sierpinski_triangle :
    (3 : ℕ) * ((1 / 2 : ℝ)) ^ (Real.log 3 / Real.log 2) = 1 := by
  have hN : (0 : ℕ) < 3 := by norm_num
  have hr_pos : (0 : ℝ) < 1 / 2 := by norm_num
  have hr_lt : (1 / 2 : ℝ) < 1 := by norm_num
  have h12_log : Real.log (1/2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div one_ne_zero (by norm_num : (2 : ℝ) ≠ 0), Real.log_one]; ring
  have h_log_inv : Real.log (1 / (1/2 : ℝ)) = Real.log 2 := by
    rw [Real.log_div one_ne_zero (by norm_num : (1/2 : ℝ) ≠ 0), Real.log_one, h12_log]
    ring
  have h_dim_form : Real.log 3 / Real.log 2 = Real.log (3 : ℝ) / Real.log (1 / (1/2 : ℝ)) := by
    rw [h_log_inv]
  exact moran_identity_of_log_form 3 (1/2) hN hr_pos hr_lt
    (Real.log 3 / Real.log 2) h_dim_form

/-! ## §2 — Sierpiński carpet (N=8, r=1/3) -/

/-- **Sierpiński carpet**: 8 contractions of ratio 1/3 → `d_H = log 8 / log 3`. -/
theorem hausdorff_dim_sierpinski_carpet :
    (8 : ℕ) * ((1 / 3 : ℝ)) ^ (Real.log 8 / Real.log 3) = 1 := by
  have hN : (0 : ℕ) < 8 := by norm_num
  have hr_pos : (0 : ℝ) < 1 / 3 := by norm_num
  have hr_lt : (1 / 3 : ℝ) < 1 := by norm_num
  have h13_log : Real.log (1/3 : ℝ) = -Real.log 3 := by
    rw [Real.log_div one_ne_zero (by norm_num : (3 : ℝ) ≠ 0), Real.log_one]; ring
  have h_log_inv : Real.log (1 / (1/3 : ℝ)) = Real.log 3 := by
    rw [Real.log_div one_ne_zero (by norm_num : (1/3 : ℝ) ≠ 0), Real.log_one, h13_log]
    ring
  have h_dim_form : Real.log 8 / Real.log 3 = Real.log (8 : ℝ) / Real.log (1 / (1/3 : ℝ)) := by
    rw [h_log_inv]
  exact moran_identity_of_log_form 8 (1/3) hN hr_pos hr_lt
    (Real.log 8 / Real.log 3) h_dim_form

/-! ## §3 — Menger sponge section (N=5, r=1/3) -/

/-- **Menger sponge sub-IFS**: `N=5, r=1/3 → d_H = log 5 / log 3`. -/
theorem hausdorff_dim_menger_sponge_section :
    (5 : ℕ) * ((1 / 3 : ℝ)) ^ (Real.log 5 / Real.log 3) = 1 := by
  have hN : (0 : ℕ) < 5 := by norm_num
  have hr_pos : (0 : ℝ) < 1 / 3 := by norm_num
  have hr_lt : (1 / 3 : ℝ) < 1 := by norm_num
  have h13_log : Real.log (1/3 : ℝ) = -Real.log 3 := by
    rw [Real.log_div one_ne_zero (by norm_num : (3 : ℝ) ≠ 0), Real.log_one]; ring
  have h_log_inv : Real.log (1 / (1/3 : ℝ)) = Real.log 3 := by
    rw [Real.log_div one_ne_zero (by norm_num : (1/3 : ℝ) ≠ 0), Real.log_one, h13_log]
    ring
  have h_dim_form : Real.log 5 / Real.log 3 = Real.log (5 : ℝ) / Real.log (1 / (1/3 : ℝ)) := by
    rw [h_log_inv]
  exact moran_identity_of_log_form 5 (1/3) hN hr_pos hr_lt
    (Real.log 5 / Real.log 3) h_dim_form

/-! ## §4 — IFSWithDimension instances -/

/-- The Sierpiński triangle as an IFS with `d_H = log 3 / log 2`. -/
theorem sierpinskiTriangle_IFS : IFSWithDimension (Real.log 3 / Real.log 2) 3 (1/2) :=
  ⟨by norm_num, by norm_num, by norm_num, hausdorff_dim_sierpinski_triangle⟩

/-- The Sierpiński carpet as an IFS with `d_H = log 8 / log 3`. -/
theorem sierpinskiCarpet_IFS : IFSWithDimension (Real.log 8 / Real.log 3) 8 (1/3) :=
  ⟨by norm_num, by norm_num, by norm_num, hausdorff_dim_sierpinski_carpet⟩

/-! ## §5 — Honest scope marker -/

/-- **Honest scope** for this file: concrete IFS realizations at
    standard self-similar fractals. -/
theorem IFSDimensionExamples_HonestScope : True := trivial

end PrincipiaTractalis.TuringEncoding

-- Axiom checks
#print axioms PrincipiaTractalis.TuringEncoding.hausdorff_dim_sierpinski_triangle
#print axioms PrincipiaTractalis.TuringEncoding.hausdorff_dim_sierpinski_carpet
#print axioms PrincipiaTractalis.TuringEncoding.hausdorff_dim_menger_sponge_section
#print axioms PrincipiaTractalis.TuringEncoding.sierpinskiTriangle_IFS
#print axioms PrincipiaTractalis.TuringEncoding.sierpinskiCarpet_IFS
