/-
# Spectral Examples — Framework V_P at Zero-Distance Sample

★ 2026-06-06 — Polylog chain piece 19 ★

## Why this file exists

For the framework's V_P kernel with sample points at zero self-distance
(d(x_i, x_j) = 0), the kernel value is `Σ_{n=0}^N a^{-n}` (the partial
harmonic sum).

## What gets closed

- `fractalKernel_at_zero_distance`: V_P(x, y) = Σ a^{-n} when d(x,y) = 0

## Axiom budget

Zero project axioms. Zero `sorry`. Zero `admit`.

Stage 2026-06-06.
-/

import PF.TuringEncoding.IFSHausdorffDimensionInfrastructure
import PF.TuringEncoding.GeometricPartialSumClosedForm

namespace PrincipiaTractalis.TuringEncoding

open Real

/-! ## §1 — Zero-distance kernel value -/

/-- **At zero distance**, V_P kernel reduces to the partial harmonic sum
    `Σ a^{-n}`. -/
theorem fractalKernel_at_zero_distance (Nlevels : ℕ) (a α : ℝ) (d : ℝ → ℝ → ℝ)
    (x y : ℝ) (h_d : d x y = 0) :
    fractalKernelTruncated Nlevels a α d x y =
    ∑ n ∈ Finset.range (Nlevels + 1), (a ^ n)⁻¹ := by
  unfold fractalKernelTruncated
  rw [h_d]
  congr 1
  ext n
  simp [Real.cos_zero]

/-- **At zero distance with positive `a > 1`, V_P value is positive**. -/
theorem fractalKernel_at_zero_distance_pos (Nlevels : ℕ) (a α : ℝ) (d : ℝ → ℝ → ℝ)
    (ha : 1 < a) (x y : ℝ) (h_d : d x y = 0) :
    0 < fractalKernelTruncated Nlevels a α d x y := by
  rw [fractalKernel_at_zero_distance Nlevels a α d x y h_d]
  have ha_pos : 0 < a := lt_trans zero_lt_one ha
  -- Σ_{n=0}^N (a^n)⁻¹ ≥ (a^0)⁻¹ = 1 > 0
  apply Finset.sum_pos
  · intro n _
    exact inv_pos.mpr (pow_pos ha_pos _)
  · exact Finset.nonempty_range_succ

/-- **At zero distance, the V_P value is bounded above by `a/(a-1)`**. -/
theorem fractalKernel_at_zero_distance_bound (Nlevels : ℕ) (a α : ℝ) (d : ℝ → ℝ → ℝ)
    (ha : 1 < a) (x y : ℝ) (h_d : d x y = 0) :
    fractalKernelTruncated Nlevels a α d x y ≤ a / (a - 1) := by
  rw [fractalKernel_at_zero_distance Nlevels a α d x y h_d]
  exact geometric_partial_sum_bound_when_a_gt_one a Nlevels ha

/-! ## §2 — Honest scope marker -/

/-- **Honest scope** for this file: zero-distance kernel identities. -/
theorem SpectralFrameworkZeroDistance_HonestScope : True := trivial

end PrincipiaTractalis.TuringEncoding

-- Axiom checks
#print axioms PrincipiaTractalis.TuringEncoding.fractalKernel_at_zero_distance
#print axioms PrincipiaTractalis.TuringEncoding.fractalKernel_at_zero_distance_pos
#print axioms PrincipiaTractalis.TuringEncoding.fractalKernel_at_zero_distance_bound
