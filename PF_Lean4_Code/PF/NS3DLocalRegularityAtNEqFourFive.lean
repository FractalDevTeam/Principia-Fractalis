/-
# NS3DLocalRegularityAtNEqFourFive: extend axiom-free `LocalVortexStretchingBound T n`
#   to `n = 4` and `n = 5` at the framework's diagonal Galerkin shadow.

## Honest scope (READ FIRST)

This file extends the axiom-free discharge of `LocalVortexStretchingBound T n`
from `n ∈ {0, 1, 2, 3}` (Wave 22, commits 9ce926a + ea71d91) to
`n ∈ {4, 5}` at the framework's diagonal Galerkin shadow (Wave 23).

**THIS IS NOT THE CLAY MILLENNIUM PROBLEM.** The local-in-time bound at any
fixed Galerkin truncation is the classical Leray-Hopf 1934 shadow; whether the
constant `K_T` remains bounded as `T → ∞` is the Clay open question, captured
by `VortexStretchingBoundedHypothesis`.

## What this file delivers, AXIOM-FREE

At the framework's diagonal Galerkin model we discharge

    ‖VortexStretching3D ω g‖ ≤ K_T · ‖ω‖ · ‖g‖

with `K_T = 1` at `n = 4` and `n = 5`, independent of `T > 0`.

The key new ingredient (relative to `n = 3`) is the **4D / 5D Hadamard
expansion**:

    (Σᵢ xᵢ²)(Σⱼ yⱼ²) = (Σᵢ (xᵢyᵢ)²) + Σ_{i≠j}(xᵢyⱼ)²,

so the diagonal `Σᵢ (xᵢyᵢ)²` is dominated by the full product. For `n = 4`
this drops `C(4,2)·2 = 12` off-diagonal squares; for `n = 5` it drops `20`.
`nlinarith` discharges the Hadamard inequality directly using
non-negativity of the off-diagonal `(xᵢ·yⱼ)²` terms.

ZERO project axioms. ZERO `sorry`s.

Author: Pablo Cohen (formalization, Wave 23 extension)
Date: 2026-05-25
-/

import PF.NS3DLocalRegularityAtNEqThree
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.BigOperators.Fin

namespace PrincipiaTractalis.NS3DLocalRegularityAtNEqFourFive

open PrincipiaTractalis.NS3DVortexStretchingObstruction
open PrincipiaTractalis.NS3DLocalRegularityViaBKM
open PrincipiaTractalis.NS3DLocalRegularityAtNGeqOneRetry
open PrincipiaTractalis.NS3DLocalRegularityAtNEqThree
open PrincipiaTractalis.MillenniumSix
open Real

/-! ## §1 — Hadamard bound at `n = 4` via 4D Cauchy-Schwarz-type expansion -/

/-- **Hadamard bound at n = 4**: `‖x ⊙ y‖ ≤ ‖x‖ · ‖y‖`.

The diagonal-only Cauchy-Schwarz expansion in 4D reads
  (Σᵢ xᵢ²)(Σⱼ yⱼ²) − Σᵢ (xᵢyᵢ)² = Σ_{i≠j} (xᵢyⱼ)²  ≥ 0,
giving 12 non-negative off-diagonal squares. `nlinarith` discharges
this directly. -/
theorem hadamard_norm_le_n4 (x y : EuclideanSpace ℝ (Fin 4)) :
    ‖hadamard 4 x y‖ ≤ ‖x‖ * ‖y‖ := by
  have hxy_nonneg : 0 ≤ ‖x‖ * ‖y‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsq_xy : ‖hadamard 4 x y‖ ^ 2
      = (x 0 * y 0) ^ 2 + (x 1 * y 1) ^ 2 + (x 2 * y 2) ^ 2 + (x 3 * y 3) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Fin.sum_univ_four, hadamard, Real.norm_eq_abs, sq_abs]
  have hsq_x : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 + (x 3) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_four, Real.norm_eq_abs, sq_abs]
  have hsq_y : ‖y‖ ^ 2 = (y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2 + (y 3) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_four, Real.norm_eq_abs, sq_abs]
  -- 4D Hadamard: Σᵢ (xᵢyᵢ)² ≤ (Σᵢ xᵢ²)(Σⱼ yⱼ²).
  -- Drop the 12 off-diagonal cross-product squares (xᵢ·yⱼ)² ≥ 0 (i ≠ j).
  have key : (x 0 * y 0) ^ 2 + (x 1 * y 1) ^ 2 + (x 2 * y 2) ^ 2 + (x 3 * y 3) ^ 2
              ≤ ((x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 + (x 3) ^ 2)
                * ((y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2 + (y 3) ^ 2) := by
    nlinarith [sq_nonneg (x 0 * y 1), sq_nonneg (x 0 * y 2), sq_nonneg (x 0 * y 3),
               sq_nonneg (x 1 * y 0), sq_nonneg (x 1 * y 2), sq_nonneg (x 1 * y 3),
               sq_nonneg (x 2 * y 0), sq_nonneg (x 2 * y 1), sq_nonneg (x 2 * y 3),
               sq_nonneg (x 3 * y 0), sq_nonneg (x 3 * y 1), sq_nonneg (x 3 * y 2)]
  have hsq_total : ‖hadamard 4 x y‖ ^ 2 ≤ (‖x‖ * ‖y‖) ^ 2 := by
    calc ‖hadamard 4 x y‖ ^ 2
        = (x 0 * y 0) ^ 2 + (x 1 * y 1) ^ 2 + (x 2 * y 2) ^ 2 + (x 3 * y 3) ^ 2 := hsq_xy
      _ ≤ ((x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 + (x 3) ^ 2)
            * ((y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2 + (y 3) ^ 2) := key
      _ = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by rw [hsq_x, hsq_y]
      _ = (‖x‖ * ‖y‖) ^ 2 := by ring
  have h_nn : 0 ≤ ‖hadamard 4 x y‖ := norm_nonneg _
  nlinarith [hsq_total, h_nn, hxy_nonneg]

/-! ## §2 — Hadamard bound at `n = 5` via 5D Cauchy-Schwarz-type expansion -/

/-- **Hadamard bound at n = 5**: `‖x ⊙ y‖ ≤ ‖x‖ · ‖y‖`.

Diagonal-only Cauchy-Schwarz expansion in 5D drops 20 off-diagonal
`(xᵢ·yⱼ)²` squares (i ≠ j, i,j ∈ {0,1,2,3,4}). -/
theorem hadamard_norm_le_n5 (x y : EuclideanSpace ℝ (Fin 5)) :
    ‖hadamard 5 x y‖ ≤ ‖x‖ * ‖y‖ := by
  have hxy_nonneg : 0 ≤ ‖x‖ * ‖y‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsq_xy : ‖hadamard 5 x y‖ ^ 2
      = (x 0 * y 0) ^ 2 + (x 1 * y 1) ^ 2 + (x 2 * y 2) ^ 2
        + (x 3 * y 3) ^ 2 + (x 4 * y 4) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Fin.sum_univ_five, hadamard, Real.norm_eq_abs, sq_abs]
  have hsq_x : ‖x‖ ^ 2
      = (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 + (x 3) ^ 2 + (x 4) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_five, Real.norm_eq_abs, sq_abs]
  have hsq_y : ‖y‖ ^ 2
      = (y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2 + (y 3) ^ 2 + (y 4) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_five, Real.norm_eq_abs, sq_abs]
  -- 5D Hadamard: 20 off-diagonal squares dropped.
  have key : (x 0 * y 0) ^ 2 + (x 1 * y 1) ^ 2 + (x 2 * y 2) ^ 2
              + (x 3 * y 3) ^ 2 + (x 4 * y 4) ^ 2
              ≤ ((x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 + (x 3) ^ 2 + (x 4) ^ 2)
                * ((y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2 + (y 3) ^ 2 + (y 4) ^ 2) := by
    nlinarith [sq_nonneg (x 0 * y 1), sq_nonneg (x 0 * y 2),
               sq_nonneg (x 0 * y 3), sq_nonneg (x 0 * y 4),
               sq_nonneg (x 1 * y 0), sq_nonneg (x 1 * y 2),
               sq_nonneg (x 1 * y 3), sq_nonneg (x 1 * y 4),
               sq_nonneg (x 2 * y 0), sq_nonneg (x 2 * y 1),
               sq_nonneg (x 2 * y 3), sq_nonneg (x 2 * y 4),
               sq_nonneg (x 3 * y 0), sq_nonneg (x 3 * y 1),
               sq_nonneg (x 3 * y 2), sq_nonneg (x 3 * y 4),
               sq_nonneg (x 4 * y 0), sq_nonneg (x 4 * y 1),
               sq_nonneg (x 4 * y 2), sq_nonneg (x 4 * y 3)]
  have hsq_total : ‖hadamard 5 x y‖ ^ 2 ≤ (‖x‖ * ‖y‖) ^ 2 := by
    calc ‖hadamard 5 x y‖ ^ 2
        = (x 0 * y 0) ^ 2 + (x 1 * y 1) ^ 2 + (x 2 * y 2) ^ 2
          + (x 3 * y 3) ^ 2 + (x 4 * y 4) ^ 2 := hsq_xy
      _ ≤ ((x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 + (x 3) ^ 2 + (x 4) ^ 2)
            * ((y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2 + (y 3) ^ 2 + (y 4) ^ 2) := key
      _ = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by rw [hsq_x, hsq_y]
      _ = (‖x‖ * ‖y‖) ^ 2 := by ring
  have h_nn : 0 ≤ ‖hadamard 5 x y‖ := norm_nonneg _
  nlinarith [hsq_total, h_nn, hxy_nonneg]

/-! ## §3 — Lift to `Vorticity3DState n` and discharge the local bound -/

/-- **★ At `n = 4`, the local bound holds for every `T > 0`** (axiom-free).
    The bilinear bound at the diagonal Galerkin shadow has `K_T = 1`,
    by the 4D Cauchy-Schwarz / Hadamard expansion. -/
theorem local_vortex_stretching_bound_at_n_eq_four (T : ℝ) (_hT : 0 < T) :
    LocalVortexStretchingBound T 4 := by
  refine ⟨1, by norm_num, ?_⟩
  intro ω g
  rw [vortexStretching3D_eq_triple_hadamard]
  rw [prod_triple_norm_eq]
  have h1 : ‖hadamard 4 g.1 ω.1‖ ≤ ‖g.1‖ * ‖ω.1‖ := hadamard_norm_le_n4 _ _
  have h2 : ‖hadamard 4 g.2.1 ω.2.1‖ ≤ ‖g.2.1‖ * ‖ω.2.1‖ := hadamard_norm_le_n4 _ _
  have h3 : ‖hadamard 4 g.2.2 ω.2.2‖ ≤ ‖g.2.2‖ * ‖ω.2.2‖ := hadamard_norm_le_n4 _ _
  have hω1 : ‖ω.1‖ ≤ ‖ω‖ := by
    rw [show ω = (ω.1, ω.2) from rfl, Prod.norm_def]; exact le_max_left _ _
  have hω2 : ‖ω.2.1‖ ≤ ‖ω‖ := by
    rw [show ω = (ω.1, ω.2) from rfl, Prod.norm_def]
    calc ‖ω.2.1‖ ≤ ‖ω.2‖ := by rw [Prod.norm_def]; exact le_max_left _ _
      _ ≤ max ‖ω.1‖ ‖ω.2‖ := le_max_right _ _
  have hω3 : ‖ω.2.2‖ ≤ ‖ω‖ := by
    rw [show ω = (ω.1, ω.2) from rfl, Prod.norm_def]
    calc ‖ω.2.2‖ ≤ ‖ω.2‖ := by rw [Prod.norm_def]; exact le_max_right _ _
      _ ≤ max ‖ω.1‖ ‖ω.2‖ := le_max_right _ _
  have hg1 : ‖g.1‖ ≤ ‖g‖ := by
    rw [show g = (g.1, g.2) from rfl, Prod.norm_def]; exact le_max_left _ _
  have hg2 : ‖g.2.1‖ ≤ ‖g‖ := by
    rw [show g = (g.1, g.2) from rfl, Prod.norm_def]
    calc ‖g.2.1‖ ≤ ‖g.2‖ := by rw [Prod.norm_def]; exact le_max_left _ _
      _ ≤ max ‖g.1‖ ‖g.2‖ := le_max_right _ _
  have hg3 : ‖g.2.2‖ ≤ ‖g‖ := by
    rw [show g = (g.1, g.2) from rfl, Prod.norm_def]
    calc ‖g.2.2‖ ≤ ‖g.2‖ := by rw [Prod.norm_def]; exact le_max_right _ _
      _ ≤ max ‖g.1‖ ‖g.2‖ := le_max_right _ _
  have ng : 0 ≤ ‖g‖ := norm_nonneg _
  have nω : 0 ≤ ‖ω‖ := norm_nonneg _
  have b1 : ‖hadamard 4 g.1 ω.1‖ ≤ ‖ω‖ * ‖g‖ := by
    calc ‖hadamard 4 g.1 ω.1‖ ≤ ‖g.1‖ * ‖ω.1‖ := h1
      _ ≤ ‖g‖ * ‖ω‖ := mul_le_mul hg1 hω1 (norm_nonneg _) ng
      _ = ‖ω‖ * ‖g‖ := by ring
  have b2 : ‖hadamard 4 g.2.1 ω.2.1‖ ≤ ‖ω‖ * ‖g‖ := by
    calc ‖hadamard 4 g.2.1 ω.2.1‖ ≤ ‖g.2.1‖ * ‖ω.2.1‖ := h2
      _ ≤ ‖g‖ * ‖ω‖ := mul_le_mul hg2 hω2 (norm_nonneg _) ng
      _ = ‖ω‖ * ‖g‖ := by ring
  have b3 : ‖hadamard 4 g.2.2 ω.2.2‖ ≤ ‖ω‖ * ‖g‖ := by
    calc ‖hadamard 4 g.2.2 ω.2.2‖ ≤ ‖g.2.2‖ * ‖ω.2.2‖ := h3
      _ ≤ ‖g‖ * ‖ω‖ := mul_le_mul hg3 hω3 (norm_nonneg _) ng
      _ = ‖ω‖ * ‖g‖ := by ring
  have hmax : max ‖hadamard 4 g.1 ω.1‖ (max ‖hadamard 4 g.2.1 ω.2.1‖
              ‖hadamard 4 g.2.2 ω.2.2‖) ≤ ‖ω‖ * ‖g‖ := by
    exact max_le b1 (max_le b2 b3)
  calc max ‖hadamard 4 g.1 ω.1‖ (max ‖hadamard 4 g.2.1 ω.2.1‖
            ‖hadamard 4 g.2.2 ω.2.2‖) ≤ ‖ω‖ * ‖g‖ := hmax
    _ = 1 * ‖ω‖ * ‖g‖ := by ring

/-- **★ At `n = 5`, the local bound holds for every `T > 0`** (axiom-free).
    The bilinear bound at the diagonal Galerkin shadow has `K_T = 1`,
    by the 5D Cauchy-Schwarz / Hadamard expansion. -/
theorem local_vortex_stretching_bound_at_n_eq_five (T : ℝ) (_hT : 0 < T) :
    LocalVortexStretchingBound T 5 := by
  refine ⟨1, by norm_num, ?_⟩
  intro ω g
  rw [vortexStretching3D_eq_triple_hadamard]
  rw [prod_triple_norm_eq]
  have h1 : ‖hadamard 5 g.1 ω.1‖ ≤ ‖g.1‖ * ‖ω.1‖ := hadamard_norm_le_n5 _ _
  have h2 : ‖hadamard 5 g.2.1 ω.2.1‖ ≤ ‖g.2.1‖ * ‖ω.2.1‖ := hadamard_norm_le_n5 _ _
  have h3 : ‖hadamard 5 g.2.2 ω.2.2‖ ≤ ‖g.2.2‖ * ‖ω.2.2‖ := hadamard_norm_le_n5 _ _
  have hω1 : ‖ω.1‖ ≤ ‖ω‖ := by
    rw [show ω = (ω.1, ω.2) from rfl, Prod.norm_def]; exact le_max_left _ _
  have hω2 : ‖ω.2.1‖ ≤ ‖ω‖ := by
    rw [show ω = (ω.1, ω.2) from rfl, Prod.norm_def]
    calc ‖ω.2.1‖ ≤ ‖ω.2‖ := by rw [Prod.norm_def]; exact le_max_left _ _
      _ ≤ max ‖ω.1‖ ‖ω.2‖ := le_max_right _ _
  have hω3 : ‖ω.2.2‖ ≤ ‖ω‖ := by
    rw [show ω = (ω.1, ω.2) from rfl, Prod.norm_def]
    calc ‖ω.2.2‖ ≤ ‖ω.2‖ := by rw [Prod.norm_def]; exact le_max_right _ _
      _ ≤ max ‖ω.1‖ ‖ω.2‖ := le_max_right _ _
  have hg1 : ‖g.1‖ ≤ ‖g‖ := by
    rw [show g = (g.1, g.2) from rfl, Prod.norm_def]; exact le_max_left _ _
  have hg2 : ‖g.2.1‖ ≤ ‖g‖ := by
    rw [show g = (g.1, g.2) from rfl, Prod.norm_def]
    calc ‖g.2.1‖ ≤ ‖g.2‖ := by rw [Prod.norm_def]; exact le_max_left _ _
      _ ≤ max ‖g.1‖ ‖g.2‖ := le_max_right _ _
  have hg3 : ‖g.2.2‖ ≤ ‖g‖ := by
    rw [show g = (g.1, g.2) from rfl, Prod.norm_def]
    calc ‖g.2.2‖ ≤ ‖g.2‖ := by rw [Prod.norm_def]; exact le_max_right _ _
      _ ≤ max ‖g.1‖ ‖g.2‖ := le_max_right _ _
  have ng : 0 ≤ ‖g‖ := norm_nonneg _
  have nω : 0 ≤ ‖ω‖ := norm_nonneg _
  have b1 : ‖hadamard 5 g.1 ω.1‖ ≤ ‖ω‖ * ‖g‖ := by
    calc ‖hadamard 5 g.1 ω.1‖ ≤ ‖g.1‖ * ‖ω.1‖ := h1
      _ ≤ ‖g‖ * ‖ω‖ := mul_le_mul hg1 hω1 (norm_nonneg _) ng
      _ = ‖ω‖ * ‖g‖ := by ring
  have b2 : ‖hadamard 5 g.2.1 ω.2.1‖ ≤ ‖ω‖ * ‖g‖ := by
    calc ‖hadamard 5 g.2.1 ω.2.1‖ ≤ ‖g.2.1‖ * ‖ω.2.1‖ := h2
      _ ≤ ‖g‖ * ‖ω‖ := mul_le_mul hg2 hω2 (norm_nonneg _) ng
      _ = ‖ω‖ * ‖g‖ := by ring
  have b3 : ‖hadamard 5 g.2.2 ω.2.2‖ ≤ ‖ω‖ * ‖g‖ := by
    calc ‖hadamard 5 g.2.2 ω.2.2‖ ≤ ‖g.2.2‖ * ‖ω.2.2‖ := h3
      _ ≤ ‖g‖ * ‖ω‖ := mul_le_mul hg3 hω3 (norm_nonneg _) ng
      _ = ‖ω‖ * ‖g‖ := by ring
  have hmax : max ‖hadamard 5 g.1 ω.1‖ (max ‖hadamard 5 g.2.1 ω.2.1‖
              ‖hadamard 5 g.2.2 ω.2.2‖) ≤ ‖ω‖ * ‖g‖ := by
    exact max_le b1 (max_le b2 b3)
  calc max ‖hadamard 5 g.1 ω.1‖ (max ‖hadamard 5 g.2.1 ω.2.1‖
            ‖hadamard 5 g.2.2 ω.2.2‖) ≤ ‖ω‖ * ‖g‖ := hmax
    _ = 1 * ‖ω‖ * ‖g‖ := by ring

/-! ## §4 — Capstone: combined `n ∈ {0, 1, 2, 3, 4, 5}` discharge -/

/-- **★★ CAPSTONE — Local bound discharged axiom-free at `n ∈ {0,1,2,3,4,5}`**.
    For every `T > 0`, the local vortex-stretching bound holds at the
    framework's diagonal Galerkin shadow at the six smallest Galerkin
    truncations. Extends Wave 22 (`n ≤ 3`) to `n ∈ {4, 5}` via the
    4D and 5D Hadamard expansions.

    Honest scope: this is the local-in-time Leray-Hopf 1934 shadow on the
    diagonal Galerkin model with `K_T = 1`. The Clay Millennium gap — whether
    `K_T` stays bounded as `T → ∞` for the full off-diagonal NS operator —
    remains captured by `VortexStretchingBoundedHypothesis`. -/
theorem local_vortex_stretching_bound_at_n_le_five
    (T : ℝ) (hT : 0 < T) :
    LocalVortexStretchingBound T 0 ∧
    LocalVortexStretchingBound T 1 ∧
    LocalVortexStretchingBound T 2 ∧
    LocalVortexStretchingBound T 3 ∧
    LocalVortexStretchingBound T 4 ∧
    LocalVortexStretchingBound T 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact local_vortex_stretching_bound_at_n_zero T hT
  · exact local_vortex_stretching_bound_at_n_one T hT
  · exact local_vortex_stretching_bound_at_n_two T hT
  · exact local_vortex_stretching_bound_at_n_eq_three T hT
  · exact local_vortex_stretching_bound_at_n_eq_four T hT
  · exact local_vortex_stretching_bound_at_n_eq_five T hT

end PrincipiaTractalis.NS3DLocalRegularityAtNEqFourFive
