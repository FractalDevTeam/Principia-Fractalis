/-
# NS3DLocalRegularityAtNEqThree: extend axiom-free `LocalVortexStretchingBound T n`
#   to `n = 3` at the framework's diagonal Galerkin shadow.

## Honest scope (READ FIRST)

This file extends the axiom-free discharge of `LocalVortexStretchingBound T n`
from `n ∈ {0, 1, 2}` (Wave 22 commit 9ce926a) to `n = 3` at the framework's
diagonal Galerkin shadow.

**THIS IS NOT THE CLAY MILLENNIUM PROBLEM.** The local-in-time bound at any
fixed Galerkin truncation is the classical Leray-Hopf 1934 shadow; whether the
constant `K_T` remains bounded as `T → ∞` is the Clay open question, captured
by `VortexStretchingBoundedHypothesis`.

## What this file delivers, AXIOM-FREE

At the framework's diagonal Galerkin model we discharge

    ‖VortexStretching3D ω g‖ ≤ K_T · ‖ω‖ · ‖g‖

with `K_T = 1` at `n = 3`, independent of `T > 0`.

The key new ingredient (relative to n = 2) is the **3D Cauchy-Schwarz**:

    (x₀² + x₁² + x₂²)(y₀² + y₁² + y₂²) ≥ (x₀y₀ + x₁y₁ + x₂y₂)²

which, via the 3D Lagrange identity, follows from non-negativity of the
three cross-product squares
`(x₀y₁ - x₁y₀)² + (x₀y₂ - x₂y₀)² + (x₁y₂ - x₂y₁)² ≥ 0`.

ZERO project axioms. ZERO `sorry`s.

Author: Pablo Cohen (formalization, Wave 22 extension)
Date: 2026-05-25
-/

import PF.NS3DLocalRegularityAtNGeqOneRetry
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.BigOperators.Fin

namespace PrincipiaTractalis.NS3DLocalRegularityAtNEqThree

open PrincipiaTractalis.NS3DVortexStretchingObstruction
open PrincipiaTractalis.NS3DLocalRegularityViaBKM
open PrincipiaTractalis.NS3DLocalRegularityAtNGeqOneRetry
open PrincipiaTractalis.MillenniumSix
open Real

/-! ## §1 — Hadamard bound at `n = 3` via 3D Lagrange identity -/

/-- **Hadamard bound at n = 3**: `‖x ⊙ y‖ ≤ ‖x‖ · ‖y‖`.

The Lagrange identity in 3D reads
  ‖x‖² · ‖y‖² − ⟨x,y⟩² = (x₀y₁ − x₁y₀)² + (x₀y₂ − x₂y₀)² + (x₁y₂ − x₂y₁)².
For the Hadamard (diagonal) bound we instead use the pointwise majorization
  (xᵢyᵢ)² ≤ xᵢ² · ‖y‖²    (since yᵢ² ≤ ‖y‖²)
summed across i = 0, 1, 2. Equivalently, the Cauchy-Schwarz-type expansion
  (x₀² + x₁² + x₂²)(y₀² + y₁² + y₂²)
    = (x₀y₀)² + (x₁y₁)² + (x₂y₂)²
      + (x₀y₁)² + (x₁y₀)² + (x₀y₂)² + (x₂y₀)² + (x₁y₂)² + (x₂y₁)²,
which dominates (x₀y₀)² + (x₁y₁)² + (x₂y₂)² since the remaining six squares
are non-negative. `nlinarith` discharges this directly. -/
theorem hadamard_norm_le_n3 (x y : EuclideanSpace ℝ (Fin 3)) :
    ‖hadamard 3 x y‖ ≤ ‖x‖ * ‖y‖ := by
  have hxy_nonneg : 0 ≤ ‖x‖ * ‖y‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsq_xy : ‖hadamard 3 x y‖ ^ 2
      = (x 0 * y 0) ^ 2 + (x 1 * y 1) ^ 2 + (x 2 * y 2) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Fin.sum_univ_three, hadamard, Real.norm_eq_abs, sq_abs]
  have hsq_x : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  have hsq_y : ‖y‖ ^ 2 = (y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  -- 3D Cauchy-Schwarz / Lagrange identity:
  -- (Σ xᵢ²)(Σ yᵢ²) − (Σ xᵢyᵢ)² = Σ_{i<j} (xᵢyⱼ − xⱼyᵢ)² ≥ 0.
  -- We do not need the full ⟨x,y⟩² ≤ — only the diagonal `Σ (xᵢyᵢ)²` ≤,
  -- which is **strictly weaker** and follows by dropping cross-products:
  -- ((x₀)² + (x₁)² + (x₂)²)·((y₀)² + (y₁)² + (y₂)²)
  --   − ((x₀y₀)² + (x₁y₁)² + (x₂y₂)²)
  --   = (x₀y₁)² + (x₀y₂)² + (x₁y₀)² + (x₁y₂)² + (x₂y₀)² + (x₂y₁)²  ≥ 0.
  have key : (x 0 * y 0) ^ 2 + (x 1 * y 1) ^ 2 + (x 2 * y 2) ^ 2
              ≤ ((x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2)
                * ((y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2) := by
    nlinarith [sq_nonneg (x 0 * y 1), sq_nonneg (x 0 * y 2),
               sq_nonneg (x 1 * y 0), sq_nonneg (x 1 * y 2),
               sq_nonneg (x 2 * y 0), sq_nonneg (x 2 * y 1)]
  have hsq_total : ‖hadamard 3 x y‖ ^ 2 ≤ (‖x‖ * ‖y‖) ^ 2 := by
    calc ‖hadamard 3 x y‖ ^ 2
        = (x 0 * y 0) ^ 2 + (x 1 * y 1) ^ 2 + (x 2 * y 2) ^ 2 := hsq_xy
      _ ≤ ((x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2)
            * ((y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2) := key
      _ = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by rw [hsq_x, hsq_y]
      _ = (‖x‖ * ‖y‖) ^ 2 := by ring
  have h_nn : 0 ≤ ‖hadamard 3 x y‖ := norm_nonneg _
  nlinarith [hsq_total, h_nn, hxy_nonneg]

/-! ## §2 — Lift to `Vorticity3DState 3` and discharge the local bound -/

/-- **★ At `n = 3`, the local bound holds for every `T > 0`** (axiom-free).
    The bilinear bound at the diagonal Galerkin shadow has `K_T = 1`,
    by the 3D Lagrange identity (Cauchy-Schwarz in 3 dimensions). -/
theorem local_vortex_stretching_bound_at_n_eq_three (T : ℝ) (_hT : 0 < T) :
    LocalVortexStretchingBound T 3 := by
  refine ⟨1, by norm_num, ?_⟩
  intro ω g
  rw [vortexStretching3D_eq_triple_hadamard]
  rw [prod_triple_norm_eq]
  have h1 : ‖hadamard 3 g.1 ω.1‖ ≤ ‖g.1‖ * ‖ω.1‖ := hadamard_norm_le_n3 _ _
  have h2 : ‖hadamard 3 g.2.1 ω.2.1‖ ≤ ‖g.2.1‖ * ‖ω.2.1‖ := hadamard_norm_le_n3 _ _
  have h3 : ‖hadamard 3 g.2.2 ω.2.2‖ ≤ ‖g.2.2‖ * ‖ω.2.2‖ := hadamard_norm_le_n3 _ _
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
  have b1 : ‖hadamard 3 g.1 ω.1‖ ≤ ‖ω‖ * ‖g‖ := by
    calc ‖hadamard 3 g.1 ω.1‖ ≤ ‖g.1‖ * ‖ω.1‖ := h1
      _ ≤ ‖g‖ * ‖ω‖ := mul_le_mul hg1 hω1 (norm_nonneg _) ng
      _ = ‖ω‖ * ‖g‖ := by ring
  have b2 : ‖hadamard 3 g.2.1 ω.2.1‖ ≤ ‖ω‖ * ‖g‖ := by
    calc ‖hadamard 3 g.2.1 ω.2.1‖ ≤ ‖g.2.1‖ * ‖ω.2.1‖ := h2
      _ ≤ ‖g‖ * ‖ω‖ := mul_le_mul hg2 hω2 (norm_nonneg _) ng
      _ = ‖ω‖ * ‖g‖ := by ring
  have b3 : ‖hadamard 3 g.2.2 ω.2.2‖ ≤ ‖ω‖ * ‖g‖ := by
    calc ‖hadamard 3 g.2.2 ω.2.2‖ ≤ ‖g.2.2‖ * ‖ω.2.2‖ := h3
      _ ≤ ‖g‖ * ‖ω‖ := mul_le_mul hg3 hω3 (norm_nonneg _) ng
      _ = ‖ω‖ * ‖g‖ := by ring
  have hmax : max ‖hadamard 3 g.1 ω.1‖ (max ‖hadamard 3 g.2.1 ω.2.1‖
              ‖hadamard 3 g.2.2 ω.2.2‖) ≤ ‖ω‖ * ‖g‖ := by
    exact max_le b1 (max_le b2 b3)
  calc max ‖hadamard 3 g.1 ω.1‖ (max ‖hadamard 3 g.2.1 ω.2.1‖
            ‖hadamard 3 g.2.2 ω.2.2‖) ≤ ‖ω‖ * ‖g‖ := hmax
    _ = 1 * ‖ω‖ * ‖g‖ := by ring

/-! ## §3 — Capstone: combined `n ∈ {0, 1, 2, 3}` discharge -/

/-- **★★ CAPSTONE — Local bound discharged axiom-free at `n ∈ {0, 1, 2, 3}`**.
    For every `T > 0`, the local vortex-stretching bound holds at the
    framework's diagonal Galerkin shadow at the four smallest Galerkin
    truncations. Extends Wave 22 (`n ≤ 2`) to `n = 3` via the
    3D Lagrange / Cauchy-Schwarz identity.

    Honest scope: this is the local-in-time Leray-Hopf 1934 shadow on the
    diagonal Galerkin model with `K_T = 1`. The Clay Millennium gap — whether
    `K_T` stays bounded as `T → ∞` for the full off-diagonal NS operator —
    remains captured by `VortexStretchingBoundedHypothesis`. -/
theorem local_vortex_stretching_bound_at_n_le_three
    (T : ℝ) (hT : 0 < T) :
    LocalVortexStretchingBound T 0 ∧
    LocalVortexStretchingBound T 1 ∧
    LocalVortexStretchingBound T 2 ∧
    LocalVortexStretchingBound T 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact local_vortex_stretching_bound_at_n_zero T hT
  · exact local_vortex_stretching_bound_at_n_one T hT
  · exact local_vortex_stretching_bound_at_n_two T hT
  · exact local_vortex_stretching_bound_at_n_eq_three T hT

end PrincipiaTractalis.NS3DLocalRegularityAtNEqThree
