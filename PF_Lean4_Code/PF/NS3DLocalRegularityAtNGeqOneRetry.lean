/-
# NS3DLocalRegularityAtNGeqOneRetry: discharge `LocalVortexStretchingBound T n`
#   axiom-free at the framework's diagonal Galerkin shadow for n = 1 and n = 2.

## Honest scope (READ FIRST)

This file extends the axiom-free discharge of `LocalVortexStretchingBound T n`
from `n = 0` (Wave 19 commit d280edb, `NS3DLocalRegularityViaBKM.lean`) to
`n = 1` and `n = 2` at the framework's diagonal Galerkin shadow.

**THIS IS NOT THE CLAY MILLENNIUM PROBLEM.** The local-in-time bound at any
fixed Galerkin truncation is the classical Leray-Hopf 1934 shadow; whether the
constant `K_T` remains bounded as `T → ∞` is the Clay open question, captured
by `VortexStretchingBoundedHypothesis`.

## What this file delivers, AXIOM-FREE

At the framework's diagonal Galerkin model

    VortexStretching3D ω g := (g₁ ⊙ ω₁, g₂ ⊙ ω₂, g₃ ⊙ ω₃)

(where `⊙` is the elementwise / Hadamard product on `EuclideanSpace ℝ (Fin n)`),
we discharge the operator-norm bound

    ‖VortexStretching3D ω g‖ ≤ K_T · ‖ω‖ · ‖g‖

with `K_T = 1` for both `n = 1` and `n = 2`, independent of `T > 0`.

The proof key fact is the pointwise / componentwise bound

    ‖(x_i · y_i)_{i}‖_{ℓ²} ≤ ‖x‖_{ℓ²} · ‖y‖_{ℓ²}

at the diagonal Galerkin shadow (the diagonal subbilinear part of
`(ω · ∇) u`). This is the worst-case pointwise bound used in BKM.

The off-diagonal contributions to `(ω · ∇) u` are what make the GLOBAL
bound Clay-hard; they are NOT captured by the diagonal Galerkin model.

ZERO project axioms. ZERO `sorry`s.

Author: Pablo Cohen (formalization, Wave 21 retry)
Date: 2026-05-25
-/

import PF.NS3DLocalRegularityViaBKM
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.BigOperators.Fin

namespace PrincipiaTractalis.NS3DLocalRegularityAtNGeqOneRetry

open PrincipiaTractalis.NS3DVortexStretchingObstruction
open PrincipiaTractalis.NS3DLocalRegularityViaBKM
open PrincipiaTractalis.MillenniumSix
open Real

/-! ## §1 — Componentwise diagonal product bound on `EuclideanSpace ℝ (Fin n)`

For x, y ∈ EuclideanSpace ℝ (Fin n) define the Hadamard product
`x ⊙ y : EuclideanSpace ℝ (Fin n)` by `(x ⊙ y) i = x i * y i`. We show
`‖x ⊙ y‖ ≤ ‖x‖ · ‖y‖` for `n = 1` and `n = 2` via direct calculation.
-/

/-- The Hadamard (elementwise) product on `EuclideanSpace ℝ (Fin n)`. -/
noncomputable def hadamard (n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) := fun i => x i * y i

/-- **Hadamard bound at n = 1**: `‖x ⊙ y‖ ≤ ‖x‖ · ‖y‖`. -/
theorem hadamard_norm_le_n1 (x y : EuclideanSpace ℝ (Fin 1)) :
    ‖hadamard 1 x y‖ ≤ ‖x‖ * ‖y‖ := by
  -- ‖x‖² = (x 0)², ‖y‖² = (y 0)², ‖x⊙y‖² = (x 0 · y 0)²
  have hx : ‖x‖ = |x 0| := by
    rw [EuclideanSpace.norm_eq]
    simp [Real.norm_eq_abs, Real.sqrt_sq_eq_abs]
  have hy : ‖y‖ = |y 0| := by
    rw [EuclideanSpace.norm_eq]
    simp [Real.norm_eq_abs, Real.sqrt_sq_eq_abs]
  have hxy : ‖hadamard 1 x y‖ = |x 0 * y 0| := by
    rw [EuclideanSpace.norm_eq]
    simp [Real.norm_eq_abs, Real.sqrt_sq_eq_abs, hadamard]
  rw [hx, hy, hxy, abs_mul]

/-- **Hadamard bound at n = 2**: `‖x ⊙ y‖ ≤ ‖x‖ · ‖y‖`. -/
theorem hadamard_norm_le_n2 (x y : EuclideanSpace ℝ (Fin 2)) :
    ‖hadamard 2 x y‖ ≤ ‖x‖ * ‖y‖ := by
  -- Strategy: show ‖x⊙y‖² ≤ (‖x‖·‖y‖)² and both sides nonneg.
  have hxy_nonneg : 0 ≤ ‖x‖ * ‖y‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  -- Pointwise: (x i · y i)² ≤ (x i)² · (‖y‖²)
  --   because |y i| ≤ ‖y‖, so (y i)² ≤ ‖y‖².
  -- Sum: ‖x⊙y‖² = Σ (x i · y i)² ≤ Σ (x i)²·‖y‖² = ‖x‖²·‖y‖² = (‖x‖·‖y‖)².
  have hsq_xy : ‖hadamard 2 x y‖ ^ 2 = (x 0 * y 0) ^ 2 + (x 1 * y 1) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Fin.sum_univ_two, hadamard, Real.norm_eq_abs, sq_abs]
  have hsq_x : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  have hsq_y : ‖y‖ ^ 2 = (y 0) ^ 2 + (y 1) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  -- Algebraic inequality: (x0 y0)² + (x1 y1)² ≤ ((x0)² + (x1)²)((y0)² + (y1)²)
  -- This is the Lagrange identity (= LHS + (x0 y1 - x1 y0)²).
  have key : (x 0 * y 0) ^ 2 + (x 1 * y 1) ^ 2
              ≤ ((x 0) ^ 2 + (x 1) ^ 2) * ((y 0) ^ 2 + (y 1) ^ 2) := by
    nlinarith [sq_nonneg (x 0 * y 1 - x 1 * y 0)]
  have hsq_total : ‖hadamard 2 x y‖ ^ 2 ≤ (‖x‖ * ‖y‖) ^ 2 := by
    calc ‖hadamard 2 x y‖ ^ 2
        = (x 0 * y 0) ^ 2 + (x 1 * y 1) ^ 2 := hsq_xy
      _ ≤ ((x 0) ^ 2 + (x 1) ^ 2) * ((y 0) ^ 2 + (y 1) ^ 2) := key
      _ = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by rw [hsq_x, hsq_y]
      _ = (‖x‖ * ‖y‖) ^ 2 := by ring
  -- Conclude ‖x⊙y‖ ≤ ‖x‖ · ‖y‖ via sqrt monotonicity.
  have h_nn : 0 ≤ ‖hadamard 2 x y‖ := norm_nonneg _
  nlinarith [hsq_total, h_nn, hxy_nonneg]

/-! ## §2 — Lift the Hadamard bound to triples (`Vorticity3DState n`)

`VortexStretching3D ω g = (hadamard ω₁ g₁, hadamard ω₂ g₂, hadamard ω₃ g₃)`.
We use `Prod.norm_def : ‖(a, b)‖ = max ‖a‖ ‖b‖` to lift the bound.
-/

/-- **Vortex stretching equals triple of Hadamard products**. -/
lemma vortexStretching3D_eq_triple_hadamard {n : ℕ}
    (ω : Vorticity3DState n) (g : VelocityGradient3DState n) :
    VortexStretching3D ω g
      = (hadamard n g.1 ω.1, hadamard n g.2.1 ω.2.1, hadamard n g.2.2 ω.2.2) := by
  unfold VortexStretching3D hadamard
  rfl

/-- Triple-product norm in terms of components. -/
lemma prod_triple_norm_eq {n : ℕ} (a b c : EuclideanSpace ℝ (Fin n)) :
    ‖((a, b, c) : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
        EuclideanSpace ℝ (Fin n))‖ = max ‖a‖ (max ‖b‖ ‖c‖) := by
  rw [Prod.norm_def, Prod.norm_def]

/-! ## §3 — The local bound at `n = 1` (axiom-free) -/

/-- **★ At `n = 1`, the local bound holds for every `T > 0`** (axiom-free).
    The bilinear bound at the diagonal Galerkin shadow has `K_T = 1`. -/
theorem local_vortex_stretching_bound_at_n_one (T : ℝ) (_hT : 0 < T) :
    LocalVortexStretchingBound T 1 := by
  refine ⟨1, by norm_num, ?_⟩
  intro ω g
  -- Rewrite VortexStretching3D as the triple of Hadamard products
  rw [vortexStretching3D_eq_triple_hadamard]
  rw [prod_triple_norm_eq]
  -- Each Hadamard component bounded by ‖g_k‖ · ‖ω_k‖
  have h1 : ‖hadamard 1 g.1 ω.1‖ ≤ ‖g.1‖ * ‖ω.1‖ := hadamard_norm_le_n1 _ _
  have h2 : ‖hadamard 1 g.2.1 ω.2.1‖ ≤ ‖g.2.1‖ * ‖ω.2.1‖ := hadamard_norm_le_n1 _ _
  have h3 : ‖hadamard 1 g.2.2 ω.2.2‖ ≤ ‖g.2.2‖ * ‖ω.2.2‖ := hadamard_norm_le_n1 _ _
  -- Bound each component by ‖ω‖ · ‖g‖ using max bounds on the product norm
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
  -- Combine: each ≤ ‖g‖·‖ω‖ ≤ ‖ω‖·‖g‖
  have ng : 0 ≤ ‖g‖ := norm_nonneg _
  have nω : 0 ≤ ‖ω‖ := norm_nonneg _
  have b1 : ‖hadamard 1 g.1 ω.1‖ ≤ ‖ω‖ * ‖g‖ := by
    calc ‖hadamard 1 g.1 ω.1‖ ≤ ‖g.1‖ * ‖ω.1‖ := h1
      _ ≤ ‖g‖ * ‖ω‖ := mul_le_mul hg1 hω1 (norm_nonneg _) ng
      _ = ‖ω‖ * ‖g‖ := by ring
  have b2 : ‖hadamard 1 g.2.1 ω.2.1‖ ≤ ‖ω‖ * ‖g‖ := by
    calc ‖hadamard 1 g.2.1 ω.2.1‖ ≤ ‖g.2.1‖ * ‖ω.2.1‖ := h2
      _ ≤ ‖g‖ * ‖ω‖ := mul_le_mul hg2 hω2 (norm_nonneg _) ng
      _ = ‖ω‖ * ‖g‖ := by ring
  have b3 : ‖hadamard 1 g.2.2 ω.2.2‖ ≤ ‖ω‖ * ‖g‖ := by
    calc ‖hadamard 1 g.2.2 ω.2.2‖ ≤ ‖g.2.2‖ * ‖ω.2.2‖ := h3
      _ ≤ ‖g‖ * ‖ω‖ := mul_le_mul hg3 hω3 (norm_nonneg _) ng
      _ = ‖ω‖ * ‖g‖ := by ring
  -- The maximum of three quantities each ≤ ‖ω‖·‖g‖ is ≤ ‖ω‖·‖g‖
  have hmax : max ‖hadamard 1 g.1 ω.1‖ (max ‖hadamard 1 g.2.1 ω.2.1‖
              ‖hadamard 1 g.2.2 ω.2.2‖) ≤ ‖ω‖ * ‖g‖ := by
    exact max_le b1 (max_le b2 b3)
  -- Final shape: 1 * ‖ω‖ * ‖g‖ = ‖ω‖ * ‖g‖
  calc max ‖hadamard 1 g.1 ω.1‖ (max ‖hadamard 1 g.2.1 ω.2.1‖
            ‖hadamard 1 g.2.2 ω.2.2‖) ≤ ‖ω‖ * ‖g‖ := hmax
    _ = 1 * ‖ω‖ * ‖g‖ := by ring

/-! ## §4 — The local bound at `n = 2` (axiom-free) -/

/-- **★ At `n = 2`, the local bound holds for every `T > 0`** (axiom-free).
    The bilinear bound at the diagonal Galerkin shadow has `K_T = 1`,
    by the Lagrange identity (Cauchy-Schwarz in 2 dimensions). -/
theorem local_vortex_stretching_bound_at_n_two (T : ℝ) (_hT : 0 < T) :
    LocalVortexStretchingBound T 2 := by
  refine ⟨1, by norm_num, ?_⟩
  intro ω g
  rw [vortexStretching3D_eq_triple_hadamard]
  rw [prod_triple_norm_eq]
  have h1 : ‖hadamard 2 g.1 ω.1‖ ≤ ‖g.1‖ * ‖ω.1‖ := hadamard_norm_le_n2 _ _
  have h2 : ‖hadamard 2 g.2.1 ω.2.1‖ ≤ ‖g.2.1‖ * ‖ω.2.1‖ := hadamard_norm_le_n2 _ _
  have h3 : ‖hadamard 2 g.2.2 ω.2.2‖ ≤ ‖g.2.2‖ * ‖ω.2.2‖ := hadamard_norm_le_n2 _ _
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
  have b1 : ‖hadamard 2 g.1 ω.1‖ ≤ ‖ω‖ * ‖g‖ := by
    calc ‖hadamard 2 g.1 ω.1‖ ≤ ‖g.1‖ * ‖ω.1‖ := h1
      _ ≤ ‖g‖ * ‖ω‖ := mul_le_mul hg1 hω1 (norm_nonneg _) ng
      _ = ‖ω‖ * ‖g‖ := by ring
  have b2 : ‖hadamard 2 g.2.1 ω.2.1‖ ≤ ‖ω‖ * ‖g‖ := by
    calc ‖hadamard 2 g.2.1 ω.2.1‖ ≤ ‖g.2.1‖ * ‖ω.2.1‖ := h2
      _ ≤ ‖g‖ * ‖ω‖ := mul_le_mul hg2 hω2 (norm_nonneg _) ng
      _ = ‖ω‖ * ‖g‖ := by ring
  have b3 : ‖hadamard 2 g.2.2 ω.2.2‖ ≤ ‖ω‖ * ‖g‖ := by
    calc ‖hadamard 2 g.2.2 ω.2.2‖ ≤ ‖g.2.2‖ * ‖ω.2.2‖ := h3
      _ ≤ ‖g‖ * ‖ω‖ := mul_le_mul hg3 hω3 (norm_nonneg _) ng
      _ = ‖ω‖ * ‖g‖ := by ring
  have hmax : max ‖hadamard 2 g.1 ω.1‖ (max ‖hadamard 2 g.2.1 ω.2.1‖
              ‖hadamard 2 g.2.2 ω.2.2‖) ≤ ‖ω‖ * ‖g‖ := by
    exact max_le b1 (max_le b2 b3)
  calc max ‖hadamard 2 g.1 ω.1‖ (max ‖hadamard 2 g.2.1 ω.2.1‖
            ‖hadamard 2 g.2.2 ω.2.2‖) ≤ ‖ω‖ * ‖g‖ := hmax
    _ = 1 * ‖ω‖ * ‖g‖ := by ring

/-! ## §5 — Capstone: combined `n ∈ {0, 1, 2}` discharge -/

/-- **★★ CAPSTONE — Local bound discharged axiom-free at `n ∈ {0, 1, 2}`**.
    For every `T > 0`, the local vortex-stretching bound holds at the
    framework's diagonal Galerkin shadow at the three smallest Galerkin
    truncations. This extends the Wave 19 `n = 0` discharge to `n = 1`
    and `n = 2` via the Lagrange identity (Cauchy-Schwarz in 2D). -/
theorem local_vortex_stretching_bound_at_n_le_two
    (T : ℝ) (hT : 0 < T) :
    LocalVortexStretchingBound T 0 ∧
    LocalVortexStretchingBound T 1 ∧
    LocalVortexStretchingBound T 2 := by
  refine ⟨?_, ?_, ?_⟩
  · exact local_vortex_stretching_bound_at_n_zero T hT
  · exact local_vortex_stretching_bound_at_n_one T hT
  · exact local_vortex_stretching_bound_at_n_two T hT

end PrincipiaTractalis.NS3DLocalRegularityAtNGeqOneRetry
