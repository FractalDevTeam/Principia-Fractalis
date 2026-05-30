/-
# NS3DUniformHadamardDischargeAttempt

Discharge attempt for `UniformHadamardBoundAllN` (the single named open
Prop introduced by Wave 33 in `NS3DGlobalKTAttempt.lean`) AXIOM-FREE.

## Honest scope (READ FIRST)

The Wave 33 file `PF/NS3DGlobalKTAttempt.lean` reduced the all-`n`
Galerkin-shadow vortex-stretching bound to a SINGLE explicit Prop:

  `UniformHadamardBoundAllN :=
      ∀ n : ℕ, ∀ (x y : EuclideanSpace ℝ (Fin n)),
        ‖hadamard n x y‖ ≤ ‖x‖ * ‖y‖`

i.e. the per-`n` Hadamard product (elementwise product on
`EuclideanSpace ℝ (Fin n)`) is sub-multiplicative w.r.t. the ℓ²-norm,
UNIFORMLY in `n`.

This file gives a uniform-in-`n` axiom-free proof of that Prop via
`EuclideanSpace.norm_sq_eq` + the elementary "single-term in a sum of
non-negatives" bound + `Finset.mul_sum`. The argument is the
diagonal-only Cauchy-Schwarz collapse:

  ‖x ⊙ y‖² = Σᵢ (xᵢ·yᵢ)² = Σᵢ xᵢ²·yᵢ²  ≤  Σᵢ xᵢ²·‖y‖²
            = ‖y‖² · Σᵢ xᵢ²  =  ‖x‖² · ‖y‖²  =  (‖x‖·‖y‖)².

Take square root (or apply `abs_le_of_sq_le_sq`) to conclude.

Once the Prop is discharged, the conditional reductions
`all_n_diag_from_uniform_hadamard` and `all_n_off_from_uniform_hadamard`
from the Wave 33 file lift the framework's local-`n` bounds to ALL `n`,
giving the FIRST all-`n` Galerkin-shadow result in the NS arc.

## What this STILL does NOT do (the honest gap)

* The bound is on the Galerkin-shadow `VortexStretching3D` /
  `VortexStretching3DOffDiagonal` operators, NOT the full
  PDE-level `(ω · ∇) u` bilinear form on Sobolev spaces. The full
  PDE-level Clay open content remains captured by
  `VortexStretchingBoundedHypothesis`.

* The framework therefore advances from "3 layers from Clay"
  (per-`n ≤ 5` discharged, all-`n` open as `UniformHadamardBoundAllN`,
  PDE-level open as `VortexStretchingBoundedHypothesis`) to
  "2 layers from Clay" (all-`n` Galerkin-shadow discharged
  unconditionally, PDE-level remains open).

This is a meaningful but bounded structural advance, NOT a Clay
discharge.

ZERO project axioms. ZERO `sorry`s. ZERO `admit`s.

Author: Pablo Cohen (formalization, Wave 33+ uniform-Hadamard discharge)
Date: 2026-05-30
-/

import PF.NS3DGlobalKTAttempt

namespace PrincipiaTractalis.NS3DUniformHadamardDischargeAttempt

open PrincipiaTractalis.NS3DVortexStretchingObstruction
open PrincipiaTractalis.NS3DLocalRegularityAtNGeqOneRetry
open PrincipiaTractalis.NS3DGlobalKTAttempt
open Real

/-! ## §1 — The uniform-in-`n` Hadamard bound (axiom-free)

For all `n : ℕ` and all `x y : EuclideanSpace ℝ (Fin n)`,
`‖x ⊙ y‖ ≤ ‖x‖ · ‖y‖`. Proof: the diagonal-only Cauchy-Schwarz
collapse via `EuclideanSpace.norm_sq_eq` and `Finset.single_le_sum`.
-/

/-- **The uniform-in-`n` Hadamard bound at a fixed `n`** (axiom-free).
    This is the single statement that, ranging over all `n`, gives
    `UniformHadamardBoundAllN`. -/
theorem hadamard_norm_le_uniform (n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) :
    ‖hadamard n x y‖ ≤ ‖x‖ * ‖y‖ := by
  -- Strategy:
  --   ‖x⊙y‖² = Σ (xᵢ yᵢ)² ≤ Σ xᵢ² · ‖y‖² = ‖y‖² · ‖x‖² = (‖x‖·‖y‖)²
  -- then sqrt monotonicity (via `abs_le_of_sq_le_sq`).
  have hxy_nonneg : 0 ≤ ‖x‖ * ‖y‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  -- Step 1: Compute the squared norms.
  have hsq_x : ‖x‖ ^ 2 = ∑ i, (x i) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, sq_abs]
  have hsq_y : ‖y‖ ^ 2 = ∑ i, (y i) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, sq_abs]
  have hsq_xy : ‖hadamard n x y‖ ^ 2 = ∑ i, (x i * y i) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    have h := sq_abs (x i * y i)
    simp [hadamard, Real.norm_eq_abs, ← h]
  -- Step 2: Pointwise bound (y i)² ≤ Σⱼ (y j)² = ‖y‖².
  have hyi_sq_le : ∀ i : Fin n, (y i) ^ 2 ≤ ‖y‖ ^ 2 := by
    intro i
    rw [hsq_y]
    exact Finset.single_le_sum (f := fun j => (y j) ^ 2)
      (fun j _ => sq_nonneg (y j)) (Finset.mem_univ i)
  -- Step 3: (x i · y i)² = (x i)² · (y i)² ≤ (x i)² · ‖y‖².
  have key_pointwise : ∀ i : Fin n,
      (x i * y i) ^ 2 ≤ (x i) ^ 2 * ‖y‖ ^ 2 := by
    intro i
    have hxi_sq_nn : 0 ≤ (x i) ^ 2 := sq_nonneg _
    have hyi := hyi_sq_le i
    have : (x i * y i) ^ 2 = (x i) ^ 2 * (y i) ^ 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hyi hxi_sq_nn
  -- Step 4: Sum the pointwise bound:
  --   Σᵢ (xᵢ·yᵢ)² ≤ Σᵢ xᵢ²·‖y‖² = ‖y‖² · Σᵢ xᵢ² = ‖y‖² · ‖x‖² = (‖x‖·‖y‖)².
  have step_sum : ∑ i, (x i * y i) ^ 2 ≤ ∑ i, (x i) ^ 2 * ‖y‖ ^ 2 :=
    Finset.sum_le_sum (fun i _ => key_pointwise i)
  have hfactor : ∑ i, (x i) ^ 2 * ‖y‖ ^ 2 = ‖y‖ ^ 2 * ∑ i, (x i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsq_bound : ‖hadamard n x y‖ ^ 2 ≤ (‖x‖ * ‖y‖) ^ 2 := by
    have h1 : ‖hadamard n x y‖ ^ 2 ≤ ‖y‖ ^ 2 * ∑ i, (x i) ^ 2 := by
      rw [hsq_xy]
      exact le_trans step_sum (le_of_eq hfactor)
    have h2 : ‖y‖ ^ 2 * ∑ i, (x i) ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by
      rw [← hsq_x]; ring
    exact le_trans h1 (le_of_eq h2)
  -- Step 5: Take square roots. Both ‖hadamard ...‖ and ‖x‖·‖y‖ are ≥ 0,
  -- so the squared inequality implies the linear one.
  have h_nn : 0 ≤ ‖hadamard n x y‖ := norm_nonneg _
  have habs : |‖hadamard n x y‖| ≤ ‖x‖ * ‖y‖ :=
    abs_le_of_sq_le_sq hsq_bound hxy_nonneg
  rwa [abs_of_nonneg h_nn] at habs

/-! ## §2 — Discharge of `UniformHadamardBoundAllN`

The all-`n` Prop falls immediately from the per-`n` theorem above.
-/

/-- **★★ MAIN DISCHARGE — `UniformHadamardBoundAllN` is axiom-free**.

    The Wave 33 file's single named open Prop is unconditionally proved
    here via the diagonal-only Cauchy-Schwarz collapse on
    `EuclideanSpace ℝ (Fin n)`. -/
theorem uniform_hadamard_bound_all_n_holds : UniformHadamardBoundAllN := by
  intro n x y
  exact hadamard_norm_le_uniform n x y

/-! ## §3 — Downstream all-`n` Galerkin-shadow bounds (unconditional)

With `UniformHadamardBoundAllN` discharged, the conditional reductions
from `NS3DGlobalKTAttempt` lift the framework's local-`n` Hadamard
bounds to ALL `n` unconditionally. These are the FIRST all-`n`
Galerkin-shadow vortex-stretching bounds in the framework.
-/

/-- **All-`n` diagonal Galerkin-shadow vortex-stretching bound**
    (axiom-free, `K = 1` uniformly). -/
theorem all_n_diag_uniform (T : ℝ) (hT : 0 < T) :
    UniformVortexStretchingBoundAllN T 1 :=
  all_n_diag_from_uniform_hadamard uniform_hadamard_bound_all_n_holds T hT

/-- **All-`n` off-diagonal Galerkin-shadow vortex-stretching bound**
    (axiom-free, `K = 2` uniformly). -/
theorem all_n_off_uniform (T : ℝ) (hT : 0 < T) :
    UniformVortexStretchingBoundOffDiagonalAllN T 2 :=
  all_n_off_from_uniform_hadamard uniform_hadamard_bound_all_n_holds T hT

/-! ## §4 — Capstone: unconditional Galerkin-shadow global K_T

Combining the two all-`n` bounds via the diagonal monotone-weakening
lift (K = 1 ⟹ K = 2) gives the FULL Galerkin-shadow global-K_T at
`K = 2`, AXIOM-FREE.
-/

/-- **★★★ CAPSTONE — Galerkin-shadow global-K_T at `K = 2`, axiom-free**.

    With Wave 33's reduction + the Wave 34 uniform-Hadamard discharge,
    the all-`n` Galerkin-shadow vortex-stretching bound at the common
    constant `K = 2` is unconditional.

    Honest scope: this is the GALERKIN-SHADOW model
    (diagonal `VortexStretching3D` + off-diagonal
    `VortexStretching3DOffDiagonal`), NOT the FULL PDE-level
    `(ω · ∇) u` bilinear form on Sobolev spaces. The Clay-open content
    remains `VortexStretchingBoundedHypothesis`. -/
theorem uniform_hadamard_discharges_galerkin_shadow_K_T
    (T : ℝ) (hT : 0 < T) :
    GlobalKTGalerkinShadow T 2 :=
  global_K_T_galerkin_shadow_from_uniform_hadamard
    uniform_hadamard_bound_all_n_holds T hT

/-! ## §5 — Honest narrowing after this discharge

  BEFORE (Wave 33):
    finite-`n ≤ 5` shared `K = 2`           [axiom-free]
      ⟸ uniform-Hadamard hypothesis at all `n`
         (`UniformHadamardBoundAllN`)        [open, structural]
      ⟸ Galerkin-shadow global-K_T at K = 2
         (`GlobalKTGalerkinShadow T 2`)      [conditional]
      ⟸ FULL PDE-level Clay bound
         (`VortexStretchingBoundedHypothesis`)  [Clay-open]

  AFTER (Wave 34, THIS FILE):
    `UniformHadamardBoundAllN`               [axiom-free THEOREM]
    `GlobalKTGalerkinShadow T 2`             [axiom-free THEOREM]
    `VortexStretchingBoundedHypothesis`      [Clay-open, unchanged]

  Distance to Clay: 3 layers → 2 layers (one layer collapsed). The
  remaining gap is the operator-level / PDE-level lift from the
  diagonal+off-diagonal Galerkin shadow on Cartesian-cubed
  `EuclideanSpace`-tuples to the full bilinear vortex-stretching
  operator on a real Sobolev / Besov space of divergence-free vector
  fields. That gap is what `VortexStretchingBoundedHypothesis`
  captures — and it is NOT discharged here.
-/

/-- **Honest assessment certificate**: the framework now establishes,
    axiom-free, BOTH the finite-`n ≤ 5` common-constant bound AND the
    all-`n` Galerkin-shadow bound. The remaining gap to Clay is exactly
    one structural Prop (`VortexStretchingBoundedHypothesis`). -/
theorem ns_3d_galerkin_shadow_unconditional_status
    (T : ℝ) (hT : 0 < T) :
    -- (1) The Wave 33 uniform-K = 2 at n ∈ {0..5} (already axiom-free).
    (UniformLocalVortexStretchingBound T 0 2 ∧
     UniformLocalVortexStretchingBound T 1 2 ∧
     UniformLocalVortexStretchingBound T 2 2 ∧
     UniformLocalVortexStretchingBound T 3 2 ∧
     UniformLocalVortexStretchingBound T 4 2 ∧
     UniformLocalVortexStretchingBound T 5 2 ∧
     UniformLocalVortexStretchingBoundOffDiagonal T 0 2 ∧
     UniformLocalVortexStretchingBoundOffDiagonal T 1 2 ∧
     UniformLocalVortexStretchingBoundOffDiagonal T 2 2 ∧
     UniformLocalVortexStretchingBoundOffDiagonal T 3 2 ∧
     UniformLocalVortexStretchingBoundOffDiagonal T 4 2 ∧
     UniformLocalVortexStretchingBoundOffDiagonal T 5 2) ∧
    -- (2) The Wave 34 all-`n` uniform Hadamard bound (axiom-free here).
    UniformHadamardBoundAllN ∧
    -- (3) Wave 34 all-`n` diagonal Galerkin-shadow bound (K = 1).
    UniformVortexStretchingBoundAllN T 1 ∧
    -- (4) Wave 34 all-`n` off-diagonal Galerkin-shadow bound (K = 2).
    UniformVortexStretchingBoundOffDiagonalAllN T 2 ∧
    -- (5) Wave 34 full Galerkin-shadow global-K_T at K = 2 (axiom-free).
    GlobalKTGalerkinShadow T 2 := by
  refine ⟨uniform_K2_at_n_le_five T hT,
          uniform_hadamard_bound_all_n_holds,
          all_n_diag_uniform T hT,
          all_n_off_uniform T hT,
          uniform_hadamard_discharges_galerkin_shadow_K_T T hT⟩

end PrincipiaTractalis.NS3DUniformHadamardDischargeAttempt
