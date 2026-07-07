/-
# r85: The 1-Lipschitz bound for the normalized matrix trace via
#      the Hilbert-Schmidt route

★ 2026-07-07 r85 — the essential analytic prerequisite for the
UHF trace extension ★

## The framework-first content

r84 landed the generalized normalized matrix trace with linearity +
unital properties. r85 supplies the 1-Lipschitz bound

    ‖normalized_matrix_trace M‖ ≤ ‖M‖ (L² operator norm)

via the Hilbert-Schmidt route (Pabs's r85 direction, 2026-07-07):

  Step 1: Cauchy-Schwarz on the diagonal
    |trace M|² = |∑_i M_ii|²
               ≤ n · ∑_i |M_ii|²
               ≤ n · ∑_{i,j} |M_ij|²
               = n · ‖M‖²_HS

  Step 2: Hilbert-Schmidt ≤ √n · operator (via column bounds)
    ‖M‖²_HS = ∑_{i,j} |M_ij|²
            = ∑_j (∑_i |M_ij|²)
            = ∑_j ‖M *ᵥ e_j‖²
            ≤ ∑_j ‖M‖²_op · ‖e_j‖²
            = n · ‖M‖²_op

  Combined: |trace M|² ≤ n · n · ‖M‖²_op = n² · ‖M‖²_op
  Hence: |trace M / n| = |normalized_matrix_trace M| ≤ ‖M‖_op

This is the essential analytic prerequisite for extending the
substrate normalized trace to `TimelessFieldCompletion` via
`UniformSpace.Completion.extension` (r86 substrate work).

## What r85 establishes (kernel-only where tractable)

The main obstacle in the direct r84 proof was `whnf` heartbeat
timeouts under the L² operator norm typeclass resolution. r85
addresses this via:

  * Explicit `Matrix.l2OpNorm` reference to avoid scoped-notation
    typeclass cascade.
  * Elevated `maxHeartbeats` scoping on the heavy proofs.
  * Step-by-step lemma decomposition avoiding cumulative
    elaboration.

Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
axioms. Zero sorries.

Stage 2026-07-07 r85 — HS-route 1-Lipschitz bound for the substrate
normalized matrix trace.
-/

import PF.SubstrateUHFBoundedTrace
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace SubstrateUHFTraceLipschitz

open scoped Matrix.Norms.L2Operator
open scoped ComplexOrder
open SubstrateUHFBoundedTrace

/-! ## §1 — Hilbert-Schmidt norm squared, defined explicitly -/

/-- **The substrate Hilbert-Schmidt norm squared on
    `Matrix (Fin n) (Fin n) ℂ`**: `‖M‖²_HS := ∑_{i,j} |M_ij|²`. -/
noncomputable def substrate_HS_norm_sq {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, ‖M i j‖ ^ 2

/-- **r85.a: HS-norm-squared is non-negative**. Kernel-decidable. -/
theorem substrate_HS_norm_sq_nonneg {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) :
    0 ≤ substrate_HS_norm_sq M := by
  unfold substrate_HS_norm_sq
  exact Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-! ## §2 — Cauchy-Schwarz on the trace diagonal

The classical Cauchy-Schwarz inequality applied to `∑ 1 · M_ii`:

    |∑_i M_ii|² ≤ (∑_i 1²) · (∑_i |M_ii|²) = n · ∑_i |M_ii|²

with `∑_i |M_ii|² ≤ ‖M‖²_HS` since the diagonal is a subset of the
full index set. -/

/-- **r85.b: trace-squared bound via Cauchy-Schwarz**.

    `|trace M|² ≤ n · ‖M‖²_HS`. Follows from Cauchy-Schwarz on the
    diagonal, using that the diagonal-sum-of-squares is at most the
    full HS norm squared. -/
theorem substrate_trace_norm_sq_le_dim_HS_norm_sq {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) :
    ‖Matrix.trace M‖ ^ 2 ≤ n * substrate_HS_norm_sq M := by
  -- `trace M = ∑ i, M i i`
  have h_trace_eq : Matrix.trace M = ∑ i : Fin n, M i i := rfl
  -- Norm of sum ≤ sum of norms
  have h_norm_sum_le : ‖∑ i : Fin n, M i i‖ ≤ ∑ i : Fin n, ‖M i i‖ :=
    norm_sum_le _ _
  -- Square with Chebyshev/Cauchy-Schwarz: (∑ |M_ii|)² ≤ n · ∑ |M_ii|²
  have h_cauchy : (∑ i : Fin n, ‖M i i‖) ^ 2 ≤
      n * ∑ i : Fin n, ‖M i i‖ ^ 2 := by
    have hCheb :
        (∑ i ∈ (Finset.univ : Finset (Fin n)), ‖M i i‖) ^ 2 ≤
        (Finset.univ : Finset (Fin n)).card *
          ∑ i ∈ (Finset.univ : Finset (Fin n)), ‖M i i‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    simpa [Finset.card_univ, Fintype.card_fin] using hCheb
  -- Diagonal-sum-of-squares ≤ HS norm squared
  have h_diag_le_HS : ∑ i : Fin n, ‖M i i‖ ^ 2 ≤ substrate_HS_norm_sq M := by
    unfold substrate_HS_norm_sq
    -- ∑ i, ‖M i i‖² ≤ ∑ i, ∑ j, ‖M i j‖² since the diagonal term
    -- is one of the terms in the inner sum for each i
    refine Finset.sum_le_sum (fun i _ => ?_)
    -- ‖M i i‖² ≤ ∑ j, ‖M i j‖²
    exact Finset.single_le_sum
      (f := fun j => ‖M i j‖ ^ 2)
      (fun _ _ => sq_nonneg _)
      (Finset.mem_univ i)
  -- Chain
  have h_trace_norm_nn : (0:ℝ) ≤ ‖Matrix.trace M‖ := norm_nonneg _
  have h_sum_norm_nn : (0:ℝ) ≤ ∑ i : Fin n, ‖M i i‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  calc ‖Matrix.trace M‖ ^ 2
      = ‖∑ i : Fin n, M i i‖ ^ 2 := by rw [h_trace_eq]
    _ ≤ (∑ i : Fin n, ‖M i i‖) ^ 2 :=
        pow_le_pow_left₀ h_trace_norm_nn h_norm_sum_le 2
    _ ≤ n * ∑ i : Fin n, ‖M i i‖ ^ 2 := h_cauchy
    _ ≤ n * substrate_HS_norm_sq M := by
        exact mul_le_mul_of_nonneg_left h_diag_le_HS (by exact_mod_cast Nat.zero_le n)

/-! ## §3 — Substrate HS-norm-squared statement (bound to op norm deferred)

The classical bound `‖M‖²_HS ≤ n · ‖M‖²_op` is proved via
`‖M *ᵥ e_j‖² ≤ ‖M‖²_op · ‖e_j‖² = ‖M‖²_op` for each column e_j,
summed to `‖M‖²_HS = ∑_j ‖M *ᵥ e_j‖² ≤ n · ‖M‖²_op`.

This step requires the same L² operator norm elaboration weight that
caused `whnf` heartbeat timeouts in r84's direct entry-norm approach.
For r85, we announce this bound as substrate content at Prop level;
the kernel-verified proof is r85b (planned follow-up) substrate work
with dedicated elaboration attention or via specific mathlib API
navigation. -/

/-- **Substrate HS-vs-Op norm bound (Prop level for r85)**.

    The Hilbert-Schmidt norm squared is bounded by n times the L²
    operator norm squared:

        substrate_HS_norm_sq M ≤ n · ‖M‖²  (under L² op norm)

    This is the classical finite-dimensional bound following from
    `‖M *ᵥ e_j‖² ≤ ‖M‖²` for each standard basis vector e_j and
    summing over j. Announced as substrate content pending
    kernel-verified proof (r85b substrate work). -/
def SubstrateHSNormBoundConjecture : Prop :=
  ∀ {n : ℕ} [NeZero n] (M : Matrix (Fin n) (Fin n) ℂ),
    substrate_HS_norm_sq M ≤ n * ‖M‖ ^ 2

/-! ## §4 — Substrate 1-Lipschitz statement of the normalized trace

Given the r85.b Cauchy-Schwarz bound + the SubstrateHSNormBoundConjecture,
the 1-Lipschitz bound `‖normalized_matrix_trace M‖ ≤ ‖M‖` follows by
combining:

    |trace M|² ≤ n · substrate_HS_norm_sq M   (r85.b)
              ≤ n · n · ‖M‖² = n² · ‖M‖²      (via SubstrateHSNormBoundConjecture)

    Therefore: |trace M| ≤ n · ‖M‖
    Hence: |trace M / n| ≤ ‖M‖. -/

/-- **Substrate 1-Lipschitz bound conjecture (Prop level)**.

    The substrate content of the r84 residual bound: the normalized
    matrix trace is 1-Lipschitz under the L² operator norm. -/
def SubstrateNormalizedTrace1LipschitzConjecture : Prop :=
  ∀ {n : ℕ} [NeZero n] (M : Matrix (Fin n) (Fin n) ℂ),
    ‖normalized_matrix_trace M‖ ≤ ‖M‖

/-- **r85: 1-Lipschitz conditional on the HS-vs-op bound**.

    Given the substrate HS-vs-op norm bound (announced as
    `SubstrateHSNormBoundConjecture`), the substrate normalized
    matrix trace is 1-Lipschitz under the L² operator norm. -/
theorem substrate_normalized_trace_1_lipschitz_of_HS_bound
    (h_HS : SubstrateHSNormBoundConjecture) :
    SubstrateNormalizedTrace1LipschitzConjecture := by
  intro n _ M
  show ‖normalized_matrix_trace M‖ ≤ ‖M‖
  -- normalized_matrix_trace M = trace M / n
  show ‖(Matrix.trace M) / (n : ℂ)‖ ≤ ‖M‖
  rw [norm_div, Complex.norm_natCast]
  have hn_pos : (0 : ℝ) < n := by
    have : (n : ℕ) ≠ 0 := NeZero.ne n
    exact_mod_cast Nat.pos_of_ne_zero this
  rw [div_le_iff₀ hn_pos]
  -- Need: ‖trace M‖ ≤ ‖M‖ * n
  -- Via ‖trace M‖² ≤ n · substrate_HS_norm_sq M ≤ n · n · ‖M‖² = n²‖M‖²
  have h_trace_sq :
      ‖Matrix.trace M‖ ^ 2 ≤ n * substrate_HS_norm_sq M :=
    substrate_trace_norm_sq_le_dim_HS_norm_sq M
  have h_HS_bound : substrate_HS_norm_sq M ≤ n * ‖M‖ ^ 2 := h_HS M
  have h_n_nn : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
  have h_M_nn : (0 : ℝ) ≤ ‖M‖ := norm_nonneg _
  have h_trace_nn : (0 : ℝ) ≤ ‖Matrix.trace M‖ := norm_nonneg _
  have h_combined :
      ‖Matrix.trace M‖ ^ 2 ≤ (n * ‖M‖) ^ 2 := by
    calc ‖Matrix.trace M‖ ^ 2
        ≤ n * substrate_HS_norm_sq M := h_trace_sq
      _ ≤ n * (n * ‖M‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h_HS_bound h_n_nn
      _ = (n * ‖M‖) ^ 2 := by ring
  -- Take sqrt
  have h_nM_nn : (0 : ℝ) ≤ n * ‖M‖ := mul_nonneg h_n_nn h_M_nn
  nlinarith [sq_nonneg (‖Matrix.trace M‖ - n * ‖M‖), h_trace_nn, h_nM_nn,
             h_combined]

/-! ## §5 — Substrate discharge + capstone -/

/-- **SubstrateHSAndLipschitzConjecture (Prop level)**.

    Combined substrate content: HS-vs-op bound AND 1-Lipschitz bound
    of the normalized trace. -/
def SubstrateHSAndLipschitzConjecture : Prop :=
  SubstrateHSNormBoundConjecture ∧ SubstrateNormalizedTrace1LipschitzConjecture

/-- **r85 substrate discharge (conditional)**.

    The HS-vs-op bound implies the 1-Lipschitz bound of the
    normalized trace, and the combined conjecture holds if HS holds.
    This is a substrate reduction: the analytic core is the HS-vs-op
    bound; once landed (via elaboration attention in r85b or via
    a mathlib API upgrade), the 1-Lipschitz bound is automatic. -/
theorem substrate_HS_implies_1_lipschitz :
    SubstrateHSNormBoundConjecture →
      SubstrateNormalizedTrace1LipschitzConjecture :=
  substrate_normalized_trace_1_lipschitz_of_HS_bound

/-! ## §6 — r85 substrate HS-route Lipschitz capstone -/

/-- **★★★ r85 SUBSTRATE HS-ROUTE LIPSCHITZ CAPSTONE ★★★**

    Bundles the r85 substrate content:

      (W1) `substrate_HS_norm_sq` — the explicit HS norm squared.
      (W2) `substrate_HS_norm_sq_nonneg` — non-negativity.
      (W3) `substrate_trace_norm_sq_le_dim_HS_norm_sq` —
           **the Cauchy-Schwarz trace-vs-HS bound**:
           `|trace M|² ≤ n · substrate_HS_norm_sq M`, kernel-proved.
      (W4) `SubstrateHSNormBoundConjecture` — Prop-level HS-vs-op bound
           `substrate_HS_norm_sq M ≤ n · ‖M‖²`, r85b substrate work.
      (W5) `SubstrateNormalizedTrace1LipschitzConjecture` — the target
           1-Lipschitz bound `‖normalized_matrix_trace M‖ ≤ ‖M‖`.
      (W6) `substrate_HS_implies_1_lipschitz` — the substrate reduction
           (kernel-proved implication).

    Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
    axioms. Zero sorries.

    Substrate significance: r85 reduces the 1-Lipschitz bound problem
    to the HS-vs-op norm bound, kernel-verifying the Cauchy-Schwarz
    trace-vs-HS half of the argument. The HS-vs-op half is separated
    as a named substrate residual (SubstrateHSNormBoundConjecture),
    to be attacked in r85b substrate work with dedicated
    elaboration attention. r86 will register the completion trace
    extension using the eventually-landed 1-Lipschitz property. -/
theorem r85_substrate_HS_route_Lipschitz_capstone :
    (∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ), 0 ≤ substrate_HS_norm_sq M) ∧
    (∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ),
      ‖Matrix.trace M‖ ^ 2 ≤ n * substrate_HS_norm_sq M) ∧
    (SubstrateHSNormBoundConjecture →
       SubstrateNormalizedTrace1LipschitzConjecture) :=
  ⟨fun {_} M => substrate_HS_norm_sq_nonneg M,
   fun {_} M => substrate_trace_norm_sq_le_dim_HS_norm_sq M,
   substrate_HS_implies_1_lipschitz⟩

/-! ## §7 — r85b: kernel-verified HS-vs-op norm bound

r85b closes the substrate residual left open by r85: the classical
column-by-column proof of the Hilbert-Schmidt vs L²-operator-norm
bound `‖M‖²_HS ≤ n · ‖M‖²_op`. The argument uses the mathlib
`Matrix.l2_opNorm_mulVec` bound applied to each standard basis vector
`EuclideanSpace.single j 1`:

    ‖M *ᵥ e_j‖²_l2 = ∑_i ‖M i j‖²
                   ≤ (‖M‖ · ‖e_j‖)²  (via l2_opNorm_mulVec)
                   = ‖M‖²             (since ‖e_j‖ = 1)

Summing over `j : Fin n` gives:

    ‖M‖²_HS = ∑_{i,j} ‖M i j‖²
            = ∑_j ∑_i ‖M i j‖²
            ≤ ∑_j ‖M‖² = n · ‖M‖²

which discharges `SubstrateHSNormBoundConjecture` and, together with
the r85 Cauchy-Schwarz half + the r85 conditional implication,
delivers the kernel-verified 1-Lipschitz bound. -/

set_option maxHeartbeats 800000 in
/-- **r85b.a: column norm-squared is bounded by the operator norm squared**.

    For each column index `j : Fin n`, `∑_i ‖M i j‖² ≤ ‖M‖²` under the
    L² operator norm. Kernel-proved via `Matrix.l2_opNorm_mulVec`
    applied to `EuclideanSpace.single j 1`. -/
theorem substrate_column_norm_sq_le_op_norm_sq {n : ℕ} [NeZero n]
    (M : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    ∑ i : Fin n, ‖M i j‖ ^ 2 ≤ ‖M‖ ^ 2 := by
  set e_j : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j (1 : ℂ) with h_ej_def
  have h_ej_norm : ‖e_j‖ = 1 := by
    simp [h_ej_def, EuclideanSpace.norm_single]
  set v : EuclideanSpace ℂ (Fin n) :=
    (EuclideanSpace.equiv (Fin n) ℂ).symm (Matrix.mulVec M e_j) with h_v_def
  -- Mathlib bound: ‖v‖ ≤ ‖M‖ * ‖e_j‖ = ‖M‖.
  have h_bound : ‖v‖ ≤ ‖M‖ := by
    have h := Matrix.l2_opNorm_mulVec M e_j
    rw [h_ej_norm, mul_one] at h
    exact h
  -- Entrywise: v i = M i j.
  have h_v_apply : ∀ i : Fin n, v i = M i j := by
    intro i
    have h_ej_apply :
        ∀ k : Fin n, (e_j : Fin n → ℂ) k = (if k = j then (1 : ℂ) else 0) := by
      intro k; rw [h_ej_def]; simp [EuclideanSpace.single_apply]
    show Matrix.mulVec M e_j i = M i j
    show ∑ k, M i k * (e_j : Fin n → ℂ) k = M i j
    calc ∑ k, M i k * (e_j : Fin n → ℂ) k
        = ∑ k, (if k = j then M i k * 1 else M i k * 0) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [h_ej_apply]
          split_ifs <;> rfl
      _ = ∑ k, (if k = j then M i k else 0) := by
          apply Finset.sum_congr rfl
          intro k _
          split_ifs
          · rw [mul_one]
          · rw [mul_zero]
      _ = M i j := by
          rw [Finset.sum_ite_eq' Finset.univ j (fun k => M i k)]
          simp
  -- Norm-sq of v = ∑_i ‖v i‖² = ∑_i ‖M i j‖².
  have h_norm_sq :
      ‖v‖ ^ 2 = ∑ i : Fin n, ‖M i j‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    rw [h_v_apply i]
  -- Square the bound and conclude.
  have h_bound_sq : ‖v‖ ^ 2 ≤ ‖M‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h_bound 2
  linarith [h_norm_sq ▸ h_bound_sq]

/-- **★★★ r85b MAIN: substrate HS-vs-op norm bound, kernel-proved ★★★**

    `substrate_HS_norm_sq M ≤ n · ‖M‖²` under the L² operator norm.
    Follows from `substrate_column_norm_sq_le_op_norm_sq` summed over
    columns. Kernel-only [propext, Classical.choice, Quot.sound]. -/
theorem substrate_HS_norm_sq_bound {n : ℕ} [NeZero n]
    (M : Matrix (Fin n) (Fin n) ℂ) :
    substrate_HS_norm_sq M ≤ n * ‖M‖ ^ 2 := by
  unfold substrate_HS_norm_sq
  -- ∑_i ∑_j ‖M i j‖² = ∑_j ∑_i ‖M i j‖² ≤ ∑_j ‖M‖² = n · ‖M‖²
  calc (∑ i : Fin n, ∑ j : Fin n, ‖M i j‖ ^ 2)
      = ∑ j : Fin n, ∑ i : Fin n, ‖M i j‖ ^ 2 := by rw [Finset.sum_comm]
    _ ≤ ∑ _ : Fin n, ‖M‖ ^ 2 :=
        Finset.sum_le_sum (fun j _ => substrate_column_norm_sq_le_op_norm_sq M j)
    _ = n * ‖M‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **r85b: substrate discharge of SubstrateHSNormBoundConjecture**.

    The r85 Prop-level residual is now kernel-proved. -/
theorem substrate_HS_bound_holds : SubstrateHSNormBoundConjecture := by
  intro n _ M
  exact substrate_HS_norm_sq_bound M

/-- **★★★ r85b: KERNEL-PROVED 1-LIPSCHITZ BOUND OF THE NORMALIZED TRACE ★★★**

    `‖normalized_matrix_trace M‖ ≤ ‖M‖` under the L² operator norm.
    Combines the r85 Cauchy-Schwarz half + the r85b HS-vs-op bound +
    the r85 conditional implication into a fully unconditional
    substrate 1-Lipschitz bound.

    This is the essential analytic prerequisite for extending the
    substrate normalized trace to `TimelessFieldCompletion` via
    `UniformSpace.Completion.extension` (r86 substrate target). -/
theorem substrate_normalized_trace_bound {n : ℕ} [NeZero n]
    (M : Matrix (Fin n) (Fin n) ℂ) :
    ‖normalized_matrix_trace M‖ ≤ ‖M‖ :=
  substrate_HS_implies_1_lipschitz substrate_HS_bound_holds M

/-- **r85b: substrate discharge of SubstrateNormalizedTrace1LipschitzConjecture**. -/
theorem substrate_1_lipschitz_holds : SubstrateNormalizedTrace1LipschitzConjecture := by
  intro n _ M
  exact substrate_normalized_trace_bound M

/-- **r85b: combined substrate discharge of SubstrateHSAndLipschitzConjecture**. -/
theorem substrate_HS_and_1_lipschitz_holds : SubstrateHSAndLipschitzConjecture :=
  ⟨substrate_HS_bound_holds, substrate_1_lipschitz_holds⟩

/-! ## §8 — r85b substrate full Lipschitz capstone -/

/-- **★★★ r85b SUBSTRATE FULL 1-LIPSCHITZ CAPSTONE ★★★**

    Bundles the r85b closure of the r85 substrate residual:

      (X1) `substrate_column_norm_sq_le_op_norm_sq` — column-by-column
           bound `∑_i ‖M i j‖² ≤ ‖M‖²` via `Matrix.l2_opNorm_mulVec`
           on `EuclideanSpace.single j 1`.
      (X2) `substrate_HS_norm_sq_bound` — **the HS-vs-op norm bound**
           `substrate_HS_norm_sq M ≤ n · ‖M‖²`, kernel-proved.
      (X3) `substrate_HS_bound_holds : SubstrateHSNormBoundConjecture`.
      (X4) **`substrate_normalized_trace_bound`** —
           **THE 1-LIPSCHITZ BOUND**
           `‖normalized_matrix_trace M‖ ≤ ‖M‖`, kernel-proved (unconditional).
      (X5) `substrate_1_lipschitz_holds : SubstrateNormalizedTrace1LipschitzConjecture`.
      (X6) `substrate_HS_and_1_lipschitz_holds : SubstrateHSAndLipschitzConjecture`.

    Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
    axioms. Zero sorries.

    Substrate significance: r85b closes the r85 residual by supplying
    the classical column-by-column proof of the HS-vs-op norm bound
    via `Matrix.l2_opNorm_mulVec` on standard basis vectors. Together
    with the r85 Cauchy-Schwarz trace-vs-HS half + r85 conditional
    implication, this delivers the FULLY UNCONDITIONAL 1-Lipschitz
    bound of the substrate normalized matrix trace — the essential
    analytic prerequisite for extending the trace to
    `TimelessFieldCompletion` via `UniformSpace.Completion.extension`
    (r86 substrate target). -/
theorem r85b_substrate_full_lipschitz_capstone :
    (∀ {n : ℕ} [NeZero n] (M : Matrix (Fin n) (Fin n) ℂ) (j : Fin n),
      ∑ i : Fin n, ‖M i j‖ ^ 2 ≤ ‖M‖ ^ 2) ∧
    (∀ {n : ℕ} [NeZero n] (M : Matrix (Fin n) (Fin n) ℂ),
      substrate_HS_norm_sq M ≤ n * ‖M‖ ^ 2) ∧
    SubstrateHSNormBoundConjecture ∧
    (∀ {n : ℕ} [NeZero n] (M : Matrix (Fin n) (Fin n) ℂ),
      ‖normalized_matrix_trace M‖ ≤ ‖M‖) ∧
    SubstrateNormalizedTrace1LipschitzConjecture ∧
    SubstrateHSAndLipschitzConjecture :=
  ⟨fun {_} _ M j => substrate_column_norm_sq_le_op_norm_sq M j,
   fun {_} _ M => substrate_HS_norm_sq_bound M,
   substrate_HS_bound_holds,
   fun {_} _ M => substrate_normalized_trace_bound M,
   substrate_1_lipschitz_holds,
   substrate_HS_and_1_lipschitz_holds⟩

end SubstrateUHFTraceLipschitz
end PrincipiaTractalis
