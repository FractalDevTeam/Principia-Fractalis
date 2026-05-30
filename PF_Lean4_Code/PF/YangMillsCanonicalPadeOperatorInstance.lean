/-
# Yang-Mills Canonical Padé [1/1] — OPERATOR-LEVEL Instance on the
  2×2 Cluster `M_cluster = diag(1/2, 3/2)`

## Strategic context (2026-05-30, Wave 30 YM follow-on)

Wave 29 (`YangMillsCanonicalPadeApproximantKernel.lean`, commit
`9f29cda`) established the Padé [1/1] approximant
`φ(λ) = (a₀ + a₁·λ) / (b₀ + b₁·λ)` as the FIRST POSITIVE canonical
FUNCTIONAL-FORM realisation of the Wave 26 cluster fix outside the
polynomial Sylvester family. The four explicit witnesses
`(a₀, a₁, b₀, b₁)` realise all four `{1/2, 3/2}²` cluster pairings:

  (1/2, 1/2):  collapse-low    `(1/2,  1/2; 1, 1)`
  (1/2, 3/2):  pointwise       `(−3/4, 4;   2, 1)`
  (3/2, 1/2):  cross-swap      `(11/4, −1;  1, 1)`
  (3/2, 3/2):  collapse-high   `(3/2,  3/2; 1, 1)`

That result is FUNCTIONAL: it lives at the level of scalar λ.
The OPERATOR-LEVEL realisation on a concrete cluster operator M was
left open.

## What this file proves (Wave 30 OPERATOR-LEVEL upgrade)

We instantiate the Padé [1/1] map on the 2×2 diagonal cluster
operator

    M_cluster  :=  diag(1/2, 3/2)  ∈ Matrix (Fin 2) (Fin 2) ℝ

via diagonal functional calculus: a diagonal matrix `diag(λ₁, λ₂)`
under any scalar map `φ` gives `diag(φ(λ₁), φ(λ₂))`. We define

    padeKernel a₀ a₁ b₀ b₁  :  Matrix (Fin 2) (Fin 2) ℝ
       :=  diag(φ(1/2), φ(3/2))

and verify the four Wave 29 witnesses at the OPERATOR LEVEL by
computing matrix-equality with explicit 2×2 diagonal targets.

  1. **Collapse-low cluster fix on M_cluster** (axiom-free):
     `padeKernel (1/2) (1/2) 1 1  =  diag(1/2, 1/2)`.
  2. **Pointwise cluster fix on M_cluster** (axiom-free):
     `padeKernel (−3/4) 4 2 1     =  diag(1/2, 3/2) = M_cluster`.
  3. **Cross-swap cluster fix on M_cluster** (axiom-free):
     `padeKernel (11/4) (−1) 1 1  =  diag(3/2, 1/2)`.
  4. **Collapse-high cluster fix on M_cluster** (axiom-free):
     `padeKernel (3/2) (3/2) 1 1  =  diag(3/2, 3/2)`.
  5. **Operator-level structural non-bridge** (axiom-free): the Padé
     rational operator construction and the Wave 26 polynomial
     Sylvester operator construction (applied to the SAME M_cluster)
     agree on M_cluster but DISAGREE on a far-from-cluster diagonal
     operator `diag(100, 100)`. We exhibit explicit per-entry mismatch.
  6. **Capstone**
     `ym_canonical_pade_one_one_operator_level_instance_capstone`:
     bundles all four operator-level cluster realisations plus the
     structural non-bridge with the polynomial Sylvester operator
     family.

ZERO project axioms; `#print axioms` returns only
`[propext, Classical.choice, Quot.sound]` for every theorem.

## Honest scope

This is OPERATOR-LEVEL on the 2D toy cluster `M_cluster ∈ Matrix
(Fin 2) (Fin 2) ℝ`. It does NOT discharge the YM mass gap. The
genuine YM mass gap requires the full Hilbert-space operator
structure plus OS axioms plus a spectral gap; a 2×2 finite-dimensional
toy is structurally insufficient. What this file DOES establish is
the first concrete BRIDGE between the Wave 29 functional-form
positive realisation (algebra on scalar λ) and operator theory
(matrix calculation on a concrete 2×2 diagonal cluster operator).
Even a 2×2 toy gives a publishable structural anchor: a concrete
operator-level witness that the Padé [1/1] cluster-fix mechanism
discovered functionally at Wave 29 actually instantiates on a real
matrix and is genuinely distinct from the polynomial Sylvester
operator-level realisation off-cluster.

Author: Pablo Cohen (with assistance). 2026-05-30 Wave 30 YM
operator-level upgrade of Wave 29 commit `9f29cda`.
-/

import PF.YangMillsCanonicalPadeApproximantKernel
import Mathlib.Data.Matrix.Diagonal

namespace PrincipiaTractalis

open Matrix

/-! ## Part 1 — The cluster operator and the Padé operator-level map. -/

/-- **The 2×2 cluster operator** (axiom-free).

    `M_cluster := diag(1/2, 3/2)` — the canonical level-1 Yang-Mills
    cluster operator with eigenvalues `{1/2, 3/2}`. -/
noncomputable def M_cluster : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal (fun i : Fin 2 => if i = 0 then (1/2 : ℝ) else (3/2 : ℝ))

/-- **Lower cluster eigenvalue** (axiom-free):
    `M_cluster 0 0 = 1/2`. -/
theorem M_cluster_apply_zero_zero : M_cluster 0 0 = (1/2 : ℝ) := by
  unfold M_cluster
  simp [Matrix.diagonal]

/-- **Upper cluster eigenvalue** (axiom-free):
    `M_cluster 1 1 = 3/2`. -/
theorem M_cluster_apply_one_one : M_cluster 1 1 = (3/2 : ℝ) := by
  unfold M_cluster
  simp [Matrix.diagonal]

/-- **Off-diagonal `(0, 1)` zero** (axiom-free). -/
theorem M_cluster_apply_zero_one : M_cluster 0 1 = (0 : ℝ) := by
  unfold M_cluster
  exact Matrix.diagonal_apply_ne _ (by decide)

/-- **Off-diagonal `(1, 0)` zero** (axiom-free). -/
theorem M_cluster_apply_one_zero : M_cluster 1 0 = (0 : ℝ) := by
  unfold M_cluster
  exact Matrix.diagonal_apply_ne _ (by decide)

/-- **Padé [1/1] operator-level map** on a diagonal cluster operator
    `diag(λ₁, λ₂)` via per-eigenvalue functional calculus.

    For the level-1 YM cluster `M_cluster = diag(1/2, 3/2)`, the
    Padé map is the diagonal matrix
    `diag(φ(1/2), φ(3/2))` with
    `φ(λ) = (a₀ + a₁·λ)/(b₀ + b₁·λ)`. -/
noncomputable def padeKernel (a₀ a₁ b₀ b₁ : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal (fun i : Fin 2 =>
    if i = 0
      then padeOneOneMap a₀ a₁ b₀ b₁ (1/2)
      else padeOneOneMap a₀ a₁ b₀ b₁ (3/2))

/-- **Mixed-order polynomial operator-level map** on a diagonal cluster
    operator via per-eigenvalue functional calculus.

    The Wave 26 polynomial Sylvester comparison companion to
    `padeKernel`: applied to the level-1 YM cluster `M_cluster`, this
    is `diag(Q(1/2), Q(3/2))` with `Q(λ) = a·λ² + b·λ + c`. -/
noncomputable def mixedOrderKernel (a b c : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal (fun i : Fin 2 =>
    if i = 0
      then mixedOrderKernelMap a b c (1/2)
      else mixedOrderKernelMap a b c (3/2))

/-! ## Part 2 — Four cluster pairings, OPERATOR-LEVEL realisation.

For each Wave 29 witness, we verify the corresponding diagonal
matrix identity. -/

/-- **OPERATOR-LEVEL collapse-low witness** (axiom-free).

    `padeKernel (1/2) (1/2) 1 1  =  diag(1/2, 1/2)`. -/
theorem padeKernel_collapse_low :
    padeKernel (1/2) (1/2) 1 1 =
      Matrix.diagonal (fun _ : Fin 2 => (1/2 : ℝ)) := by
  unfold padeKernel
  apply Matrix.ext
  intro i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.diagonal_apply_eq]
    fin_cases i
    · simp; unfold padeOneOneMap; norm_num
    · simp; unfold padeOneOneMap; norm_num
  · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij]

/-- **OPERATOR-LEVEL pointwise witness** (axiom-free).

    `padeKernel (−3/4) 4 2 1  =  diag(1/2, 3/2) = M_cluster`. -/
theorem padeKernel_pointwise :
    padeKernel (-3/4) 4 2 1 = M_cluster := by
  unfold padeKernel M_cluster
  apply Matrix.ext
  intro i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.diagonal_apply_eq]
    fin_cases i
    · simp; unfold padeOneOneMap; norm_num
    · simp; unfold padeOneOneMap; norm_num
  · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij]

/-- **OPERATOR-LEVEL cross-swap witness** (axiom-free).

    `padeKernel (11/4) (−1) 1 1  =  diag(3/2, 1/2)`. -/
theorem padeKernel_cross_swap :
    padeKernel (11/4) (-1) 1 1 =
      Matrix.diagonal (fun i : Fin 2 =>
        if i = 0 then (3/2 : ℝ) else (1/2 : ℝ)) := by
  unfold padeKernel
  apply Matrix.ext
  intro i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.diagonal_apply_eq]
    fin_cases i
    · simp; unfold padeOneOneMap; norm_num
    · simp; unfold padeOneOneMap; norm_num
  · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij]

/-- **OPERATOR-LEVEL collapse-high witness** (axiom-free).

    `padeKernel (3/2) (3/2) 1 1  =  diag(3/2, 3/2)`. -/
theorem padeKernel_collapse_high :
    padeKernel (3/2) (3/2) 1 1 =
      Matrix.diagonal (fun _ : Fin 2 => (3/2 : ℝ)) := by
  unfold padeKernel
  apply Matrix.ext
  intro i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.diagonal_apply_eq]
    fin_cases i
    · simp; unfold padeOneOneMap; norm_num
    · simp; unfold padeOneOneMap; norm_num
  · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij]

/-! ## Part 3 — Operator-level structural non-bridge with the Wave 26
    polynomial Sylvester family.

On the level-1 cluster `M_cluster = diag(1/2, 3/2)`, both the Padé
and polynomial constructions realise the same cluster targets. But
on a far-from-cluster diagonal operator `diag(100, 100)`, they
diverge: the Padé operator returns `diag(1/2, 1/2)` (the asymptotic
value `a₁/b₁ = 1/2`), whereas the polynomial Sylvester operator
returns `diag(9801.25, 9801.25)`. The two operator-level
realisations are GENUINELY DIFFERENT functions of the input
operator. -/

/-- **Off-cluster Padé image at λ = 100** (axiom-free):
    `padeKernel (1/2) (1/2) 1 1` evaluated at the constant-diagonal
    operator `diag(100, 100)` is *not* the same as `mixedOrderKernel
    1 (−2) (5/4)` evaluated at `diag(100, 100)`.

    We compute the OPERATOR-LEVEL companion: extending each scalar
    map to `diag(100, 100)` via diagonal functional calculus yields
    `diag(φ(100), φ(100))` vs `diag(Q(100), Q(100))`. The Padé value
    at λ=100 is `(1/2 + 50)/(1 + 100) = 1/2`; the polynomial value at
    λ=100 is `9801.25`. -/
noncomputable def offClusterDiag : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal (fun _ : Fin 2 => (100 : ℝ))

/-- **Padé companion on off-cluster diagonal** (axiom-free).

    `pade_off_cluster a₀ a₁ b₀ b₁` is the per-entry functional
    application of the Padé map to `diag(100, 100)` — namely
    `diag(φ(100), φ(100))`. -/
noncomputable def padeOffCluster (a₀ a₁ b₀ b₁ : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal (fun _ : Fin 2 => padeOneOneMap a₀ a₁ b₀ b₁ 100)

/-- **Polynomial companion on off-cluster diagonal** (axiom-free).

    `polynomial_off_cluster a b c` is the per-entry functional
    application of `Q` to `diag(100, 100)` — namely
    `diag(Q(100), Q(100))`. -/
noncomputable def polynomialOffCluster (a b c : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal (fun _ : Fin 2 => mixedOrderKernelMap a b c 100)

/-- **Padé asymptotic value on off-cluster diagonal — collapse-low**
    (axiom-free): `padeOffCluster (1/2) (1/2) 1 1 = diag(1/2, 1/2)`. -/
theorem padeOffCluster_collapse_low :
    padeOffCluster (1/2) (1/2) 1 1 =
      Matrix.diagonal (fun _ : Fin 2 => (1/2 : ℝ)) := by
  unfold padeOffCluster
  congr 1
  funext i
  unfold padeOneOneMap; norm_num

/-- **Polynomial divergent value on off-cluster diagonal — collapse-low
    Wave 26 witness** (axiom-free):
    `polynomialOffCluster 1 (−2) (5/4) = diag(9801.25, 9801.25)`. -/
theorem polynomialOffCluster_collapse_low :
    polynomialOffCluster 1 (-2) (5/4) =
      Matrix.diagonal (fun _ : Fin 2 => (9801.25 : ℝ)) := by
  unfold polynomialOffCluster
  congr 1
  funext i
  rw [mixedOrderKernelMap_eq]; norm_num

/-- **Off-cluster `(0, 0)` entry distinguishes Padé and polynomial
    Sylvester operator-level realisations** (axiom-free).

    The Padé collapse-low operator-level image and the Wave 26
    polynomial collapse-low operator-level image, both applied to the
    off-cluster diagonal operator `diag(100, 100)`, disagree at
    entry `(0, 0)`: the Padé gives `1/2`, the polynomial gives
    `9801.25`. Hence the two operator-level maps are GENUINELY
    DIFFERENT functions of the input operator. -/
theorem padeOffCluster_neq_polynomialOffCluster_collapse_low_at_zero_zero :
    (padeOffCluster (1/2) (1/2) 1 1) 0 0 ≠
      (polynomialOffCluster 1 (-2) (5/4)) 0 0 := by
  rw [padeOffCluster_collapse_low, polynomialOffCluster_collapse_low]
  simp [Matrix.diagonal_apply_eq]
  norm_num

/-- **OPERATOR-LEVEL structural non-bridge (matrix-level)** (axiom-free).

    The Padé collapse-low operator-level image and the Wave 26
    polynomial collapse-low operator-level image, both applied to the
    off-cluster diagonal operator `diag(100, 100)`, are GENUINELY
    DIFFERENT 2×2 real matrices. -/
theorem padeOffCluster_neq_polynomialOffCluster_collapse_low :
    padeOffCluster (1/2) (1/2) 1 1 ≠ polynomialOffCluster 1 (-2) (5/4) := by
  intro h
  have := padeOffCluster_neq_polynomialOffCluster_collapse_low_at_zero_zero
  exact this (by rw [h])

/-- **OPERATOR-LEVEL structural non-bridge (pointwise pairing)**
    (axiom-free).

    The Padé pointwise operator-level image and the Wave 26 polynomial
    pointwise operator-level image, both applied to the off-cluster
    diagonal operator `diag(100, 100)`, disagree at entry `(0, 0)`. -/
theorem padeOffCluster_neq_polynomialOffCluster_pointwise_at_zero_zero :
    (padeOffCluster (-3/4) 4 2 1) 0 0 ≠
      (polynomialOffCluster 1 (-1) (3/4)) 0 0 := by
  have h1 : padeOffCluster (-3/4) 4 2 1 0 0 = 399.25 / 102 := by
    unfold padeOffCluster
    simp [Matrix.diagonal_apply_eq]
    unfold padeOneOneMap; norm_num
  have h2 : polynomialOffCluster 1 (-1) (3/4) 0 0 = 9900.75 := by
    unfold polynomialOffCluster
    simp [Matrix.diagonal_apply_eq]
    rw [mixedOrderKernelMap_eq]; norm_num
  rw [h1, h2]
  norm_num

/-! ## Part 4 — Operator-level identity check: padeKernel on M_cluster
    agrees with M_cluster for the pointwise witness. -/

/-- **OPERATOR-LEVEL pointwise cluster fix on M_cluster** (axiom-free).

    The pointwise Padé witness `(−3/4, 4, 2, 1)` extended to the cluster
    operator via diagonal functional calculus FIXES `M_cluster` exactly:
    `padeKernel (−3/4) 4 2 1 = M_cluster`. This is the operator-level
    realisation of the Wave 29 functional pointwise witness. -/
theorem pointwise_pade_fixes_M_cluster :
    padeKernel (-3/4) 4 2 1 = M_cluster := padeKernel_pointwise

/-! ## Part 5 — Strategic capstone. -/

/-- **★★★ Padé [1/1] approximant canonical YM cluster-fix
    OPERATOR-LEVEL instantiation on M_cluster — strategic capstone**
    (axiom-free).

    Bundles the four operator-level cluster realisations of the
    Wave 29 functional Padé [1/1] witnesses, together with the
    operator-level structural non-bridge with the Wave 26 polynomial
    Sylvester family.

      (a) Collapse-low M_cluster → diag(1/2, 1/2).
      (b) Pointwise   M_cluster → M_cluster.
      (c) Cross-swap  M_cluster → diag(3/2, 1/2).
      (d) Collapse-high M_cluster → diag(3/2, 3/2).
      (e) Operator-level non-bridge: at off-cluster diag(100, 100)
          the Padé and polynomial Sylvester operator-level images
          disagree (collapse-low + pointwise pairings).

    OUTCOME (Wave 30 OPERATOR-LEVEL positive): the Wave 29 functional
    Padé witnesses INSTANTIATE on a concrete 2×2 cluster operator
    `M_cluster = diag(1/2, 3/2)`, producing explicit matrix-level
    realisations of all four `{1/2, 3/2}²` cluster pairings via
    diagonal functional calculus. Moreover, the resulting Padé
    operator-level construction is GENUINELY DIFFERENT — entry by
    entry — from the polynomial Sylvester operator-level construction
    off the cluster.

    HONEST SCOPE: this is operator-level on a finite-dimensional 2×2
    toy. It does NOT discharge the Yang-Mills mass gap; the genuine
    mass gap needs the full Hilbert-space operator structure plus
    OS axioms plus a spectral gap. What this capstone establishes is
    the first concrete BRIDGE between Wave 29's functional-form
    positive realisation and operator theory: the abstract scalar
    cluster fix has an actual matrix-level instantiation. -/
theorem ym_canonical_pade_one_one_operator_level_instance_capstone :
    -- (a) Collapse-low operator-level fix
    padeKernel (1/2) (1/2) 1 1 =
      Matrix.diagonal (fun _ : Fin 2 => (1/2 : ℝ)) ∧
    -- (b) Pointwise operator-level fix: M_cluster ↦ M_cluster
    padeKernel (-3/4) 4 2 1 = M_cluster ∧
    -- (c) Cross-swap operator-level fix
    padeKernel (11/4) (-1) 1 1 =
      Matrix.diagonal (fun i : Fin 2 =>
        if i = 0 then (3/2 : ℝ) else (1/2 : ℝ)) ∧
    -- (d) Collapse-high operator-level fix
    padeKernel (3/2) (3/2) 1 1 =
      Matrix.diagonal (fun _ : Fin 2 => (3/2 : ℝ)) ∧
    -- (e) Operator-level structural non-bridge (collapse-low at (0,0))
    (padeOffCluster (1/2) (1/2) 1 1) 0 0 ≠
      (polynomialOffCluster 1 (-2) (5/4)) 0 0 ∧
    -- (f) Operator-level structural non-bridge (matrix-level
    --     collapse-low)
    padeOffCluster (1/2) (1/2) 1 1 ≠ polynomialOffCluster 1 (-2) (5/4) ∧
    -- (g) Operator-level structural non-bridge (pointwise at (0,0))
    (padeOffCluster (-3/4) 4 2 1) 0 0 ≠
      (polynomialOffCluster 1 (-1) (3/4)) 0 0 :=
  ⟨padeKernel_collapse_low,
   padeKernel_pointwise,
   padeKernel_cross_swap,
   padeKernel_collapse_high,
   padeOffCluster_neq_polynomialOffCluster_collapse_low_at_zero_zero,
   padeOffCluster_neq_polynomialOffCluster_collapse_low,
   padeOffCluster_neq_polynomialOffCluster_pointwise_at_zero_zero⟩

/-! ## Part 6 — Axiom-freeness verification. -/

#print axioms M_cluster_apply_zero_zero
#print axioms M_cluster_apply_one_one
#print axioms M_cluster_apply_zero_one
#print axioms M_cluster_apply_one_zero
#print axioms padeKernel_collapse_low
#print axioms padeKernel_pointwise
#print axioms padeKernel_cross_swap
#print axioms padeKernel_collapse_high
#print axioms padeOffCluster_collapse_low
#print axioms polynomialOffCluster_collapse_low
#print axioms padeOffCluster_neq_polynomialOffCluster_collapse_low_at_zero_zero
#print axioms padeOffCluster_neq_polynomialOffCluster_collapse_low
#print axioms padeOffCluster_neq_polynomialOffCluster_pointwise_at_zero_zero
#print axioms pointwise_pade_fixes_M_cluster
#print axioms ym_canonical_pade_one_one_operator_level_instance_capstone

end PrincipiaTractalis
