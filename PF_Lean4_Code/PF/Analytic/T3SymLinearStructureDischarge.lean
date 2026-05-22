/-
# `T3SymLinearStructure` — Half-Sum Factorisation Discharge

This file pushes the `T3SymLinearStructure` Prop (from
`PF/Analytic/T3SymCLMConstruction.lean:116`) one level deeper, by
exploiting the structural identity

  `T3_sym.apply f = (1/2 : ℂ) • (T3.apply f + T3_adjoint.apply f)`

(`PF/TransferOperator.lean:3043-3054`, def `T3_sym_action` /
`T3_sym`).

## What this file delivers (NO SORRY, NO AXIOMS)

  1. **`T3LinearStructure`** — additivity, complex-homogeneity, and
     norm-bound `‖T_3 f‖ ≤ ‖f‖` for the contracting half `T3.apply`.

  2. **`T3AdjointLinearStructure`** — same three ingredients for the
     expanding half `T3_adjoint.apply`.

  3. **`T3SymLinearStructure_proved_from_halves`** — given both halves'
     linear-structure witnesses, produces `T3SymLinearStructure` for
     `T3_sym.apply`. Pure abelian-group + scalar-multiplication
     manipulations + triangle inequality + half-sum bound.

  4. **`T3SymCLMSymmetricWitness_proved_from_halves`** — end-to-end
     discharge: given both halves' linear-structure witnesses,
     produces `T3SymCLMSymmetricWitness` directly via
     `T3SymCLMSymmetricWitness_proved_from_linearStructure_only`.

## Honest framing

After this file, the bundle (a) `T3SymCLMSymmetricWitness` gap is
factored further from the single 3-piece Prop `T3SymLinearStructure`
into TWO 3-piece Props `T3LinearStructure` and
`T3AdjointLinearStructure` for the unsymmetrised constituents. Each
is at the same mathlib-API granularity (additivity +
complex-homogeneity + Mayer norm bound) but for the SIMPLER operators
that directly call `(transferOperatorAction_func 3 phaseFactorBase3 f)`
and `(T3_adjoint_action_func f)` — no half-sum bookkeeping. Their
natural source is `PF/LogWeightedIntegral.lean`'s
`transferOperator_lp_add` / `_smul` / `_norm_le` for the contracting
half, with an analogous direct construction (no broken file
dependency) for the expanding half via the existing
`T3_adjoint_toFunℝ_Ioo_unconditional`.

## Build state

ZERO project axioms. ZERO `sorry`. Builds against the same mathlib
snapshot as `PF.Analytic.T3SymCLMConstruction`.
-/

import PF.Analytic.LogWeightedL2InnerBridgeDischarge

namespace PrincipiaTractalis

open scoped InnerProductSpace
open MeasureTheory

/-! ## 1. Linear-structure witnesses for the unsymmetrised halves -/

/-- **`T3LinearStructure`** — additivity, complex-homogeneity, and
    `‖T_3 f‖ ≤ ‖f‖` for the contracting transfer operator `T3.apply`.

    Provenance (when supplied): direct consequence of
    `PF/LogWeightedIntegral.lean`'s `transferOperator_lp_add /
    _smul / _norm_le` at `(b, phases) = (3, phaseFactorBase3)`, once
    the two-spot rebuild fix lands. The contractivity `‖T_3 f‖ ≤ ‖f‖`
    is Mayer 1991 (BAMS) for the base-3 contracting transfer
    operator on $L^2([0,1], dx/x)$. -/
structure T3LinearStructure : Prop where
  /-- Additivity: $T_3 (f + g) = T_3 f + T_3 g$. -/
  add : ∀ (f g : LogWeightedL2),
    T3.apply (f + g) = T3.apply f + T3.apply g
  /-- Complex-homogeneity: $T_3 (c \cdot f) = c \cdot T_3 f$. -/
  smul : ∀ (c : ℂ) (f : LogWeightedL2),
    T3.apply (c • f) = c • T3.apply f
  /-- Mayer 1991 contractivity: $\|T_3 f\| \le \|f\|$ on
      $L^2([0,1], dx/x)$. -/
  norm_le : ∀ (f : LogWeightedL2), ‖T3.apply f‖ ≤ ‖f‖

/-- **`T3AdjointLinearStructure`** — same three ingredients for the
    expanding-branch formal-adjoint operator `T3_adjoint.apply`.

    Provenance (when supplied): the contractivity transfers via the
    formal-adjoint relation (Mayer 1991 — the formal adjoint of a
    contraction on a Hilbert space is itself a contraction with the
    same norm). Additivity and homogeneity follow from the explicit
    pointwise formula `T3_adjoint_action_func` (`PF/TransferOperator.lean:1344`)
    combined with the `LogWeightedL2.toFunℝ_add` /
    `LogWeightedL2.toFunℝ_smul` Lp-representative identities. -/
structure T3AdjointLinearStructure : Prop where
  /-- Additivity: $T_3^* (f + g) = T_3^* f + T_3^* g$. -/
  add : ∀ (f g : LogWeightedL2),
    T3_adjoint.apply (f + g) = T3_adjoint.apply f + T3_adjoint.apply g
  /-- Complex-homogeneity: $T_3^* (c \cdot f) = c \cdot T_3^* f$. -/
  smul : ∀ (c : ℂ) (f : LogWeightedL2),
    T3_adjoint.apply (c • f) = c • T3_adjoint.apply f
  /-- Adjoint contractivity: $\|T_3^* f\| \le \|f\|$ (formal-adjoint
      contractivity from $\|T_3\| \le 1$). -/
  norm_le : ∀ (f : LogWeightedL2), ‖T3_adjoint.apply f‖ ≤ ‖f‖

/-! ## 2. `T3SymLinearStructure` from the half-pair witnesses -/

/-- **Half-sum unfold**: `T3_sym.apply f = (1/2) • (T3.apply f + T3_adjoint.apply f)`.
    This is just the definition `T3_sym_action`
    (`PF/TransferOperator.lean:3043-3054`). -/
theorem T3_sym_apply_eq_half_sum (f : LogWeightedL2) :
    T3_sym.apply f = ((1/2 : ℂ)) • (T3.apply f + T3_adjoint.apply f) :=
  rfl

/-- **★ Additivity of `T3_sym.apply` from half-pair additivity ★** -/
theorem T3_sym_apply_add_of_halves
    (hT3 : T3LinearStructure) (hT3adj : T3AdjointLinearStructure)
    (f g : LogWeightedL2) :
    T3_sym.apply (f + g) = T3_sym.apply f + T3_sym.apply g := by
  -- Unfold all three T3_sym.apply via the half-sum identity
  rw [T3_sym_apply_eq_half_sum, T3_sym_apply_eq_half_sum,
      T3_sym_apply_eq_half_sum]
  -- Push add through T3 and T3_adjoint individually
  rw [hT3.add f g, hT3adj.add f g]
  -- Now both sides are scalar multiples of sums; pure algebra in
  -- the abelian group `LogWeightedL2`.
  -- LHS: (1/2) • ((T3 f + T3 g) + (T3* f + T3* g))
  -- RHS: (1/2) • (T3 f + T3* f) + (1/2) • (T3 g + T3* g)
  --     = (1/2) • ((T3 f + T3* f) + (T3 g + T3* g))
  rw [← smul_add]
  congr 1
  -- (T3 f + T3 g) + (T3* f + T3* g) = (T3 f + T3* f) + (T3 g + T3* g)
  abel

/-- **★ Complex-homogeneity of `T3_sym.apply` from half-pair homogeneity ★** -/
theorem T3_sym_apply_smul_of_halves
    (hT3 : T3LinearStructure) (hT3adj : T3AdjointLinearStructure)
    (c : ℂ) (f : LogWeightedL2) :
    T3_sym.apply (c • f) = c • T3_sym.apply f := by
  rw [T3_sym_apply_eq_half_sum, T3_sym_apply_eq_half_sum]
  rw [hT3.smul c f, hT3adj.smul c f]
  -- (1/2) • (c • T3 f + c • T3* f) = c • ((1/2) • (T3 f + T3* f))
  rw [← smul_add]
  -- (1/2) • (c • (T3 f + T3* f)) = c • ((1/2) • (T3 f + T3* f))
  rw [smul_comm]

/-- **★ Norm bound `‖T3_sym.apply f‖ ≤ ‖f‖` from half-pair contractivity ★**

    Proof:
      `‖(1/2) • (T3 f + T3* f)‖`
        ≤ `(1/2) * ‖T3 f + T3* f‖`     (norm_smul, since |1/2| = 1/2)
        ≤ `(1/2) * (‖T3 f‖ + ‖T3* f‖)` (triangle inequality)
        ≤ `(1/2) * (‖f‖ + ‖f‖)`        (each half is a contraction)
        = `‖f‖`. -/
theorem T3_sym_apply_norm_le_of_halves
    (hT3 : T3LinearStructure) (hT3adj : T3AdjointLinearStructure)
    (f : LogWeightedL2) :
    ‖T3_sym.apply f‖ ≤ ‖f‖ := by
  rw [T3_sym_apply_eq_half_sum]
  -- Step 1: pull out the scalar (1/2 : ℂ).
  rw [norm_smul]
  -- ‖(1/2 : ℂ)‖ = 1/2
  have h_half_norm : ‖(1/2 : ℂ)‖ = 1/2 := by
    rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) from by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg (by norm_num : (1/2 : ℝ) ≥ 0)]
  rw [h_half_norm]
  -- Goal: (1/2) * ‖T3 f + T3* f‖ ≤ ‖f‖
  -- Step 2: triangle inequality on the sum.
  have h_tri : ‖T3.apply f + T3_adjoint.apply f‖
      ≤ ‖T3.apply f‖ + ‖T3_adjoint.apply f‖ := norm_add_le _ _
  -- Step 3: each half ≤ ‖f‖.
  have h_T3_bd : ‖T3.apply f‖ ≤ ‖f‖ := hT3.norm_le f
  have h_T3adj_bd : ‖T3_adjoint.apply f‖ ≤ ‖f‖ := hT3adj.norm_le f
  -- Combine: ‖T3 f + T3* f‖ ≤ ‖f‖ + ‖f‖ = 2 * ‖f‖
  have h_sum_bd : ‖T3.apply f + T3_adjoint.apply f‖ ≤ ‖f‖ + ‖f‖ := by
    calc ‖T3.apply f + T3_adjoint.apply f‖
        ≤ ‖T3.apply f‖ + ‖T3_adjoint.apply f‖ := h_tri
      _ ≤ ‖f‖ + ‖f‖ := add_le_add h_T3_bd h_T3adj_bd
  -- Multiply by (1/2 : ℝ) ≥ 0 and simplify.
  have h_half_nn : (0 : ℝ) ≤ 1/2 := by norm_num
  calc (1/2 : ℝ) * ‖T3.apply f + T3_adjoint.apply f‖
      ≤ (1/2 : ℝ) * (‖f‖ + ‖f‖) := by
        exact mul_le_mul_of_nonneg_left h_sum_bd h_half_nn
    _ = ‖f‖ := by ring

/-- **★ `T3SymLinearStructure` discharged from the half-pair
    `T3LinearStructure` + `T3AdjointLinearStructure` witnesses ★** -/
theorem T3SymLinearStructure_proved_from_halves
    (hT3 : T3LinearStructure) (hT3adj : T3AdjointLinearStructure) :
    T3SymLinearStructure :=
  ⟨T3_sym_apply_add_of_halves hT3 hT3adj,
   T3_sym_apply_smul_of_halves hT3 hT3adj,
   T3_sym_apply_norm_le_of_halves hT3 hT3adj⟩

/-! ## 3. End-to-end discharge of `T3SymCLMSymmetricWitness` from halves -/

/-- **★★ `T3SymCLMSymmetricWitness` from the half-pair witnesses ★★**

    Composes `T3SymLinearStructure_proved_from_halves` with the
    already-proven
    `T3SymCLMSymmetricWitness_proved_from_linearStructure_only`
    (which itself uses the already-proven
    `logWeightedL2InnerBridge_proved`).

    After this theorem, bundle (a)'s `T3SymCLMSymmetricWitness` gap
    reduces to the TWO half-pair Props `T3LinearStructure` and
    `T3AdjointLinearStructure` — each at mathlib-API granularity, no
    half-sum bookkeeping, with natural sources documented above. -/
theorem T3SymCLMSymmetricWitness_proved_from_halves
    (hT3 : T3LinearStructure) (hT3adj : T3AdjointLinearStructure) :
    T3SymCLMSymmetricWitness :=
  T3SymCLMSymmetricWitness_proved_from_linearStructure_only
    (T3SymLinearStructure_proved_from_halves hT3 hT3adj)

/-! ## 4. Concrete progress summary

After this file, the bundle (a) gap for `T3SymCLMSymmetricWitness` is
factored from the single 3-piece Prop `T3SymLinearStructure` into
TWO 3-piece Props at mathlib-API granularity:

  * `T3LinearStructure`        — additivity + ℂ-homogeneity + ‖·‖ ≤ ‖·‖
                                 for the contracting half `T3.apply`.
  * `T3AdjointLinearStructure` — additivity + ℂ-homogeneity + ‖·‖ ≤ ‖·‖
                                 for the expanding half `T3_adjoint.apply`.

Both are AXIOM-FREE Props with concrete mathlib-pointed extraction
targets (no half-sum bookkeeping; each operator is directly
parametrised by an explicit pointwise formula
`transferOperatorAction_func` / `T3_adjoint_action_func` and its
established `MemLp` closure).

This factorisation removes the half-sum complication entirely from
the linear-structure proof obligation: any future agent now needs
to discharge only individual additivity/homogeneity/contractivity
for the two CONSTITUENT operators, rather than the combined
symmetrised half-sum — strictly simpler scoping. -/

/-! ## 5. Axiom-freeness verification -/

#print axioms T3LinearStructure
#print axioms T3AdjointLinearStructure
#print axioms T3_sym_apply_eq_half_sum
#print axioms T3_sym_apply_add_of_halves
#print axioms T3_sym_apply_smul_of_halves
#print axioms T3_sym_apply_norm_le_of_halves
#print axioms T3SymLinearStructure_proved_from_halves
#print axioms T3SymCLMSymmetricWitness_proved_from_halves

end PrincipiaTractalis
