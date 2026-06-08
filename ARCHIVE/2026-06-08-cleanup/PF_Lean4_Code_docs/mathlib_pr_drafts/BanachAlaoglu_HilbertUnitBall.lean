/-
Copyright (c) 2026 Pablo Cohen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Cohen
-/
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Compact

/-!
# Banach-Alaoglu for Hilbert spaces: sequential form + Rayleigh-supremum attainment

## Mathlib gap

Mathlib currently has the topological Banach-Alaoglu theorem in
`Mathlib/Analysis/Normed/Module/WeakDual.lean`:

* `WeakDual.isCompact_polar` — polar of a 0-neighborhood is weak-* compact
* `WeakDual.isCompact_closedBall` — closed dual balls are weak-* compact

These are stated on the **dual** `WeakDual 𝕜 E` and depend on `ProperSpace 𝕜`.
They do NOT give:

1. The **sequential** Banach-Alaoglu theorem: every bounded sequence
   in a Hilbert space has a weakly convergent subsequence
   (mathlib's `WeakDual.lean` line 54 explicitly lists this as a
   TODO).
2. A **primal-side** statement: in a Hilbert space `H`, bounded
   sequences `xₙ : H` admit weakly convergent subsequences in the
   primal topology. Hilbert spaces are reflexive, so the abstract
   weak-* dual statement transports, but the reflexivity API is
   itself not in mathlib's analysis layer.
3. The compact-self-adjoint **Rayleigh-quotient maximizer** theorem
   (`Mathlib/Analysis/InnerProductSpace/Spectrum.lean` line 48 has
   the TODO: "Spectral theory for compact self-adjoint operators").

This file states the **three minimal mathlib lemmas** whose addition
would close the gap, in the form needed for spectral theory of
compact self-adjoint operators. Each statement is a candidate for a
distinct mathlib PR.

## PR-1: Sequential Banach-Alaoglu on Hilbert spaces

The cleanest form is on the primal:

```
theorem IsBoundedSequence.exists_weaklyConvergent_subseq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (x : ℕ → H) (hBdd : ∃ C : ℝ, ∀ n, ‖x n‖ ≤ C) :
    ∃ (φ : ℕ → ℕ) (_ : StrictMono φ) (x∞ : H),
      ∀ (y : H), Filter.Tendsto (fun k => ⟪x (φ k), y⟫_ℂ) Filter.atTop (𝓝 ⟪x∞, y⟫_ℂ)
```

**Proof outline** (Brezis V.4 / Reed-Simon I.10):
* `H` is Hilbert ⟹ `H` is reflexive (no mathlib API yet, but
  Riesz representation `Mathlib/Analysis/InnerProductSpace/Dual.lean`
  gives `H ≃ₗᵢ H*` directly).
* Bounded sequences in reflexive Banach spaces have weakly
  convergent subsequences (`Brezis Théorème III.27`).
* Equivalently, identify `x n` with its Riesz image in `H*`,
  apply `WeakDual.isCompact_closedBall` to get a weak-*
  cluster point, transport back via `H ≃ H*`.

## PR-2: Weak convergence + compact operator ⟹ strong convergence on image

```
theorem IsCompactOperator.tendsto_strong_of_tendsto_weak
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (hT : IsCompactOperator T)
    (x : ℕ → H) (x∞ : H)
    (hWeak : ∀ y, Filter.Tendsto (fun n => ⟪x n, y⟫_ℂ) Filter.atTop (𝓝 ⟪x∞, y⟫_ℂ))
    (hBdd : ∃ C : ℝ, ∀ n, ‖x n‖ ≤ C) :
    Filter.Tendsto (fun n => T (x n)) Filter.atTop (𝓝 (T x∞))
```

**Proof outline**:
* `T` is compact ⟹ image of bounded set is relatively compact ⟹
  in metric spaces, relatively compact + every weak-cluster point
  equals strong-cluster point.
* `x` weak-converges to `x∞` ⟹ `T x` weak-converges to `T x∞`
  (continuous-linear `T` preserves weak convergence).
* Strong continuity in `H` plus weak ⟹ strong on compact image
  is the textbook gluing argument.

## PR-3: Rayleigh-supremum attainment for compact self-adjoint operators

The headline target. Combines PR-1 and PR-2:

```
theorem IsCompactOperator.IsSymmetric.rayleighSupremum_attained
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H]
    (T : H →L[ℂ] H) (hCompact : IsCompactOperator T)
    (hSym : (T : H →ₗ[ℂ] H).IsSymmetric) :
    ∃ x₀ : H, x₀ ≠ 0 ∧
      IsMaxOn T.reApplyInnerSelf (Metric.sphere (0 : H) ‖x₀‖) x₀
```

**Proof outline** (Brezis VI.11):
1. Let `M := ⨆ x : { x : H // x ≠ 0 }, T.rayleighQuotient x`.
   This supremum is finite because `T` is bounded, hence
   `T.reApplyInnerSelf x ≤ ‖T‖ · ‖x‖²` gives an a-priori bound.
2. Choose a maximizing sequence `xₙ` on the unit sphere
   (i.e., `‖xₙ‖ = 1` and `T.reApplyInnerSelf xₙ → M`).
3. Apply PR-1 to `xₙ` (bounded by `1`): extract a subsequence
   `xₙₖ` weakly converging to some `x∞ ∈ H`.
4. Apply PR-2 (with `T`): `T xₙₖ → T x∞` strongly.
5. Bilinear continuity:
   `⟪T xₙₖ, xₙₖ⟫ - ⟪T x∞, x∞⟫
      = ⟪T xₙₖ - T x∞, xₙₖ⟫ + ⟪T x∞, xₙₖ - x∞⟫ → 0`
   (first term: strong `T xₙₖ → T x∞` × bounded `xₙₖ`;
   second term: weak convergence `xₙₖ ⇀ x∞` against fixed `T x∞`).
6. Hence `T.reApplyInnerSelf x∞ = M`.
7. Weak lower semicontinuity of the norm gives `‖x∞‖ ≤ 1`. If
   `‖x∞‖ < 1`, scaling `x∞ / ‖x∞‖` would strictly increase the
   ratio `⟨T x, x⟩.re / ‖x‖²`, contradicting maximality of `M`.
   So `‖x∞‖ = 1`, in particular `x∞ ≠ 0`.
8. Take `x₀ := x∞`. Then `T.reApplyInnerSelf` is maximized on
   `Metric.sphere 0 ‖x₀‖ = unit sphere` by `x₀`.

**Total length**: 100–200 lines of mathlib (combined PR-1 + PR-2 + PR-3).

## Where this lemma feeds into Principia Fractalis

This lemma is the exact missing input for
`PF/Analytic/CompactSelfAdjointDiscreteEnumerationDischarge.lean`:

* `RayleighSupremumAttainedUniversally H` (Prop) — direct restatement
  of PR-3 with universal quantification over `T`.
* Composing PR-3 with mathlib's existing
  `IsSelfAdjoint.hasEigenvector_of_isMaxOn`
  (`Mathlib/Analysis/InnerProductSpace/Rayleigh.lean` line 177)
  produces the **Brezis VI.11 / Reed-Simon VI.16** statement: every
  compact symmetric operator on a nontrivial complex Hilbert space
  has at least one real eigenvalue with a non-zero eigenvector.
* Iterating (Brezis VI.11 corollary) produces the ℕ-indexed
  eigenvalue sequence required by `(W1)`
  (`CompactSelfAdjointDiscreteEigenvalueEnumeration`).

This file contains only the **statement targets**. No proofs.
Adding `sorry` would defeat the purpose of recording these as
mathlib gaps; the file is therefore a `-- statement-only` draft,
suitable for opening as a mathlib PR with the proofs filled in.
-/

namespace MathlibPRDraft

open scoped InnerProductSpace
open Filter Topology Metric

/-! ## PR-1 target statement -/

/-- **PR-1 (mathlib draft)**: every bounded sequence in a complex
    Hilbert space admits a weakly convergent subsequence.

    Status: stated, not proved. The proof goes through Hilbert ⟹
    reflexive ⟹ bounded ⟹ weak-cluster-point via
    `WeakDual.isCompact_closedBall`.

    This is the **sequential Banach-Alaoglu theorem** that
    `Mathlib/Analysis/Normed/Module/WeakDual.lean` line 54 lists as
    "TODO". -/
def IsBoundedSequence_exists_weaklyConvergent_subseq_target
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : Prop :=
  ∀ (x : ℕ → H),
    (∃ C : ℝ, ∀ n, ‖x n‖ ≤ C) →
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧ ∃ (xInf : H),
      ∀ (y : H), Tendsto (fun k => ⟪x (φ k), y⟫_ℂ) atTop (𝓝 ⟪xInf, y⟫_ℂ)

/-! ## PR-2 target statement -/

/-- **PR-2 (mathlib draft)**: weak convergence + compact `T` ⟹
    strong convergence of `T xₙ → T x∞`.

    Status: stated, not proved. Standard "compactness upgrades weak
    to strong" argument. -/
def IsCompactOperator_tendsto_strong_of_tendsto_weak_target
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : Prop :=
  ∀ (T : H →L[ℂ] H), IsCompactOperator T →
  ∀ (x : ℕ → H) (xInf : H),
    (∀ y, Tendsto (fun n => ⟪x n, y⟫_ℂ) atTop (𝓝 ⟪xInf, y⟫_ℂ)) →
    (∃ C : ℝ, ∀ n, ‖x n‖ ≤ C) →
    Tendsto (fun n => T (x n)) atTop (𝓝 (T xInf))

/-! ## PR-3 target statement — THE key target

This is the precise statement that, when added to mathlib, allows
`RayleighSupremumAttainedUniversally H` in
`PF/Analytic/CompactSelfAdjointDiscreteEnumerationDischarge.lean`
to become a proven theorem (not a hypothesis).
-/

/-- **PR-3 (mathlib draft)**: compact self-adjoint operators on a
    nontrivial complex Hilbert space have a Rayleigh-supremum
    maximizer.

    Status: stated, not proved. Combines PR-1 + PR-2 + bilinear
    continuity + weak lower semicontinuity of the norm
    (Brezis Théorème VI.11).

    This is the exact statement needed to upgrade
    `RayleighSupremumAttainedUniversally H` from hypothesis to
    theorem in the Principia Fractalis Lean codebase. -/
def IsCompactOperator_IsSymmetric_rayleighSupremum_attained_target
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] : Prop :=
  ∀ (T : H →L[ℂ] H), IsCompactOperator T →
    (T : H →ₗ[ℂ] H).IsSymmetric →
    ∃ x₀ : H, x₀ ≠ 0 ∧
      IsMaxOn T.reApplyInnerSelf (Metric.sphere (0 : H) ‖x₀‖) x₀

/-! ## Composite: PR-1 + PR-2 + bilinear continuity ⟹ PR-3

The reduction PR-1 ∧ PR-2 ⟹ PR-3 is the actual proof step that
would live in a mathlib PR. Recording it here as a Prop so the
dependency structure is explicit for downstream consumers.
-/

/-- **Reduction Prop**: PR-1 + PR-2 ⟹ PR-3 (the Brezis VI.11
    proof, modulo bilinear continuity which mathlib already has via
    `inner_continuous`).

    Status: stated as a `→` between Props. The implication itself
    requires the bilinear-continuity + scaling argument (~50 lines
    of mathlib). -/
def Brezis_VI11_reduction_target
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] : Prop :=
  IsBoundedSequence_exists_weaklyConvergent_subseq_target H →
  IsCompactOperator_tendsto_strong_of_tendsto_weak_target H →
  IsCompactOperator_IsSymmetric_rayleighSupremum_attained_target H

end MathlibPRDraft
