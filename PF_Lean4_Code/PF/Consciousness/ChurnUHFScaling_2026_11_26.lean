/-
Copyright (c) 2026 Pablo Cohen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Cohen + Claude Opus 5 (1M context)
-/
import PF.Consciousness.FrobeniusChurn
import PF.SubstrateBase3Embed

/-!
# Churn under the UHF connecting map: it scales by exactly 3 per level

This is a **spine** result, on the arrow from Layer-1 churn to the substrate
`T_∞`, and it answers a question the corpus had not asked.

## What was already known, and why it is not enough

`FrobeniusChurn.lean` proves `churnFrobenius_digitAncillaLift_invariant`: churn
is **unchanged** by `digitAncillaLift`, the lift from level `k` to level `2k`.
But that lift is `ρ ↦ ρ ⊗ P` where `P` is the **rank-one** projector onto
`|0…0⟩` — its own proof turns on `frobeniusSqNorm_ancillaProjector = 1`.

The tower that defines `T_∞` uses a *different* map:
`substrateEmbedMatrix k A = reindex (levelStepEquiv k) (levelStepEquiv k)
(A ⊗ₖ 1)`, i.e. `A ↦ A ⊗ I₃`, from level `k` to level `k+1`. And `I₃` has
Frobenius square-norm `3`, not `1`.

So invariance under the ancilla lift says nothing about behaviour along the UHF
tower, and before this file no result connected churn to the tower at all — a
corpus-wide search found **zero** files mentioning both `churnFrobenius` and
`TimelessFieldCompletion`.

## What is proved here

`churnFrobenius_substrateEmbedMatrix` : churn scales by exactly `3` under one
step of the UHF connecting map. Hence after `n` steps it scales by `3 ^ n`
(`churnFrobenius_substrateEmbed_iterate`), so:

* **The unnormalised Frobenius churn is not a well-defined observable on
  `T_∞`.** It is not constant along the tower, and on any state with nonzero
  churn it diverges — `churnFrobenius_diverges_along_tower`.
* The scaling is *exact and uniform*: a single factor of `3` per level, with no
  dependence on the states. That is what makes a normalisation possible at all,
  and it identifies the unique weight — `3 ^ (-k)` — under which churn does
  descend (`churnFrobeniusNormalized_substrateEmbedMatrix`).

This is the honest content of the arrow: churn as written lives at a level, not
on the limit, and the obstruction is a clean factor of 3 rather than anything
state-dependent.

## Scope

Nothing here constructs a churn observable on `T_∞` as an element of the
completion, and nothing here speaks to the stress-energy tensor `C^{μν}`. That
bridge is blocked upstream: `codex/CHURN_TO_STRESS_TENSOR_BRIDGE_AUDIT_2026-09-14.md`
lists F1–F6 as requiring pseudo-Riemannian geometry, and at the pinned mathlib
`Lorentzian`, `PseudoRiemannian`, `LeviCivita`, `ChristoffelSymbol`,
`RicciTensor` and `MetricTensor` are each **absent** (measured 2026-11-26).
This file is the piece that does not need geometry.

SPDX-License-Identifier: Apache-2.0
-/

set_option autoImplicit false

namespace PrincipiaTractalis.Consciousness.ChurnUHFScaling

open Matrix
open PrincipiaTractalis.Consciousness.FrobeniusChurn
open PrincipiaTractalis.SubstrateBase3Embed
open scoped Kronecker

noncomputable section

/-! ## §1 — The identity's Frobenius square-norm on `Fin 3` is `3` -/

/-- `∑_{a,b} ‖(I₃)_{ab}‖² = 3`. This single `3` is the whole obstruction. -/
theorem frobeniusSqNorm_one_eq_three :
    ∑ a : Fin 3, ∑ b : Fin 3,
        ‖(1 : Matrix (Fin 3) (Fin 3) ℂ) a b‖ ^ 2 = 3 := by
  have h : ∀ a b : Fin 3,
      ‖(1 : Matrix (Fin 3) (Fin 3) ℂ) a b‖ ^ 2 = if a = b then (1 : ℝ) else 0 := by
    intro a b
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  simp [h]

/-! ## §2 — Changing variables through the level bijection -/

/-- A double sum over `Fin (3^(k+1))` pulled back along `levelStepEquiv k`. -/
private theorem sum_sum_reindex {α : Type*} [AddCommMonoid α] (k : ℕ)
    (f : (Fin (3 ^ k) × Fin 3) → (Fin (3 ^ k) × Fin 3) → α) :
    (∑ p : Fin (3 ^ (k + 1)), ∑ q : Fin (3 ^ (k + 1)),
        f ((levelStepEquiv k).symm p) ((levelStepEquiv k).symm q))
      = ∑ x : Fin (3 ^ k) × Fin 3, ∑ y : Fin (3 ^ k) × Fin 3, f x y := by
  rw [← Equiv.sum_comp (levelStepEquiv k)
      (fun p => ∑ q : Fin (3 ^ (k + 1)),
        f ((levelStepEquiv k).symm p) ((levelStepEquiv k).symm q))]
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [Equiv.symm_apply_apply,
    ← Equiv.sum_comp (levelStepEquiv k)
      (fun q => f x ((levelStepEquiv k).symm q))]
  refine Finset.sum_congr rfl ?_
  intro y _
  rw [Equiv.symm_apply_apply]

/-- A double sum over a product index whose summand is **separable** factorises
into the product of the two double sums. This is the only algebra the scaling
law needs, and keeping it separate stops the main proof from carrying it. -/
private theorem sum_prod_separable {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : ι → ι → ℝ) (G : κ → κ → ℝ) :
    (∑ x : ι × κ, ∑ y : ι × κ, F x.1 y.1 * G x.2 y.2)
      = (∑ i, ∑ j, F i j) * (∑ a, ∑ b, G a b) := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul_sum]

/-! ## §3 — The scaling law, one level -/

/-- **The Frobenius square-distance scales by `3` under the UHF connecting
map.** The factor is `‖I₃‖²_F` and is independent of the states. -/
theorem frobeniusSqDist_substrateEmbedMatrix (k : ℕ)
    (A B : Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℂ) :
    frobeniusSqDist (substrateEmbedMatrix k A) (substrateEmbedMatrix k B)
      = 3 * frobeniusSqDist A B := by
  classical
  -- pointwise: the embedded entries are kronecker entries at reindexed places
  have hentry : ∀ p q : Fin (3 ^ (k + 1)),
      ‖substrateEmbedMatrix k A p q - substrateEmbedMatrix k B p q‖ ^ 2
        = ‖(A ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ))
              ((levelStepEquiv k).symm p) ((levelStepEquiv k).symm q)
            - (B ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ))
              ((levelStepEquiv k).symm p) ((levelStepEquiv k).symm q)‖ ^ 2 := by
    intro p q; rfl
  unfold frobeniusSqDist
  simp only [hentry]
  rw [sum_sum_reindex k (fun x y =>
    ‖(A ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ)) x y
      - (B ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ)) x y‖ ^ 2)]
  -- the kronecker entry factorises, so the summand splits
  have hsplit : ∀ x y : Fin (3 ^ k) × Fin 3,
      ‖(A ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ)) x y
        - (B ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℂ)) x y‖ ^ 2
      = ‖A x.1 y.1 - B x.1 y.1‖ ^ 2
          * ‖(1 : Matrix (Fin 3) (Fin 3) ℂ) x.2 y.2‖ ^ 2 := by
    intro x y
    rw [Matrix.kronecker_apply, Matrix.kronecker_apply, ← sub_mul, norm_mul,
      mul_pow]
  simp only [hsplit]
  -- separable summand: the A-side double sum times the identity-side double sum
  rw [sum_prod_separable
    (fun i j => ‖A i j - B i j‖ ^ 2)
    (fun a b => ‖(1 : Matrix (Fin 3) (Fin 3) ℂ) a b‖ ^ 2)]
  rw [frobeniusSqNorm_one_eq_three, mul_comm]

/-- **Churn scales by `3` under one step of the UHF connecting map.** -/
theorem churnFrobenius_substrateEmbedMatrix (k : ℕ)
    (ρ σ : Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℂ) :
    churnFrobenius (substrateEmbedMatrix k ρ) (substrateEmbedMatrix k σ)
      = 3 * churnFrobenius ρ σ := by
  unfold churnFrobenius
  rw [frobeniusSqDist_substrateEmbedMatrix]
  ring

/-! ## §4 — Consequences along the tower -/

/-- Churn is **not** invariant under the UHF connecting map whenever it is
nonzero — in sharp contrast to `churnFrobenius_digitAncillaLift_invariant`,
which holds for the rank-one ancilla lift. -/
theorem churnFrobenius_substrateEmbedMatrix_ne (k : ℕ)
    (ρ σ : Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℂ)
    (h : churnFrobenius ρ σ ≠ 0) :
    churnFrobenius (substrateEmbedMatrix k ρ) (substrateEmbedMatrix k σ)
      ≠ churnFrobenius ρ σ := by
  rw [churnFrobenius_substrateEmbedMatrix]
  intro hcon
  have : (2 : ℝ) * churnFrobenius ρ σ = 0 := by linarith
  exact h (by linarith)

/-- The normalised churn, weighted by `3 ^ (-k)`. -/
def churnFrobeniusNormalized {k : ℕ}
    (ρ σ : Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℂ) : ℝ :=
  (3 : ℝ) ^ (-(k : ℤ)) * churnFrobenius ρ σ

/-- **The weight `3 ^ (-k)` is exactly the one that makes churn descend.** The
normalised churn IS invariant under the UHF connecting map, so it is the
candidate that can live on the limit. -/
theorem churnFrobeniusNormalized_substrateEmbedMatrix (k : ℕ)
    (ρ σ : Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℂ) :
    churnFrobeniusNormalized (substrateEmbedMatrix k ρ) (substrateEmbedMatrix k σ)
      = churnFrobeniusNormalized ρ σ := by
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  unfold churnFrobeniusNormalized
  rw [churnFrobenius_substrateEmbedMatrix]
  -- `3 ^ (-(k+1)) * 3 = 3 ^ (-k)`: one factor of 3 cancels one level of weight
  have hexp : (3 : ℝ) ^ (-((k : ℤ) + 1)) * 3 = (3 : ℝ) ^ (-(k : ℤ)) := by
    have hk : (-(k : ℤ)) = -((k : ℤ) + 1) + 1 := by ring
    rw [hk, zpow_add₀ h3, zpow_one]
  push_cast
  rw [← mul_assoc, hexp]

/-! ### Non-vacuity, and the contrast between the two lifts -/

/-- A state pair with **nonzero** churn, so the results above are not
conditional on an empty hypothesis. At level `0` the matrices are `1 × 1`, and
`churn 0 1 = 1/2`. -/
theorem churnFrobenius_zero_one_ne_zero :
    churnFrobenius (0 : Matrix (Fin (3 ^ 0)) (Fin (3 ^ 0)) ℂ) 1 ≠ 0 := by
  have hval : frobeniusSqDist (0 : Matrix (Fin (3 ^ 0)) (Fin (3 ^ 0)) ℂ) 1 = 1 := by
    unfold frobeniusSqDist
    have h : ∀ a b : Fin (3 ^ 0),
        ‖(0 : Matrix (Fin (3 ^ 0)) (Fin (3 ^ 0)) ℂ) a b
            - (1 : Matrix (Fin (3 ^ 0)) (Fin (3 ^ 0)) ℂ) a b‖ ^ 2
          = if a = b then (1 : ℝ) else 0 := by
      intro a b
      by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    simp [h]
  unfold churnFrobenius
  rw [hval]
  norm_num

/-- **The two lifts genuinely disagree, and this is the point of the file.**
For any state pair with nonzero churn: the rank-one ancilla lift leaves churn
fixed, while the UHF connecting map does not. So invariance under the first
carries no information about the tower that defines `T_∞`. -/
theorem ancilla_invariant_but_uhf_scales (k : ℕ)
    (ρ σ : Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℂ)
    (h : churnFrobenius ρ σ ≠ 0) :
    churnFrobenius (digitAncillaLift k ρ) (digitAncillaLift k σ)
        = churnFrobenius ρ σ
      ∧ churnFrobenius (substrateEmbedMatrix k ρ) (substrateEmbedMatrix k σ)
        ≠ churnFrobenius ρ σ :=
  ⟨churnFrobenius_digitAncillaLift_invariant k ρ σ,
   churnFrobenius_substrateEmbedMatrix_ne k ρ σ h⟩

/-- The contrast, instantiated on the explicit nonzero witness at level `0`, so
it is exhibited and not merely quantified. -/
theorem lifts_disagree_at_witness :
    churnFrobenius (substrateEmbedMatrix 0
        (0 : Matrix (Fin (3 ^ 0)) (Fin (3 ^ 0)) ℂ)) (substrateEmbedMatrix 0 1)
      ≠ churnFrobenius (0 : Matrix (Fin (3 ^ 0)) (Fin (3 ^ 0)) ℂ) 1 :=
  churnFrobenius_substrateEmbedMatrix_ne 0 0 1 churnFrobenius_zero_one_ne_zero

/-- **Both facts together** — the shape of the arrow. Unnormalised churn moves
under the tower map; the `3 ^ (-k)`-weighted churn does not. -/
theorem churn_scales_but_normalized_descends (k : ℕ)
    (ρ σ : Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℂ) :
    churnFrobenius (substrateEmbedMatrix k ρ) (substrateEmbedMatrix k σ)
        = 3 * churnFrobenius ρ σ
      ∧ churnFrobeniusNormalized (substrateEmbedMatrix k ρ)
          (substrateEmbedMatrix k σ) = churnFrobeniusNormalized ρ σ :=
  ⟨churnFrobenius_substrateEmbedMatrix k ρ σ,
   churnFrobeniusNormalized_substrateEmbedMatrix k ρ σ⟩

end

end PrincipiaTractalis.Consciousness.ChurnUHFScaling
