/-
# r111: The L²-OPERATOR-NORM CONTRACTION of the base-3 partial trace —
  discharging `PartialTraceStepOpNormContraction`, the last analytic wall
  of the completion-tier faithfulness summit.

★ 2026-07-23 r111 — THE LAST LEMMA. The single-step base-3 partial trace
`partialTraceStep n : M_{3^{n+1}} → M_{3^n}` is an L²-operator-norm
contraction: `‖partialTraceStep n B‖ ≤ ‖B‖`. ★

## What r111 establishes (UNCONDITIONAL, kernel-only)

r110 (`PF/SubstrateCondExpContraction.lean`) discharged the *2-norm*
Kadison–Schwarz contraction elementarily but flagged one residual gating
the SUMMIT: the **operator-norm** contraction

    `PartialTraceStepOpNormContraction : ∀ n B, ‖partialTraceStep n B‖ ≤ ‖B‖`

in the L²-operator norm (`Matrix.Norms.L2Operator`), which r110 called "the
one lemma NOT reachable elementarily (matrix partial-trace complete
positivity is absent from mathlib)".

r111 discharges it **without any completely-positive-map theory**, via the
Stinespring/isometry decomposition of the partial trace. Writing
`E B = (1/3) Σ_{t : Fin 3} Wₜᴴ B Wₜ`, where `Wₜ : M_{3^n → 3^{n+1}}` is the
coordinate-injection isometry `v ↦ v ⊗ eₜ` (`Winj`), each `Wₜ` satisfies
`Wₜᴴ Wₜ = 1`, hence — by the C*-identity `‖Wₜᴴ Wₜ‖ = ‖Wₜ‖²` and
`‖1‖ = ‖id‖ ≤ 1` — obeys `‖Wₜ‖² ≤ 1`. Submultiplicativity of the operator
norm and `‖Wₜᴴ‖ = ‖Wₜ‖` then give

    ‖Wₜᴴ B Wₜ‖ ≤ ‖Wₜᴴ‖ ‖B‖ ‖Wₜ‖ = ‖Wₜ‖² ‖B‖ ≤ ‖B‖,

and averaging over the three tensor slots closes it:
`‖E B‖ ≤ (1/3) Σ_t ‖Wₜᴴ B Wₜ‖ ≤ (1/3)(3‖B‖) = ‖B‖`.

The only mathlib inputs are the L²-operator-norm C*-structure
(`Matrix.l2_opNorm_mul`, `Matrix.l2_opNorm_conjTranspose`,
`Matrix.l2_opNorm_conjTranspose_mul_self`, `Matrix.cstar_norm_def`) and
`ContinuousLinearMap.norm_id_le`. No complete positivity, no PSD order.

## Consequence

Via r110, this discharges the LOAD-BEARING analytic input for r109's
residual (3) `CondExpCompletionExtension` (the uniform-continuity extension
of `E_k` to `TimelessFieldCompletion`): `‖partialTraceStep‖ ≤ 1` iterates
to `‖condExp k x‖ ≤ ‖x‖`, i.e. `E_k` is a norm-1 map, hence uniformly
continuous and extendable to the completion. The remaining gap to the
SUMMIT is the completion-side density/extension packaging, discussed in the
capstone docstring.

Kernel-only [propext, Classical.choice, Quot.sound]. Zero project axioms.
Zero sorries.

Stage 2026-07-23 r111 — the operator-norm contraction of the partial trace.
-/

import PF.SubstrateConditionalExpectation
import PF.SubstrateCondExpContraction
import PF.SubstrateTimelessFieldNorm
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace SubstrateCondExpOpNorm

open scoped Matrix
open scoped Matrix.Norms.L2Operator
open SubstrateBase3Embed
open SubstrateDirectLimit
open SubstrateConditionalExpectation
open SubstrateCondExpContraction
open SubstrateTimelessFieldNorm

/-! ## §1 — The coordinate-injection isometry `Wₜ : M_{3^n → 3^{n+1}}` -/

/-- **The base-3 coordinate injection** into the `t`-th tensor slot:
    `Wₜ p j = 1` iff `p = levelStepEquiv n (j, t)`, else `0`. As a linear
    map `ℂ^{3^n} → ℂ^{3^{n+1}}` it is `v ↦ v ⊗ eₜ`, an isometry. -/
noncomputable def Winj (n : ℕ) (t : Fin 3) :
    Matrix (Fin (3^(n+1))) (Fin (3^n)) ℂ :=
  Matrix.of fun p j => if p = levelStepEquiv n (j, t) then 1 else 0

@[simp] theorem Winj_apply (n : ℕ) (t : Fin 3)
    (p : Fin (3^(n+1))) (j : Fin (3^n)) :
    Winj n t p j = if p = levelStepEquiv n (j, t) then 1 else 0 := rfl

theorem Winj_conjTranspose_apply (n : ℕ) (t : Fin 3)
    (j : Fin (3^n)) (p : Fin (3^(n+1))) :
    (Winj n t)ᴴ j p = if p = levelStepEquiv n (j, t) then 1 else 0 := by
  rw [Matrix.conjTranspose_apply, Winj_apply]
  by_cases h : p = levelStepEquiv n (j, t) <;> simp [h]

/-- **`Wₜ` is an isometry**: `Wₜᴴ Wₜ = 1` (orthonormal columns). -/
theorem Winj_conjTranspose_mul_self (n : ℕ) (t : Fin 3) :
    (Winj n t)ᴴ * Winj n t = (1 : Matrix (Fin (3^n)) (Fin (3^n)) ℂ) := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    rw [Finset.sum_eq_single (levelStepEquiv n (i, t))]
    · rw [Winj_conjTranspose_apply, Winj_apply, if_pos rfl, one_mul]
    · intro p _ hp
      rw [Winj_conjTranspose_apply, if_neg hp, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro p _
    by_cases hpi : p = levelStepEquiv n (i, t)
    · by_cases hpj : p = levelStepEquiv n (j, t)
      · exact absurd
          ((Prod.ext_iff.mp ((levelStepEquiv n).injective (hpi.symm.trans hpj))).1) hij
      · rw [Winj_apply, if_neg hpj, mul_zero]
    · rw [Winj_conjTranspose_apply, if_neg hpi, zero_mul]

/-! ## §2 — The Stinespring/isometry decomposition of the partial trace -/

/-- **The triple product entry**: `(Wₜᴴ B Wₜ) i j = B (lse (i,t)) (lse (j,t))`. -/
theorem Winj_mul_apply (n : ℕ) (t : Fin 3)
    (B : Matrix (Fin (3^(n+1))) (Fin (3^(n+1))) ℂ) (i j : Fin (3^n)) :
    ((Winj n t)ᴴ * B * Winj n t) i j =
      B (levelStepEquiv n (i, t)) (levelStepEquiv n (j, t)) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (levelStepEquiv n (j, t))]
  · rw [Winj_apply, if_pos rfl, mul_one, Matrix.mul_apply,
        Finset.sum_eq_single (levelStepEquiv n (i, t))]
    · rw [Winj_conjTranspose_apply, if_pos rfl, one_mul]
    · intro p _ hp
      rw [Winj_conjTranspose_apply, if_neg hp, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro q _ hq
    rw [Winj_apply, if_neg hq, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **★ The partial trace as an averaged isometric compression ★**
    `E B = (1/3) Σ_t Wₜᴴ B Wₜ`. -/
theorem partialTraceStep_eq_smul_sum (n : ℕ)
    (B : Matrix (Fin (3^(n+1))) (Fin (3^(n+1))) ℂ) :
    partialTraceStep n B =
      (3⁻¹ : ℂ) • ∑ t : Fin 3, (Winj n t)ᴴ * B * Winj n t := by
  ext i j
  rw [partialTraceStep_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply]
  congr 1
  exact Finset.sum_congr rfl (fun t _ => (Winj_mul_apply n t B i j).symm)

/-! ## §3 — The isometry has operator norm ≤ 1 -/

/-- **`‖Wₜ‖² ≤ 1`** — from `Wₜᴴ Wₜ = 1`, the C*-identity, and `‖id‖ ≤ 1`. -/
theorem Winj_opNorm_sq_le_one (n : ℕ) (t : Fin 3) :
    ‖Winj n t‖ * ‖Winj n t‖ ≤ 1 := by
  rw [← Matrix.l2_opNorm_conjTranspose_mul_self, Winj_conjTranspose_mul_self,
      Matrix.cstar_norm_def, map_one, ContinuousLinearMap.one_def]
  exact ContinuousLinearMap.norm_id_le

/-! ## §4 — ★★★ r111 THE OPERATOR-NORM CONTRACTION ★★★ -/

/-- **★★★ r111 — THE LAST LEMMA ★★★**
    The single-step base-3 partial trace is an L²-operator-norm contraction:
    `‖partialTraceStep n B‖ ≤ ‖B‖`. -/
theorem partialTraceStep_opNorm_le (n : ℕ)
    (B : Matrix (Fin (3^(n+1))) (Fin (3^(n+1))) ℂ) :
    ‖partialTraceStep n B‖ ≤ ‖B‖ := by
  -- Each averaged term is a contraction.
  have term_bound : ∀ t : Fin 3,
      ‖(Winj n t)ᴴ * B * Winj n t‖ ≤ ‖B‖ := by
    intro t
    calc ‖(Winj n t)ᴴ * B * Winj n t‖
        ≤ ‖(Winj n t)ᴴ * B‖ * ‖Winj n t‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ ‖(Winj n t)ᴴ‖ * ‖B‖ * ‖Winj n t‖ := by
            gcongr; exact Matrix.l2_opNorm_mul _ _
      _ = ‖Winj n t‖ * ‖Winj n t‖ * ‖B‖ := by
            rw [Matrix.l2_opNorm_conjTranspose]; ring
      _ ≤ 1 * ‖B‖ := by gcongr; exact Winj_opNorm_sq_le_one n t
      _ = ‖B‖ := one_mul _
  have hnorm3 : ‖(3⁻¹ : ℂ)‖ = 3⁻¹ := by
    rw [norm_inv]; norm_num
  rw [partialTraceStep_eq_smul_sum, norm_smul]
  calc ‖(3⁻¹ : ℂ)‖ * ‖∑ t : Fin 3, (Winj n t)ᴴ * B * Winj n t‖
      ≤ ‖(3⁻¹ : ℂ)‖ * ∑ t : Fin 3, ‖(Winj n t)ᴴ * B * Winj n t‖ := by
        gcongr; exact norm_sum_le _ _
    _ ≤ ‖(3⁻¹ : ℂ)‖ * ∑ _t : Fin 3, ‖B‖ := by
        gcongr with t; exact term_bound t
    _ = ‖B‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hnorm3, nsmul_eq_mul]
        push_cast
        rw [← mul_assoc]
        norm_num

/-! ## §5 — Discharging the r110 residual `PartialTraceStepOpNormContraction` -/

/-- **★★★ r111 — `PartialTraceStepOpNormContraction` IS A THEOREM ★★★**
    The r110-named operator-norm residual is discharged unconditionally: it
    is exactly `partialTraceStep_opNorm_le` universally quantified. -/
theorem partialTraceStepOpNormContraction_holds :
    PartialTraceStepOpNormContraction :=
  partialTraceStep_opNorm_le

/-! ## §6 — Iterating: the operator-norm contraction of `partialTraceDown` -/

/-- **The iterated partial trace is an operator-norm contraction.** -/
theorem partialTraceDown_opNorm_le (k : ℕ) :
    ∀ (j : ℕ) (h : k ≤ j) (B : Matrix (Fin (3^j)) (Fin (3^j)) ℂ),
    ‖partialTraceDown k j h B‖ ≤ ‖B‖ := by
  intro j h
  induction j, h using Nat.le_induction with
  | base =>
    intro B
    rw [partialTraceDown_self]
    exact le_of_eq rfl
  | succ n hn ih =>
    intro B
    rw [partialTraceDown_succ_apply k n hn (Nat.le_succ_of_le hn)]
    exact le_trans (ih (partialTraceStep n B)) (partialTraceStep_opNorm_le n B)

/-! ## §6b — Descending to `condExp`: `E_k` is a norm-1 map on `T∞` -/

/-- **★ `E_k` is a `‖·‖`-contraction on `T∞` ★**
    `‖condExp k x‖ ≤ ‖x‖`, where both norms are the actual completion-tier
    norm (the level-wise L²-operator norm the `TimelessFieldRing` norm is
    built from). For `k ≤ m` this is `partialTraceDown_opNorm_le`; for
    `m ≤ k` it is the embedding isometry (equality). This is the norm-1
    property of the conditional expectation — the load-bearing input for the
    uniform-continuity extension `CondExpCompletionExtension`. -/
theorem condExp_opNorm_le (k : ℕ) (x : TimelessFieldRing) :
    ‖condExp k x‖ ≤ ‖x‖ := by
  obtain ⟨m, A, rfl⟩ := DirectLimit.exists_eq_mk
    (fun i j (h : i ≤ j) => substrateRingHomIter i j h) x
  rw [condExp_of_level]
  have hx : ‖(⟦⟨m, A⟩⟧ : TimelessFieldRing)‖ = ‖A‖ := rfl
  rw [hx]
  by_cases hkm : k ≤ m
  · rw [levelToLevelK_of_le k m hkm]
    exact partialTraceDown_opNorm_le k m hkm A
  · have hmk : m ≤ k := le_of_not_ge hkm
    rw [levelToLevelK_of_ge k m hmk, substrateRingHomIter_opNorm_eq m k hmk A]

/-! ## §7 — r111 capstone -/

/-- **★★★ r111 SUBSTRATE PARTIAL-TRACE OPERATOR-NORM CONTRACTION
    CAPSTONE ★★★**

    **LANDED (unconditional, kernel-only):**

      (a) `Winj_conjTranspose_mul_self` — the coordinate injection `Wₜ` is
          an isometry (`Wₜᴴ Wₜ = 1`).
      (b) `partialTraceStep_eq_smul_sum` — the Stinespring decomposition
          `E B = (1/3) Σ_t Wₜᴴ B Wₜ`.
      (c) `Winj_opNorm_sq_le_one` — `‖Wₜ‖² ≤ 1` via the C*-identity.
      (d) `partialTraceStep_opNorm_le` — **THE LAST LEMMA**: the single-step
          L²-operator-norm contraction `‖E B‖ ≤ ‖B‖`.
      (e) `partialTraceStepOpNormContraction_holds` — discharges the r110
          residual `PartialTraceStepOpNormContraction` (definitionally).
      (f) `partialTraceDown_opNorm_le` — its iterate over the gap.

    **STATUS OF THE SUMMIT.**

    r111 removes the last *analytic* wall: the operator-norm contraction of
    the partial trace, which r110 isolated as the one lemma "not reachable
    elementarily". Together with r110's 2-norm contraction and r109's
    algebraic keystone, the conditional expectation `E_k : T∞ → M_{3^k}` is
    now known to be a norm-1 (contractive) *-linear map, trace-preserving,
    and identity on the level-`k` corner — all unconditional.

    The remaining step to completion faithfulness (r109 residual (3)
    `CondExpCompletionExtension`) is the completion-side PACKAGING:
    assembling `partialTraceDown_opNorm_le` into `UniformContinuous (E k)`
    on `TimelessFieldRing`, extending along the dense embedding into
    `TimelessFieldCompletion`, and proving `ι_k(Ê_k x) → x` from the
    identity-on-levels property. That is a uniform-space/density argument,
    no longer an analytic obstruction — the mountain from r108 has been
    reduced to its foothills.

    Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
    axioms. Zero sorries. -/
theorem r111_substrate_partial_trace_opnorm_capstone :
    -- (d) single-step operator-norm contraction
    (∀ (n : ℕ) (B : Matrix (Fin (3^(n+1))) (Fin (3^(n+1))) ℂ),
      ‖partialTraceStep n B‖ ≤ ‖B‖) ∧
    -- (e) r110 residual discharged
    PartialTraceStepOpNormContraction ∧
    -- (f) iterated operator-norm contraction
    (∀ (k j : ℕ) (h : k ≤ j) (B : Matrix (Fin (3^j)) (Fin (3^j)) ℂ),
      ‖partialTraceDown k j h B‖ ≤ ‖B‖) ∧
    -- (g) E_k is a norm-1 map on T∞ (the completion-tier norm)
    (∀ (k : ℕ) (x : TimelessFieldRing), ‖condExp k x‖ ≤ ‖x‖) :=
  ⟨partialTraceStep_opNorm_le,
   partialTraceStepOpNormContraction_holds,
   fun k j h B => partialTraceDown_opNorm_le k j h B,
   condExp_opNorm_le⟩

/-! ## §8 — Axiom audit -/

#print axioms Winj_conjTranspose_mul_self
#print axioms partialTraceStep_eq_smul_sum
#print axioms Winj_opNorm_sq_le_one
#print axioms partialTraceStep_opNorm_le
#print axioms partialTraceStepOpNormContraction_holds
#print axioms partialTraceDown_opNorm_le
#print axioms condExp_opNorm_le
#print axioms r111_substrate_partial_trace_opnorm_capstone

end SubstrateCondExpOpNorm
end PrincipiaTractalis
