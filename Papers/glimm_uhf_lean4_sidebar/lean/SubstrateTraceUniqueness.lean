/-
# r113: UNIQUENESS of the substrate UHF tracial state — the Glimm 3^∞ capstone.

★ 2026-07-24 r113 — the substrate UHF trace `τ_UHF` is the UNIQUE tracial state
on `T∞ = TimelessFieldCompletion`. Combined with r112's completion-tier
FAITHFULNESS and C*-SIMPLICITY, this completes the identification of `T∞` as the
Glimm `3^∞` UHF factor. ★

## Mathematical route (the standard UHF unique-trace argument)

A tracial state on a UHF algebra is unique because it is determined on each
matrix level by the normalized matrix trace (the unique tracial state on
`M_n(ℂ)`), and the levels are dense.

  1. `IsTracialState φ` — the honest, MINIMAL hypothesis set: `φ` is continuous,
     additive, ℂ-homogeneous, unital (`φ 1 = 1`), and tracial (`φ(xy)=φ(yx)`).
     POSITIVITY IS NOT REQUIRED — uniqueness holds for every continuous unital
     ℂ-linear tracial functional (the commutator/basis argument uses only
     linearity + the trace property + unitality).

  2. `matrix_tracial_state_unique` — the finite-dimensional keystone: on
     `M_n(ℂ)`, any additive + ℂ-homogeneous + tracial φ with `φ 1 = 1` equals
     the normalized matrix trace. Proof: `φ(single i j 1) = 0` for `i≠j` (it is a
     commutator killed by the trace property), all diagonal `φ(single i i 1)` are
     equal (`E_ii = E_ij E_ji`, `E_jj = E_ji E_ij`, cyclic), so
     `φ M = φ(single 0 0 1) · trace M`; feeding `M = 1` and `φ 1 = 1` forces the
     constant to be `1/n`.

  3. `tracialState_coe_level` — lift: `φ ∘ (↑ ∘ ι_k)` is an additive +
     ℂ-homogeneous + tracial + unital functional on `M_{3^k}`, hence equals the
     normalized matrix trace there = `τ_UHF` on the level image.

  4. `substrate_UHF_trace_unique` — density lift: `φ` and `τ_UHF` are continuous
     and agree on the dense direct-limit image `↑ ∘ ι_k`, so `φ = τ_UHF`
     everywhere (`Completion.induction_on` + `isClosed_eq`, exactly as r112).

  5. `r113_substrate_UHF_factor_capstone` — `T∞` is faithful (r112) + simple
     (r112) + uniquely-traced (this) : the Glimm `3^∞` UHF factor.

Kernel-only [propext, Classical.choice, Quot.sound]. Zero project axioms. Zero
sorries.

Stage 2026-07-24 r113 — uniqueness of the substrate UHF tracial state.
-/

import PF.SubstrateCompletionFaithful
import PF.SubstrateUHFTraceIsTracial
import PF.SubstrateUHFTraceCauchySchwarz
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace SubstrateTraceUniqueness

open scoped Matrix.Norms.L2Operator
open scoped ComplexOrder
open Matrix
open SubstrateBase3Embed SubstrateDirectLimit
open SubstrateTimelessFieldNorm SubstrateTimelessFieldCompletion
open SubstrateUHFBoundedTrace SubstrateUHFPreTraceDirectLimit
open SubstrateUHFTraceIsTracial SubstrateUHFTraceCauchySchwarz
open SubstrateCompletionFaithful

/-! ## §1 — The finite-dimensional keystone: the normalized matrix trace is the
    unique additive + ℂ-homogeneous + unital tracial functional on `M_n(ℂ)`. -/

/-- **★ r113.a — FINITE-DIMENSIONAL UNIQUENESS ★**

    On `M_n(ℂ)` (`n ≥ 1`), any function `φ` that is additive, ℂ-homogeneous,
    tracial (`φ(AB)=φ(BA)`) and unital (`φ 1 = 1`) coincides with the normalized
    matrix trace. No positivity is needed.

    Proof outline: `M_n(ℂ)` is spanned by the identity and commutators;
    `trace` kills commutators, so `φ M = φ(single 0 0 1) · trace M`, and unitality
    pins the constant to `1/n`. -/
theorem matrix_tracial_state_unique {n : ℕ} [NeZero n]
    (φ : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hadd : ∀ A B, φ (A + B) = φ A + φ B)
    (hsmul : ∀ (c : ℂ) A, φ (c • A) = c * φ A)
    (htr : ∀ A B, φ (A * B) = φ (B * A))
    (hone : φ 1 = 1)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    φ M = normalized_matrix_trace M := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  set i0 : Fin n := ⟨0, hnpos⟩ with hi0
  -- φ 0 = 0.
  have hφ0 : φ 0 = 0 := by
    have h := hsmul 0 0
    rwa [zero_smul, zero_mul] at h
  -- AddMonoidHom bundle, for `map_sum`.
  set Φ : Matrix (Fin n) (Fin n) ℂ →+ ℂ := AddMonoidHom.mk' φ hadd with hΦ
  have hΦφ : ∀ A, Φ A = φ A := fun _ => rfl
  -- Off-diagonal single vanishes (it is a commutator killed by the trace).
  have hoff : ∀ i j : Fin n, i ≠ j → φ (single i j (1 : ℂ)) = 0 := by
    intro i j hij
    have e1 : single i j (1 : ℂ) = single i j (1 : ℂ) * single j j (1 : ℂ) := by
      rw [single_mul_single_same, mul_one]
    have e2 : single j j (1 : ℂ) * single i j (1 : ℂ) = 0 :=
      single_mul_single_of_ne (1 : ℂ) j j i (Ne.symm hij) (1 : ℂ)
    calc φ (single i j (1 : ℂ))
        = φ (single i j (1 : ℂ) * single j j (1 : ℂ)) := by rw [← e1]
      _ = φ (single j j (1 : ℂ) * single i j (1 : ℂ)) := htr _ _
      _ = φ 0 := by rw [e2]
      _ = 0 := hφ0
  -- Diagonal singles are all equal (cyclic invariance).
  have hdiag : ∀ i j : Fin n,
      φ (single i i (1 : ℂ)) = φ (single j j (1 : ℂ)) := by
    intro i j
    have e1 : single i i (1 : ℂ) = single i j (1 : ℂ) * single j i (1 : ℂ) := by
      rw [single_mul_single_same, mul_one]
    have e2 : single j j (1 : ℂ) = single j i (1 : ℂ) * single i j (1 : ℂ) := by
      rw [single_mul_single_same, mul_one]
    rw [e1, e2]
    exact htr _ _
  -- The common diagonal value.
  set d : ℂ := φ (single i0 i0 (1 : ℂ)) with hd
  -- Key reduction: `φ N = d · trace N` for all N.
  have hkey : ∀ N : Matrix (Fin n) (Fin n) ℂ, φ N = d * Matrix.trace N := by
    intro N
    have hsum : φ N = ∑ i, ∑ j, (N i j) * φ (single i j (1 : ℂ)) := by
      conv_lhs => rw [matrix_eq_sum_single N]
      rw [← hΦφ, map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hΦφ]
      have hone_smul : single i j (N i j) = (N i j) • single i j (1 : ℂ) := by
        rw [smul_single, smul_eq_mul, mul_one]
      rw [hone_smul, hsmul]
    rw [hsum]
    -- Collapse the inner sum: only `j = i` survives.
    have hcollapse : ∀ i : Fin n,
        (∑ j, (N i j) * φ (single i j (1 : ℂ))) = (N i i) * d := by
      intro i
      have hsingle :=
        Finset.sum_eq_single (s := (Finset.univ : Finset (Fin n)))
          (f := fun j => (N i j) * φ (single i j (1 : ℂ))) i
          (fun b _ hbi => by dsimp only; rw [hoff i b (Ne.symm hbi), mul_zero])
          (fun h => absurd (Finset.mem_univ i) h)
      rw [hsingle]
      dsimp only
      rw [hdiag i i0, ← hd]
    rw [Finset.sum_congr rfl (fun i _ => hcollapse i), ← Finset.sum_mul]
    have htr_eq : Matrix.trace N = ∑ i, N i i := rfl
    rw [htr_eq, mul_comm]
  -- Pin the constant via unitality: `d · n = 1`.
  have hd_val : d * (n : ℂ) = 1 := by
    have h1 := hkey 1
    rw [hone, Matrix.trace_one, Fintype.card_fin] at h1
    exact h1.symm
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have hd_eq : d = 1 / (n : ℂ) := (eq_div_iff hn).mpr hd_val
  rw [hkey M]
  show d * Matrix.trace M = Matrix.trace M / (n : ℂ)
  rw [hd_eq]; ring

/-! ## §2 — The tracial-state predicate on the completion. -/

/-- **`IsTracialState φ`** — the honest MINIMAL hypothesis set for a tracial state
    on `T∞ = TimelessFieldCompletion`: continuous, additive, ℂ-homogeneous,
    unital, and tracial. Positivity is deliberately omitted: uniqueness holds for
    every continuous unital ℂ-linear tracial functional. -/
structure IsTracialState (φ : TimelessFieldCompletion → ℂ) : Prop where
  continuous : Continuous φ
  add : ∀ x y, φ (x + y) = φ x + φ y
  smul : ∀ (c : ℂ) x, φ (c • x) = c * φ x
  tracial : ∀ x y, φ (x * y) = φ (y * x)
  unital : φ 1 = 1

/-! ## §3 — Level lift: a tracial state is the normalized matrix trace on each
    finite level. -/

/-- **★ r113.b — LEVEL DETERMINATION ★**

    For any tracial state `φ` on `T∞`, its value on the coerced level image
    `↑(ι_k A)` is the normalized matrix trace of `A`. This is the finite-dim
    keystone applied to `ψ_k A := φ (↑(ι_k A))`, which inherits additivity,
    ℂ-homogeneity, traciality and unitality from `φ` through the level
    embedding + completion coercion. -/
theorem tracialState_coe_level (φ : TimelessFieldCompletion → ℂ)
    (hφ : IsTracialState φ) (k : ℕ)
    (A : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    φ ((substrateLevelToTimelessField k A : TimelessFieldRing) :
        TimelessFieldCompletion) = normalized_matrix_trace A := by
  haveI : NeZero (3^k) := ⟨pow_ne_zero k (by norm_num)⟩
  refine matrix_tracial_state_unique
    (fun B => φ ((substrateLevelToTimelessField k B : TimelessFieldRing) :
        TimelessFieldCompletion)) ?_ ?_ ?_ ?_ A
  · -- additive
    intro B C
    dsimp only
    rw [show (substrateLevelToTimelessField k (B + C) : TimelessFieldRing)
          = substrateLevelToTimelessField k B + substrateLevelToTimelessField k C
        from (substrate_quotient_add_same_level k B C).symm,
        UniformSpace.Completion.coe_add, hφ.add]
  · -- ℂ-homogeneous
    intro c B
    dsimp only
    rw [show (substrateLevelToTimelessField k (c • B) : TimelessFieldRing)
          = c • substrateLevelToTimelessField k B
        from (substrate_quotient_smul_same_level c k B).symm,
        UniformSpace.Completion.coe_smul, hφ.smul]
  · -- tracial
    intro B C
    dsimp only
    rw [show (substrateLevelToTimelessField k (B * C) : TimelessFieldRing)
          = substrateLevelToTimelessField k B * substrateLevelToTimelessField k C
        from (substrate_quotient_mul_same_level k B C).symm,
        show (substrateLevelToTimelessField k (C * B) : TimelessFieldRing)
          = substrateLevelToTimelessField k C * substrateLevelToTimelessField k B
        from (substrate_quotient_mul_same_level k C B).symm,
        UniformSpace.Completion.coe_mul, UniformSpace.Completion.coe_mul]
    exact hφ.tracial _ _
  · -- unital
    dsimp only
    have hone_level : (substrateLevelToTimelessField k 1 : TimelessFieldRing) = 1 := by
      have hiter := substrateLevelToTimelessField_iter 0 k (Nat.zero_le k)
        (1 : Matrix (Fin (3^0)) (Fin (3^0)) ℂ)
      rw [map_one] at hiter
      rw [hiter]
      exact (DirectLimit.one_def
        (G := fun k : ℕ => Matrix (Fin (3^k)) (Fin (3^k)) ℂ)
        (f := fun i j (h : i ≤ j) => substrateRingHomIter i j h) 0).symm
    rw [hone_level, UniformSpace.Completion.coe_one, hφ.unital]

/-! ## §4 — The uniqueness theorem: density lift. -/

/-- **★★★ r113.c — UNIQUENESS OF THE SUBSTRATE UHF TRACIAL STATE ★★★**

    Any tracial state `φ` on `T∞ = TimelessFieldCompletion` coincides with the
    canonical substrate UHF trace `τ_UHF = UHF_trace`:

        `∀ x, φ x = UHF_trace x`.

    Proof: `φ` and `UHF_trace` are continuous and agree on the dense direct-limit
    image `↑(ι_k A)` (r113.b + `substrate_pre_trace_of_level` + `UHF_trace_coe`),
    hence agree everywhere by `Completion.induction_on` + `isClosed_eq`. -/
theorem substrate_UHF_trace_unique (φ : TimelessFieldCompletion → ℂ)
    (hφ : IsTracialState φ) (x : TimelessFieldCompletion) :
    φ x = UHF_trace x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq hφ.continuous UHF_trace_uniformContinuous.continuous
  | ih a =>
    obtain ⟨k, A, rfl⟩ :=
      DirectLimit.exists_eq_mk
        (fun i j (h : i ≤ j) => substrateRingHomIter i j h) a
    rw [UHF_trace_coe]
    exact (tracialState_coe_level φ hφ k A).trans
      (substrate_pre_trace_of_level k A).symm

/-! ## §5 — The canonical trace IS a tracial state (non-vacuity). -/

/-- **r113.d — `UHF_trace` is itself a tracial state**, so the uniqueness
    statement is non-vacuous: the class of tracial states on `T∞` is exactly
    `{UHF_trace}`. Bundles r87 (UC) + r102 (add/smul) + r94 (tracial) + unitality. -/
theorem uhf_trace_isTracialState : IsTracialState UHF_trace where
  continuous := UHF_trace_uniformContinuous.continuous
  add := UHF_trace_add
  smul := UHF_trace_smul
  tracial := UHF_trace_mul_comm
  unital := by
    rw [← UniformSpace.Completion.coe_one, UHF_trace_coe, substrate_pre_trace_one]

/-! ## §6 — r113 capstone: T∞ is the Glimm 3^∞ UHF factor. -/

/-- **★★★ r113 GLIMM 3^∞ UHF FACTOR CAPSTONE ★★★**

    The substrate spectral-bridge algebra `T∞ = TimelessFieldCompletion` is the
    Glimm `3^∞` UHF factor:

      (G1) **UNIQUE TRACE** — every tracial state on `T∞` equals `τ_UHF`
           (r113, this file); and `τ_UHF` is a tracial state (non-vacuity).
      (G2) **FAITHFUL** — `τ_UHF(x⋆x) = 0 → x = 0`  (r112 `UHF_trace_faithful`).
      (G3) **SIMPLE** — every two-sided ideal of `T∞` is `⊥` or `⊤`
           (r112 `substrate_completion_simple_unconditional`).

    A unital, simple C*-algebra with a unique tracial state that is faithful is
    (the norm closure of) a UHF algebra with a factor tracial state — the Glimm
    `3^∞` UHF factor.

    Kernel-only [propext, Classical.choice, Quot.sound]. Zero project axioms.
    Zero sorries. -/
theorem r113_substrate_UHF_factor_capstone :
    (∀ φ : TimelessFieldCompletion → ℂ, IsTracialState φ →
       ∀ x, φ x = UHF_trace x) ∧
    IsTracialState UHF_trace ∧
    (∀ x : TimelessFieldCompletion, UHF_trace (star x * x) = 0 → x = 0) ∧
    (∀ I : TwoSidedIdeal TimelessFieldCompletion, I = ⊥ ∨ I = ⊤) :=
  ⟨substrate_UHF_trace_unique,
   uhf_trace_isTracialState,
   UHF_trace_faithful,
   substrate_completion_simple_unconditional⟩

/-! ## §7 — Axiom audit. -/

#print axioms matrix_tracial_state_unique
#print axioms tracialState_coe_level
#print axioms substrate_UHF_trace_unique
#print axioms uhf_trace_isTracialState
#print axioms r113_substrate_UHF_factor_capstone

end SubstrateTraceUniqueness
end PrincipiaTractalis
