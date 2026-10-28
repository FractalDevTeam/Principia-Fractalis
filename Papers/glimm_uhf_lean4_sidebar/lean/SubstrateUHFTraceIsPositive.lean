/-
# r98: The substrate UHF trace is POSITIVE: τ_UHF(x* · x) ≥ 0

★ 2026-07-08 r98 — the substrate UHF trace as a full POSITIVE
Hermitian tracial STATE on the substrate UHF C*-algebra ★

## The framework-first content

r87 delivered τ_UHF as additive + unital + 1-Lipschitz + UC on
`TimelessFieldCompletion`; r94 upgraded τ_UHF to a tracial state;
r96 upgraded τ_UHF to a Hermitian tracial state via star-preservation.
r98 completes the last essential structural property of a C*-algebra
state:

    τ_UHF(x* · x) ≥ 0   for every x : TimelessFieldCompletion.

Combined with r87 (additive + unital + 1-Lipschitz + UC), r94 (tracial),
and r96 (star-preserving), r98 makes τ_UHF a genuine
**tracial state on the substrate UHF C*-algebra** in the full operator-
algebra sense:

  * ℂ-linear (r87)
  * unital τ_UHF(1) = 1 (r87)
  * 1-Lipschitz + uniformly continuous (r87)
  * tracial τ_UHF(x·y) = τ_UHF(y·x) (r94)
  * star-preserving τ_UHF(x*) = conj(τ_UHF(x)) (r96)
  * **POSITIVE τ_UHF(x*·x) ≥ 0 (r98)**

A positive Hermitian tracial state on a unital C*-algebra is the
essential canonical object of tracial-state theory — the substrate
Dixmier tracial state on the substrate UHF C*-algebra
`TimelessFieldCompletion`.

## Three-tier chain

  (P1) Level-k: `normalized_matrix_trace(star M * M) ≥ 0` via mathlib's
       `Matrix.posSemidef_conjTranspose_mul_self` +
       `Matrix.PosSemidef.trace_nonneg` + `ne_zero_of_lt` +
       `div_nonneg` in the ComplexOrder.

  (P2) Pre-trace on `TimelessFieldRing`:
       `substrate_pre_trace(star x * x) ≥ 0` via
       `DirectLimit.exists_eq_mk` reducing to single-level +
       `substrate_quotient_star_same_level` + `substrate_quotient_mul_same_level`
       + P1.

  (P3) UHF trace on `TimelessFieldCompletion`:
       `UHF_trace(star x * x) ≥ 0` via
       `UniformSpace.Completion.induction_on` on the closed set
       (`OrderClosedTopology ℂ` under `ComplexOrder` gives `isClosed_le`
       for continuous functions; both sides continuous — LHS `const 0`,
       RHS = `UHF_trace ∘ (fun x => star x * x)` continuous via
       r54 continuous_star + continuous multiplication + r87 UC) with
       dense-image reduction via `star_coe_TimelessFieldCompletion` +
       `UniformSpace.Completion.coe_mul` + `UHF_trace_coe` + P2.

Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
axioms. Zero sorries.

Stage 2026-07-08 r98 — substrate UHF trace POSITIVITY completing the
substrate UHF C*-algebra tracial state.
-/

import PF.SubstrateUHFTraceIsStarPreserving
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace SubstrateUHFTraceIsPositive

open scoped Matrix.Norms.L2Operator
open scoped ComplexOrder
open SubstrateUHFBoundedTrace SubstrateUHFTraceLipschitz
open SubstrateUHFCompletionTrace SubstrateUHFPreTraceDirectLimit
open SubstrateUHFTraceIsTracial SubstrateUHFTraceIsStarPreserving
open SubstrateDirectLimit SubstrateTimelessFieldCompletion

/-! ## §1 — Level-k matrix trace is positive on star M * M -/

/-- **r98.a: normalized matrix trace is positive on `star M * M`**
    at every substrate finite level:
    `0 ≤ τ_n(star M * M) = τ_n(Mᴴ · M)` (in the ComplexOrder).

    Follows from mathlib's `Matrix.posSemidef_conjTranspose_mul_self`
    (Mᴴ · M is positive semidefinite) + `Matrix.PosSemidef.trace_nonneg`
    (trace of PSD matrix is ≥ 0) + division by the positive natural n. -/
theorem normalized_matrix_trace_star_mul_self_nonneg {n : ℕ} [NeZero n]
    (M : Matrix (Fin n) (Fin n) ℂ) :
    0 ≤ normalized_matrix_trace (star M * M) := by
  show 0 ≤ Matrix.trace (star M * M) / (n : ℂ)
  have h_PSD : Matrix.PosSemidef (star M * M) := by
    show Matrix.PosSemidef (Matrix.conjTranspose M * M)
    exact Matrix.posSemidef_conjTranspose_mul_self M
  have h_trace_nn : 0 ≤ Matrix.trace (star M * M) := h_PSD.trace_nonneg
  have h_n_pos : (0 : ℂ) < (n : ℂ) := by
    have hn_nat : 0 < (n : ℕ) := Nat.pos_of_ne_zero (NeZero.ne n)
    exact_mod_cast hn_nat
  exact div_nonneg h_trace_nn (le_of_lt h_n_pos)

/-! ## §2 — Substrate pre-trace on TimelessFieldRing is positive -/

/-- **r98.b: substrate pre-trace on TimelessFieldRing is positive
    on `star x * x`**:
    `0 ≤ substrate_pre_trace(star x * x)` for every x : TimelessFieldRing.

    Proof: reduce x to a single-level representative via
    `DirectLimit.exists_eq_mk`; use `substrate_quotient_star_same_level`
    + `substrate_quotient_mul_same_level` to reduce to
    `⟦(k, star A * A)⟧`; substitute via `substrate_pre_trace_of_level`;
    apply r98.a. -/
theorem substrate_pre_trace_star_mul_self_nonneg (x : TimelessFieldRing) :
    0 ≤ substrate_pre_trace (star x * x) := by
  obtain ⟨k, A, hxA⟩ :=
    DirectLimit.exists_eq_mk
      (fun i j (h : i ≤ j) => substrateRingHomIter i j h) x
  subst hxA
  rw [substrate_quotient_star_same_level k A,
      substrate_quotient_mul_same_level k (star A) A,
      substrate_pre_trace_of_level]
  exact normalized_matrix_trace_star_mul_self_nonneg A

/-! ## §3 — Substrate UHF trace on TimelessFieldCompletion is positive -/

/-- **★★★ r98.c: THE SUBSTRATE UHF TRACE IS POSITIVE ★★★**

    `0 ≤ UHF_trace(star x * x)` for every x : TimelessFieldCompletion,
    in the ComplexOrder.

    Proof: `UniformSpace.Completion.induction_on` on the closed set
    S := {x : 0 ≤ UHF_trace(star x * x)}. Under `open scoped ComplexOrder`,
    the instance `Complex.orderClosedTopology : OrderClosedTopology ℂ`
    gives `isClosed_le` for continuous functions:
      * const 0 : TFC → ℂ is continuous
      * `x ↦ UHF_trace(star x * x) : TFC → ℂ` is continuous via
        - r54 `continuous_star_TimelessFieldCompletion` (star continuous)
        - continuous multiplication on the completion (r53 NormedRing)
        - r87 `UHF_trace_uniformContinuous` (τ_UHF continuous)
      So S is closed.
    Dense-image reduction: for a : TimelessFieldRing,
      UHF_trace(star (↑a) * (↑a)) = UHF_trace(↑(star a) * ↑a)  via star_coe
        = UHF_trace(↑(star a * a))                             via coe_mul
        = substrate_pre_trace(star a * a)                      via UHF_trace_coe
        ≥ 0                                                     via r98.b. -/
theorem UHF_trace_star_mul_self_nonneg (x : TimelessFieldCompletion) :
    0 ≤ UHF_trace (star x * x) := by
  refine UniformSpace.Completion.induction_on x
    (p := fun x => 0 ≤ UHF_trace (star x * x)) ?_ ?_
  · -- Closed set: OrderClosedTopology ℂ + continuous composition.
    have h_cont : Continuous
        (fun x : TimelessFieldCompletion => UHF_trace (star x * x)) :=
      UHF_trace_uniformContinuous.continuous.comp
        (continuous_mul.comp
          (continuous_star_TimelessFieldCompletion.prodMk continuous_id))
    exact isClosed_le continuous_const h_cont
  · -- Dense image reduction.
    intro a
    rw [star_coe_TimelessFieldCompletion,
        ← UniformSpace.Completion.coe_mul,
        UHF_trace_coe]
    exact substrate_pre_trace_star_mul_self_nonneg a

/-! ## §4 — r98 capstone -/

/-- **★★★ r98 SUBSTRATE UHF TRACE POSITIVITY CAPSTONE ★★★**

    Bundles the r98 substrate positivity content across all three
    tiers of the substrate UHF trace construction:

      (P1) `normalized_matrix_trace_star_mul_self_nonneg` — level-k
           positivity via `Matrix.posSemidef_conjTranspose_mul_self` +
           `Matrix.PosSemidef.trace_nonneg`.
      (P2) `substrate_pre_trace_star_mul_self_nonneg` — pre-trace
           positivity on `TimelessFieldRing`.
      (P3) **`UHF_trace_star_mul_self_nonneg`** — **THE UHF TRACE IS
           POSITIVE** on `TimelessFieldCompletion` via
           `UniformSpace.Completion.induction_on` + `OrderClosedTopology ℂ`
           + `isClosed_le` with continuous composition of star and
           multiplication and τ_UHF.

    Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
    axioms. Zero sorries.

    Substrate significance: r98 upgrades τ_UHF from a "Hermitian tracial
    state" (r94 + r96) to a full POSITIVE HERMITIAN TRACIAL STATE on
    the substrate UHF C*-algebra — the essential canonical object of
    tracial-state theory. Combined with r87 (linear + unital + 1-Lipschitz
    + UC), r89 (spectral-bridge closure τ(ι_2(E_ii))=1/9), r90 + r92
    (explicit closed-form α/λ-skeleton spectral outputs), r94 (tracial),
    r96 (star-preserving), r98 completes the substrate UHF trace as
    THE canonical substrate Dixmier tracial state on
    `TimelessFieldCompletion`. -/
theorem r98_substrate_UHF_trace_positive_capstone :
    (∀ {n : ℕ} [NeZero n] (M : Matrix (Fin n) (Fin n) ℂ),
      0 ≤ normalized_matrix_trace (star M * M)) ∧
    (∀ x : TimelessFieldRing,
      0 ≤ substrate_pre_trace (star x * x)) ∧
    (∀ x : TimelessFieldCompletion,
      0 ≤ UHF_trace (star x * x)) :=
  ⟨fun {_} _ M => normalized_matrix_trace_star_mul_self_nonneg M,
   substrate_pre_trace_star_mul_self_nonneg,
   UHF_trace_star_mul_self_nonneg⟩

end SubstrateUHFTraceIsPositive
end PrincipiaTractalis
