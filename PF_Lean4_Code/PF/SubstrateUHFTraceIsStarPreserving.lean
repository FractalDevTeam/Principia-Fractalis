/-
# r96: The substrate UHF trace is STAR-PRESERVING:
#      τ_UHF(x*) = star(τ_UHF(x)) = conj(τ_UHF(x))

★ 2026-07-08 r96 — substrate UHF trace as a *-preserving tracial state
on the substrate UHF C*-algebra ★

## The framework-first content

r87 delivered τ_UHF as additive + unital + 1-Lipschitz + UC on
`TimelessFieldCompletion`; r94 upgraded τ_UHF to a genuine tracial
state. r96 adds the third essential structural property of a
C*-algebra tracial state:

    τ_UHF(x*) = star(τ_UHF(x)) = conj(τ_UHF(x))

Combined with r87 (linear + unital + UC) and r94 (tracial), the
substrate UHF trace now satisfies:

  * ℂ-linear (additive + ℂ-scalar homogeneous — r87)
  * unital (τ_UHF(1) = 1 — r87)
  * 1-Lipschitz + uniformly continuous (r87)
  * tracial (τ_UHF(x·y) = τ_UHF(y·x) — r94)
  * **star-preserving** (τ_UHF(x*) = conj(τ_UHF(x)) — r96, this file)

This makes τ_UHF a Hermitian tracial state on the substrate UHF
C*-algebra — the essential structural character of an
operator-algebra state. In particular, τ_UHF sends self-adjoint
elements to real numbers: for `x* = x`, we have τ_UHF(x) = τ_UHF(x*)
= conj(τ_UHF(x)), so τ_UHF(x) ∈ ℝ.

## Three-tier chain

  (S1) Level-k: normalized_matrix_trace (star M) = star (τ_n(M))
       via mathlib's `Matrix.trace_conjTranspose` + division by
       real n (since `star (n : ℂ) = n` for `n : ℕ`).

  (S2) Pre-trace on TimelessFieldRing:
       substrate_pre_trace(star x) = star(substrate_pre_trace x)
       via `DirectLimit.exists_eq_mk` reducing to a single-level
       representative, `Quotient.map_mk` for the star action on the
       raw Quotient, and S1.

  (S3) UHF trace on TimelessFieldCompletion:
       UHF_trace(star x) = star(UHF_trace x)
       via `UniformSpace.Completion.induction_on` on the closed
       equality set — both sides continuous in x (LHS via
       continuous_star_TimelessFieldCompletion composed with UC of
       UHF_trace; RHS via UC of UHF_trace composed with continuous
       star on ℂ) — dense-image reduction via
       `star_coe_TimelessFieldCompletion` + `UHF_trace_coe` + S2.

Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
axioms. Zero sorries.

Stage 2026-07-08 r96 — substrate UHF trace star-preservation
completing the Hermitian tracial-state structure.
-/

import PF.SubstrateUHFTraceIsTracial
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace SubstrateUHFTraceIsStarPreserving

open scoped Matrix.Norms.L2Operator
open scoped ComplexOrder
open SubstrateUHFBoundedTrace SubstrateUHFTraceLipschitz
open SubstrateUHFCompletionTrace SubstrateUHFPreTraceDirectLimit
open SubstrateUHFTraceIsTracial
open SubstrateDirectLimit SubstrateTimelessFieldCompletion

/-! ## §1 — Level-k matrix trace is star-preserving -/

/-- **r96.a: normalized matrix trace is star-preserving at every
    substrate finite level**:
    `τ_n(star M) = star(τ_n M) = conj(τ_n M)`
    for `M : Matrix (Fin n) (Fin n) ℂ` with `[NeZero n]`.
    Follows from mathlib's `Matrix.trace_conjTranspose` plus
    `star_natCast` (since `star (n : ℂ) = n` for `n : ℕ`). -/
theorem normalized_matrix_trace_star {n : ℕ} [NeZero n]
    (M : Matrix (Fin n) (Fin n) ℂ) :
    normalized_matrix_trace (star M) =
      star (normalized_matrix_trace M) := by
  show (Matrix.trace (star M)) / (n : ℂ) = star ((Matrix.trace M) / (n : ℂ))
  show (Matrix.trace (Matrix.conjTranspose M)) / (n : ℂ) =
       star ((Matrix.trace M) / (n : ℂ))
  rw [Matrix.trace_conjTranspose, star_div₀]
  congr 1
  exact (star_natCast n).symm

/-! ## §2 — Substrate pre-trace on TimelessFieldRing is star-preserving -/

/-- **Auxiliary**: `star ⟦⟨k, A⟩⟧ = ⟦⟨k, star A⟩⟧` as a
    same-level identity on the raw substrate Quotient type,
    which is definitionally `TimelessFieldRing`. -/
theorem substrate_quotient_star_same_level (k : ℕ)
    (A : Matrix (Fin (3^k)) (Fin (3^k)) ℂ) :
    (star ((⟦⟨k, A⟩⟧ : TimelessFieldRing))) =
      ((⟦⟨k, star A⟩⟧ : TimelessFieldRing)) := by
  show Quotient.map substrate_sigma_star substrate_sigma_star_respects_setoid
    (⟦⟨k, A⟩⟧) = ⟦⟨k, star A⟩⟧
  rfl

/-- **r96.b: substrate pre-trace on TimelessFieldRing is
    star-preserving**:
    `substrate_pre_trace(star x) = star(substrate_pre_trace x)`.
    Proved via `DirectLimit.exists_eq_mk` reducing to a single-level
    representative + `substrate_quotient_star_same_level` +
    `substrate_pre_trace_of_level` + r96.a. -/
theorem substrate_pre_trace_star (x : TimelessFieldRing) :
    substrate_pre_trace (star x) = star (substrate_pre_trace x) := by
  obtain ⟨k, A, hxA⟩ :=
    DirectLimit.exists_eq_mk
      (fun i j (h : i ≤ j) => substrateRingHomIter i j h) x
  subst hxA
  rw [substrate_quotient_star_same_level k A,
      substrate_pre_trace_of_level, substrate_pre_trace_of_level]
  exact normalized_matrix_trace_star A

/-! ## §3 — Substrate UHF trace on TimelessFieldCompletion is
    star-preserving -/

/-- **★★★ r96.c: THE SUBSTRATE UHF TRACE IS STAR-PRESERVING ★★★**

    `UHF_trace(star x) = star(UHF_trace x) = conj(UHF_trace x)`
    for every `x : TimelessFieldCompletion`.

    Proof: `UniformSpace.Completion.induction_on` on the closed
    equality set. Both sides continuous in x:
      * LHS: `UHF_trace ∘ star` — star is continuous on
        TimelessFieldCompletion (from r54's continuous_star extension),
        UHF_trace is uniformly continuous (r87).
      * RHS: `star ∘ UHF_trace` — UHF_trace UC, star on ℂ is continuous.
    Dense-image reduction: for a : TimelessFieldRing,
      UHF_trace(star (↑a)) = UHF_trace(↑(star a))    via star_coe
        = substrate_pre_trace(star a)                 via UHF_trace_coe
        = star(substrate_pre_trace a)                 via r96.b
        = star(UHF_trace(↑a))                         via UHF_trace_coe. -/
theorem UHF_trace_star (x : TimelessFieldCompletion) :
    UHF_trace (star x) = star (UHF_trace x) := by
  refine UniformSpace.Completion.induction_on x
    (p := fun x => UHF_trace (star x) = star (UHF_trace x))
    ?_ ?_
  · -- Closed equality set.
    refine isClosed_eq ?_ ?_
    · exact UHF_trace_uniformContinuous.continuous.comp
        continuous_star_TimelessFieldCompletion
    · exact continuous_star.comp UHF_trace_uniformContinuous.continuous
  · -- Dense-image reduction.
    intro a
    rw [star_coe_TimelessFieldCompletion, UHF_trace_coe, UHF_trace_coe]
    exact substrate_pre_trace_star a

/-! ## §4 — Self-adjoint UHF-trace values are real -/

/-- **r96.d: self-adjoint UHF-trace values are real**.

    If `x* = x` (i.e., x is self-adjoint / Hermitian in the substrate
    UHF C*-algebra), then `UHF_trace(x) ∈ ℝ` (i.e., is a fixed point of
    the star operation on ℂ, equivalently has zero imaginary part). -/
theorem UHF_trace_self_adjoint (x : TimelessFieldCompletion) (h : star x = x) :
    star (UHF_trace x) = UHF_trace x := by
  rw [← UHF_trace_star, h]

/-! ## §5 — r96 capstone -/

/-- **★★★ r96 SUBSTRATE UHF TRACE STAR-PRESERVATION CAPSTONE ★★★**

    Bundles the r96 substrate star-preservation content:

      (S1) `normalized_matrix_trace_star` — level-k matrix
           star-preservation via `Matrix.trace_conjTranspose`.
      (S2) `substrate_quotient_star_same_level` — auxiliary
           same-level identity `star ⟦(k, A)⟧ = ⟦(k, star A)⟧` on
           the raw substrate Quotient.
      (S3) `substrate_pre_trace_star` — pre-trace star-preservation
           on TimelessFieldRing via `DirectLimit.exists_eq_mk` + S1.
      (S4) **`UHF_trace_star`** — **THE UHF TRACE IS STAR-PRESERVING**
           on TimelessFieldCompletion via `Completion.induction_on`
           + closed equality set with continuous star on both sides
           + `star_coe_TimelessFieldCompletion` + `UHF_trace_coe` + S3.
      (S5) `UHF_trace_self_adjoint` — corollary: self-adjoint substrate
           UHF C*-algebra elements have real UHF-trace values.

    Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
    axioms. Zero sorries.

    Substrate significance: r96 completes the essential structural
    character of τ_UHF as a Hermitian tracial state on the substrate
    UHF C*-algebra `TimelessFieldCompletion`. Combined with r87
    (additive + unital + 1-Lipschitz + UC), r94 (tracial), and r89 +
    r90 + r92 (explicit closed-form spectral outputs), the substrate
    UHF trace on `TimelessFieldCompletion` is now the complete
    operator-algebra Hermitian tracial state of the substrate ToE
    spectral bridge: linear + unital + UC + tracial + star-preserving,
    with explicit closed-form outputs on both substrate skeletons. -/
theorem r96_substrate_UHF_trace_star_preserving_capstone :
    (∀ {n : ℕ} [NeZero n] (M : Matrix (Fin n) (Fin n) ℂ),
      normalized_matrix_trace (star M) =
        star (normalized_matrix_trace M)) ∧
    (∀ (k : ℕ) (A : Matrix (Fin (3^k)) (Fin (3^k)) ℂ),
      star ((⟦⟨k, A⟩⟧ : TimelessFieldRing)) =
        (⟦⟨k, star A⟩⟧ : TimelessFieldRing)) ∧
    (∀ x : TimelessFieldRing,
      substrate_pre_trace (star x) = star (substrate_pre_trace x)) ∧
    (∀ x : TimelessFieldCompletion,
      UHF_trace (star x) = star (UHF_trace x)) ∧
    (∀ x : TimelessFieldCompletion, star x = x →
      star (UHF_trace x) = UHF_trace x) :=
  ⟨fun {_} _ M => normalized_matrix_trace_star M,
   substrate_quotient_star_same_level,
   substrate_pre_trace_star,
   UHF_trace_star,
   UHF_trace_self_adjoint⟩

end SubstrateUHFTraceIsStarPreserving
end PrincipiaTractalis
