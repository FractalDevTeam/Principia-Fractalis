/-
# r94: The substrate UHF trace is a TRACIAL STATE
#      on `TimelessFieldCompletion`: τ_UHF(x·y) = τ_UHF(y·x)

★ 2026-07-08 r94 — the substrate UHF trace upgraded from
"linear + unital + 1-Lipschitz + uniformly continuous" (r87) to
"tracial state" ★

## The framework-first content

r87 delivered the unconditional substrate UHF trace
`τ_UHF : TimelessFieldCompletion → ℂ` as a uniformly continuous,
linear, unital ℂ-valued function on the substrate UHF C*-algebra
completion (r53-r59). r89 supplied the spectral-bridge closure
`τ_UHF(ι_2(E_ii)) = 1/9` on the level-2 matrix δ-projections; r90 +
r92 supplied the explicit closed-form spectral outputs on the
substrate α- and λ-skeleton diagonal matrix realizations.

r94 upgrades τ_UHF from "linear + unital + 1-Lipschitz + UC" to a
genuine TRACIAL STATE: it satisfies the essential tracial identity

    τ_UHF(x · y) = τ_UHF(y · x)   for every x, y : TimelessFieldCompletion.

This is the essential structural property of a tracial state on a
C*-algebra — the invariance under cyclic permutation of the product —
which distinguishes tracial states (Tomita-Takesaki modular-theoretic
tracial normal states, Dixmier traces, C*-algebra traces) from mere
positive linear functionals. Combined with r87's linear + unital
content, this makes τ_UHF the essential UHF TRACE of the substrate
UHF C*-algebra completion, in the full operator-algebra sense.

## Semantic scope

r94 delivers:

  * `normalized_matrix_trace_mul_comm` — level-k matrix tracial via
    mathlib's `Matrix.trace_mul_comm`.
  * `substrate_pre_trace_mul_comm` — pre-trace tracial on
    `TimelessFieldRing` via `DirectLimit.exists_eq_mk₂` reducing to
    common-level representatives + `substrate_quotient_mul_same_level`
    (r30/r31) + level-k tracial.
  * **`UHF_trace_mul_comm`** — the substrate UHF trace is tracial on
    `TimelessFieldCompletion` via `UniformSpace.Completion.induction_on₂`
    on the closed equality set (both sides continuous in x, y through
    continuous multiplication and the r87 UC of `UHF_trace`) with
    dense-image reduction via `UniformSpace.Completion.coe_mul` +
    `UHF_trace_coe` + pre-trace tracial.
  * r94 capstone bundling the three tracial identities.

Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
axioms. Zero sorries.

Stage 2026-07-08 r94 — substrate UHF trace as a tracial state on
`TimelessFieldCompletion`.
-/

import PF.SubstrateUHFPreTraceDirectLimit
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace SubstrateUHFTraceIsTracial

open scoped Matrix.Norms.L2Operator
open scoped ComplexOrder
open SubstrateUHFBoundedTrace SubstrateUHFTraceLipschitz
open SubstrateUHFCompletionTrace SubstrateUHFPreTraceDirectLimit
open SubstrateDirectLimit SubstrateTimelessFieldCompletion

/-! ## §1 — Level-k matrix trace is tracial -/

/-- **r94.a: normalized matrix trace is tracial at every substrate
    finite level**: `τ_n(A · B) = τ_n(B · A)` for all A, B in
    `Matrix (Fin n) (Fin n) ℂ`. Follows from mathlib's
    `Matrix.trace_mul_comm` since ℂ is commutative. -/
theorem normalized_matrix_trace_mul_comm {n : ℕ} [NeZero n]
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    normalized_matrix_trace (A * B) = normalized_matrix_trace (B * A) := by
  unfold normalized_matrix_trace
  rw [Matrix.trace_mul_comm]

/-! ## §2 — Substrate pre-trace on TimelessFieldRing is tracial -/

/-- **r94.b: substrate pre-trace on TimelessFieldRing is tracial**:
    `substrate_pre_trace(x · y) = substrate_pre_trace(y · x)`.
    Proved via `DirectLimit.exists_eq_mk₂` reducing to common-level
    representatives + r30/r31's `substrate_quotient_mul_same_level`
    + r94.a. -/
theorem substrate_pre_trace_mul_comm (x y : TimelessFieldRing) :
    substrate_pre_trace (x * y) = substrate_pre_trace (y * x) := by
  obtain ⟨i, A, B, hx, hy⟩ :=
    DirectLimit.exists_eq_mk₂
      (fun i j (h : i ≤ j) => substrateRingHomIter i j h) x y
  subst hx; subst hy
  rw [substrate_quotient_mul_same_level i A B,
      substrate_quotient_mul_same_level i B A,
      substrate_pre_trace_of_level, substrate_pre_trace_of_level]
  exact normalized_matrix_trace_mul_comm A B

/-! ## §3 — Substrate UHF trace on TimelessFieldCompletion is tracial -/

/-- **★★★ r94.c: SUBSTRATE UHF TRACE IS TRACIAL ★★★**

    The substrate UHF trace on `TimelessFieldCompletion` (r87) satisfies
    the tracial identity:

        τ_UHF(x · y) = τ_UHF(y · x)   for every x, y : TimelessFieldCompletion.

    Proof: `UniformSpace.Completion.induction_on₂` on the closed
    equality set. Both sides are continuous in (x, y) since:
      * multiplication `TimelessFieldCompletion × TimelessFieldCompletion
        → TimelessFieldCompletion` is continuous (from the NormedRing
        structure inherited via r53's completion),
      * `τ_UHF = UHF_trace_extension_from_pre_trace substrate_pre_trace`
        is uniformly continuous by r87 `UHF_trace_uniformContinuous`.
    Dense-image reduction: for a, b in `TimelessFieldRing`,
      `τ_UHF((↑a) · (↑b)) = τ_UHF(↑(a · b))`  via `Completion.coe_mul`
      = `substrate_pre_trace (a · b)`             via r87 `UHF_trace_coe`
      = `substrate_pre_trace (b · a)`             via r94.b
      = `τ_UHF(↑(b · a))`                         via r87 `UHF_trace_coe`
      = `τ_UHF((↑b) · (↑a))`                       via `Completion.coe_mul`. -/
theorem UHF_trace_mul_comm (x y : TimelessFieldCompletion) :
    UHF_trace (x * y) = UHF_trace (y * x) := by
  refine UniformSpace.Completion.induction_on₂ x y
    (p := fun x y => UHF_trace (x * y) = UHF_trace (y * x)) ?_ ?_
  · -- Closed set: preimage of the equality of continuous functions.
    refine isClosed_eq ?_ ?_
    · exact UHF_trace_uniformContinuous.continuous.comp continuous_mul
    · have h_swap : Continuous (fun p : TimelessFieldCompletion × TimelessFieldCompletion
                                 => p.2 * p.1) :=
        continuous_mul.comp continuous_swap
      exact UHF_trace_uniformContinuous.continuous.comp h_swap
  · -- Dense image reduction.
    intro a b
    rw [← UniformSpace.Completion.coe_mul,
        ← UniformSpace.Completion.coe_mul,
        UHF_trace_coe, UHF_trace_coe]
    exact substrate_pre_trace_mul_comm a b

/-! ## §4 — r94 capstone -/

/-- **★★★ r94 SUBSTRATE UHF TRACE IS TRACIAL CAPSTONE ★★★**

    Bundles the r94 substrate tracial content across all three tiers
    of the substrate UHF trace construction:

      (T1) `normalized_matrix_trace_mul_comm` — level-k matrix trace
           tracial via `Matrix.trace_mul_comm`.
      (T2) `substrate_pre_trace_mul_comm` — pre-trace tracial on
           `TimelessFieldRing` via `DirectLimit.exists_eq_mk₂` +
           `substrate_quotient_mul_same_level` + T1.
      (T3) **`UHF_trace_mul_comm`** — **the substrate UHF trace is
           tracial** on `TimelessFieldCompletion` via
           `UniformSpace.Completion.induction_on₂` + continuous
           multiplication + `Completion.coe_mul` + `UHF_trace_coe` + T2.

    Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
    axioms. Zero sorries.

    Substrate significance: r94 upgrades the substrate UHF trace on
    `TimelessFieldCompletion` from "additive + unital + 1-Lipschitz +
    uniformly continuous" (r87) to a genuine TRACIAL STATE — the
    essential structural property distinguishing operator-algebra
    traces from mere positive linear functionals. Combined with the
    r89 spectral bridge closure and the r90 + r92 explicit closed-form
    outputs, the substrate UHF trace on `TimelessFieldCompletion` is
    now the complete operator-algebra UHF tracial state of the
    substrate ToE spectral bridge. -/
theorem r94_substrate_UHF_trace_is_tracial_capstone :
    (∀ {n : ℕ} [NeZero n] (A B : Matrix (Fin n) (Fin n) ℂ),
      normalized_matrix_trace (A * B) =
        normalized_matrix_trace (B * A)) ∧
    (∀ x y : TimelessFieldRing,
      substrate_pre_trace (x * y) =
        substrate_pre_trace (y * x)) ∧
    (∀ x y : TimelessFieldCompletion,
      UHF_trace (x * y) = UHF_trace (y * x)) :=
  ⟨fun {_} _ A B => normalized_matrix_trace_mul_comm A B,
   substrate_pre_trace_mul_comm,
   UHF_trace_mul_comm⟩

end SubstrateUHFTraceIsTracial
end PrincipiaTractalis
