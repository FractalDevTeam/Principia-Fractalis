/-
# r89: The substrate UHF trace on the matrix δ-projections
#      at level k=2 — τ_UHF(embed(E_ii)) = 1/9

★ 2026-07-07 r89 — spectral bridge closure: connecting the substrate
UHF trace `τ_UHF : TimelessFieldCompletion → ℂ` (r87) to the r82
canonical trace value `τ(δ_i) = 1/9` via the level-2 matrix δ-projections ★

## The framework-first content

r81 supplied the substrate 9-projection concrete realization on the
commutative substrate `Fin 9 → ℂ` (five kernel-verified projection
identities). r82 supplied the canonical trace with the essential
spectral invariant `τ(δ_i) = 1/9`. r87 supplied the unconditional
substrate UHF trace `τ_UHF : TimelessFieldCompletion → ℂ` as the
completion extension of the substrate pre-trace on `TimelessFieldRing`,
which itself descends from the level-k normalized matrix traces via
`DirectLimit.lift` on the r30 substrate direct limit.

r89 closes the SPECTRAL BRIDGE by lifting the r82 substrate spectral
invariant `τ(δ_i) = 1/9` from the commutative substrate `Fin 9 → ℂ`
into the NON-COMMUTATIVE substrate `Matrix (Fin 9) (Fin 9) ℂ` = A_2
(the substrate level-2 finite matrix algebra, r27), and thereby into
`TimelessFieldCompletion` via the r43 canonical embedding + r87 UHF
trace extension. The lift uses the diagonal matrix projections
`E_ii := Matrix.single i i 1` — the substrate matrix δ-projections
at level 2 — with:

  * Nine kernel-verified matrix projection identities (idempotent,
    self-adjoint, orthogonal, sum-to-identity, normalized trace = 1/9).
  * Under the r43 canonical embedding
    `substrateLevelToTimelessField 2 : Matrix (Fin 9) (Fin 9) ℂ →
    TimelessFieldRing` the trace value 1/9 is preserved:
    `substrate_pre_trace (embed E_ii) = 1/9`.
  * Under the r87 dense-image agreement + the completion coercion:
    `UHF_trace ((embed E_ii : TimelessFieldCompletion)) = 1/9`.

## Semantic scope

r89 delivers the **spectral bridge closure**: the substrate UHF trace
value on each of the nine canonical level-2 matrix δ-projections is
kernel-verified to equal 1/9. This is the essential numerical
identification pin between the substrate UHF trace on
`TimelessFieldCompletion` (r87 analytic content) and the r82
substrate canonical spectral invariant `τ(δ_i) = 1/9` (r82 algebraic
content).

Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
axioms. Zero sorries.

Stage 2026-07-07 r89 — substrate UHF trace on matrix δ-projections
= 1/9; spectral bridge closure.
-/

import PF.SubstrateUHFPreTraceDirectLimit
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace SubstrateUHFTraceOnMatrixProjections

open scoped Matrix.Norms.L2Operator
open scoped ComplexOrder
open scoped Matrix
open SubstrateUHFBoundedTrace SubstrateUHFTraceLipschitz
open SubstrateUHFCompletionTrace SubstrateUHFPreTraceDirectLimit
open SubstrateDirectLimit SubstrateTimelessFieldCompletion

/-! ## §1 — Substrate matrix δ-projections at level 2 -/

/-- **The substrate matrix δ-projection at level 2**, for each i : Fin 9,
    defined as `Matrix.single i i 1 : Matrix (Fin 9) (Fin 9) ℂ`. This is
    the diagonal projection E_ii with 1 at entry (i,i) and 0 elsewhere.

    The nine E_ii sit inside the substrate level-2 algebra A_2 =
    Matrix (Fin (3^2)) (Fin (3^2)) ℂ = Matrix (Fin 9) (Fin 9) ℂ (r27).
    They realize the r82 substrate 9-projection spectral structure
    in the non-commutative substrate setting. -/
noncomputable def substrate_matrix_delta_projection (i : Fin 9) :
    Matrix (Fin 9) (Fin 9) ℂ :=
  Matrix.single i i 1

/-! ## §2 — Nine kernel-verified matrix-projection identities -/

/-- **r89.a: matrix δ-projections are idempotent**:
    `E_ii · E_ii = E_ii`. -/
theorem substrate_matrix_delta_projection_idempotent (i : Fin 9) :
    substrate_matrix_delta_projection i * substrate_matrix_delta_projection i =
      substrate_matrix_delta_projection i := by
  unfold substrate_matrix_delta_projection
  rw [Matrix.single_mul_single_same]
  simp

/-- **r89.b: matrix δ-projections are self-adjoint**:
    `star E_ii = E_ii`. -/
theorem substrate_matrix_delta_projection_star (i : Fin 9) :
    star (substrate_matrix_delta_projection i) =
      substrate_matrix_delta_projection i := by
  show Matrix.conjTranspose (Matrix.single i i (1 : ℂ)) = Matrix.single i i 1
  rw [Matrix.conjTranspose_single, star_one]

/-- **r89.c: matrix δ-projections are pairwise orthogonal**:
    `E_ii · E_jj = 0` for `i ≠ j`. -/
theorem substrate_matrix_delta_projection_orthogonal
    (i j : Fin 9) (h : i ≠ j) :
    substrate_matrix_delta_projection i * substrate_matrix_delta_projection j = 0 := by
  unfold substrate_matrix_delta_projection
  exact Matrix.single_mul_single_of_ne (c := 1) i i j h 1

/-- **r89.d: matrix δ-projections sum to identity**:
    `∑_i E_ii = 1`. -/
theorem substrate_matrix_delta_projection_sum_eq_one :
    ∑ i : Fin 9, substrate_matrix_delta_projection i =
      (1 : Matrix (Fin 9) (Fin 9) ℂ) := by
  ext i' j'
  simp only [Matrix.sum_apply, substrate_matrix_delta_projection, Matrix.single,
             Matrix.of_apply, Matrix.one_apply]
  by_cases h : i' = j'
  · subst h
    simp only [and_self]
    rw [Finset.sum_ite_eq' Finset.univ i' (fun _ => (1 : ℂ))]
    simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro x _
    rw [if_neg]
    rintro ⟨hxi, hxj⟩
    exact h (hxi.symm.trans hxj)

/-- **r89.e: normalized matrix trace of E_ii = 1/9** — the essential
    r82 substrate spectral invariant `τ(δ_i) = 1/9` realized at the
    non-commutative level-2 substrate. -/
theorem substrate_matrix_delta_projection_normalized_trace (i : Fin 9) :
    normalized_matrix_trace (substrate_matrix_delta_projection i) = (1 : ℂ) / 9 := by
  unfold normalized_matrix_trace substrate_matrix_delta_projection
  rw [Matrix.trace_single_eq_same]
  norm_num

/-! ## §3 — Lift to the substrate pre-trace on TimelessFieldRing -/

/-- **r89.f: `substrate_pre_trace` on the level-2 embedded matrix
    δ-projection equals 1/9**. Kernel-immediate from
    `substrate_pre_trace_of_level` + r89.e. -/
theorem substrate_pre_trace_on_matrix_delta_projection (i : Fin 9) :
    substrate_pre_trace
        (substrateLevelToTimelessField 2 (substrate_matrix_delta_projection i)) =
      (1 : ℂ) / 9 := by
  show substrate_pre_trace
      ((⟦⟨2, substrate_matrix_delta_projection i⟩⟧ : TimelessFieldRing)) =
    (1 : ℂ) / 9
  rw [substrate_pre_trace_of_level]
  exact substrate_matrix_delta_projection_normalized_trace i

/-! ## §4 — Lift to the substrate UHF trace on TimelessFieldCompletion -/

/-- **★★★ r89.g: SUBSTRATE UHF TRACE ON THE MATRIX δ-PROJECTIONS = 1/9 ★★★**

    The substrate UHF trace on `TimelessFieldCompletion` (r87) applied
    to the level-2 embedded matrix δ-projection (viewed inside the
    completion via the canonical dense embedding) equals 1/9:

        UHF_trace ((substrateLevelToTimelessField 2 E_ii :
                    TimelessFieldCompletion)) = 1/9

    Kernel-proved by chaining r87's `UHF_trace_coe` (dense-image
    agreement of the UHF trace with the substrate pre-trace) with
    r89.f (substrate pre-trace value on the level-2 embedded
    matrix δ-projection).

    This kernel-verifies the **substrate spectral bridge closure**:
    the r82 canonical spectral invariant `τ(δ_i) = 1/9` lifts through
    the r43 canonical embedding into the substrate UHF trace on the
    completion. -/
theorem UHF_trace_on_matrix_delta_projection (i : Fin 9) :
    UHF_trace
        ((substrateLevelToTimelessField 2 (substrate_matrix_delta_projection i)
          : TimelessFieldCompletion)) =
      (1 : ℂ) / 9 := by
  rw [UHF_trace_coe]
  exact substrate_pre_trace_on_matrix_delta_projection i

/-! ## §5 — Sum of UHF-trace values equals 1 (matching unital τ(1) = 1) -/

/-- **r89.h: the sum of the substrate UHF trace values over the nine
    matrix δ-projections equals 1**, matching the unital τ(1) = 1 via
    the sum-to-identity `∑ E_ii = 1`. -/
theorem UHF_trace_sum_on_matrix_delta_projections :
    ∑ i : Fin 9, UHF_trace
      ((substrateLevelToTimelessField 2 (substrate_matrix_delta_projection i)
        : TimelessFieldCompletion)) = 1 := by
  simp_rw [UHF_trace_on_matrix_delta_projection]
  norm_num

/-! ## §6 — r89 spectral bridge capstone -/

/-- **★★★ r89 SUBSTRATE UHF TRACE ON MATRIX δ-PROJECTIONS CAPSTONE ★★★**

    Bundles the r89 substrate spectral bridge closure content:

      (A1) `substrate_matrix_delta_projection : Fin 9 →
           Matrix (Fin 9) (Fin 9) ℂ` — the diagonal E_ii projections
           at substrate level 2.
      (A2) `substrate_matrix_delta_projection_idempotent` — E_ii · E_ii = E_ii.
      (A3) `substrate_matrix_delta_projection_star` — star E_ii = E_ii.
      (A4) `substrate_matrix_delta_projection_orthogonal` —
           E_ii · E_jj = 0 for i ≠ j.
      (A5) `substrate_matrix_delta_projection_sum_eq_one` — ∑_i E_ii = 1.
      (A6) `substrate_matrix_delta_projection_normalized_trace` —
           **τ_9(E_ii) = 1/9** at the matrix substrate level.
      (A7) `substrate_pre_trace_on_matrix_delta_projection` —
           substrate pre-trace on TimelessFieldRing of the embedded
           E_ii = 1/9.
      (A8) **`UHF_trace_on_matrix_delta_projection`** — **the essential
           bridge closure**: `τ_UHF(embed E_ii) = 1/9` on
           TimelessFieldCompletion.
      (A9) `UHF_trace_sum_on_matrix_delta_projections` — sum-to-1 matching
           unital τ(1) = 1.

    Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
    axioms. Zero sorries.

    Substrate significance: r89 closes the SUBSTRATE SPECTRAL BRIDGE
    from the r82 canonical spectral invariant `τ(δ_i) = 1/9` (on the
    commutative substrate `Fin 9 → ℂ`) to the r87 substrate UHF trace
    on `TimelessFieldCompletion` (the substrate UHF C*-algebra
    completion of r30's `TimelessFieldRing`) via the non-commutative
    matrix substrate `A_2 = Matrix (Fin 9) (Fin 9) ℂ` (r27) and the
    r43 canonical dense embedding. The substrate UHF trace value 1/9
    on each of the nine canonical matrix δ-projections is now
    kernel-verified — the essential numerical identification pin for
    the substrate spectral bridge from the algebraic 9-count to the
    substrate Dixmier-tracial spectrum. -/
theorem r89_substrate_UHF_trace_on_matrix_projections_capstone :
    (∀ i : Fin 9, substrate_matrix_delta_projection i *
                  substrate_matrix_delta_projection i =
                  substrate_matrix_delta_projection i) ∧
    (∀ i : Fin 9, star (substrate_matrix_delta_projection i) =
                  substrate_matrix_delta_projection i) ∧
    (∀ i j : Fin 9, i ≠ j →
      substrate_matrix_delta_projection i *
      substrate_matrix_delta_projection j = 0) ∧
    (∑ i : Fin 9, substrate_matrix_delta_projection i =
       (1 : Matrix (Fin 9) (Fin 9) ℂ)) ∧
    (∀ i : Fin 9,
      normalized_matrix_trace (substrate_matrix_delta_projection i) =
        (1 : ℂ) / 9) ∧
    (∀ i : Fin 9,
      substrate_pre_trace
          (substrateLevelToTimelessField 2
            (substrate_matrix_delta_projection i)) = (1 : ℂ) / 9) ∧
    (∀ i : Fin 9,
      UHF_trace
          ((substrateLevelToTimelessField 2 (substrate_matrix_delta_projection i)
            : TimelessFieldCompletion)) = (1 : ℂ) / 9) ∧
    (∑ i : Fin 9,
      UHF_trace
          ((substrateLevelToTimelessField 2 (substrate_matrix_delta_projection i)
            : TimelessFieldCompletion)) = 1) :=
  ⟨substrate_matrix_delta_projection_idempotent,
   substrate_matrix_delta_projection_star,
   substrate_matrix_delta_projection_orthogonal,
   substrate_matrix_delta_projection_sum_eq_one,
   substrate_matrix_delta_projection_normalized_trace,
   substrate_pre_trace_on_matrix_delta_projection,
   UHF_trace_on_matrix_delta_projection,
   UHF_trace_sum_on_matrix_delta_projections⟩

end SubstrateUHFTraceOnMatrixProjections
end PrincipiaTractalis
