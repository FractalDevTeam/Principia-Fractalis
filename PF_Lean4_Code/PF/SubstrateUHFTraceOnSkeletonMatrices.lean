/-
# r90: The substrate UHF trace on the α-skeleton and λ-skeleton
#      diagonal matrices at level 2 — explicit closed-form spectral values

★ 2026-07-07 r90 — substrate ToE spectral bridge: explicit closed-form
values for the substrate UHF trace on the α- and λ-skeleton matrix
realizations at completion level ★

## The framework-first content

r83 supplied the substrate trace pairings on the commutative substrate
`Fin 9 → ℂ`:

    τ(α_complex) = (Σ_i α_i : ℂ) / 9 = (19/4 + √2 + 2φ + 9π/4 + √(2π))/9
    τ(λ_complex) = (Σ_i λ_i : ℂ) / 9  (r75 universal-coupling skeleton)

r89 kernel-verified the spectral bridge closure `UHF_trace(embed E_ii)
= 1/9` on `TimelessFieldCompletion` (the substrate UHF C*-algebra
completion, r53–r59), via the diagonal matrix δ-projections
`E_ii := Matrix.single i i 1` in the substrate matrix substrate
`A_2 = Matrix (Fin 9) (Fin 9) ℂ` (r27).

r90 delivers the ANALOGOUS lift for the substrate α- and λ-skeletons:
the diagonal-matrix realizations of the r83 skeletons at substrate
level 2 lift through the r43 canonical embedding + r87 UHF trace
extension to explicit closed-form spectral values on
`TimelessFieldCompletion`:

    UHF_trace ((embed α_matrix : TimelessFieldCompletion)) =
       (19/4 + √2 + 2φ + 9π/4 + √(2π)) / 9

    UHF_trace ((embed λ_matrix : TimelessFieldCompletion)) =
       (Σ_i λ_i : ℂ) / 9

Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
axioms. Zero sorries.

Stage 2026-07-07 r90 — substrate UHF trace on α/λ-skeleton diagonal
matrices at completion level, with explicit closed-form.
-/

import PF.SubstrateUHFTraceOnMatrixProjections
import PF.SubstrateTracePairing
import Mathlib.Data.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace SubstrateUHFTraceOnSkeletonMatrices

open scoped Matrix.Norms.L2Operator
open scoped ComplexOrder
open SubstrateUHFBoundedTrace SubstrateUHFTraceLipschitz
open SubstrateUHFCompletionTrace SubstrateUHFPreTraceDirectLimit
open SubstrateUHFTraceOnMatrixProjections
open SubstrateDirectLimit SubstrateTimelessFieldCompletion
open SubstrateTracePairing

/-! ## §1 — Substrate α-skeleton and λ-skeleton diagonal matrices at level 2 -/

/-- **The substrate α-skeleton diagonal matrix** at substrate level 2:
    `Matrix.diagonal substrate_alpha_skeleton_complex`, a
    `Matrix (Fin 9) (Fin 9) ℂ` with `α_i` on the diagonal at position
    (i, i) and 0 off-diagonal. -/
noncomputable def substrate_alpha_matrix : Matrix (Fin 9) (Fin 9) ℂ :=
  Matrix.diagonal substrate_alpha_skeleton_complex

/-- **The substrate λ-skeleton diagonal matrix** at substrate level 2:
    `Matrix.diagonal substrate_lambda_skeleton_complex`, a
    `Matrix (Fin 9) (Fin 9) ℂ` with `λ_i` on the diagonal at position
    (i, i) and 0 off-diagonal. -/
noncomputable def substrate_lambda_matrix : Matrix (Fin 9) (Fin 9) ℂ :=
  Matrix.diagonal substrate_lambda_skeleton_complex

/-! ## §2 — Trace of the skeleton matrices -/

/-- **r90.a: trace of the substrate α-skeleton matrix**:
    `trace α_matrix = ∑_i α_i`. -/
theorem substrate_alpha_matrix_trace :
    Matrix.trace substrate_alpha_matrix =
      ∑ i : Fin 9, substrate_alpha_skeleton_complex i := by
  unfold substrate_alpha_matrix
  exact Matrix.trace_diagonal _

/-- **r90.b: trace of the substrate λ-skeleton matrix**:
    `trace λ_matrix = ∑_i λ_i`. -/
theorem substrate_lambda_matrix_trace :
    Matrix.trace substrate_lambda_matrix =
      ∑ i : Fin 9, substrate_lambda_skeleton_complex i := by
  unfold substrate_lambda_matrix
  exact Matrix.trace_diagonal _

/-! ## §3 — Normalized matrix trace of the skeleton matrices -/

/-- **r90.c: normalized matrix trace of the α-skeleton matrix**:
    `τ_9(α_matrix) = (∑_i α_i)/9`. -/
theorem substrate_alpha_matrix_normalized_trace :
    normalized_matrix_trace substrate_alpha_matrix =
      (∑ i : Fin 9, substrate_alpha_skeleton_complex i) / 9 := by
  unfold normalized_matrix_trace
  rw [substrate_alpha_matrix_trace]
  norm_num

/-- **r90.d: normalized matrix trace of the λ-skeleton matrix**:
    `τ_9(λ_matrix) = (∑_i λ_i)/9`. -/
theorem substrate_lambda_matrix_normalized_trace :
    normalized_matrix_trace substrate_lambda_matrix =
      (∑ i : Fin 9, substrate_lambda_skeleton_complex i) / 9 := by
  unfold normalized_matrix_trace
  rw [substrate_lambda_matrix_trace]
  norm_num

/-! ## §4 — Lift to the substrate pre-trace on TimelessFieldRing -/

/-- **r90.e: substrate pre-trace on TimelessFieldRing of the α-skeleton
    matrix at level 2 equals (∑_i α_i)/9**. -/
theorem substrate_pre_trace_on_alpha_matrix :
    substrate_pre_trace
        (substrateLevelToTimelessField 2 substrate_alpha_matrix) =
      (∑ i : Fin 9, substrate_alpha_skeleton_complex i) / 9 := by
  show substrate_pre_trace
      ((⟦⟨2, substrate_alpha_matrix⟩⟧ : TimelessFieldRing)) =
    (∑ i : Fin 9, substrate_alpha_skeleton_complex i) / 9
  rw [substrate_pre_trace_of_level]
  exact substrate_alpha_matrix_normalized_trace

/-- **r90.f: substrate pre-trace on TimelessFieldRing of the λ-skeleton
    matrix at level 2 equals (∑_i λ_i)/9**. -/
theorem substrate_pre_trace_on_lambda_matrix :
    substrate_pre_trace
        (substrateLevelToTimelessField 2 substrate_lambda_matrix) =
      (∑ i : Fin 9, substrate_lambda_skeleton_complex i) / 9 := by
  show substrate_pre_trace
      ((⟦⟨2, substrate_lambda_matrix⟩⟧ : TimelessFieldRing)) =
    (∑ i : Fin 9, substrate_lambda_skeleton_complex i) / 9
  rw [substrate_pre_trace_of_level]
  exact substrate_lambda_matrix_normalized_trace

/-! ## §5 — Lift to the substrate UHF trace on TimelessFieldCompletion -/

/-- **★★★ r90.g: SUBSTRATE UHF TRACE ON THE α-SKELETON MATRIX ★★★**

    The substrate UHF trace on `TimelessFieldCompletion` (r87) applied
    to the level-2 embedded α-skeleton matrix equals `(∑_i α_i)/9`.
    Kernel-proved via r87 `UHF_trace_coe` + r90.e. -/
theorem UHF_trace_on_alpha_matrix :
    UHF_trace
        ((substrateLevelToTimelessField 2 substrate_alpha_matrix
          : TimelessFieldCompletion)) =
      (∑ i : Fin 9, substrate_alpha_skeleton_complex i) / 9 := by
  rw [UHF_trace_coe]
  exact substrate_pre_trace_on_alpha_matrix

/-- **★★★ r90.h: SUBSTRATE UHF TRACE ON THE λ-SKELETON MATRIX ★★★**

    The substrate UHF trace on `TimelessFieldCompletion` applied to
    the level-2 embedded λ-skeleton matrix equals `(∑_i λ_i)/9`. -/
theorem UHF_trace_on_lambda_matrix :
    UHF_trace
        ((substrateLevelToTimelessField 2 substrate_lambda_matrix
          : TimelessFieldCompletion)) =
      (∑ i : Fin 9, substrate_lambda_skeleton_complex i) / 9 := by
  rw [UHF_trace_coe]
  exact substrate_pre_trace_on_lambda_matrix

/-! ## §6 — Chain with r83's closed form for the α-skeleton sum -/

/-- **★★★ r90.i: EXPLICIT CLOSED-FORM SPECTRAL VALUE ★★★**

    Combining r90.g with r83's kernel-verified α-skeleton sum closed
    form yields the explicit closed-form spectral value of the
    substrate UHF trace on the level-2 embedded α-skeleton matrix:

        UHF_trace ((embed α_matrix : TimelessFieldCompletion))
          = (19/4 + √2 + 2φ + 9π/4 + √(2π)) / 9

    This is the substrate ToE's SPECTRAL BRIDGE OUTPUT: an explicit,
    kernel-verified, closed-form complex-number invariant on the
    substrate UHF C*-algebra completion, tied to the r72 α-skeleton
    values (√2 for P; φ+1/4 for NP; 3π/4 for BSD; φ for Hodge;
    √(2π) for QG; etc.) via the r89 spectral bridge closure. -/
theorem UHF_trace_on_alpha_matrix_closed_form :
    UHF_trace
        ((substrateLevelToTimelessField 2 substrate_alpha_matrix
          : TimelessFieldCompletion)) =
      ((19/4 : ℂ) + Complex.ofReal (Real.sqrt 2)
        + 2 * Complex.ofReal ((1 + Real.sqrt 5) / 2)
        + 9 * (Real.pi : ℂ) / 4
        + Complex.ofReal (Real.sqrt (2 * Real.pi))) / 9 := by
  rw [UHF_trace_on_alpha_matrix]
  -- Reduce Σ_i α_complex_i to (Σ_i α_i : ℝ) : ℂ via push_cast
  have h_sum_cast :
      ∑ i : Fin 9, substrate_alpha_skeleton_complex i =
        ((substrate_alpha_skeleton_sum : ℝ) : ℂ) := by
    unfold substrate_alpha_skeleton_sum substrate_alpha_skeleton_complex
    push_cast
    rfl
  rw [h_sum_cast]
  -- r83's kernel-verified closed form for the α-skeleton sum
  rw [substrate_alpha_skeleton_sum_closed_form]
  push_cast
  ring

/-! ## §7 — Substrate spectral-bridge output theorem + r90 capstone -/

/-- **★★★ r90 SUBSTRATE SPECTRAL-BRIDGE OUTPUT CAPSTONE ★★★**

    Bundles the r90 substrate spectral-bridge outputs on the α- and
    λ-skeleton matrix realizations at completion level:

      (B1) `substrate_alpha_matrix` — the diagonal α-matrix at level 2.
      (B2) `substrate_lambda_matrix` — the diagonal λ-matrix at level 2.
      (B3) `substrate_alpha_matrix_normalized_trace` —
           τ_9(α_matrix) = (Σ α_i)/9.
      (B4) `substrate_lambda_matrix_normalized_trace` —
           τ_9(λ_matrix) = (Σ λ_i)/9.
      (B5) `substrate_pre_trace_on_alpha_matrix` — the r87 substrate
           pre-trace on TimelessFieldRing of embed α_matrix = (Σ α_i)/9.
      (B6) `substrate_pre_trace_on_lambda_matrix` — the r87 substrate
           pre-trace on TimelessFieldRing of embed λ_matrix = (Σ λ_i)/9.
      (B7) `UHF_trace_on_alpha_matrix` — **the α-matrix UHF trace** on
           TimelessFieldCompletion = (Σ α_i)/9.
      (B8) `UHF_trace_on_lambda_matrix` — **the λ-matrix UHF trace** on
           TimelessFieldCompletion = (Σ λ_i)/9.
      (B9) **`UHF_trace_on_alpha_matrix_closed_form`** — **THE EXPLICIT
           CLOSED-FORM SPECTRAL VALUE**:
           `UHF_trace(embed α_matrix) =
              (19/4 + √2 + 2φ + 9π/4 + √(2π)) / 9`.

    Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
    axioms. Zero sorries.

    Substrate significance: r90 delivers the substrate ToE's spectral
    bridge OUTPUT — kernel-verified, explicit, closed-form complex
    numerical invariants on the substrate UHF C*-algebra completion,
    tied to the r72 substrate α-skeleton (the 9-class analytic
    skeleton whose values include P's √2, NP's φ+1/4, BSD's 3π/4,
    QG's √(2π), etc.) via the r89 spectral bridge closure applied to
    the diagonal α-matrix realization at substrate level 2. The
    substrate spectral bridge from base-3 fractal dynamics (r25) to
    canonical UHF spectral invariants (r90 output) is complete. -/
theorem r90_substrate_UHF_trace_on_skeleton_matrices_capstone :
    (Matrix.trace substrate_alpha_matrix =
      ∑ i : Fin 9, substrate_alpha_skeleton_complex i) ∧
    (Matrix.trace substrate_lambda_matrix =
      ∑ i : Fin 9, substrate_lambda_skeleton_complex i) ∧
    (normalized_matrix_trace substrate_alpha_matrix =
      (∑ i : Fin 9, substrate_alpha_skeleton_complex i) / 9) ∧
    (normalized_matrix_trace substrate_lambda_matrix =
      (∑ i : Fin 9, substrate_lambda_skeleton_complex i) / 9) ∧
    (substrate_pre_trace
        (substrateLevelToTimelessField 2 substrate_alpha_matrix) =
      (∑ i : Fin 9, substrate_alpha_skeleton_complex i) / 9) ∧
    (substrate_pre_trace
        (substrateLevelToTimelessField 2 substrate_lambda_matrix) =
      (∑ i : Fin 9, substrate_lambda_skeleton_complex i) / 9) ∧
    (UHF_trace
        ((substrateLevelToTimelessField 2 substrate_alpha_matrix
          : TimelessFieldCompletion)) =
      (∑ i : Fin 9, substrate_alpha_skeleton_complex i) / 9) ∧
    (UHF_trace
        ((substrateLevelToTimelessField 2 substrate_lambda_matrix
          : TimelessFieldCompletion)) =
      (∑ i : Fin 9, substrate_lambda_skeleton_complex i) / 9) ∧
    (UHF_trace
        ((substrateLevelToTimelessField 2 substrate_alpha_matrix
          : TimelessFieldCompletion)) =
      ((19/4 : ℂ) + Complex.ofReal (Real.sqrt 2)
        + 2 * Complex.ofReal ((1 + Real.sqrt 5) / 2)
        + 9 * (Real.pi : ℂ) / 4
        + Complex.ofReal (Real.sqrt (2 * Real.pi))) / 9) :=
  ⟨substrate_alpha_matrix_trace,
   substrate_lambda_matrix_trace,
   substrate_alpha_matrix_normalized_trace,
   substrate_lambda_matrix_normalized_trace,
   substrate_pre_trace_on_alpha_matrix,
   substrate_pre_trace_on_lambda_matrix,
   UHF_trace_on_alpha_matrix,
   UHF_trace_on_lambda_matrix,
   UHF_trace_on_alpha_matrix_closed_form⟩

end SubstrateUHFTraceOnSkeletonMatrices
end PrincipiaTractalis
