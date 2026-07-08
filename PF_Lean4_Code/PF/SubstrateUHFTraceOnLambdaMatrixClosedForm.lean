/-
# r92: Explicit closed-form UHF trace on the substrate λ-skeleton
#      diagonal matrix at completion level

★ 2026-07-07 r92 — kernel-verified closed-form spectral output on the
r75 universal-coupling λ-skeleton, mirroring r90's α-skeleton output ★

## The framework-first content

r90 delivered the substrate ToE's spectral-bridge OUTPUT on the r72
α-skeleton diagonal matrix realization at completion level:

    UHF_trace ((ι_2(diag α_•)) : TimelessFieldCompletion) =
      (19/4 + √2 + 2φ + 9π/4 + √(2π)) / 9

r92 lands the analogous kernel-verified closed-form spectral output
on the r75 universal-coupling λ-skeleton `λ_i := π/(10·α_i)`:

    UHF_trace ((ι_2(diag λ_•)) : TimelessFieldCompletion) =
      (13π/60 + 1/5 + π/(10√2) + π/(10φ)
        + π/(10(φ+1/4)) + π/(10√(2π))) / 9

The closed form for `Σ_i λ_i` is nontrivial because the substrate
α-values `α_6 = 3π/4` and `α_8 = 3π/2` cause the corresponding λ
values `λ_6 = 2/15` and `λ_8 = 1/15` to be rational (π cancels),
while the other five λ_i remain π-transcendental. The rational
component `13π/60 + 1/5` collects the four "π-visible" values with
α ∈ {1, 2, 3/2, plus π-cancellation contributions from α_6 and α_8}.

Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
axioms. Zero sorries.

Stage 2026-07-07 r92 — explicit closed-form UHF trace on the
substrate λ-skeleton diagonal matrix at completion level.
-/

import PF.SubstrateUHFTraceOnSkeletonMatrices
import PF.SpectralIsolationSubstrateDischarge
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace SubstrateUHFTraceOnLambdaMatrixClosedForm

open scoped Matrix.Norms.L2Operator
open scoped ComplexOrder
open SubstrateUHFBoundedTrace SubstrateUHFTraceLipschitz
open SubstrateUHFCompletionTrace SubstrateUHFPreTraceDirectLimit
open SubstrateUHFTraceOnMatrixProjections SubstrateUHFTraceOnSkeletonMatrices
open SubstrateDirectLimit SubstrateTimelessFieldCompletion
open SubstrateTracePairing
open SpectralIsolationSubstrateDischarge

/-! ## §1 — Closed form for the substrate λ-skeleton sum

The r75 substrate λ-skeleton is defined pointwise by
`λ_i := π/(10·α_i)` against the r72 substrate α-skeleton. Expanding
against the nine explicit α-values:

    λ_0 = π/10           (α_Poincaré = 1)
    λ_1 = π/(10√2)       (α_P = √2)
    λ_2 = π/20           (α_YM = 2)
    λ_3 = π/15           (α_RH = 3/2)
    λ_4 = π/(10·φ)       (α_Hodge = φ)
    λ_5 = π/(10·(φ+1/4)) (α_NP = φ + 1/4)
    λ_6 = 2/15           (α_BSD = 3π/4; π cancels)
    λ_7 = π/(10·√(2π))   (α_QG = √(2π))
    λ_8 = 1/15           (α_NS = 3π/2; π cancels)

Rational π-visible terms: π/10 + π/20 + π/15 = 13π/60.
Constants (π-cancelled): 2/15 + 1/15 = 1/5.
Remaining transcendentals: π/(10√2), π/(10·φ), π/(10·(φ+1/4)),
π/(10·√(2π)). -/

/-- **r92.a: substrate λ-skeleton sum closed form** on `ℝ`.

    `Σ_i λ_i = 13π/60 + 1/5 + π/(10√2) + π/(10·φ) + π/(10·(φ+1/4))
    + π/(10·√(2π))`, obtained by direct expansion of the nine
    substrate α-values, with π-cancellation at indices 6 and 8. -/
theorem substrate_lambda_skeleton_sum_closed_form :
    substrate_lambda_skeleton_sum =
      13 * Real.pi / 60 + 1 / 5
      + Real.pi / (10 * Real.sqrt 2)
      + Real.pi / (10 * Real.goldenRatio)
      + Real.pi / (10 * (Real.goldenRatio + 1 / 4))
      + Real.pi / (10 * Real.sqrt (2 * Real.pi)) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  -- Individual λ_i values, particularly the π-cancelling ones at 6 and 8.
  have h0 : substrate_lambda_skeleton 0 = Real.pi / 10 := by
    show Real.pi / (10 * (1 : ℝ)) = Real.pi / 10; ring
  have h1 : substrate_lambda_skeleton 1 = Real.pi / (10 * Real.sqrt 2) := rfl
  have h2 : substrate_lambda_skeleton 2 = Real.pi / 20 := by
    show Real.pi / (10 * (2 : ℝ)) = Real.pi / 20; ring
  have h3 : substrate_lambda_skeleton 3 = Real.pi / 15 := by
    show Real.pi / (10 * (3 / 2 : ℝ)) = Real.pi / 15; ring
  have h4 : substrate_lambda_skeleton 4 = Real.pi / (10 * Real.goldenRatio) := rfl
  have h5 : substrate_lambda_skeleton 5 =
              Real.pi / (10 * (Real.goldenRatio + 1 / 4)) := rfl
  have h6 : substrate_lambda_skeleton 6 = 2 / 15 := by
    show Real.pi / (10 * (3 * Real.pi / 4)) = 2 / 15
    field_simp; ring
  have h7 : substrate_lambda_skeleton 7 =
              Real.pi / (10 * Real.sqrt (2 * Real.pi)) := rfl
  have h8 : substrate_lambda_skeleton 8 = 1 / 15 := by
    show Real.pi / (10 * (3 * Real.pi / 2)) = 1 / 15
    field_simp; ring
  -- Decompose the Fin 9 sum via 9× Fin.sum_univ_succ.
  show (∑ i : Fin 9, substrate_lambda_skeleton i) =
       13 * Real.pi / 60 + 1 / 5
       + Real.pi / (10 * Real.sqrt 2)
       + Real.pi / (10 * Real.goldenRatio)
       + Real.pi / (10 * (Real.goldenRatio + 1 / 4))
       + Real.pi / (10 * Real.sqrt (2 * Real.pi))
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
  -- Substitute each λ_i value; then reduce the rational combination.
  rw [h0, show (Fin.succ 0 : Fin 9) = 1 from rfl, h1,
      show (Fin.succ (Fin.succ 0) : Fin 9) = 2 from rfl, h2,
      show (Fin.succ (Fin.succ (Fin.succ 0)) : Fin 9) = 3 from rfl, h3,
      show (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0))) : Fin 9) = 4 from rfl, h4,
      show (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0)))) : Fin 9) = 5 from rfl, h5,
      show (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0))))) : Fin 9) = 6 from rfl, h6,
      show (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0)))))) : Fin 9) = 7 from rfl, h7,
      show (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0))))))) : Fin 9) = 8 from rfl, h8]
  ring

/-! ## §2 — Substrate UHF trace closed-form output on the λ-matrix -/

/-- **★★★ r92 EXPLICIT CLOSED-FORM SUBSTRATE UHF TRACE ON THE
    λ-SKELETON MATRIX ★★★**

    Combining r90's `UHF_trace_on_lambda_matrix` with r92.a's
    kernel-verified λ-skeleton sum closed form yields the explicit
    closed-form spectral value of the substrate UHF trace on the
    level-2 embedded λ-skeleton diagonal matrix:

        UHF_trace ((ι_2(diag λ_•)) : TimelessFieldCompletion)
          = (13π/60 + 1/5 + π/(10√2) + π/(10·φ)
              + π/(10·(φ+1/4)) + π/(10·√(2π))) / 9

    This is the r75 universal-coupling counterpart to r90's α-skeleton
    closed-form output: an explicit, kernel-verified, closed-form
    complex-number invariant on the substrate UHF C*-algebra
    completion, tied to the r75 substrate λ-skeleton via the r89
    spectral bridge closure applied to the diagonal λ-matrix
    realization at substrate level 2. -/
theorem UHF_trace_on_lambda_matrix_closed_form :
    UHF_trace
        ((substrateLevelToTimelessField 2 substrate_lambda_matrix
          : TimelessFieldCompletion)) =
      ((13 * (Real.pi : ℂ) / 60) + (1 / 5 : ℂ)
        + (Real.pi : ℂ) / (10 * Complex.ofReal (Real.sqrt 2))
        + (Real.pi : ℂ) / (10 * Complex.ofReal Real.goldenRatio)
        + (Real.pi : ℂ) / (10 * (Complex.ofReal Real.goldenRatio + 1/4))
        + (Real.pi : ℂ) / (10 * Complex.ofReal (Real.sqrt (2 * Real.pi))))
        / 9 := by
  rw [UHF_trace_on_lambda_matrix]
  -- Reduce Σ λ_complex_i to (Σ_i λ_i : ℝ) : ℂ via push_cast
  have h_sum_cast :
      ∑ i : Fin 9, substrate_lambda_skeleton_complex i =
        ((substrate_lambda_skeleton_sum : ℝ) : ℂ) := by
    unfold substrate_lambda_skeleton_sum substrate_lambda_skeleton_complex
    push_cast
    rfl
  rw [h_sum_cast, substrate_lambda_skeleton_sum_closed_form]
  push_cast
  ring

/-! ## §3 — r92 capstone -/

/-- **★★★ r92 SUBSTRATE UHF TRACE CLOSED-FORM ON λ-MATRIX CAPSTONE ★★★**

    Bundles the r92 substrate content:

      (C1) `substrate_lambda_skeleton_sum_closed_form` — the explicit
           closed form on ℝ:
           `Σ_i λ_i = 13π/60 + 1/5 + π/(10√2) + π/(10·φ)
              + π/(10·(φ+1/4)) + π/(10·√(2π))`.
      (C2) **`UHF_trace_on_lambda_matrix_closed_form`** — the substrate
           UHF trace closed form on the level-2 embedded λ-skeleton
           diagonal matrix at completion level.

    Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
    axioms. Zero sorries.

    Substrate significance: r92 completes the substrate ToE's
    spectral-bridge output on BOTH the r72 α-skeleton (r90) AND the
    r75 universal-coupling λ-skeleton (r92), delivering two
    kernel-verified explicit closed-form complex-number invariants
    on the substrate UHF C*-algebra completion. The substrate spectral
    bridge from base-3 fractal dynamics to explicit UHF spectral
    output on both substrate skeletons is complete. -/
theorem r92_substrate_UHF_trace_lambda_matrix_closed_form_capstone :
    (substrate_lambda_skeleton_sum =
      13 * Real.pi / 60 + 1 / 5
      + Real.pi / (10 * Real.sqrt 2)
      + Real.pi / (10 * Real.goldenRatio)
      + Real.pi / (10 * (Real.goldenRatio + 1 / 4))
      + Real.pi / (10 * Real.sqrt (2 * Real.pi))) ∧
    (UHF_trace
        ((substrateLevelToTimelessField 2 substrate_lambda_matrix
          : TimelessFieldCompletion)) =
      ((13 * (Real.pi : ℂ) / 60) + (1 / 5 : ℂ)
        + (Real.pi : ℂ) / (10 * Complex.ofReal (Real.sqrt 2))
        + (Real.pi : ℂ) / (10 * Complex.ofReal Real.goldenRatio)
        + (Real.pi : ℂ) / (10 * (Complex.ofReal Real.goldenRatio + 1/4))
        + (Real.pi : ℂ) / (10 * Complex.ofReal (Real.sqrt (2 * Real.pi))))
        / 9) :=
  ⟨substrate_lambda_skeleton_sum_closed_form,
   UHF_trace_on_lambda_matrix_closed_form⟩

end SubstrateUHFTraceOnLambdaMatrixClosedForm
end PrincipiaTractalis
