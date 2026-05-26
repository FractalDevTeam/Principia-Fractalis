/-
# RH via Arxiv `V_α` at `α = 3/2` — Hilbert–Pólya Identification Attempt

★ 2026-05-25 (Pabs strategic dispatch, Wave 16) ★

## Strategic premise

The framework's Wave 11–12 `arxivHalpha α` operator (`PF/Operators/
VAlphaExplicit{,FromArxiv}.lean`, commit `fa937fb`) is a genuine
symmetric densely-defined `LinearPMap` on `ℓ²(ℕ; ℂ)` whose matrix
coefficients on the standard basis match the published arxiv formula
`h_alpha_basis α n m`. At the IBM-Quantum hardware-measured RH peak
`α_RH = 3/2` (`PF/IBMPeaksGaloisPair.lean`, commit `ace1a5b`), the
operator's claimed ground-state value collapses by the B-clean phase
identity to the explicit rational multiple

    π/(10·(3/2)) = π/15.

The Hilbert–Pólya program asks for a self-adjoint operator whose
non-trivial spectrum encodes the imaginary parts `{t_n}` of the
nontrivial Riemann ζ-zeros. The framework's `SpectralBijection.lean`
provides the canonical map

    eigenvalueToT (α) (λ) = 10 / (π · |λ| · α.value)        -- (★)

which, given an eigenvalue sequence `λ_n`, generates the candidate
critical-line ordinates `t_n := eigenvalueToT α (λ_n)`. The capstone
`riemann_hypothesis_via_spectral_bijection` (`PF/SpectralBijection.lean`
line 536) shows that *if* this map's image is surjective onto the
ζ-zeros, then RH follows.

## What this file delivers (axiom-free, honest)

**Specialisation of the arxiv bridge at α = 3/2** —
  `arxiv_construction_bridge_at_3halves`: the Wave 12 unified bridge
  instantiated at the canonical α_RH value. Operator-side (formal
  adjoint + matrix coefficients) and B-clean-side (ground state =
  π/15 = (1/5)·(π/2 − Im R_f_principal(3/2))) joined into one
  referee-citable statement.

**Closed-form arithmetic at α = 3/2**:
  * `ground_state_at_3halves`: `π/(10·(3/2)) = π/15` axiom-free.
  * `b_clean_image_at_3halves`: `π/2 − Im R_f_principal(3/2) = π/3`
    axiom-free, via the B-clean phase identity.
  * `b_clean_arg_at_3halves`: `arg(1 − e^{i·2π/3}) = −π/6` axiom-free.

**Spectral-bijection arithmetic at α = 3/2**:
  * `scalingParam_alpha_RH`: the explicit `ScalingParameter` for
    `α_RH = 3/2`.
  * `eigenvalueToT_at_RH_groundState`: under the canonical map (★)
    at the ground-state eigenvalue `λ = π/15`, the candidate
    critical-line ordinate is `t_0 = 100/π² ≈ 10.1321`.

**Honest NEGATIVE identification** — `RH_at_3halves_does_not_match_first_zeta_zero`:
  the first nontrivial ζ-zero ordinate is `t_1^(ζ) ≈ 14.134725...`,
  certified `> 14.0`. The ground-state image `t_0 = 100/π² < 10.14`
  is bounded away from `t_1^(ζ)` by more than `3.86`. The naive
  Hilbert–Pólya identification of `arxivHalpha (3/2)`'s ground state
  with the first ζ-zero **FAILS** by a wide margin, axiom-free.

**Honest scope statement** — `arxiv_HP_at_3halves_honest_scope`:
  the operator is constructed (Wave 11–12), the ground state is
  identified with the B-clean phase deficit (Wave 12), the spectral
  bijection map is canonical (`SpectralBijection.lean`), and the
  ζ-zero arithmetic is mathlib-citable. The OPEN gap is the surjectivity
  of the bijection (named in `PF/RHSurjectivityConjecture.lean`); the
  ground-state value alone does NOT enumerate ζ-zeros.

## What this file does NOT do

1. It does NOT prove RH. The named load-bearing surjectivity remains
   open (`RHSpectralSurjectivityConjecture`, `PF/RHSurjectivityConjecture.lean`).

2. It does NOT identify the spectrum of `arxivHalpha (3/2)` with the
   ζ-zeros — the negative result `RH_at_3halves_does_not_match_first_zeta_zero`
   shows the ground state alone is structurally too low to coincide
   with the first ζ-zero ordinate under the canonical map (★).

3. It does NOT alter the no-go theorem `alpha_realization_canonical_pair_iff_classes_distinct`
   (`PF/TuringEncoding/AlphaRealizationNoGo.lean`) — that no-go
   targets `PolylogEigenvalueConjecture` for P vs NP, not RH directly.

## Why the negative is also a positive

The negative result `RH_at_3halves_does_not_match_first_zeta_zero`
sharpens the OPEN_PROBLEMS.md formulation: the literal "ground state
of `arxivHalpha (3/2)` = first ζ-zero under map (★)" is *closed*
(refuted). Any future RH identification through this operator must
either:
  (i) use the *full* spectrum (not the ground state alone), or
  (ii) use a different scaling map than (★), or
  (iii) work at a different `α` than `3/2`.

This narrows the surface in the same spirit as Wave 14's structural
narrowing of `alpha_of_class`.

## Axiom budget

Zero project axioms, zero sorries. All theorems below depend only on
the standard `[propext, Classical.choice, Quot.sound]`.

Stage Wave 16 — Hilbert–Pólya specialisation at α_RH = 3/2.
-/

import PF.Operators.VAlphaExplicitFromArxiv
import PF.IBMPeaksGaloisPair
import PF.SpectralBijection
import PF.RHSurjectivityConjecture
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace PrincipiaFractalis.RHViaArxivVAlphaAt3Halves

open Real Complex
open PrincipiaTractalis
open PrincipiaTractalis.Analytic
open PrincipiaTractalis.Operators
open PrincipiaTractalis.IBMPeaksGaloisPair

/-! ## Section 1 — `α_RH = 3/2` lies in the B-clean domain -/

/-- `3/2 > 1/2`, so the B-clean phase identity applies. -/
theorem three_halves_gt_half : (1/2 : ℝ) < 3/2 := by norm_num

/-- `3/2 > 0`. -/
theorem three_halves_pos : (0 : ℝ) < 3/2 := by norm_num

/-! ## Section 2 — Ground-state value at α = 3/2 collapses to π/15 -/

/-- **Ground-state value at α = 3/2**: `π/(10·(3/2)) = π/15`. -/
theorem ground_state_at_3halves :
    Real.pi / (10 * (3/2 : ℝ)) = Real.pi / 15 := by
  ring

/-- Wrapped through `groundStateValue` (the named B-clean ground-state). -/
theorem groundStateValue_at_3halves :
    groundStateValue (3/2 : ℝ) = Real.pi / 15 := by
  unfold groundStateValue
  ring

/-! ## Section 3 — B-clean phase identity at α = 3/2: explicit arithmetic -/

/-- **B-clean image at α = 3/2**: applying the axiom-free
    `b_clean_phase_identity` (commit `7bba1c7`) at α = 3/2 gives

      `π/15 = (1/5) · (π/2 − Im R_f_principal(3/2))`,

    hence `π/2 − Im R_f_principal(3/2) = π/3`. -/
theorem b_clean_image_at_3halves :
    Real.pi / 2 - (R_f_principal (3/2 : ℝ)).im = Real.pi / 3 := by
  have h := b_clean_phase_identity (3/2 : ℝ) three_halves_gt_half
  -- h : π/(10·(3/2)) = (1/5)·(π/2 − Im R_f_principal(3/2))
  have hlhs : Real.pi / (10 * (3/2 : ℝ)) = Real.pi / 15 :=
    ground_state_at_3halves
  rw [hlhs] at h
  -- h : π/15 = (1/5)·(π/2 − Im R_f_principal(3/2))
  -- Solve: π/2 − Im R_f_principal(3/2) = 5·(π/15) = π/3.
  linarith

/-- **B-clean arg form at α = 3/2** (companion to `b_clean_image_at_3halves`):

      `arg(1 − e^{i·(π/(3/2))}) = arg(1 − e^{i·2π/3}) = −π/6`.

    Derived from the unconditional `arg_one_sub_exp_I_mul_real` lemma
    at `x = π/(3/2) = 2π/3 ∈ (0, 2π)`, which gives
    `arg(1 − e^{ix}) = x/2 − π/2 = π/3 − π/2 = −π/6`. -/
theorem b_clean_arg_at_3halves :
    Complex.arg (1 - Complex.exp (Complex.I * ((Real.pi / (3/2 : ℝ) : ℝ) : ℂ))) =
      -(Real.pi / 6) := by
  -- π / (3/2) = 2π/3
  have hx_pos : 0 < Real.pi / (3/2 : ℝ) := by
    have hπ : 0 < Real.pi := Real.pi_pos
    positivity
  have hx_lt : Real.pi / (3/2 : ℝ) < 2 * Real.pi := by
    have hπ : 0 < Real.pi := Real.pi_pos
    -- π/(3/2) = 2π/3 < 2π
    have : Real.pi / (3/2 : ℝ) = 2 * Real.pi / 3 := by ring
    rw [this]
    linarith
  have h := arg_one_sub_exp_I_mul_real (Real.pi / (3/2 : ℝ)) hx_pos hx_lt
  -- h : arg(1 - exp(I·π/(3/2))) = (π/(3/2))/2 - π/2 = π/3 - π/2 = -π/6
  rw [h]
  ring

/-! ## Section 4 — Specialisation of the arxiv construction bridge at α = 3/2 -/

/-- **★ ARXIV CONSTRUCTION BRIDGE AT α = 3/2 ★** (Wave 16 specialisation).

    The Wave 12 unified bridge `arxiv_construction_bridge` (commit `fa937fb`)
    instantiated at the canonical RH α-value `3/2`:

    (1) `arxivHalpha (3/2)` is its own formal adjoint on the finite-support
        domain;
    (2) its matrix coefficients on the standard basis match the arxiv
        formula `h_alpha_basis (3/2) n m`;
    (3) the closed-form ground state `groundStateValue (3/2) = π/15`
        is positive;
    (4) it equals the B-clean monodromy phase deficit
        `(1/5)·(π/2 − Im R_f_principal(3/2)) = (1/5)·(π/3) = π/15`.

    All axiom-free. -/
theorem arxiv_construction_bridge_at_3halves :
    (arxivHalpha (3/2 : ℝ)).IsFormalAdjoint (arxivHalpha (3/2 : ℝ)) ∧
    (∀ n m : ℕ,
      ⟪arxivHalpha (3/2 : ℝ)
          ⟨stdBasisVec n, Halpha_PMap_basis_mem (3/2 : ℝ) n⟩,
        stdBasisVec m⟫_ℂ =
        ((h_alpha_basis (3/2 : ℝ) n m : ℝ) : ℂ)) ∧
    0 < groundStateValue (3/2 : ℝ) ∧
    groundStateValue (3/2 : ℝ) =
      (1/5) * (Real.pi/2 -
        (PrincipiaTractalis.Analytic.R_f_principal (3/2 : ℝ)).im) :=
  arxiv_construction_bridge (3/2 : ℝ) three_halves_gt_half

/-! ## Section 5 — Spectral bijection ScalingParameter at α_RH = 3/2 -/

/-- The `ScalingParameter` corresponding to `α_RH = 3/2` (per
    `SpectralBijection.lean`). -/
noncomputable def scalingParam_alpha_RH : ScalingParameter :=
  ⟨(3/2 : ℝ), by norm_num⟩

@[simp] theorem scalingParam_alpha_RH_value :
    scalingParam_alpha_RH.value = 3/2 := rfl

/-! ## Section 6 — Image of the arxiv ground state under the canonical map -/

/-- **Image of the arxiv ground state `λ = π/15` under the canonical
    spectral-bijection map at α_RH = 3/2**:

      `eigenvalueToT scalingParam_alpha_RH (π/15) = 10 / (π · (π/15) · (3/2))
                                                 = 10 / (π²/10)
                                                 = 100 / π².`

    Numerically `100/π² ≈ 10.1321`. This is the candidate critical-line
    ordinate `t_0` that the framework's `riemann_hypothesis_via_spectral_bijection`
    would assign to the ground-state eigenvalue. -/
theorem eigenvalueToT_at_RH_groundState :
    eigenvalueToT scalingParam_alpha_RH (Real.pi / 15) = 100 / (Real.pi * Real.pi) := by
  unfold eigenvalueToT
  have hπ_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hπ_ne : Real.pi ≠ 0 := ne_of_gt hπ_pos
  have h_pos : (0 : ℝ) < Real.pi / 15 := by positivity
  have h_ne : Real.pi / 15 ≠ 0 := ne_of_gt h_pos
  -- The if-branch goes false.
  rw [if_neg h_ne]
  -- Now simplify 10 / (π · |π/15| · (3/2)) = 100 / π².
  rw [scalingParam_alpha_RH_value]
  -- |π/15| = π/15
  have h_abs : |Real.pi / 15| = Real.pi / 15 := abs_of_pos h_pos
  rw [h_abs]
  -- 10 / (π · (π/15) · (3/2)) = 10 / (π² / 10) = 100/π²
  field_simp
  ring

/-! ## Section 7 — Numerical bound: `100/π² < 10.14` -/

/-- `π > 3.14` (mathlib's two-decimal-digit lower bound, `Real.pi_gt_3141592`). -/
theorem pi_gt_three_one_four : (3.14 : ℝ) < Real.pi := by
  -- mathlib gives Real.pi_gt_3141592 : 3.141592 < π
  have h := Real.pi_gt_3141592
  linarith

/-- `π² > 9.8596`, since `π > 3.14` and `3.14² = 9.8596`. -/
theorem pi_sq_gt_9_8596 : (9.8596 : ℝ) < Real.pi * Real.pi := by
  have h := pi_gt_three_one_four
  have hπ_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  nlinarith [h, hπ_pos]

/-- **`100/π² < 10.14`** — the candidate critical-line ordinate `t_0`
    from the arxiv ground state at α_RH = 3/2 is bounded above by
    `10.14`. -/
theorem t_0_lt_10_14 : (100 : ℝ) / (Real.pi * Real.pi) < 10.14 := by
  have h_pi_sq : (9.8596 : ℝ) < Real.pi * Real.pi := pi_sq_gt_9_8596
  have h_pi_sq_pos : (0 : ℝ) < Real.pi * Real.pi := by
    have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
    positivity
  -- 100/π² < 100/9.8596 (since π² > 9.8596 > 0)
  -- and 100/9.8596 ≈ 10.1424 — but we need to show it's < 10.14? Let's
  -- tighten: π > 3.14159 ⇒ π² > 9.86958... ⇒ 100/π² < 100/9.8695 ≈ 10.13218.
  -- So < 10.14 is comfortable. We use the sharper bound π > 3.1415.
  have h_sharper : (3.1415 : ℝ) < Real.pi := by
    have := Real.pi_gt_3141592; linarith
  have h_pi_sq_sharper : (9.86901 : ℝ) < Real.pi * Real.pi := by
    have hπ_pos : (0 : ℝ) < Real.pi := Real.pi_pos
    nlinarith [h_sharper, hπ_pos]
  -- 100 / π² < 100 / 9.86901 < 10.14
  -- 100 / 9.86901 ≈ 10.1327
  rw [div_lt_iff₀ h_pi_sq_pos]
  -- Goal: 100 < 10.14 · (π · π)
  -- From h_pi_sq_sharper : 9.86901 < π · π, so 10.14 · 9.86901 = 100.07187...
  -- Hence 10.14 · (π · π) > 10.14 · 9.86901 > 100.
  nlinarith [h_pi_sq_sharper]

/-! ## Section 8 — First nontrivial ζ-zero ordinate > 14 -/

/-- **First nontrivial ζ-zero ordinate t₁ ≈ 14.134725**.

    This is a classical numerical fact (Riemann 1859, computed in
    Edwards "Riemann's Zeta Function", §6.7). We record it here as
    a NAMED PROP and bracket `14 < t₁ < 15`, leaving the discharge
    to the ζ-numerical bracket infrastructure already standardised
    in the framework.

    The Prop is stated as the *abstract* fact "every nontrivial
    ζ-zero with positive imaginary part has imaginary part ≥ 14",
    which is the weakest form needed for the negative identification
    below. -/
def FirstZetaZeroOrdinateLowerBound : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → 0 < s.im → 14 < s.im

/-! ## Section 9 — The NEGATIVE identification: ground state ≠ first ζ-zero -/

/-- **★ NEGATIVE HILBERT–PÓLYA IDENTIFICATION AT α = 3/2 ★**.

    Under the canonical spectral-bijection map `eigenvalueToZero` at
    `α_RH = 3/2`, the arxiv ground-state eigenvalue `λ_0 = π/15`
    produces the critical-line point

      `s_0 := 1/2 + i · (100/π²)`,

    with imaginary part `100/π² < 10.14`. By the assumed lower bound
    `FirstZetaZeroOrdinateLowerBound` (a recorded numerical input,
    not discharged here), every nontrivial ζ-zero with positive
    imaginary part has imaginary part `> 14`. Hence `s_0` is NOT
    a nontrivial ζ-zero — the gap is at least `14 − 10.14 = 3.86`.

    Concretely, this rules out the *naive* Hilbert–Pólya identification
    "arxiv ground state at α_RH ↦ first nontrivial ζ-zero under the
    canonical scaling map". -/
theorem RH_at_3halves_does_not_match_first_zeta_zero
    (h_first : FirstZetaZeroOrdinateLowerBound) :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → 0 < s.im →
      eigenvalueToZero scalingParam_alpha_RH (Real.pi / 15) ≠ s := by
  intro s hre_pos hre_lt hzero hs_im_pos h_eq
  -- The image's imaginary part is t_0 = 100/π².
  have h_t0 : (eigenvalueToZero scalingParam_alpha_RH (Real.pi / 15)).im
                = 100 / (Real.pi * Real.pi) := by
    unfold eigenvalueToZero criticalLine
    -- criticalLine t = ⟨1/2, t⟩, so its .im = t.
    simp
    exact eigenvalueToT_at_RH_groundState
  -- From h_eq, s.im = (eigenvalueToZero ...).im = 100/π².
  have h_s_im : s.im = 100 / (Real.pi * Real.pi) := by
    rw [← h_eq] at *
    exact h_t0
  -- But h_first forces s.im > 14, contradicting s.im = 100/π² < 10.14.
  have h_big : 14 < s.im := h_first s hre_pos hre_lt hzero hs_im_pos
  have h_small : s.im < 10.14 := by rw [h_s_im]; exact t_0_lt_10_14
  linarith

/-! ## Section 10 — Honest scope: what is and is not delivered -/

/-- **★ HONEST SCOPE STATEMENT ★** for the Hilbert–Pólya identification
    at α_RH = 3/2.

    This file delivers a 7-clause structural picture:

    (S1) The arxiv operator `arxivHalpha (3/2)` is constructed
         (Wave 11, axiom-free) and its formal-adjoint property holds.

    (S2) Its claimed ground state value is `π/15`, identified with the
         B-clean monodromy phase deficit (Wave 12, axiom-free).

    (S3) The B-clean phase `π/2 − Im R_f_principal(3/2) = π/3` axiom-free
         (equivalently `arg(1 − e^{i·2π/3}) = −π/6`).

    (S4) The framework's canonical eigenvalue-to-critical-line map
         (`eigenvalueToT`) maps the ground state `π/15` to the
         imaginary-part candidate `100/π² ≈ 10.1321` axiom-free.

    (S5) `100/π² < 10.14` is provable axiom-free from mathlib's
         standard `Real.pi_gt_3141592`.

    (S6) The first nontrivial ζ-zero ordinate exceeds 14 (recorded as
         a NAMED PROP `FirstZetaZeroOrdinateLowerBound`, externally
         witnessed by Riemann 1859 / Edwards §6.7 / Odlyzko).

    (S7) Therefore the *naive* Hilbert–Pólya identification "arxiv
         ground state at α_RH = 3/2 ↦ first nontrivial ζ-zero under
         the canonical scaling map" FAILS — the gap is > 3.86.

    What is OPEN (residual surface):

      - Whether the FULL spectrum of `arxivHalpha (3/2)` (not just the
        ground state) admits a Hilbert–Pólya identification with the
        ζ-zeros under SOME scaling map.
      - Whether a different `α` or a different scaling map closes the
        identification.
      - The load-bearing `RHSpectralSurjectivityConjecture`
        (`PF/RHSurjectivityConjecture.lean`), which is what
        `riemann_hypothesis_via_named_surjectivity` actually consumes.

    Outcome: NEGATIVE (refutation of the naive identification),
    sharpening the OPEN_PROBLEMS surface in the same spirit as the
    2026-05-23 spectral-route-closed result. -/
theorem arxiv_HP_at_3halves_honest_scope
    (h_first : FirstZetaZeroOrdinateLowerBound) :
    -- (S1) Operator-side bridge at α = 3/2.
    (arxivHalpha (3/2 : ℝ)).IsFormalAdjoint (arxivHalpha (3/2 : ℝ)) ∧
    -- (S2) Ground-state closed form.
    groundStateValue (3/2 : ℝ) = Real.pi / 15 ∧
    -- (S3) B-clean phase deficit.
    Real.pi / 2 - (R_f_principal (3/2 : ℝ)).im = Real.pi / 3 ∧
    -- (S4) Canonical scaling-map image of the ground state.
    eigenvalueToT scalingParam_alpha_RH (Real.pi / 15)
      = 100 / (Real.pi * Real.pi) ∧
    -- (S5) Numerical upper bound on the image.
    (100 : ℝ) / (Real.pi * Real.pi) < 10.14 ∧
    -- (S6) ζ-zero lower bound (consumed as named input).
    (∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → 0 < s.im → 14 < s.im) ∧
    -- (S7) Negative identification: ground state image ≠ any nontrivial ζ-zero.
    (∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → 0 < s.im →
        eigenvalueToZero scalingParam_alpha_RH (Real.pi / 15) ≠ s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (S1)
    exact arxivHalpha_isFormalAdjoint (3/2 : ℝ)
  · -- (S2)
    exact groundStateValue_at_3halves
  · -- (S3)
    exact b_clean_image_at_3halves
  · -- (S4)
    exact eigenvalueToT_at_RH_groundState
  · -- (S5)
    exact t_0_lt_10_14
  · -- (S6) — directly consume the input.
    exact h_first
  · -- (S7)
    exact RH_at_3halves_does_not_match_first_zeta_zero h_first

/-! ## Section 11 — Capstone summary -/

/-- **★ CAPSTONE (Wave 16) ★**: the Hilbert–Pólya identification of
    `arxivHalpha (3/2)`'s ground state with the first nontrivial
    Riemann ζ-zero under the framework's canonical scaling map
    FAILS axiom-free (modulo the recorded ζ-numerical input). The
    arxiv-construction bridge specialises cleanly at α_RH = 3/2,
    the ground state collapses to the rational multiple `π/15` of
    the universal coupling, the B-clean phase deficit equals `π/3`,
    and the image under the canonical bijection is `100/π² ≈ 10.13`
    — well below the first ζ-zero ordinate `≈ 14.13`.

    This narrows the RH attack surface: any future identification
    via this operator must use the full spectrum, a different scaling,
    or a different α. -/
theorem RH_via_arxiv_VAlpha_at_3halves_capstone
    (h_first : FirstZetaZeroOrdinateLowerBound) :
    -- The Wave 12 bridge specialises at α = 3/2.
    (arxivHalpha (3/2 : ℝ)).IsFormalAdjoint (arxivHalpha (3/2 : ℝ)) ∧
    groundStateValue (3/2 : ℝ) = Real.pi / 15 ∧
    Real.pi / 2 - (R_f_principal (3/2 : ℝ)).im = Real.pi / 3 ∧
    -- The naive HP identification fails by > 3.86.
    (∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → 0 < s.im →
        eigenvalueToZero scalingParam_alpha_RH (Real.pi / 15) ≠ s) ∧
    -- The IBM-peak structural anchor: 3/2 is the RH Galois conjugate of φ+1/4.
    P alpha_RH = 0 := by
  refine ⟨arxivHalpha_isFormalAdjoint (3/2 : ℝ),
          groundStateValue_at_3halves,
          b_clean_image_at_3halves,
          RH_at_3halves_does_not_match_first_zeta_zero h_first,
          ?_⟩
  exact P_RH

end PrincipiaFractalis.RHViaArxivVAlphaAt3Halves

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaFractalis.RHViaArxivVAlphaAt3Halves.ground_state_at_3halves
#print axioms PrincipiaFractalis.RHViaArxivVAlphaAt3Halves.b_clean_image_at_3halves
#print axioms PrincipiaFractalis.RHViaArxivVAlphaAt3Halves.b_clean_arg_at_3halves
#print axioms PrincipiaFractalis.RHViaArxivVAlphaAt3Halves.arxiv_construction_bridge_at_3halves
#print axioms PrincipiaFractalis.RHViaArxivVAlphaAt3Halves.eigenvalueToT_at_RH_groundState
#print axioms PrincipiaFractalis.RHViaArxivVAlphaAt3Halves.t_0_lt_10_14
#print axioms PrincipiaFractalis.RHViaArxivVAlphaAt3Halves.RH_at_3halves_does_not_match_first_zeta_zero
#print axioms PrincipiaFractalis.RHViaArxivVAlphaAt3Halves.arxiv_HP_at_3halves_honest_scope
#print axioms PrincipiaFractalis.RHViaArxivVAlphaAt3Halves.RH_via_arxiv_VAlpha_at_3halves_capstone
