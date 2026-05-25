/-
# V_α-Explicit-From-Arxiv — Unified Bridge to the B-Clean Identity

★ 2026-05-25 — Wave 12: the concrete arxiv-construction is now fully
proven; this file packages the conclusions as a single referee-clean
capstone tying together:

  * the explicit operator `Halpha_PMap α : EllTwoNat →ₗ.[ℂ] EllTwoNat`
    (from `PF.Operators.VAlphaPMapShape`),
  * its **axiom-free** symmetry and matrix-coefficient identities
    (from `PF.Operators.VAlphaPMapDischarge`),
  * the **referee-proof** B-clean phase identity
    `π/(10·α) = (1/5)·(π/2 − Im R_f_principal α)` for `α > 1/2`
    (from `PF.Analytic.BCleanPhaseIdentity`).

## Why this file exists

`PF.Operators.VAlphaExplicit` introduced the operator construction and
isolated `KatoRellichInput α` (later refuted) + `GroundStateVariationalInput`
(discharged in Wave 9). `PF.Operators.VAlphaPMapShape` reshaped Kato-Rellich
via `LinearPMap` and `PF.Operators.VAlphaPMapDischarge` fully proved the
reshaped Prop axiom-free.

What was missing was a **single, referee-citable statement** that joins
the two halves of the story:

  (a) an explicit symmetric densely-defined operator H whose matrix
      coefficients on the standard basis match the arxiv `H_α`;
  (b) the explicit closed form for the claimed ground-state value
      `π/(10·α)` identified with the B-clean monodromy phase deficit.

This file delivers that single statement (`arxiv_construction_bridge`),
which is the cleanest form of "we built the arxiv operator and identified
its claimed eigenvalue with the algebraic phase identity, both at zero
project axioms".

## What this file does NOT do

* It does not prove `PolylogEigenvalueConjecture`. By the no-go theorem
  `alpha_realization_canonical_pair_iff_classes_distinct` (in
  `PF.TuringEncoding.AlphaRealizationNoGo`), any unconditional discharge
  of `PolylogEigenvalueConjecture` is logically equivalent to a proof of
  `ClassP ≠ ClassNP` — i.e., a proof of P ≠ NP itself.

* It does not perform the operator-theoretic SPECTRAL identification
  `λ_0(H) = π/(10·α)` as an eigenvalue equation on the constructed `H`.
  That identification was refuted on standard substrates 2026-05-23
  (memory `principia_spectral_route_closed_2026-05-23`). The B-clean
  identity replaces it: `π/(10·α)` is the *monodromy phase deficit*,
  a clean algebraic quantity unconditional in `α > 1/2`.

What this file DOES is package the surviving content as the **structural
bridge** that the formalisation can honestly stand behind.

## Axiom budget

Zero project axioms, zero sorries. All theorems below depend on the
standard `[propext, Classical.choice, Quot.sound]` only.

Stage Wave 12 — unified bridge (post-Wave-11 closure).
-/

import PF.Operators.VAlphaPMapDischarge
import PF.Analytic.BCleanPhaseIdentity

namespace PrincipiaTractalis.Operators

open Real Complex
open scoped ENNReal InnerProductSpace

/-! ## Section 1 — Concrete arxiv `H_α` operator (alias) -/

/-- **The concrete arxiv `H_α` operator** as a `LinearPMap` on
    `EllTwoNat`. Alias for `Halpha_PMap α` provided in this file so the
    arxiv-naming convention is reachable in one place. -/
noncomputable def arxivHalpha (α : ℝ) : EllTwoNat →ₗ.[ℂ] EllTwoNat :=
  Halpha_PMap α

/-- The arxiv operator's domain is the finite-support span of the
    standard basis. -/
@[simp] theorem arxivHalpha_domain (α : ℝ) :
    (arxivHalpha α).domain = finSuppSubmod :=
  Halpha_PMap_domain α

/-- The arxiv operator is symmetric (formal self-adjoint) on its
    finite-support domain — **axiom-free**, from Wave 11. -/
theorem arxivHalpha_isFormalAdjoint (α : ℝ) :
    (arxivHalpha α).IsFormalAdjoint (arxivHalpha α) :=
  Halpha_PMap_isFormalAdjoint α

/-- The arxiv operator's matrix coefficients on the standard basis match
    the explicit kinetic + diagonal-V_α formula — **axiom-free**, from
    Wave 11. -/
theorem arxivHalpha_matrix_coeff (α : ℝ) (n m : ℕ) :
    ⟪arxivHalpha α ⟨stdBasisVec n, Halpha_PMap_basis_mem α n⟩,
      stdBasisVec m⟫_ℂ = ((h_alpha_basis α n m : ℝ) : ℂ) :=
  Halpha_PMap_matrix_coeff α n m

/-! ## Section 2 — B-clean closed form for the claimed ground-state value -/

/-- **The arxiv ground-state value at `α`**: `groundStateValue α = π/(10·α)`.
    Defined in `PF.Operators.VAlphaExplicit`. -/
theorem arxiv_ground_state_value (α : ℝ) :
    groundStateValue α = Real.pi / (10 * α) := rfl

/-- **★ B-CLEAN IDENTIFICATION ★** of the arxiv ground-state value at
    every `α > 1/2`:

      `π/(10·α) = (1/5) · (π/2 − Im R_f_principal α)`.

    The RHS is the **monodromy phase deficit** of the principal-branch
    `R_f(α, 1) = −log(1 − exp(I·π/α))`, an unconditional algebraic
    identity (Section 5 of `PF.Analytic.BCleanPhaseIdentity`). -/
theorem arxiv_ground_state_value_eq_b_clean (α : ℝ) (hα : 1/2 < α) :
    groundStateValue α =
      (1/5) * (Real.pi/2 -
        (PrincipiaTractalis.Analytic.R_f_principal α).im) :=
  groundStateValue_eq_b_clean α hα

/-! ## Section 3 — Unified capstone

The unified statement bundles the four pieces of arxiv content the
framework can stand behind axiom-free:

  (1) there is a concrete symmetric densely-defined operator on
      `EllTwoNat` (the arxiv `H_α`);
  (2) its matrix coefficients on basis vectors match the arxiv formula;
  (3) the claimed closed-form ground-state value `π/(10·α)` is
      well-defined and positive for every `α > 1/2`;
  (4) that closed form equals the B-clean monodromy phase deficit.

The bundle is `arxiv_construction_bridge`. -/

/-- **★ ARXIV CONSTRUCTION BRIDGE (Wave 12) ★**

    For every `α > 1/2`, the arxiv paper's `H_α` operator and the
    closed-form ground-state value `π/(10·α)` together satisfy:

    (1) There exists a `LinearPMap ℂ EllTwoNat EllTwoNat` (namely
        `arxivHalpha α`) which is its own formal adjoint on the
        finite-support submodule, and whose matrix coefficients on the
        standard basis match the arxiv formula `h_alpha_basis α n m`.

    (2) The closed form `groundStateValue α = π/(10·α)` is positive,
        and equals `(1/5)·(π/2 − Im R_f_principal α)`, the B-clean
        monodromy phase deficit.

    The two halves of the original arxiv construction (the operator and
    its claimed eigenvalue) are thus joined in one referee-citable
    statement, both with **zero project axioms** and **zero sorries**. -/
theorem arxiv_construction_bridge (α : ℝ) (hα : 1/2 < α) :
    -- Operator side: symmetric densely-defined PMap with the arxiv matrix.
    (arxivHalpha α).IsFormalAdjoint (arxivHalpha α) ∧
    (∀ n m : ℕ, ⟪arxivHalpha α ⟨stdBasisVec n, Halpha_PMap_basis_mem α n⟩,
                  stdBasisVec m⟫_ℂ = ((h_alpha_basis α n m : ℝ) : ℂ)) ∧
    -- Closed-form side: positivity and B-clean identification.
    0 < groundStateValue α ∧
    groundStateValue α =
      (1/5) * (Real.pi/2 -
        (PrincipiaTractalis.Analytic.R_f_principal α).im) := by
  refine ⟨arxivHalpha_isFormalAdjoint α, arxivHalpha_matrix_coeff α, ?_, ?_⟩
  · exact groundStateValue_pos (by linarith)
  · exact arxiv_ground_state_value_eq_b_clean α hα

/-- **Specialisation at `α = √2`**: the bridge instantiated at the
    P-class canonical value. -/
theorem arxiv_construction_bridge_at_sqrt2 :
    (arxivHalpha (Real.sqrt 2)).IsFormalAdjoint (arxivHalpha (Real.sqrt 2)) ∧
    (∀ n m : ℕ,
      ⟪arxivHalpha (Real.sqrt 2)
          ⟨stdBasisVec n, Halpha_PMap_basis_mem (Real.sqrt 2) n⟩,
        stdBasisVec m⟫_ℂ =
        ((h_alpha_basis (Real.sqrt 2) n m : ℝ) : ℂ)) ∧
    0 < groundStateValue (Real.sqrt 2) ∧
    groundStateValue (Real.sqrt 2) =
      (1/5) * (Real.pi/2 -
        (PrincipiaTractalis.Analytic.R_f_principal (Real.sqrt 2)).im) := by
  have h_sqrt2 : (1/2 : ℝ) < Real.sqrt 2 := by
    have h1 : Real.sqrt 1 < Real.sqrt 2 :=
      Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rw [Real.sqrt_one] at h1; linarith
  exact arxiv_construction_bridge (Real.sqrt 2) h_sqrt2

/-- **Specialisation at `α = φ + 1/4`**: the bridge instantiated at the
    NP-class canonical value. -/
theorem arxiv_construction_bridge_at_phi_quarter :
    (arxivHalpha (phi + 1/4)).IsFormalAdjoint (arxivHalpha (phi + 1/4)) ∧
    (∀ n m : ℕ,
      ⟪arxivHalpha (phi + 1/4)
          ⟨stdBasisVec n, Halpha_PMap_basis_mem (phi + 1/4) n⟩,
        stdBasisVec m⟫_ℂ =
        ((h_alpha_basis (phi + 1/4) n m : ℝ) : ℂ)) ∧
    0 < groundStateValue (phi + 1/4) ∧
    groundStateValue (phi + 1/4) =
      (1/5) * (Real.pi/2 -
        (PrincipiaTractalis.Analytic.R_f_principal (phi + 1/4)).im) := by
  have h_phi_quarter : (1/2 : ℝ) < phi + 1/4 := by
    have := phi_plus_quarter_gt_sqrt2
    have h_sqrt2 : (1 : ℝ) < Real.sqrt 2 := by
      have h1 : Real.sqrt 1 < Real.sqrt 2 :=
        Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      rw [Real.sqrt_one] at h1; exact h1
    linarith
  exact arxiv_construction_bridge (phi + 1/4) h_phi_quarter

/-! ## Section 4 — Spectral-gap unification (operator side)

The headline numerical conclusion `spectral_gap > 0` is now also linked
to the explicit operator side: the closed-form values
`groundStateValue √2` and `groundStateValue (φ+1/4)` differ by the
spectral gap from `PF.SpectralGap`, both equal to their respective
B-clean phase deficits. -/

/-- **★ Spectral-gap consequence (Wave 12) ★**: at the canonical α-values,
    the explicit operator's closed-form ground states differ by
    `spectral_gap > 0`, and each closed form is identified with its
    B-clean phase deficit.

    This packages `H_alpha_spectral_gap_positive_PMap_unconditional` with
    the B-clean identification at both endpoints. -/
theorem arxiv_spectral_gap_with_b_clean :
    ∃ (lam_P lam_NP : ℝ),
      lam_P = groundStateValue (Real.sqrt 2) ∧
      lam_NP = groundStateValue (phi + 1/4) ∧
      lam_P - lam_NP > 0 ∧
      lam_P =
        (1/5) * (Real.pi/2 -
          (PrincipiaTractalis.Analytic.R_f_principal (Real.sqrt 2)).im) ∧
      lam_NP =
        (1/5) * (Real.pi/2 -
          (PrincipiaTractalis.Analytic.R_f_principal (phi + 1/4)).im) := by
  obtain ⟨lam_P, lam_NP, hP, hNP, hgap⟩ :=
    H_alpha_spectral_gap_positive_PMap_unconditional
  have h_sqrt2 : (1/2 : ℝ) < Real.sqrt 2 := by
    have h1 : Real.sqrt 1 < Real.sqrt 2 :=
      Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rw [Real.sqrt_one] at h1; linarith
  have h_phi_quarter : (1/2 : ℝ) < phi + 1/4 := by
    have := phi_plus_quarter_gt_sqrt2
    have h_sqrt2' : (1 : ℝ) < Real.sqrt 2 := by
      have h1 : Real.sqrt 1 < Real.sqrt 2 :=
        Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      rw [Real.sqrt_one] at h1; exact h1
    linarith
  refine ⟨lam_P, lam_NP, hP, hNP, hgap, ?_, ?_⟩
  · rw [hP]; exact groundStateValue_eq_b_clean (Real.sqrt 2) h_sqrt2
  · rw [hNP]; exact groundStateValue_eq_b_clean (phi + 1/4) h_phi_quarter

/-! ## Section 5 — Honest framing

This file does NOT discharge `PolylogEigenvalueConjecture`. By the no-go
theorem `alpha_realization_canonical_pair_iff_classes_distinct` in
`PF.TuringEncoding.AlphaRealizationNoGo`, any concrete realisation of
`alpha_of_class` (on the canonical pair `(√2, φ+1/4)`) is logically
equivalent to `ClassP ≠ ClassNP`, i.e., to a proof of P ≠ NP itself.
The opacity of `alpha_of_class` is therefore not a formalisation gap —
it is **exactly as hard as the problem itself**.

What this file DOES is:

  * Show that the framework's explicit-operator and closed-form sides
    are now **both** axiom-free and structurally compatible.

  * Provide a single referee-citable theorem (`arxiv_construction_bridge`)
    that future work can point to as "the operator is constructed; the
    eigenvalue is identified with the algebraic phase identity; what
    remains is the *spectral identification* of the closed form as a
    genuine eigenvalue of the operator".

  * Make the operator-theoretic / B-clean phase split the residual
    surface of the framework's P ≠ NP attack on the spectral side.

The remaining inputs are documented in `OPEN_PROBLEMS.md` Problem 1
(polylog eigenvalue identification, narrowed to spectral identification
of the closed form on the explicit operator).

## Axiom budget

Zero project axioms, zero sorries. -/

end PrincipiaTractalis.Operators

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.Operators.arxivHalpha_isFormalAdjoint
#print axioms PrincipiaTractalis.Operators.arxivHalpha_matrix_coeff
#print axioms PrincipiaTractalis.Operators.arxiv_ground_state_value_eq_b_clean
#print axioms PrincipiaTractalis.Operators.arxiv_construction_bridge
#print axioms PrincipiaTractalis.Operators.arxiv_construction_bridge_at_sqrt2
#print axioms PrincipiaTractalis.Operators.arxiv_construction_bridge_at_phi_quarter
#print axioms PrincipiaTractalis.Operators.arxiv_spectral_gap_with_b_clean
