/-
# RH Maximally-Discharged Wrapper

This file delivers the **maximally-discharged form** of the Principia
Fractalis Riemann Hypothesis chain, consolidating the Phase A inner-product
discharge work of May 2026 (commits f727998, e09e571, cd7a806) into a
single user-facing entry point.

## Background

The capstone `riemann_hypothesis_via_T3_sym_framework` in
`PF/SpectralBijection.lean` originally took FOUR hypothesis bundles:

  1. Phase A inner-product structure on `LogWeightedL2` (three sub-hypotheses:
     `hsmul_left`, `hsmul_right`, `hpos_def`).
  2. Spectral-theorem witness (eigenvalue sequence with `1/n` decay).
  3. Non-degeneracy (nonzero, distinct moduli).
  4. Surjectivity onto nontrivial ζ-zeros — the LOAD-BEARING open conjecture.

The May 2026 work proved all three Phase A sub-hypotheses as theorems:
  * `hsmul_left_LogWeightedL2`  (from `LogWeightedL2.inner_smul_left`)
  * `hsmul_right_LogWeightedL2` (from `LogWeightedL2.inner_smul_right`)
  * `hpos_def_LogWeightedL2`    (via 7-step `MemLp.integrable_norm_pow` chain)

This file re-exposes `riemann_hypothesis_via_T3_sym_framework_fully_discharged`
under the name `riemann_hypothesis_residual_only`, making the residual
hypothesis bundle (bundles 2, 3, 4 — the genuinely-open content) the only
thing the caller must supply.

## What the user supplies (RESIDUAL HYPOTHESES)

  (a) `eigenvalues, hev, K, hK, hbound` — spectral-theorem witness
      (mathlib `IsCompactOperator` API hookup — research engineering).
  (b) `α, hne, hdistinct` — non-degeneracy of the spectrum (numerical
      verification, Mayer 1991).
  (c) `surjectivity` — THE load-bearing open mathematical conjecture
      (det/trace-formula completion, Manuscript Ch 20
      `rem:bijection-surjectivity`).

ZERO project axioms; ZERO `sorry`.
-/
import PF.SpectralBijection

namespace PrincipiaTractalis

open scoped InnerProductSpace

/-- **★★★★ RH residual-only wrapper ★★★★**

    Maximally-discharged form of `riemann_hypothesis_via_T3_sym_framework`.
    All three Phase A inner-product hypotheses are discharged internally
    via `hsmul_left_LogWeightedL2`, `hsmul_right_LogWeightedL2`,
    `hpos_def_LogWeightedL2` (proven theorems in `SpectralBijection.lean`).

    The caller need only supply the residual bundle:

      * Spectral-theorem witness (`eigenvalues, hev, K, hK, hbound`).
      * Non-degeneracy (`α, hne, hdistinct`).
      * Surjectivity (`surjectivity`) — the load-bearing open conjecture.

    Same discipline as the May 20 cascade refactor that retired
    `alpha_class_polylog_eigenvalue_conjecture`: the open content is
    surfaced explicitly; the discharged content is internalised.

    Build state: ZERO project axioms; ZERO `sorry`. -/
theorem riemann_hypothesis_residual_only
    -- Spectral-theorem witness (eigenvalue sequence with 1/n decay)
    (eigenvalues : ℕ → ℝ)
    (h_eig_spec : ∀ n : ℕ, IsEigenvalue T3_sym.apply ((eigenvalues n : ℂ)))
    (K : ℝ) (hK_pos : K > 0)
    (h_K_bound : ∀ n : ℕ, |eigenvalues n| ≤ K / ((n : ℝ) + 1))
    -- Non-degeneracy (nonzero, distinct moduli)
    (α : ScalingParameter)
    (h_nonzero : ∀ n, eigenvalues n ≠ 0)
    (h_distinct : ∀ n m, n ≠ m → |eigenvalues n| ≠ |eigenvalues m|)
    -- Surjectivity onto nontrivial ζ-zeros (LOAD-BEARING open conjecture)
    (h_surjectivity : ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 →
        ∃ n : ℕ, eigenvalueToZero α (eigenvalues n) = s) :
    RiemannHypothesis :=
  riemann_hypothesis_via_T3_sym_framework_fully_discharged
    eigenvalues h_eig_spec K hK_pos h_K_bound
    α h_nonzero h_distinct
    h_surjectivity

/-! ## Axiom-freeness verification

The following `#print axioms` commands certify that
`riemann_hypothesis_residual_only` and its Phase A inputs depend on
ZERO project axioms — only mathlib's standard
`propext`, `Classical.choice`, `Quot.sound`. -/

#print axioms riemann_hypothesis_residual_only
#print axioms hsmul_left_LogWeightedL2
#print axioms hsmul_right_LogWeightedL2
#print axioms hpos_def_LogWeightedL2
#print axioms riemann_hypothesis_via_T3_sym_framework_fully_discharged

end PrincipiaTractalis
