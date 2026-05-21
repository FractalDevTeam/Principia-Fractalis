/-
# RH Spectral Witness Bundle: Structural Packaging + Discharge Wrapper

This file delivers a **structural packaging** of bundle (a) — the
spectral-witness bundle — of `riemann_hypothesis_residual_only` from
`PF/Analytic/RHMaxDischarged.lean`, plus an explicit discharge wrapper
that consumes the packaging structure.

## Background — bundle (a) state

The current residual `riemann_hypothesis_residual_only` exposes 5
hypotheses in bundle (a):

  * `eigenvalues : ℕ → ℝ`
  * `h_eig_spec : ∀ n, IsEigenvalue T3_sym.apply ↑(eigenvalues n)`
  * `K : ℝ`
  * `hK_pos : K > 0`
  * `h_K_bound : ∀ n, |eigenvalues n| ≤ K / (n+1)`

These collectively assert: "T₃_sym admits a discrete eigenvalue sequence
with decay rate `K/(n+1)`".

## Structural gap identified in this session (2026-05-21)

`T3_sym.apply : LogWeightedL2 → LogWeightedL2` is a **bare function**,
not a `ContinuousLinearMap`. The Mathlib `IsCompactOperator` API
(`Mathlib.Analysis.Normed.Operator.Compact`) requires its argument to
be a CLM. Therefore the natural path

  `IsCompactOperator T3_sym.apply  ⟹  eigenvalue sequence + 1/n decay`

cannot proceed in a single session — it requires first wrapping `T3_sym`
as a `LogWeightedL2 →L[ℂ] LogWeightedL2`, which is multi-week work
(bounding the operator norm of `T3_sym_action`, then constructing the
CLM via `LinearMap.mkContinuous`).

The mature compact-operator infrastructure in this codebase
(`PF/Analytic/HPOperatorConstruction.lean`,
`PF/Analytic/HNPOperatorConstruction.lean`) lives on `Lp ℂ 2 μ` for
the **Cantor substrate** (`H_P_canonical`, `H_NP_canonical`), not on
`LogWeightedL2`. Even with `H_P` compact + self-adjoint, an isomorphism
`Lp ℂ 2 μ_Cantor ≃ₗᵢ[ℂ] LogWeightedL2` is needed to transport spectral
data — and no such bridge exists in this codebase yet.

## What this file delivers (NO SORRY)

1. **`T3SymSpectralWitness`** — a `structure` packaging bundle (a) as a
   single value. The structure has exactly the five fields that the
   `riemann_hypothesis_residual_only` caller must supply.

2. **`riemann_hypothesis_residual_after_spectral_witness`** — a wrapper
   that takes a `T3SymSpectralWitness` plus bundles (b) (non-degeneracy)
   and (c) (surjectivity) and produces `RiemannHypothesis`. This
   factors `riemann_hypothesis_residual_only` through the structural
   witness, making the spectral-witness bundle a single named input.

3. **`T3SymSpectralWitness.from_compact_operator_witness`** — a future-
   facing `def : Prop` documenting precisely what mathlib infrastructure
   would discharge the witness once T3_sym is wrapped as a CLM and
   the compact-operator spectral theorem is invoked. (No constructor
   given — this is a documentation Prop, not an axiom.)

## Discharge state after this file

After consuming the wrapper:

  * Bundle (a) collapsed to: produce a `T3SymSpectralWitness` value
    (mathlib `IsCompactOperator` + CLM wrapping for `T3_sym`, plus
    eigenvalue-decay extraction — multi-week research engineering).
  * Bundle (b) unchanged: empirical non-degeneracy (Mayer 1991).
  * Bundle (c) unchanged: surjectivity (LOAD-BEARING open conjecture).

ZERO project axioms; ZERO `sorry`.
-/
import PF.Analytic.RHMaxDischarged

namespace PrincipiaTractalis

open scoped InnerProductSpace

/-! ## 1. The spectral-witness packaging structure -/

/-- **`T3SymSpectralWitness`** — packaging of bundle (a) of
    `riemann_hypothesis_residual_only` as a single Lean value.

    A value of this type asserts: `T₃^sym` admits a discrete eigenvalue
    sequence `(eigenvalues n)_{n : ℕ}` of real numbers, each a genuine
    eigenvalue of `T₃^sym.apply`, with modulus bounded by `K/(n+1)`
    for some positive constant `K`.

    Provenance (when produced): mathlib `IsCompactOperator` API applied
    to a CLM wrapping of `T3_sym`, combined with the standard compact
    self-adjoint spectral theorem yielding an eigenvalue sequence
    accumulating at 0, plus a Hilbert-Schmidt singular-value
    asymptotics to give the explicit `K/(n+1)` bound. -/
structure T3SymSpectralWitness where
  /-- The eigenvalue sequence (real, since `T₃^sym` is self-adjoint
      on `LogWeightedL2` per the proven `T3_self_adjoint_conj`). -/
  eigenvalues : ℕ → ℝ
  /-- Each entry is a genuine eigenvalue of `T₃^sym.apply`. -/
  h_eig_spec : ∀ n : ℕ, IsEigenvalue T3_sym.apply ((eigenvalues n : ℂ))
  /-- The decay-rate constant `K`. -/
  K : ℝ
  /-- Positivity of the decay constant. -/
  hK_pos : K > 0
  /-- The `1/n`-style decay bound. -/
  h_K_bound : ∀ n : ℕ, |eigenvalues n| ≤ K / ((n : ℝ) + 1)

/-! ## 2. The discharge wrapper -/

/-- **★★★★ RH residual-only wrapper, with bundle (a) packaged ★★★★**

    Same as `riemann_hypothesis_residual_only` but takes the
    spectral-witness bundle (a) as a single `T3SymSpectralWitness`
    value instead of five separate hypotheses.

    The remaining caller obligation is to supply:
      * a `T3SymSpectralWitness` (mathlib `IsCompactOperator` route,
        research engineering);
      * bundle (b): non-degeneracy (`α, h_nonzero, h_distinct` —
        Mayer 1991 numerical verification);
      * bundle (c): surjectivity (`h_surjectivity` — THE load-bearing
        open mathematical conjecture).

    Build state: ZERO project axioms; ZERO `sorry`. -/
theorem riemann_hypothesis_residual_after_spectral_witness
    (W : T3SymSpectralWitness)
    -- Bundle (b): non-degeneracy
    (α : ScalingParameter)
    (h_nonzero : ∀ n, W.eigenvalues n ≠ 0)
    (h_distinct : ∀ n m, n ≠ m → |W.eigenvalues n| ≠ |W.eigenvalues m|)
    -- Bundle (c): surjectivity (LOAD-BEARING open conjecture)
    (h_surjectivity : ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 →
        ∃ n : ℕ, eigenvalueToZero α (W.eigenvalues n) = s) :
    RiemannHypothesis :=
  riemann_hypothesis_residual_only
    W.eigenvalues W.h_eig_spec W.K W.hK_pos W.h_K_bound
    α h_nonzero h_distinct
    h_surjectivity

/-! ## 3. Documentation Prop: what infrastructure would discharge the witness -/

/-- **`T3SymCompactCLMWitness`** — documentation `Prop` describing
    the mathlib infrastructure that would discharge a
    `T3SymSpectralWitness`. NOT an axiom; NO constructor; this is
    purely a forward-facing target spec.

    A discharge along this route would consist of:

      (i)   a `ContinuousLinearMap` wrapping of `T3_sym`,
            `T3_sym_CLM : LogWeightedL2 →L[ℂ] LogWeightedL2`
            (requires bounding `‖T3_sym_action f‖ ≤ C · ‖f‖`);
      (ii)  `IsCompactOperator T3_sym_CLM` (Hilbert-Schmidt route or
            finite-rank tower via `isCompactOperator_of_tendsto`);
      (iii) self-adjointness of `T3_sym_CLM` (already known at the
            bare-function level: `T3_self_adjoint_conj`); transfer
            to the CLM form requires `LinearMap.IsSymmetric` packaging;
      (iv)  invocation of the compact self-adjoint spectral theorem
            yielding an `EigenvalueSequence`;
      (v)   Weyl/Hilbert-Schmidt decay bound `|λ_n| ≤ K/(n+1)`
            extracted from the operator's Hilbert-Schmidt norm. -/
def T3SymCompactCLMWitnessDescription : Prop :=
  ∃ (_T3_sym_CLM : LogWeightedL2 →L[ℂ] LogWeightedL2),
    -- (i) the CLM agrees with T3_sym at the action level
    (∀ f, _T3_sym_CLM f = T3_sym.apply f) ∧
    -- (ii) it is a compact operator
    IsCompactOperator _T3_sym_CLM ∧
    -- (iii) it is symmetric (= self-adjoint at the linear-map level
    --       on a Hilbert space — `LinearMap.IsSymmetric` is the
    --       predicate that lifts to `IsSelfAdjoint` once the Hilbert-
    --       adjoint instance is established for the CLM)
    (_T3_sym_CLM : LogWeightedL2 →ₗ[ℂ] LogWeightedL2).IsSymmetric

/-- **Conditional**: if `T3SymCompactCLMWitnessDescription` holds, then
    a `T3SymSpectralWitness` can in principle be extracted via the
    compact self-adjoint spectral theorem.

    NOTE: this is stated as a Prop-level *target*, not a theorem.
    The actual extraction requires further mathlib infrastructure
    (an `ℕ`-indexed eigenvalue enumeration for the discrete spectrum
    of a compact self-adjoint operator plus a Weyl-type decay bound)
    that goes beyond `Mathlib.Analysis.InnerProductSpace.Spectrum` —
    that module currently treats only the finite-dimensional case
    (see lines 244-270 of mathlib's Spectrum.lean, which all assume
    `Module.finrank 𝕜 E = n`).

    The corresponding infinite-dim compact-operator spectral theorem
    is the missing piece in mathlib. Once it lands (or once the
    project builds a manual eigenvalue-enumeration helper from the
    finite-rank tower), the discharge becomes mechanical. -/
def T3SymSpectralWitnessExtractionTarget : Prop :=
  T3SymCompactCLMWitnessDescription → Nonempty T3SymSpectralWitness

/-! ## 4. Axiom-freeness verification

The following `#print axioms` commands certify that the wrapper and the
documentation Props depend on ZERO project axioms — only mathlib's
standard `propext`, `Classical.choice`, `Quot.sound`. -/

#print axioms T3SymSpectralWitness
#print axioms riemann_hypothesis_residual_after_spectral_witness
#print axioms T3SymCompactCLMWitnessDescription
#print axioms T3SymSpectralWitnessExtractionTarget

end PrincipiaTractalis
