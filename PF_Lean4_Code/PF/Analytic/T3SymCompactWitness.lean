/-
# T3_sym Compact Witness Infrastructure: Discharge Chain for Bundle (a)

This file pushes past the three blockers documented in
`PF/Analytic/RHSpectralWitness.lean` and delivers concrete partial
progress on bundle (a) — the spectral-witness bundle — of
`riemann_hypothesis_residual_only` from `PF/Analytic/RHMaxDischarged.lean`.

## Blockers identified by the previous agent

  1. `T3_sym.apply : LogWeightedL2 → LogWeightedL2` is a **bare function**,
     not a `ContinuousLinearMap`. The Mathlib `IsCompactOperator` API
     requires its argument to be a CLM.
  2. Mathlib lacks an `ℕ`-indexed compact-operator spectral theorem
     in the version pinned by this project
     (`Mathlib.Analysis.InnerProductSpace.Spectrum` only treats the
     finite-dim case via `Module.finrank 𝕜 E = n`).
  3. `LogWeightedL2 → Lp ℂ 2 μ` isomorphism — actually a definitional
     equality (`def LogWeightedL2 := MeasureTheory.Lp ℂ 2 (logWeightedMeasure.restrict (Ioo 0 1))`
     post the 2026-05-08 refactor). Blocker #3 is therefore vacuous —
     `LogWeightedL2` *is* the Lp form already.

## What this file delivers (NO SORRY, NO AXIOMS)

  1. **`T3SymCLMSymmetricWitness`** — structured Prop packaging:
     "a self-adjoint `LogWeightedL2 →L[ℂ] LogWeightedL2` CLM exists
     whose action agrees with `T3_sym.apply`". This packages
     Blocker #1 as a named target.

  2. **`T3SymFiniteRankTower`** — analog of `H_P_finiteRankTower` from
     `PF/Analytic/HPOperatorConstruction.lean:207`. A finite-rank tower
     witness for a candidate `T3_sym` CLM, allowing compactness via
     mathlib's `isCompactOperator_of_tendsto`.

  3. **`T3_sym_clm_isCompactOperator_of_finiteRankTower`** — extraction
     theorem from tower to `IsCompactOperator`. Mirror of
     `H_P_construction_isCompactOperator_of_finiteRankTower`.

  4. **`T3SymEigenvalueExtraction`** — structured Prop encoding the
     output of the (currently mathlib-missing) compact self-adjoint
     spectral theorem on a CLM that agrees with `T3_sym.apply`. An
     `ℕ`-indexed eigenvalue sequence with `K/(n+1)` decay. Bridges to
     `T3SymSpectralWitness`.

  5. **`T3_sym_spectralWitness_from_witnesses`** — conditional
     extraction of a `T3SymSpectralWitness` from the CLM-agreement
     witness + an eigenvalue-extraction witness.

  6. **`riemann_hypothesis_residual_after_witness_discharge`** — the
     end-to-end discharge wrapper. Given a CLM witness, a tower
     witness (for compactness), an eigenvalue-extraction witness,
     plus bundles (b) and (c), produces `RiemannHypothesis`.

## Discharge state after this file

After consuming the wrapper, the remaining caller obligations are:

  * **Bundle (a) factored** into three named open Props, each at
    mathlib-API granularity (Symmetric CLM = Mayer 1991 §2 packaging
    + adjoint CLM construction; FiniteRankTower = Grothendieck
    nuclear-class theory or Mercer decomposition; Eigenvalue extraction
    = mathlib's missing `ℕ`-indexed compact self-adjoint spectral
    theorem). NONE are axioms — all are honestly named Props with
    concrete extraction targets in mathlib's near future.
  * **Bundle (b)** unchanged: Mayer 1991 numerical non-degeneracy.
  * **Bundle (c)** unchanged: surjectivity (LOAD-BEARING open
    conjecture).

ZERO project axioms; ZERO `sorry`.

## Honest framing

This file does NOT prove that T3_sym is compact (compactness of T3 is
substantive content — Mayer 1991 §3 uses analytic-continuation arguments
to a holomorphic extension plus Grothendieck nuclear-class theory, none
of which is currently in mathlib).

What it DOES deliver:

  (a) A factoring of the "spectral witness" gap into three smaller,
      named, axiom-free Props matching mathlib's actual API surface.
  (b) An end-to-end discharge chain that reduces the bundle (a) gap
      to one structured input per name (CLM + tower + extraction),
      mirroring the project's pattern in `H_P_finiteRankTower` and
      `GroundStateEigenvalueTarget`.
  (c) Mechanical extraction of `T3SymSpectralWitness` once the three
      pieces are supplied.

This is the same disciplined pattern the project applies elsewhere
(see `H_P_construction_axiom_retirement_certificate` for the
load-bearing parallel): surface what is open as a named Prop at
mathlib-API granularity, not as an axiom.

## Note on `PF.LogWeightedIntegral`

The file `PF/LogWeightedIntegral.lean` (which would supply a concrete
CLM wrapping `transferOperator_clm`) contains legacy structural code
(pre-2026-05-08 refactor) that does not compile in isolation against
the current `LogWeightedL2 := Lp ℂ 2 μ` definition. It is therefore
not imported here. The structural Props below are CLM-shaped and
ready to consume any concrete CLM constructed once that file is
refactored.

Stage T3 — T3_sym CLM + spectral-witness conditional extraction.
-/

import PF.Analytic.RHSpectralWitness
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace PrincipiaTractalis

open scoped InnerProductSpace
open MeasureTheory

/-! ## 1. Symmetric CLM witness for T3_sym -/

/-- **`T3SymCLMSymmetricWitness`** — structured Prop asserting the
    existence of a `LogWeightedL2 →L[ℂ] LogWeightedL2` CLM whose
    underlying function agrees with `T3_sym.apply` and which is
    symmetric (a.k.a. self-adjoint at the linear-map level on a
    Hilbert space).

    NOT an axiom; this is a target Prop the consumer must supply.

    Provenance (when produced): take the project's existing
    `transferOperator_clm` (`PF/LogWeightedIntegral.lean:2190`, the
    CLM wrapping of the contracting T_3 via `LinearMap.mkContinuous`
    with operator norm ≤ 1), build a parallel `T3_adjoint_clm` via
    the mirror of the contracting-half chain on the expanding-branch
    if-cascade `T3_adjoint_action_func`, halve their sum to get
    `T3_sym_clm := (1/2) • (T3_clm + T3_adjoint_clm)`, then prove
    `T3_sym_clm.toFun = T3_sym.apply` via Lp-level extensionality and
    symmetry of T3_sym_clm from `T3_self_adjoint_conj_via_MemLp2`
    transferred to the CLM packaging. -/
def T3SymCLMSymmetricWitness : Prop :=
  ∃ (T : LogWeightedL2 →L[ℂ] LogWeightedL2),
    (∀ f, T f = T3_sym.apply f) ∧
    (T : LogWeightedL2 →ₗ[ℂ] LogWeightedL2).IsSymmetric

/-! ## 2. Finite-rank tower hypothesis

Analog of `H_P_finiteRankTower` from
`PF/Analytic/HPOperatorConstruction.lean:207`. A finite-rank tower
witness is a sequence of self-adjoint compact CLMs converging to the
target CLM in operator norm. By mathlib's `isCompactOperator_of_tendsto`,
the limit is then a compact operator.

This is the **load-bearing analytic content** for Blocker #2
(compactness of T3_sym). Per Mayer 1991 §3, T3 admits a holomorphic
extension whose nuclear-class membership gives compactness; the
finite-rank tower predicate packages exactly the kind of approximating
sequence that this analytic content would produce. -/

/-- **`T3SymFiniteRankTower`** — a finite-rank tower for a candidate
    `T3_sym` CLM. A sequence of self-adjoint compact CLMs converging
    to the candidate in operator norm.

    Analog of `H_P_finiteRankTower`
    (`PF/Analytic/HPOperatorConstruction.lean:207`). Existence of such
    a tower proves compactness of the target via
    `isCompactOperator_of_tendsto`. -/
def T3SymFiniteRankTower (T : LogWeightedL2 →L[ℂ] LogWeightedL2) : Prop :=
  ∃ (S : ℕ → (LogWeightedL2 →L[ℂ] LogWeightedL2)),
    (∀ N, IsSelfAdjoint (S N)) ∧
    (∀ N, IsCompactOperator (S N)) ∧
    Filter.Tendsto S Filter.atTop (nhds T)

/-- **Compactness from a finite-rank tower** for a `T3_sym` CLM
    candidate. Direct application of `isCompactOperator_of_tendsto`.

    Mirror of `H_P_construction_isCompactOperator_of_finiteRankTower`
    (`PF/Analytic/HPOperatorConstruction.lean:223`). -/
theorem T3_sym_clm_isCompactOperator_of_finiteRankTower
    (T : LogWeightedL2 →L[ℂ] LogWeightedL2)
    (hTower : T3SymFiniteRankTower T) :
    IsCompactOperator T := by
  obtain ⟨S, _, hS_K, hS_tendsto⟩ := hTower
  exact isCompactOperator_of_tendsto hS_tendsto
    (Filter.Eventually.of_forall hS_K)

/-! ## 3. Eigenvalue extraction Prop

The mathlib version pinned by this project provides
`Mathlib.Analysis.InnerProductSpace.Spectrum` with a finite-dim
spectral theorem (`LinearMap.IsSymmetric.eigenvalues` etc., for
`Module.finrank 𝕜 E = n`). The `ℕ`-indexed compact self-adjoint
spectral theorem (accumulating eigenvalues at 0 with `K/(n+1)` Weyl
decay) is not yet in mathlib at this commit. We surface that gap as
a named Prop. -/

/-- **`T3SymEigenvalueExtraction`** — the structured Prop encoding
    the output of applying the compact self-adjoint spectral theorem
    to a `T3_sym` CLM candidate that agrees with `T3_sym.apply`.

    Asserts the existence of an `ℕ`-indexed real eigenvalue sequence
    (with each entry a genuine eigenvalue of `T3_sym.apply`) plus a
    `K/(n+1)` decay bound.

    The `_h_agree` parameter is unused in the conclusion (the eigenvalue
    spec is stated in `T3_sym.apply`-form to match
    `T3SymSpectralWitness`) but binds the CLM to T3_sym semantically,
    documenting that the extraction *only makes sense* in the context
    of a CLM faithfully representing `T3_sym.apply`.

    Not an axiom; this is the structured target spec for the
    spectral-theorem extraction step. -/
def T3SymEigenvalueExtraction
    (_T : LogWeightedL2 →L[ℂ] LogWeightedL2)
    (_h_agree : ∀ f, _T f = T3_sym.apply f) : Prop :=
  ∃ (eigenvalues : ℕ → ℝ),
    (∀ n : ℕ, IsEigenvalue T3_sym.apply ((eigenvalues n : ℂ))) ∧
    ∃ (K : ℝ), K > 0 ∧
      (∀ n : ℕ, |eigenvalues n| ≤ K / ((n : ℝ) + 1))

/-! ## 4. Conditional extraction of `T3SymSpectralWitness` -/

/-- **`T3_sym_spectralWitness_from_witnesses`** — extracts a
    `T3SymSpectralWitness` from a CLM (with action-agreement
    certificate) and an eigenvalue-extraction witness.

    Mechanical: unpacks the existential and packages it into the
    `T3SymSpectralWitness` structure. -/
noncomputable def T3_sym_spectralWitness_from_witnesses
    (T : LogWeightedL2 →L[ℂ] LogWeightedL2)
    (h_agree : ∀ f, T f = T3_sym.apply f)
    (h_extract : T3SymEigenvalueExtraction T h_agree) :
    T3SymSpectralWitness :=
  -- Unpack the existential via Classical.choose (allowed since the
  -- output type is in `Type`, not `Prop`).
  let eigenvalues : ℕ → ℝ := Classical.choose h_extract
  let h_spec := Classical.choose_spec h_extract
  let h_eig := h_spec.1
  let h_K_existential := h_spec.2
  let K : ℝ := Classical.choose h_K_existential
  let h_K_spec := Classical.choose_spec h_K_existential
  { eigenvalues := eigenvalues
    h_eig_spec := h_eig
    K := K
    hK_pos := h_K_spec.1
    h_K_bound := h_K_spec.2 }

/-! ## 5. End-to-end discharge wrapper -/

/-- **★★★★ RH residual-only wrapper, with bundle (a) factored into
    three named witnesses ★★★★**

    Given:
      * a `T3SymCLMSymmetricWitness` (CLM existence with action
        agreement and symmetry),
      * a `T3SymFiniteRankTower` for that CLM (the compactness
        certificate, currently the load-bearing analytic gap on
        the operator side; not directly consumed by the spectral
        witness but exposed for the chain of obligations),
      * a `T3SymEigenvalueExtraction` (the output of the missing
        `ℕ`-indexed compact self-adjoint spectral theorem),
    plus bundles (b) (non-degeneracy, Mayer 1991 numerical) and
    (c) (surjectivity, LOAD-BEARING open conjecture),
    yields `RiemannHypothesis`.

    Build state: ZERO project axioms; ZERO `sorry`. -/
theorem riemann_hypothesis_residual_after_witness_discharge
    -- Bundle (a) factored: CLM + tower + spectral extraction
    (T : LogWeightedL2 →L[ℂ] LogWeightedL2)
    (h_agree : ∀ f, T f = T3_sym.apply f)
    (_h_sym : (T : LogWeightedL2 →ₗ[ℂ] LogWeightedL2).IsSymmetric)
    (_hTower : T3SymFiniteRankTower T)
    (h_extract : T3SymEigenvalueExtraction T h_agree)
    -- Bundle (b): non-degeneracy
    (α : ScalingParameter)
    (h_nonzero : ∀ n,
      (T3_sym_spectralWitness_from_witnesses T h_agree h_extract).eigenvalues n ≠ 0)
    (h_distinct : ∀ n m, n ≠ m →
      |(T3_sym_spectralWitness_from_witnesses T h_agree h_extract).eigenvalues n|
        ≠ |(T3_sym_spectralWitness_from_witnesses T h_agree h_extract).eigenvalues m|)
    -- Bundle (c): surjectivity (LOAD-BEARING open conjecture)
    (h_surjectivity : ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 →
        ∃ n : ℕ,
          eigenvalueToZero α
            ((T3_sym_spectralWitness_from_witnesses T h_agree h_extract).eigenvalues n)
              = s) :
    RiemannHypothesis :=
  riemann_hypothesis_residual_after_spectral_witness
    (T3_sym_spectralWitness_from_witnesses T h_agree h_extract)
    α h_nonzero h_distinct h_surjectivity

/-! ## 6. Concrete progress summary

After this file, the bundle (a) state is:

  * The remaining work to wrap `T3_sym` as a CLM is structured as
    `T3SymCLMSymmetricWitness` (constructive completion = take the
    project's existing `transferOperator_clm` for the contracting
    half, build `T3_adjoint_clm` via the mirror chain on the
    expanding-branch if-cascade `T3_adjoint_action_func`, halve,
    prove symmetry).
  * The compactness gap is structured as `T3SymFiniteRankTower`
    (analog of `H_P_finiteRankTower`), with the standard
    `isCompactOperator_of_tendsto` extraction proven in source
    (`T3_sym_clm_isCompactOperator_of_finiteRankTower`).
  * The mathlib gap for the `ℕ`-indexed spectral theorem is structured
    as `T3SymEigenvalueExtraction`.
  * `T3_sym_spectralWitness_from_witnesses` chains the CLM-agreement +
    extraction into a `T3SymSpectralWitness`.
  * `riemann_hypothesis_residual_after_witness_discharge` chains
    everything into `RiemannHypothesis`.

The three structured Props are at mathlib-API granularity. None is
an axiom; each is a concrete extraction target. -/

/-! ## 7. Axiom-freeness verification

`#print axioms` certifies that every export above depends on ZERO
project axioms — only mathlib's standard `propext`, `Classical.choice`,
`Quot.sound`. -/

#print axioms T3SymCLMSymmetricWitness
#print axioms T3SymFiniteRankTower
#print axioms T3_sym_clm_isCompactOperator_of_finiteRankTower
#print axioms T3SymEigenvalueExtraction
#print axioms T3_sym_spectralWitness_from_witnesses
#print axioms riemann_hypothesis_residual_after_witness_discharge

end PrincipiaTractalis
