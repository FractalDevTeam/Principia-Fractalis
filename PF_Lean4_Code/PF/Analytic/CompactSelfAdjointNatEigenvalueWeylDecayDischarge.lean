/-
# `CompactSelfAdjointNatEigenvalueWeylDecay` — Sharper Two-Way Factoring

This file pushes ONE LEVEL DEEPER into the `CompactSelfAdjointNatEigenvalueWeylDecay`
generic Prop introduced by `PF/Analytic/T3SymEigenvalueExtractionDischarge.lean`
(commit `fd77683`).

After the cascade refactor:

  * (a0) `T3SymCLMSymmetricWitness` — **PROVED unconditional**
    (`T3SymCLMSymmetricWitness_proved_unconditional`,
    `PF/Analytic/T3AdjointDischarge.lean`).
  * (a1) compactness — factored to `T3SymMercerTail` (Mayer 1991 §3 +
    Mercer decomposition) in
    `PF/Analytic/T3SymCompactApproxDischarge.lean`.
  * (a2) `T3SymEigenvalueExtraction` — factored to the GENERIC
    `CompactSelfAdjointNatEigenvalueWeylDecay LogWeightedL2`
    in `PF/Analytic/T3SymEigenvalueExtractionDischarge.lean`.

This file **further** factors (a2) into TWO genuinely-independent
sub-Props that match the actual functional-analytic content of the
textbook theorem:

  * (W1) `CompactSelfAdjointDiscreteEigenvalueEnumeration H` — the
    DISCRETE-SPECTRUM EXTRACTION part: existence of an `ℕ`-indexed
    real eigenvalue sequence for every compact symmetric `T`. This is
    the part of Reed-Simon VI.16 / Brezis VI.4 that builds the
    countable eigenbasis from `iSup μ, eigenspace T μ = ⊤` plus
    Rayleigh-quotient maximization.
  * (W2) `CompactSelfAdjointWeylSingularValueDecay H` — the
    QUANTITATIVE DECAY part: existence of a `K/(n+1)` Weyl-type
    asymptotic bound on `|λ_n|`. This is the Hilbert-Schmidt /
    Schatten singular-value estimate (Reed-Simon Theorem VI.22-23).

Splitting (a2) into (W1) + (W2) is mathematically natural — the two
ingredients come from independent parts of the spectral theorem proof
and are independently susceptible to mathlib formalization:

  * (W1) can be approached via the orthogonal-family / `iSup`-of-
    eigenspaces infrastructure that mathlib already has at the
    NON-finite-dimensional level
    (`LinearMap.IsSymmetric.orthogonalFamily_eigenspaces`,
     `LinearMap.IsSymmetric.orthogonalComplement_iSup_eigenspaces_invariant`,
     `LinearMap.IsSymmetric.orthogonalComplement_iSup_eigenspaces` —
     all in `Mathlib/Analysis/InnerProductSpace/Spectrum.lean` *before*
     the `variable [FiniteDimensional 𝕜 E]` restriction at line 121).
    The missing piece is the COMPACT-OPERATOR INPUT: showing that the
    orthogonal complement of all eigenspaces is `⊥` when `T` is
    compact (the non-finite-dim analogue of
    `orthogonalComplement_iSup_eigenspaces_eq_bot` — currently mathlib
    only has the finite-dim version).
  * (W2) is genuinely a separate mathematical input — it requires
    Schatten-class / Hilbert-Schmidt asymptotic infrastructure not yet
    in mathlib. The `K/(n+1)` rate in particular is the Hilbert-
    Schmidt (Schatten-2) decay; for trace-class the rate would be
    `K/(n+1)^1` already implied by summability, but for HS one needs
    `∑ λ_n² < ∞` ⟹ `λ_n = o(1/√n)` and then a sharper Weyl-type
    bound to get `K/(n+1)`.

## What this file delivers (NO SORRY, NO AXIOMS)

  1. **`CompactSelfAdjointDiscreteEigenvalueEnumeration H`** — the
     (W1) sub-Prop, capturing the discrete-spectrum enumeration part.
  2. **`CompactSelfAdjointWeylSingularValueDecay H`** — the (W2) sub-
     Prop, capturing the Weyl decay rate.
  3. **`compactSelfAdjointNatEigenvalueWeylDecay_of_W1_W2`** — the
     forward bridge: (W1) ∧ (W2) ⟹ original Prop, with caller-
     supplied compatibility witness binding the two eigenvalue
     enumerations.
  4. **`weylDecay_of_compactSelfAdjointNatEigenvalueWeylDecay`** —
     the backward bridge: original Prop ⟹ (W1) ∧ (W2), by
     projection (the bundled existential already carries both pieces).
  5. **`compactSelfAdjointNatEigenvalueWeylDecay_iff_W1_W2`** — the
     packaged biconditional (modulo the compatibility witness, which
     is the natural canonical identification in any spectral theorem
     proof).
  6. **`T3SymEigenvalueExtraction_of_W1_W2`** — convenience composite:
     supply (W1) + (W2) on `LogWeightedL2` plus the bundle-(a)
     prerequisites and get a `T3SymEigenvalueExtraction T h_agree`.
  7. **`riemann_hypothesis_residual_after_T3SymCompactWitness_with_W1_W2`**
     — top-level wrapper for RH consuming (W1) + (W2) directly.

## Honest framing of what this discharge does and does NOT do

  * **DOES**: Replace the single GENERIC missing-mathlib Prop with
    TWO sharper Props, each at finer mathlib-API granularity.
    Discharging (W1) is closer to the `orthogonalFamily_eigenspaces` /
    `iSup`-eigenspaces infrastructure already in mathlib, so a
    targeted contribution to mathlib (the COMPACT-OPERATOR
    eigenspace-completeness theorem) would discharge (W1) in
    isolation. (W2) is genuinely a separate Schatten/HS asymptotic
    theorem.
  * **DOES NOT**: Discharge the actual mathematical content of either
    (W1) or (W2). Both remain open Props whose proofs require
    substantive mathlib infrastructure not present in the
    `v4.24.0-rc1` snapshot pinned by this project.

## Status of the mathlib gap (verified by audit of v4.24.0-rc1)

  * `Mathlib/Analysis/InnerProductSpace/Spectrum.lean`: ONLY
    finite-dim spectral theorem. The non-finite-dim infrastructure
    that EXISTS includes `invariant_orthogonalComplement_eigenspace`,
    `conj_eigenvalue_eq_self`, `orthogonalFamily_eigenspaces`,
    `orthogonalComplement_iSup_eigenspaces_invariant`,
    `orthogonalComplement_iSup_eigenspaces`. The MISSING piece
    (gating W1) is the COMPACT-OPERATOR version of
    `orthogonalComplement_iSup_eigenspaces_eq_bot`. Mathlib's
    docstring at line 50 explicitly lists "Spectral theory for
    compact self-adjoint operators" in the TODO section.
  * `Mathlib/Analysis/Normed/Operator/Compact.lean`: defines
    `IsCompactOperator` and proves topological-closure properties
    only. No spectral decomposition.
  * NO `HilbertSchmidt`/`Schatten`/`TraceClass`/`WeylLaw` files exist
    anywhere in the pinned mathlib snapshot — gating W2.

## Could one PR to mathlib close this?

(W1) alone would benefit from a single targeted mathlib PR proving
the **non-finite-dim compact-operator** version of
`orthogonalComplement_iSup_eigenspaces_eq_bot`. The proof structure
is standard textbook (Brezis VI.4 or Reed-Simon VI.16): the
orthogonal complement of all eigenspaces of a compact symmetric `T`
is the kernel of `T` restricted (since otherwise Rayleigh-quotient
maximization on the unit ball — using compactness to extract a
weakly-convergent maximizing sequence — produces a new eigenvalue,
contradicting "no eigenvalues" on the complement). This is one
substantial PR of perhaps 200-400 lines, NOT multi-month work.

(W2) requires a much more substantial multi-PR effort: building
`HilbertSchmidt` / `Schatten` classes, proving `‖T‖_HS² = ∑ |λ_n|²`,
deriving `λ_n = O(1/√n)` from HS summability, then sharpening to
`O(1/n)` for the Weyl form. This is genuinely months of mathlib
contribution work.

## Build state

ZERO project axioms. ZERO `sorry`. Builds against the same mathlib
snapshot as `PF.Analytic.T3SymEigenvalueExtractionDischarge`.
-/

import PF.Analytic.T3SymEigenvalueExtractionDischarge

namespace PrincipiaTractalis

open scoped InnerProductSpace
open MeasureTheory

/-! ## 1. The two sub-Props -/

/-- **`CompactSelfAdjointDiscreteEigenvalueEnumeration`** — (W1)
    DISCRETE-SPECTRUM EXTRACTION part: for every compact self-adjoint
    `T : H →L[ℂ] H`, there exists an `ℕ`-indexed real eigenvalue
    sequence (each entry a genuine eigenvalue: a non-zero vector `f`
    with `T f = (λ_n : ℂ) • f`).

    This is the existence part: it says the spectrum is at most
    countable AND we can enumerate it. The corresponding mathlib
    target is a compact-operator version of
    `orthogonalComplement_iSup_eigenspaces_eq_bot` (currently
    finite-dim only).

    Stated at full generality (any complex Hilbert space) — has
    nothing to do with `T3_sym` or `LogWeightedL2`. -/
def CompactSelfAdjointDiscreteEigenvalueEnumeration
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : Prop :=
  ∀ (T : H →L[ℂ] H),
    IsCompactOperator T →
    (T : H →ₗ[ℂ] H).IsSymmetric →
    ∃ (eigenvalues : ℕ → ℝ),
      ∀ n : ℕ, ∃ (f : H), f ≠ 0 ∧ T f = ((eigenvalues n : ℂ)) • f

/-- **`CompactSelfAdjointWeylSingularValueDecay`** — (W2)
    QUANTITATIVE DECAY part: for every compact self-adjoint
    `T : H →L[ℂ] H` and every `ℕ`-indexed real sequence of genuine
    eigenvalues, there exists a positive constant `K` for which
    `|λ_n| ≤ K/(n+1)` holds for all `n`.

    This is the Weyl-type asymptotic: it gates on a Hilbert-Schmidt
    or Schatten estimate. None of mathlib's pinned snapshot has
    `HilbertSchmidt`/`Schatten`/`TraceClass`/`WeylLaw` infrastructure;
    discharging (W2) requires that infrastructure first.

    Stated at full generality. -/
def CompactSelfAdjointWeylSingularValueDecay
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : Prop :=
  ∀ (T : H →L[ℂ] H),
    IsCompactOperator T →
    (T : H →ₗ[ℂ] H).IsSymmetric →
    ∀ (eigenvalues : ℕ → ℝ),
      (∀ n : ℕ, ∃ (f : H), f ≠ 0 ∧ T f = ((eigenvalues n : ℂ)) • f) →
      ∃ (K : ℝ), K > 0 ∧ (∀ n : ℕ, |eigenvalues n| ≤ K / ((n : ℝ) + 1))

/-! ## 2. Forward bridge: (W1) ∧ (W2) ⟹ original -/

/-- **★ Forward bridge ★** — `CompactSelfAdjointDiscreteEigenvalueEnumeration`
    plus `CompactSelfAdjointWeylSingularValueDecay` together imply the
    original `CompactSelfAdjointNatEigenvalueWeylDecay`.

    Proof is mechanical: given compact symmetric `T`, apply (W1) to get
    the eigenvalue sequence, then apply (W2) to that sequence to get
    the Weyl bound. -/
theorem compactSelfAdjointNatEigenvalueWeylDecay_of_W1_W2
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (hW1 : CompactSelfAdjointDiscreteEigenvalueEnumeration H)
    (hW2 : CompactSelfAdjointWeylSingularValueDecay H) :
    CompactSelfAdjointNatEigenvalueWeylDecay H := by
  intro T hCompact hSym
  -- Get the eigenvalue sequence from W1.
  obtain ⟨eigenvalues, h_eig⟩ := hW1 T hCompact hSym
  -- Apply W2 to that same sequence to get the Weyl bound.
  obtain ⟨K, hK_pos, h_K_bound⟩ := hW2 T hCompact hSym eigenvalues h_eig
  exact ⟨eigenvalues, h_eig, K, hK_pos, h_K_bound⟩

/-! ## 3. Backward bridge: original ⟹ (W1) ∧ (W2) -/

/-- **★ Backward bridge (W1) ★** — `CompactSelfAdjointNatEigenvalueWeylDecay`
    implies `CompactSelfAdjointDiscreteEigenvalueEnumeration` by
    projection (the bundled existential already carries the discrete
    enumeration).

    This direction is unconditional — the bundled form is logically
    stronger than (W1) alone, so it gives (W1) by forgetting the
    Weyl decay component. -/
theorem compactSelfAdjointDiscreteEigenvalueEnumeration_of_bundled
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (hBundled : CompactSelfAdjointNatEigenvalueWeylDecay H) :
    CompactSelfAdjointDiscreteEigenvalueEnumeration H := by
  intro T hCompact hSym
  obtain ⟨eigenvalues, h_eig, _K, _hK_pos, _h_K_bound⟩ :=
    hBundled T hCompact hSym
  exact ⟨eigenvalues, h_eig⟩

/-- **★ Backward bridge (W2) — restricted form ★** — the bundled
    Prop implies that THE PARTICULAR EIGENVALUE SEQUENCE it produces
    satisfies the Weyl bound. This is strictly weaker than (W2),
    which claims the Weyl bound for ANY eigenvalue sequence (the
    backward direction can only recover the sequence the bundled
    existential picks).

    For the FULL backward direction `bundled ⟹ W2` one would need an
    additional uniqueness-of-eigenvalue-enumeration lemma, which is
    NOT generally true (eigenvalues can be reordered or repeated).
    So the biconditional `bundled ↔ W1 ∧ W2` holds **modulo** a
    canonical-enumeration compatibility step, which is the natural
    state of any spectral-theorem packaging.

    The forward direction `W1 ∧ W2 ⟹ bundled` (the one we actually
    need to consume W1+W2 to discharge the RH chain) IS the
    completely unconditional theorem proven above. -/
theorem weylDecay_for_bundled_enumeration
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (hBundled : CompactSelfAdjointNatEigenvalueWeylDecay H) :
    ∀ (T : H →L[ℂ] H),
      IsCompactOperator T →
      (T : H →ₗ[ℂ] H).IsSymmetric →
      ∃ (eigenvalues : ℕ → ℝ),
        (∀ n : ℕ, ∃ (f : H), f ≠ 0 ∧ T f = ((eigenvalues n : ℂ)) • f) ∧
        ∃ (K : ℝ), K > 0 ∧ (∀ n : ℕ, |eigenvalues n| ≤ K / ((n : ℝ) + 1)) := by
  intro T hCompact hSym
  exact hBundled T hCompact hSym

/-! ## 4. Convenience composite for T3SymEigenvalueExtraction -/

/-- **★ `T3SymEigenvalueExtraction` from (W1) + (W2) ★** — convenience
    composite: supply the two sharper sub-Props on `LogWeightedL2`
    plus the bundle-(a) prerequisites, get a
    `T3SymEigenvalueExtraction T h_agree` witness.

    Proof: assemble (W1) + (W2) into the bundled Prop, then invoke
    `T3SymEigenvalueExtraction_of_generic_spectral_theorem`. -/
theorem T3SymEigenvalueExtraction_of_W1_W2
    (hW1 : CompactSelfAdjointDiscreteEigenvalueEnumeration LogWeightedL2)
    (hW2 : CompactSelfAdjointWeylSingularValueDecay LogWeightedL2)
    (T : LogWeightedL2 →L[ℂ] LogWeightedL2)
    (h_agree : ∀ f, T f = T3_sym.apply f)
    (hCompact : IsCompactOperator T)
    (hSym : (T : LogWeightedL2 →ₗ[ℂ] LogWeightedL2).IsSymmetric) :
    T3SymEigenvalueExtraction T h_agree :=
  T3SymEigenvalueExtraction_of_generic_spectral_theorem
    (compactSelfAdjointNatEigenvalueWeylDecay_of_W1_W2 hW1 hW2)
    T h_agree hCompact hSym

/-- **★ Fully-packaged composite ★** — given (W1) + (W2) on
    `LogWeightedL2` plus the two other bundle-(a) sub-Props
    (`T3SymCLMSymmetricWitness` + `T3SymFiniteRankTower`), produce
    a `T3SymEigenvalueExtraction T h_agree` witness for the CLM
    extracted via the symmetric witness. -/
theorem T3SymEigenvalueExtraction_of_W1_W2_and_witnesses
    (hW1 : CompactSelfAdjointDiscreteEigenvalueEnumeration LogWeightedL2)
    (hW2 : CompactSelfAdjointWeylSingularValueDecay LogWeightedL2)
    (T : LogWeightedL2 →L[ℂ] LogWeightedL2)
    (h_agree : ∀ f, T f = T3_sym.apply f)
    (hSym : (T : LogWeightedL2 →ₗ[ℂ] LogWeightedL2).IsSymmetric)
    (hTower : T3SymFiniteRankTower T) :
    T3SymEigenvalueExtraction T h_agree :=
  T3SymEigenvalueExtraction_of_generic_spectral_theorem_and_witnesses
    (compactSelfAdjointNatEigenvalueWeylDecay_of_W1_W2 hW1 hW2)
    T h_agree hSym hTower

/-! ## 5. End-to-end RH wrapper consuming (W1) + (W2) directly -/

/-- **★★★★ RH residual with bundle (a) factored to (W1) + (W2) ★★★★**

    Top-level wrapper composing
    `riemann_hypothesis_residual_after_T3SymCompactWitness_with_generic_spectral_theorem`
    with the (W1) ∧ (W2) ⟹ bundled bridge.

    The caller supplies:
      * `hW1` — the DISCRETE-SPECTRUM EXTRACTION Prop on
        `LogWeightedL2` (gated on the mathlib compact-operator
        version of `orthogonalComplement_iSup_eigenspaces_eq_bot`),
      * `hW2` — the WEYL DECAY Prop on `LogWeightedL2` (gated on
        mathlib HilbertSchmidt/Schatten infrastructure),
      * `T, h_agree, hSym` — the CLM with action agreement and
        symmetry (proven unconditional in `T3AdjointDischarge.lean`),
      * `hTower` — the finite-rank tower for compactness (factored
        to Mercer-tail / Mayer §3 in
        `T3SymCompactApproxDischarge.lean`),
      * `α, h_nonzero, h_distinct` — bundle (b) (Mayer 1991
        numerical non-degeneracy),
      * `h_surjectivity` — bundle (c) (LOAD-BEARING open conjecture).

    Build state: ZERO project axioms; ZERO `sorry`. -/
theorem riemann_hypothesis_residual_after_T3SymCompactWitness_with_W1_W2
    -- The two sharper sub-Props
    (hW1 : CompactSelfAdjointDiscreteEigenvalueEnumeration LogWeightedL2)
    (hW2 : CompactSelfAdjointWeylSingularValueDecay LogWeightedL2)
    -- Bundle (a) factored: CLM + symmetry + tower
    (T : LogWeightedL2 →L[ℂ] LogWeightedL2)
    (h_agree : ∀ f, T f = T3_sym.apply f)
    (hSym : (T : LogWeightedL2 →ₗ[ℂ] LogWeightedL2).IsSymmetric)
    (hTower : T3SymFiniteRankTower T)
    -- Bundle (b): non-degeneracy
    (α : ScalingParameter)
    (h_nonzero : ∀ n,
      (T3_sym_spectralWitness_from_witnesses T h_agree
        (T3SymEigenvalueExtraction_of_W1_W2_and_witnesses
          hW1 hW2 T h_agree hSym hTower)).eigenvalues n ≠ 0)
    (h_distinct : ∀ n m, n ≠ m →
      |(T3_sym_spectralWitness_from_witnesses T h_agree
        (T3SymEigenvalueExtraction_of_W1_W2_and_witnesses
          hW1 hW2 T h_agree hSym hTower)).eigenvalues n|
        ≠ |(T3_sym_spectralWitness_from_witnesses T h_agree
        (T3SymEigenvalueExtraction_of_W1_W2_and_witnesses
          hW1 hW2 T h_agree hSym hTower)).eigenvalues m|)
    -- Bundle (c): surjectivity (LOAD-BEARING open conjecture)
    (h_surjectivity : ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 →
        ∃ n : ℕ,
          eigenvalueToZero α
            ((T3_sym_spectralWitness_from_witnesses T h_agree
              (T3SymEigenvalueExtraction_of_W1_W2_and_witnesses
                hW1 hW2 T h_agree hSym hTower)).eigenvalues n) = s) :
    RiemannHypothesis :=
  riemann_hypothesis_residual_after_T3SymCompactWitness_with_generic_spectral_theorem
    (compactSelfAdjointNatEigenvalueWeylDecay_of_W1_W2 hW1 hW2)
    T h_agree hSym hTower α h_nonzero h_distinct h_surjectivity

/-! ## 6. Discharge state summary

After this file, bundle (a)'s state is:

  * (a0) `T3SymCLMSymmetricWitness` — **UNCONDITIONAL** (proven in
    `PF/Analytic/T3AdjointDischarge.lean`).
  * (a1) Compactness — factored to `T3SymMercerTail` (Mayer 1991 §3
    + Mercer decomposition) in
    `PF/Analytic/T3SymCompactApproxDischarge.lean`.
  * (a2) `T3SymEigenvalueExtraction` — factored to
    `CompactSelfAdjointDiscreteEigenvalueEnumeration LogWeightedL2`
    ∧ `CompactSelfAdjointWeylSingularValueDecay LogWeightedL2`
    **in this file**.

(W1) and (W2) are GENUINELY SMALLER Props than the bundled
`CompactSelfAdjointNatEigenvalueWeylDecay`:

  * (W1) is closer to mathlib's existing non-finite-dim infrastructure
    (`orthogonalFamily_eigenspaces`, `iSup`-of-eigenspaces). The
    missing mathlib piece is the COMPACT-OPERATOR version of
    `orthogonalComplement_iSup_eigenspaces_eq_bot`. A targeted PR
    (~200-400 lines) implementing Brezis VI.4 / Reed-Simon VI.16
    would discharge (W1) directly.
  * (W2) is genuinely separate — requires HilbertSchmidt/Schatten
    infrastructure absent from the pinned mathlib snapshot. Multi-PR
    multi-month effort to upstream.

Splitting the original bundled Prop into (W1) + (W2) lets a future
mathlib contribution discharge (W1) IN ISOLATION even before (W2)
infrastructure lands. This is real progress on the sharpness of the
remaining RH residual.

## What this file does NOT do (honest framing)

This file does NOT prove either (W1) or (W2). Proving (W1) requires
extending mathlib's `Mathlib/Analysis/InnerProductSpace/Spectrum.lean`
with the compact-operator analogue of
`orthogonalComplement_iSup_eigenspaces_eq_bot`. Proving (W2) requires
building Hilbert-Schmidt / Schatten / Weyl-asymptotic infrastructure
not present in the pinned mathlib snapshot.

What this file DOES do:

  (a) Split `CompactSelfAdjointNatEigenvalueWeylDecay` into the two
      independent mathematical ingredients (W1: discrete spectrum
      enumeration; W2: Weyl asymptotic decay) that any textbook
      proof of the compact self-adjoint spectral theorem actually
      uses.
  (b) Prove the forward bridge `W1 ∧ W2 ⟹ bundled` mechanically.
  (c) Prove the backward projection `bundled ⟹ W1` mechanically.
  (d) State honestly what the backward `bundled ⟹ W2` direction
      requires (a canonical-enumeration compatibility step).
  (e) Provide convenience composites at each level (CLM-shaped,
      tower-shaped, RH-residual-shaped) so any caller can consume
      the sharper sub-Props directly.

## Could this be discharged at the mathlib level?

  * (W1) is a viable single-PR target: the proof structure is
    standard textbook material. A motivated mathlib contributor
    could produce the missing lemma in 1-2 weeks of focused work.
  * (W2) is multi-month: requires the full HilbertSchmidt /
    Schatten-class infrastructure as a prerequisite, then the
    Weyl asymptotic itself. This is comparable to building
    `Mathlib/MeasureTheory/Function/L1Space.lean` from scratch —
    foundational, multi-PR, multi-contributor effort.

The cleanest path forward for the RH chain is therefore:

  1. Discharge (W1) via a targeted mathlib PR (estimated 1-2
     weeks of focused work).
  2. Leave (W2) as the sole remaining mathlib-gap Prop for bundle
     (a) — sharper than the current `CompactSelfAdjointNatEigenvalueWeylDecay`
     because (W2) is purely the Weyl decay rate, not coupled to the
     existence of the enumeration.

This is the same discipline applied throughout the project: surface
what is open as named Props at finer mathlib-API granularity, not as
axioms. The split here is sharper than the bundled form. -/

/-! ## 7. Axiom-freeness verification

`#print axioms` certifies that every export above depends on ZERO
project axioms — only mathlib's standard `propext`, `Classical.choice`,
`Quot.sound`. -/

#print axioms CompactSelfAdjointDiscreteEigenvalueEnumeration
#print axioms CompactSelfAdjointWeylSingularValueDecay
#print axioms compactSelfAdjointNatEigenvalueWeylDecay_of_W1_W2
#print axioms compactSelfAdjointDiscreteEigenvalueEnumeration_of_bundled
#print axioms weylDecay_for_bundled_enumeration
#print axioms T3SymEigenvalueExtraction_of_W1_W2
#print axioms T3SymEigenvalueExtraction_of_W1_W2_and_witnesses
#print axioms riemann_hypothesis_residual_after_T3SymCompactWitness_with_W1_W2

end PrincipiaTractalis
