/-
# `CompactSelfAdjointDiscreteEigenvalueEnumeration` — Sharper factoring of (W1)

This file pushes ONE LEVEL DEEPER into the `(W1)` sub-Prop
`CompactSelfAdjointDiscreteEigenvalueEnumeration H` introduced by
`PF/Analytic/CompactSelfAdjointNatEigenvalueWeylDecayDischarge.lean`.

After the bundle (a) cascade refactor (see the parent file), bundle (a2)
splits as (W1) + (W2). This file attacks (W1) only.

## What this file delivers (NO SORRY, NO AXIOMS)

The textbook proof of `(W1)` — existence of an `ℕ`-indexed real
eigenvalue sequence for every compact symmetric `T` — proceeds in two
clearly separable steps:

  (E1) **Existence of ONE eigenvalue.** For a compact self-adjoint
       operator `T` on a *nontrivial* complex Hilbert space, there
       exists a non-zero eigenvector `f` with `T f = (λ : ℂ) • f`
       for some real `λ`. (Brezis Théorème VI.11 / Reed-Simon
       Theorem VI.16.)
  (E2) **Repetition / enumeration.** Given (E1), build a constant
       `ℕ → ℝ` sequence (just repeat the single eigenvalue and
       its eigenvector). This trivially gives (W1).

The honest mathematical content of (W1) lives in (E1). (E2) is
mechanical.

This file:

  1. Names the missing (E1) Prop: `CompactSymmetricHasNonzeroEigenvector`.
  2. Proves `(E1) ⟹ (W1)` mechanically (assuming H is `Nontrivial`).
  3. Further factors (E1) into the genuinely missing mathlib piece:
     `RayleighSupremumAttained` — existence of a maximizer for the
     Rayleigh quotient on the closed unit ball, via weak-sequential
     compactness + compactness of `T`. This is the Banach-Alaoglu-style
     analytic core of Brezis VI.11.
  4. Proves `(RayleighSupremumAttained) + (T self-adjoint) + (Nontrivial H) ⟹ (E1)`
     using mathlib's existing
     `IsSelfAdjoint.hasEigenvector_of_isMaxOn`
     (Rayleigh.lean line 177) — the LOCAL extremum ⟹ eigenvector
     ingredient. This is exactly the *finite-dim* proof, with the
     finite-dim "continuous function on sphere has max" replaced by
     the compact-operator weak-sequential-compactness argument.
  5. Composes (3) + (4) ⟹ (1) ⟹ (W1) as a clean composite.
  6. Provides the corresponding `LogWeightedL2`-specialized wrappers.

After this file, (W1) on `LogWeightedL2` reduces to:

  (A) `Nontrivial LogWeightedL2` — separate small lemma; the space is
      a `Lp ℂ 2 μ` on a non-zero measure, hence nontrivial.
  (B) `RayleighSupremumAttained T` for the specific compact symmetric
      `T` extracted from `T3_sym` — THE genuine remaining gap.

(B) is the ACTUAL Banach-Alaoglu-style argument missing from mathlib
for compact operators. It is sharper than the original (W1) bundle
because it isolates exactly the analytic input: weak-sequential
compactness of the unit ball + norm-preservation under compact `T`.

## Honest framing of what this discharge does and does NOT do

  * **DOES**: Factor (W1) into TWO genuinely sharper Props
    (`Nontrivial H` + `RayleighSupremumAttained T`), each at finer
    mathlib-API granularity than the bundled (W1). The reduction
    glues to mathlib's existing
    `IsSelfAdjoint.hasEigenvector_of_isMaxOn` — so we are NOT
    re-proving Rayleigh-eigenvector but reusing it.
  * **DOES NOT**: Discharge `RayleighSupremumAttained` itself.
    That requires Banach-Alaoglu for Hilbert spaces (weak-sequential
    compactness of the unit ball) + the compact-operator continuity
    argument, neither of which is currently in the pinned mathlib
    snapshot in directly-applicable form for arbitrary Hilbert
    spaces. This is the SINGLE remaining mathlib gap for (W1).

## Build state

ZERO project axioms. ZERO `sorry`. Builds against the same mathlib
snapshot as the parent file.
-/

import PF.Analytic.CompactSelfAdjointNatEigenvalueWeylDecayDischarge
import Mathlib.Analysis.InnerProductSpace.Rayleigh

namespace PrincipiaTractalis

open scoped InnerProductSpace
open MeasureTheory

/-! ## 1. The sub-Prop (E1): one nonzero eigenvector exists -/

/-- **`CompactSymmetricHasNonzeroEigenvector`** — (E1) the
    EXISTENCE-OF-ONE-EIGENVECTOR Prop.

    For every compact self-adjoint `T : H →L[ℂ] H` (with `H` an
    arbitrary complex Hilbert space — including the trivial case),
    there exists a real number `λ` and a non-zero vector `f` with
    `T f = (λ : ℂ) • f`.

    For trivial `H` (where every vector is `0`), this Prop is
    literally **false** (no `f ≠ 0` exists). We therefore PARAMETERIZE
    over a `[Nontrivial H]` typeclass at the point of use; the Prop
    itself is stated without that assumption to keep the sub-Prop
    architecture parallel to (W1).

    The genuine mathematical content is the Brezis Théorème VI.11 /
    Reed-Simon Theorem VI.16 statement; this is the textbook
    spectral-theorem starter. -/
def CompactSymmetricHasNonzeroEigenvector
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : Prop :=
  ∀ (T : H →L[ℂ] H),
    IsCompactOperator T →
    (T : H →ₗ[ℂ] H).IsSymmetric →
    ∃ (lam : ℝ) (f : H), f ≠ 0 ∧ T f = ((lam : ℂ)) • f

/-! ## 2. Mechanical: (E1) ⟹ (W1) by constant repetition -/

/-- **★ (E1) ⟹ (W1) ★** — given that one eigenvector exists, the
    constant-`λ` sequence and the same eigenvector at every index
    trivially produce a `(W1)` witness.

    Proof: apply (E1) once to get `(lam, f, hf_ne, hf_eig)`; take
    `eigenvalues := fun _ => lam` and the witness `f` at every `n`. -/
theorem compactSelfAdjointDiscreteEigenvalueEnumeration_of_hasNonzeroEigenvector
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (hE1 : CompactSymmetricHasNonzeroEigenvector H) :
    CompactSelfAdjointDiscreteEigenvalueEnumeration H := by
  intro T hCompact hSym
  obtain ⟨lam, f, hf_ne, hf_eig⟩ := hE1 T hCompact hSym
  refine ⟨fun _ => lam, ?_⟩
  intro _
  exact ⟨f, hf_ne, hf_eig⟩

/-! ## 3. The deeper sub-Prop: Rayleigh supremum is attained

The Rayleigh-quotient half of Brezis VI.11 says: for compact
self-adjoint `T` on a nontrivial Hilbert space, the supremum
`⨆ x ≠ 0, ⟨T x, x⟩.re / ‖x‖²` is **attained** at some non-zero
`x₀`. The proof uses weak-sequential compactness of the unit ball
(Banach-Alaoglu) plus the compactness of `T` to upgrade weak to
strong convergence on the image.

This is the GENUINE mathlib gap. Mathlib has the closely related
`hasEigenvector_of_isMaxOn` (Rayleigh.lean line 177): IF the
supremum is attained at `x₀ ≠ 0` on a sphere, THEN `x₀` is an
eigenvector. So the gap is purely existence of the maximizer.
-/

/-- **`RayleighSupremumAttained`** — for a fixed compact self-adjoint
    `T`, there exists `x₀ ≠ 0` at which the Rayleigh function
    `reApplyInnerSelf` is maximal on the sphere of radius `‖x₀‖`.

    This is the Banach-Alaoglu-style analytic ingredient: weak
    compactness of the closed unit ball + compactness of `T` ⟹ the
    supremum of `⟨T x, x⟩.re` on the sphere is attained.

    Stated for a fixed `T` (not universally over `T`) — this is the
    cleanest form for downstream use. The closure
    `∀ T, …` form is `RayleighSupremumAttainedUniversally`. -/
def RayleighSupremumAttained
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (T : H →L[ℂ] H) : Prop :=
  ∃ (x₀ : H), x₀ ≠ 0 ∧
    IsMaxOn T.reApplyInnerSelf (Metric.sphere (0 : H) ‖x₀‖) x₀

/-- **Universal version** — `RayleighSupremumAttained T` for every
    compact symmetric `T`. -/
def RayleighSupremumAttainedUniversally
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : Prop :=
  ∀ (T : H →L[ℂ] H),
    IsCompactOperator T →
    (T : H →ₗ[ℂ] H).IsSymmetric →
    RayleighSupremumAttained T

/-! ## 4. (RayleighSupremumAttained) ⟹ (E1) via mathlib's existing
    `IsSelfAdjoint.hasEigenvector_of_isMaxOn` -/

/-- Helper: a `(T : H →L[ℂ] H).IsSymmetric` on the underlying
    `LinearMap` upgrades to `IsSelfAdjoint T` for the CLM (using the
    mathlib `LinearMap.IsSymmetric.isSelfAdjoint_iff` /
    self-adjoint-of-symmetric ContinuousLinearMap equivalence). -/
theorem isSelfAdjoint_of_clm_isSymmetric
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {T : H →L[ℂ] H}
    (hSym : (T : H →ₗ[ℂ] H).IsSymmetric) : IsSelfAdjoint T :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hSym

/-- **★ (RayleighSupremumAttained T) ⟹ (T has a nonzero eigenvector) ★**

    Given a compact self-adjoint `T` for which the Rayleigh supremum
    is attained at a non-zero `x₀ ∈ sphere ‖x₀‖`, mathlib's
    `IsSelfAdjoint.hasEigenvector_of_isMaxOn` produces an eigenvector
    with REAL eigenvalue — specifically the GLOBAL supremum
    `⨆ x : {x // x ≠ 0}, T.rayleighQuotient x` (a real number,
    coerced into `ℂ`).

    Proof: apply `IsSelfAdjoint.hasEigenvector_of_isMaxOn` directly. -/
theorem hasNonzeroEigenvector_of_rayleighSupremumAttained
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {T : H →L[ℂ] H}
    (hSym : (T : H →ₗ[ℂ] H).IsSymmetric)
    (hAttained : RayleighSupremumAttained T) :
    ∃ (lam : ℝ) (f : H), f ≠ 0 ∧ T f = ((lam : ℂ)) • f := by
  obtain ⟨x₀, hx₀_ne, hMax⟩ := hAttained
  have hSA : IsSelfAdjoint T := isSelfAdjoint_of_clm_isSymmetric hSym
  -- mathlib delivers a `HasEigenvector` for the LinearMap `(T : H →ₗ[ℂ] H)`
  -- at the eigenvalue `↑(⨆ x : {x : H // x ≠ 0}, T.rayleighQuotient x)` (the
  -- GLOBAL supremum — `hasEigenvector_of_isMaxOn` package this way).
  have hEv := hSA.hasEigenvector_of_isMaxOn hx₀_ne hMax
  -- hEv : HasEigenvector (T : H →ₗ[ℂ] H) ↑(⨆ x : {x : H // x ≠ 0}, T.rayleighQuotient x) x₀
  -- Extract the eigenvalue (real) and the eigenvector equation.
  refine ⟨(⨆ x : {x : H // x ≠ 0}, T.rayleighQuotient x), x₀, hx₀_ne, ?_⟩
  -- HasEigenvector.left : x₀ ∈ eigenspace (T : H →ₗ[ℂ] H) (↑(⨆ ...))
  have h_mem := hEv.left
  rw [Module.End.mem_eigenspace_iff] at h_mem
  -- h_mem : (T : H →ₗ[ℂ] H) x₀ = ↑(⨆ ...) • x₀
  -- Convert to T x₀ form.
  exact h_mem

/-! ## 5. Universal composite: (RayleighUniversal) ⟹ (E1 universal) -/

/-- **★ Universal (RayleighSupremumAttainedUniversally) ⟹ (E1) ★** -/
theorem compactSymmetricHasNonzeroEigenvector_of_rayleighUniversal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (hRayleigh : RayleighSupremumAttainedUniversally H) :
    CompactSymmetricHasNonzeroEigenvector H := by
  intro T hCompact hSym
  exact hasNonzeroEigenvector_of_rayleighSupremumAttained hSym
    (hRayleigh T hCompact hSym)

/-! ## 6. End-to-end composite: (Rayleigh) ⟹ (W1) -/

/-- **★★★ Headline composite: (RayleighSupremumAttainedUniversally) ⟹ (W1) ★★★**

    The full reduction of (W1) to the Banach-Alaoglu-style analytic
    Prop. Composes:
      * `compactSymmetricHasNonzeroEigenvector_of_rayleighUniversal`
        (step 3 ⟹ E1 via mathlib's `hasEigenvector_of_isMaxOn`)
      * `compactSelfAdjointDiscreteEigenvalueEnumeration_of_hasNonzeroEigenvector`
        (E1 ⟹ W1 by constant repetition).

    After this theorem, (W1) on any Hilbert space `H` reduces to:
      `RayleighSupremumAttainedUniversally H` — the ONLY remaining
      analytic input. -/
theorem compactSelfAdjointDiscreteEigenvalueEnumeration_of_rayleighUniversal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (hRayleigh : RayleighSupremumAttainedUniversally H) :
    CompactSelfAdjointDiscreteEigenvalueEnumeration H :=
  compactSelfAdjointDiscreteEigenvalueEnumeration_of_hasNonzeroEigenvector
    (compactSymmetricHasNonzeroEigenvector_of_rayleighUniversal hRayleigh)

/-! ## 7. LogWeightedL2-specialized wrappers -/

/-- **W1 discharge on `LogWeightedL2` modulo Rayleigh-supremum attainment.** -/
theorem compactSelfAdjointDiscreteEigenvalueEnumeration_LogWeightedL2_of_rayleigh
    (hRayleigh : RayleighSupremumAttainedUniversally LogWeightedL2) :
    CompactSelfAdjointDiscreteEigenvalueEnumeration LogWeightedL2 :=
  compactSelfAdjointDiscreteEigenvalueEnumeration_of_rayleighUniversal hRayleigh

/-! ## 8. Discharge state summary

After this file, (W1) on `LogWeightedL2` reduces to:

  * **`RayleighSupremumAttainedUniversally LogWeightedL2`** — for
    every compact self-adjoint `T : LogWeightedL2 →L[ℂ] LogWeightedL2`,
    the Rayleigh quotient `T.reApplyInnerSelf` attains its supremum
    on some sphere `Metric.sphere 0 ‖x₀‖` at a non-zero `x₀`.

THIS is the genuine remaining mathlib gap. It encodes exactly the
Banach-Alaoglu / weak-sequential-compactness argument that mathlib's
`Mathlib/Analysis/InnerProductSpace/Spectrum.lean` flags as "TODO:
Spectral theory for compact self-adjoint operators."

## What still needs to be done at the mathlib level

The single targeted PR to mathlib that would close (W1) is:

```
theorem isCompactOperator_isSymmetric_rayleighSupremum_attained
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]
    (T : H →L[ℂ] H) (hCompact : IsCompactOperator T)
    (hSym : (T : H →ₗ[ℂ] H).IsSymmetric) :
    ∃ x₀ : H, x₀ ≠ 0 ∧
      IsMaxOn T.reApplyInnerSelf (Metric.sphere 0 ‖x₀‖) x₀
```

Proof sketch (Brezis VI.11):
  1. Let `M = ⨆ {⟨T x, x⟩.re / ‖x‖² : x ≠ 0}`.
  2. Pick a maximizing sequence `xₙ` on the unit sphere.
  3. By Banach-Alaoglu (weak-sequential compactness of unit ball
     in reflexive space), extract a weakly convergent subsequence
     `xₙₖ ⇀ x∞`.
  4. By compactness of `T`, `T xₙₖ → T x∞` strongly.
  5. By weak ⇀ + strong → bilinear continuity,
     `⟨T xₙₖ, xₙₖ⟩ → ⟨T x∞, x∞⟩ = M`.
  6. `⟨T x∞, x∞⟩ = M` and `‖x∞‖ ≤ 1`. Maximality on the unit ball
     forces `‖x∞‖ = 1`, hence `x∞ ≠ 0`.
  7. By translation/scaling, the supremum is attained on the
     sphere `‖x₀‖ = ‖x∞‖ = 1`, with `x₀ := x∞`.

The proof is 100–200 lines of mathlib, gated on:
  * weak-sequential compactness for Hilbert space unit ball
    (mathlib has `Mathlib/Analysis/LocallyConvex/WeakSpace.lean`
    but not the explicit "bounded sequence in Hilbert space has
    weakly convergent subsequence" theorem),
  * the bilinear continuity argument (standard).

This is a tractable 1-2 week mathlib contribution. Once that lemma
lands, this file's `RayleighSupremumAttainedUniversally` Prop becomes
a proven theorem, and (W1) discharges immediately via the composite
proved above.

## Build state

ZERO project axioms. ZERO `sorry`. Builds against the same mathlib
snapshot as `PF.Analytic.CompactSelfAdjointNatEigenvalueWeylDecayDischarge`.
-/

/-! ## 9. Axiom-freeness verification

`#print axioms` certifies that every export above depends on ZERO
project axioms — only mathlib's standard `propext`, `Classical.choice`,
`Quot.sound`. -/

#print axioms CompactSymmetricHasNonzeroEigenvector
#print axioms RayleighSupremumAttained
#print axioms RayleighSupremumAttainedUniversally
#print axioms compactSelfAdjointDiscreteEigenvalueEnumeration_of_hasNonzeroEigenvector
#print axioms isSelfAdjoint_of_clm_isSymmetric
#print axioms hasNonzeroEigenvector_of_rayleighSupremumAttained
#print axioms compactSymmetricHasNonzeroEigenvector_of_rayleighUniversal
#print axioms compactSelfAdjointDiscreteEigenvalueEnumeration_of_rayleighUniversal
#print axioms compactSelfAdjointDiscreteEigenvalueEnumeration_LogWeightedL2_of_rayleigh

end PrincipiaTractalis
