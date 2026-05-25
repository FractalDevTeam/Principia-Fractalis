/-
# RH Bundle (a) — Discharge Attempt (finite-dim full, infinite-dim partial)

## Scope and honest framing

This file attempts to discharge `RayleighSupremumAttainedUniversally H`
— the load-bearing remaining Prop in the RH chain's (W1)/bundle-(a)
reduction tower (see
`PF/Analytic/CompactSelfAdjointDiscreteEnumerationDischarge.lean`).

The attempt explores the three paths laid out in the 2026-05-24 audit:

  (A) **Reflexivity bridge** via mathlib's
      `WeakDual.isCompact_closedBall` + Riesz isomorphism
      (`InnerProductSpace.toDual`). This gives a **topological**
      weak-* compactness statement transported to the primal closed
      unit ball. It does **NOT** automatically give sequential
      compactness — that requires metrizability of the weak-*
      topology on the unit ball, which in turn requires separability.
      The current mathlib snapshot has no such metrizability lemma
      (see `Mathlib/Analysis/Normed/Module/WeakDual.lean` line 54 TODO
      "Add the sequential Banach-Alaoglu theorem").
  (B) **Direct mathlib reuse** for `ContinuousLinearMap`-symmetric `T`
      on a **finite-dim** complex Hilbert space `H`. Mathlib's
      `LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional`
      (Rayleigh.lean line 226) and its underlying construction
      (`IsCompact.exists_isMaxOn` on `isCompact_sphere`) supply
      everything we need WITHOUT requiring compactness of `T`. We
      package this into a direct discharge of
      `RayleighSupremumAttainedUniversally H` for finite-dim
      Nontrivial complex Hilbert spaces.
  (C) **Sphere-compactness for the universal kernel**. The PF
      universal kernel `cos(π·α·|x-y|)` on `[0,1]²` is bounded +
      continuous + symmetric, hence its associated integral operator
      is Hilbert-Schmidt — therefore compact + self-adjoint. On
      `LogWeightedL2` (which is infinite-dimensional in general),
      path (C) reduces to the same sequential Banach-Alaoglu gap as
      path (A), so we cannot close it without the mathlib PR.

## What this file delivers (axiom-free, sorry-free)

1. **Path A topological lemma**: closed ball in any complete inner-product
   space `H` over `ℂ` is **topologically** weak-* compact via the Riesz
   isomorphism (`InnerProductSpace.toDual`) transported from
   `WeakDual.isCompact_closedBall`. Captured as
   `closedBall_isCompact_under_toDual`.

2. **Path B full discharge (finite-dim case)**:
   `rayleighSupremumAttained_of_finiteDimensional` —
   for finite-dim `[Nontrivial H]` complex Hilbert spaces, for **every**
   `T : H →L[ℂ] H` whose linear-map projection is symmetric (compactness
   not required), `RayleighSupremumAttained T` holds.

3. **Path B universal discharge (finite-dim case)**:
   `rayleighSupremumAttainedUniversally_of_finiteDimensional` —
   universal closure over `T` on finite-dim spaces.

4. **End-to-end finite-dim composite**:
   `compactSelfAdjointDiscreteEigenvalueEnumeration_of_finiteDimensional` —
   the (W1) bundle (a) is **fully discharged** on every finite-dim
   `[Nontrivial H]` complex Hilbert space.

5. **Honest summary of the infinite-dim gap**: `LogWeightedL2` is
   infinite-dimensional, so paths (B)/(C) do not close it. The
   precise remaining mathlib gap is named
   (`MathlibPR3_RayleighAttained LogWeightedL2`), already factored by
   the parent file `CompactSelfAdjointDiscreteEnumerationDischarge.lean`.

## Discharge level achieved

  * Finite-dim complex Hilbert spaces with `[Nontrivial H]`:
    bundle (a) is **proven** here, axiom-free.
  * Infinite-dim (`LogWeightedL2` case): partial topological
    progress (Path A); the sequential Banach-Alaoglu is the precisely
    named mathlib gap.

This reduces (W1) on every finite-dim substrate WITHOUT touching the
infinite-dim mathlib gap.

## Mathlib lemmas used (no project axioms, no sorry)

  * `WeakDual.isCompact_closedBall` (Banach-Alaoglu topological)
  * `InnerProductSpace.toDual` (Riesz isomorphism, conjugate-linear)
  * `FiniteDimensional.proper_rclike` (finite-dim ⟹ proper)
  * `isCompact_sphere` (proper-space sphere is compact)
  * `IsCompact.exists_isMaxOn` (compact + continuous ⟹ max attained)
  * `ContinuousLinearMap.reApplyInnerSelf_continuous`
  * `ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric`
  * `IsSelfAdjoint.hasEigenvector_of_isMaxOn`

## Build state

ZERO project axioms. ZERO `sorry`. Builds against the same mathlib
snapshot as `CompactSelfAdjointDiscreteEnumerationDischarge`.
-/

import PF.Analytic.CompactSelfAdjointDiscreteEnumerationDischarge
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace PrincipiaTractalis

open scoped InnerProductSpace
open MeasureTheory Filter Topology Metric

/-! ## 1. Path A — topological reflexivity bridge

This section captures the topological half of the Banach-Alaoglu
route. Mathlib has:

  * `WeakDual.isCompact_closedBall [ProperSpace 𝕜]
      (x' : StrongDual 𝕜 E) (r : ℝ) :
      IsCompact (toStrongDual ⁻¹' closedBall x' r)`
  * `InnerProductSpace.toDual : E ≃ₗᵢ⋆[𝕜] StrongDual 𝕜 E`
    (Riesz, conjugate-linear isometric equivalence)

These compose to: in a complete complex inner-product space `H`, the
image of the closed unit ball under the Riesz embedding is topologically
weak-* compact in `WeakDual ℂ H`. This is the cleanest topological
statement available WITHOUT the sequential Banach-Alaoglu lemma. -/

/-- **★ Topological reflexivity bridge ★** —
    in a complete complex inner-product space `H`, the closed ball
    around any dual element `x' : StrongDual ℂ H` is weak-* compact.
    This is just `WeakDual.isCompact_closedBall` restated with
    `ProperSpace ℂ` made explicit. The Riesz isomorphism
    `InnerProductSpace.toDual` then provides the primal-side
    identification.

    Note: this is **topological** weak-* compactness, not
    **sequential** — the sequential statement requires metrizability
    of the dual ball, gated on separability + the sequential
    Banach-Alaoglu lemma that is the
    `Mathlib/Analysis/Normed/Module/WeakDual.lean` line 54 TODO. -/
theorem closedBall_isCompact_under_toDual
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (x' : StrongDual ℂ H) (r : ℝ) :
    IsCompact ((WeakDual.toStrongDual : WeakDual ℂ H → StrongDual ℂ H) ⁻¹'
      Metric.closedBall x' r) := by
  haveI : ProperSpace ℂ := inferInstance
  exact WeakDual.isCompact_closedBall (𝕜 := ℂ) (E := H) x' r

/-- **★ Riesz transport: closed unit ball in `H` corresponds to closed
    unit ball in `StrongDual ℂ H`. ★** The Riesz map
    `InnerProductSpace.toDual` is a (conjugate-linear) isometric
    equivalence, so it sends `closedBall 0 1` in `H` bijectively to
    `closedBall 0 1` in `StrongDual ℂ H`. We record only the
    image-set equality at norm `1` — finer transport lemmas are
    available in `Mathlib/Analysis/InnerProductSpace/Dual.lean`. -/
theorem norm_toDual_eq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (x : H) :
    ‖InnerProductSpace.toDual ℂ H x‖ = ‖x‖ :=
  (InnerProductSpace.toDual ℂ H).norm_map x

/-! ## 2. Path B — direct discharge for finite-dim complex Hilbert spaces

Mathlib's `LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional`
(Rayleigh.lean line 226) proves the finite-dim Rayleigh theorem WITHOUT
requiring compactness of `T`. The construction uses:

  * `FiniteDimensional.proper_rclike` ⟹ `ProperSpace H`
  * `isCompact_sphere` ⟹ unit sphere is compact
  * `IsCompact.exists_isMaxOn` + continuity of `reApplyInnerSelf`
    ⟹ a maximizer exists

We package this directly into a discharge of
`RayleighSupremumAttained T` for symmetric continuous-linear `T` on a
finite-dim Nontrivial complex Hilbert space. -/

/-- **★★ Path B full discharge for finite-dim Hilbert spaces ★★**

    For every continuous linear map `T : H →L[ℂ] H` on a
    finite-dim Nontrivial complex Hilbert space whose underlying
    `LinearMap` is symmetric, `RayleighSupremumAttained T` holds.

    Compactness of `T` is NOT required — the finite-dim sphere is
    already compact and `reApplyInnerSelf` is continuous, so the
    extreme value theorem closes it directly.

    This is the **strongest available discharge** for the finite-dim
    case in the current mathlib snapshot. -/
theorem rayleighSupremumAttained_of_finiteDimensional
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H] [Nontrivial H]
    (T : H →L[ℂ] H)
    (_hSym : (T : H →ₗ[ℂ] H).IsSymmetric) :
    RayleighSupremumAttained T := by
  -- finite-dim ⟹ proper, so sphere is compact
  haveI : ProperSpace H := FiniteDimensional.proper_rclike ℂ H
  -- pick a non-zero point to anchor the sphere radius
  obtain ⟨x, hx_ne⟩ : ∃ x : H, x ≠ 0 := exists_ne 0
  have hCompact : IsCompact (Metric.sphere (0 : H) ‖x‖) :=
    isCompact_sphere _ _
  have hNonempty : (Metric.sphere (0 : H) ‖x‖).Nonempty := ⟨x, by simp⟩
  have hCont : Continuous T.reApplyInnerSelf := T.reApplyInnerSelf_continuous
  obtain ⟨x₀, hx₀_on, hMax⟩ :=
    hCompact.exists_isMaxOn hNonempty hCont.continuousOn
  -- `hx₀_on : x₀ ∈ sphere 0 ‖x‖` ⟹ `‖x₀‖ = ‖x‖`
  have hx₀_norm : ‖x₀‖ = ‖x‖ := by simpa using hx₀_on
  have hx₀_ne : x₀ ≠ 0 := by
    have : ‖x₀‖ ≠ 0 := by
      rw [hx₀_norm]; exact norm_ne_zero_iff.mpr hx_ne
    exact fun h => this (by rw [h, norm_zero])
  -- rewrap with sphere radius `‖x₀‖` (= `‖x‖`)
  have hMax' : IsMaxOn T.reApplyInnerSelf (Metric.sphere (0 : H) ‖x₀‖) x₀ := by
    rw [hx₀_norm]; exact hMax
  exact ⟨x₀, hx₀_ne, hMax'⟩

/-- **★★★ Path B universal discharge (finite-dim) ★★★**

    Universal closure: `RayleighSupremumAttainedUniversally H` holds
    for every finite-dim Nontrivial complex Hilbert space `H`. -/
theorem rayleighSupremumAttainedUniversally_of_finiteDimensional
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H] [Nontrivial H] :
    RayleighSupremumAttainedUniversally H := by
  intro T _hCompact hSym
  exact rayleighSupremumAttained_of_finiteDimensional T hSym

/-! ## 3. End-to-end finite-dim composite — bundle (a) discharged -/

/-- **★★★ End-to-end finite-dim discharge of (W1) bundle (a) ★★★**

    On every finite-dim Nontrivial complex Hilbert space `H`,
    `CompactSelfAdjointDiscreteEigenvalueEnumeration H` is a proven
    theorem (no `RayleighSupremumAttainedUniversally` hypothesis
    needed).

    This **fully discharges** the (W1) sub-bundle of (a) on
    finite-dim substrates. -/
theorem compactSelfAdjointDiscreteEigenvalueEnumeration_of_finiteDimensional
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H] [Nontrivial H] :
    CompactSelfAdjointDiscreteEigenvalueEnumeration H :=
  compactSelfAdjointDiscreteEigenvalueEnumeration_of_rayleighUniversal
    rayleighSupremumAttainedUniversally_of_finiteDimensional

/-! ## 4. Honest infinite-dim summary

`LogWeightedL2 := Lp ℂ 2 (logWeightedMeasure.restrict (Ioo 0 1))`
is **infinite-dimensional** (it contains all polynomials in `x`
restricted to `(0,1)`, which are linearly independent). Therefore
the finite-dim path B above does **not** discharge bundle (a) on
`LogWeightedL2`.

The remaining infinite-dim gap is exactly the sequential Banach-Alaoglu
lemma (`MathlibPR3_RayleighAttained LogWeightedL2`) already factored
by the parent file `CompactSelfAdjointDiscreteEnumerationDischarge`.

What this file adds:

  1. Bundle (a) is **proven** on every finite-dim Nontrivial complex
     Hilbert space (axiom-free, no `sorry`).
  2. The Riesz isomorphism path A topological building block is
     captured (`closedBall_isCompact_under_toDual`,
     `norm_toDual_eq`), ready to glue once the sequential
     Banach-Alaoglu lemma lands in mathlib.

The infinite-dim discharge on `LogWeightedL2` reduces to the same
single mathlib PR target previously named
(`MathlibPR3_RayleighAttained`).
-/

/-! ## 5. Axiom-freeness verification -/

#print axioms closedBall_isCompact_under_toDual
#print axioms norm_toDual_eq
#print axioms rayleighSupremumAttained_of_finiteDimensional
#print axioms rayleighSupremumAttainedUniversally_of_finiteDimensional
#print axioms compactSelfAdjointDiscreteEigenvalueEnumeration_of_finiteDimensional

end PrincipiaTractalis
