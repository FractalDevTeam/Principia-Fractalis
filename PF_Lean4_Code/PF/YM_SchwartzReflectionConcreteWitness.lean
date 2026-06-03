/-
# Schwartz Reflection — Concrete Time-Reflection Witness (Wave 58 STRENGTHENING)

★ 2026-06-02 — STRENGTHENING of `SchwartzReflectionTypedStatement` (G2)
from `PF/YM_WightmanContinuumGapsTypedUpgrade.lean` (Wave 57-YM-W-UPGRADE),
mirroring the Bochner-Minlos concrete-witness pattern landed today at
`PF/YM_BochnerMinlosConcreteWitness.lean`.

The Wave 57 typed form

  `∃ θ : 𝓢(ℝ⁴, ℝ) →L[ℝ] 𝓢(ℝ⁴, ℝ), ∀ f x, θ (θ f) x = f x`

is satisfied by `schwartzReflectionCLM` (pull-back along the FULL-SPACE
negation `(neg ℝ) : x ↦ -x`). That witness inverts all four coordinates
of `EuclideanSpace ℝ (Fin 4)` — it is NOT the genuine OS-axiom 4 time
reflection, which inverts only the time coordinate `i = 0` and leaves
the spatial coordinates fixed.

This file provides:

  (1) A STRENGTHENED typed Prop
      `SchwartzReflectionConcreteTypedStatement` requiring the reflection
      to be the literal TIME-AXIS NEGATION
      `τ(t, x⃗) := (-t, x⃗)` on `EuclideanSpace ℝ (Fin 4) = ℝ × ℝ³`
      (encoded coordinate-wise as `τ x i := if i = 0 then -x 0 else x i`).

  (2) A CONCRETE WITNESS — the time-reflection
      `EuclideanSpace ℝ (Fin 4) ≃L[ℝ] EuclideanSpace ℝ (Fin 4)`
      built from a `LinearEquiv` (the self-inverse time-axis negation)
      via `LinearEquiv.toContinuousLinearEquiv` (finite-dim), then fed
      into `SchwartzMap.compCLMOfContinuousLinearEquiv`.

  (3) The cascade: strengthened concrete ⇒ Wave 57 typed
      `SchwartzReflectionTypedStatement` ⇒ Wave 56
      `SchwartzReflectionStructure`.

## Honest scope

  1. This file PROVES the existence of a continuous linear involution
     on `𝓢(ℝ⁴, ℝ)` whose underlying point map is the genuine OS
     time-reflection `(t, x⃗) ↦ (-t, x⃗)` — the literal Osterwalder-
     Schrader axiom 4 spatial structure (NOT the full-space negation
     that the Wave 57 typed form admits as a degenerate witness).

  2. Ruled out: the full-space `-id` reflection of the Wave 57 typed
     witness `schwartzReflectionCLM`. That map inverts all four
     coordinates; this map inverts ONLY the time coordinate.

  3. NOT a Clay discharge. The OS reflection-positivity content of
     axiom 4 (positivity of `⟨f, θ f⟩` under the time-reflection
     pairing against the Schwinger measure) is NOT addressed here.

## Build

ZERO project axioms. ZERO sorries.

Author: Wave 58 STRENGTHENING (Schwartz time-reflection concrete),
2026-06-02.
-/

import PF.YM_WightmanContinuumGapsTypedUpgrade
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

set_option autoImplicit false

namespace PrincipiaTractalis
namespace YM_SchwartzReflectionConcreteWitness

open PrincipiaTractalis
open PrincipiaTractalis.YM_Wave56ContinuumLiftAttempt
open PrincipiaTractalis.YM_WightmanReconstructionScaffold
open PrincipiaTractalis.YM_WightmanContinuumGapsTypedUpgrade
open SchwartzMap

/-! ## §1 — Time-reflection on `EuclideanSpace ℝ (Fin 4)`

We model `ℝ⁴ = ℝ × ℝ³` with the time coordinate at index `0 : Fin 4`
and the three spatial coordinates at indices `1, 2, 3 : Fin 4`. The
OS-axiom 4 time reflection is

  `τ : (t, x¹, x², x³) ↦ (-t, x¹, x², x³)`,

equivalently in `Fin 4`-index form,

  `τ x i := if i = 0 then -(x 0) else x i`.

Below we build this map first as a `LinearMap`, then as a
self-inverse `LinearEquiv`, then promote to a `ContinuousLinearEquiv`
via the finite-dimensional automatic-continuity instance. -/

/-- **Time-reflection point map** on `EuclideanSpace ℝ (Fin 4)`. -/
def timeReflectFun (x : EuclideanSpace ℝ (Fin 4)) :
    EuclideanSpace ℝ (Fin 4) :=
  fun i => if i = 0 then -(x 0) else x i

@[simp] lemma timeReflectFun_apply (x : EuclideanSpace ℝ (Fin 4))
    (i : Fin 4) :
    timeReflectFun x i = (if i = 0 then -(x 0) else x i) := rfl

/-- **Time-reflection is an involution at the point-map level**. -/
lemma timeReflectFun_involution (x : EuclideanSpace ℝ (Fin 4)) :
    timeReflectFun (timeReflectFun x) = x := by
  funext i
  by_cases hi : i = 0
  · subst hi
    simp [timeReflectFun]
  · simp [timeReflectFun, hi]

/-- **Time-reflection preserves addition**. -/
lemma timeReflectFun_add (x y : EuclideanSpace ℝ (Fin 4)) :
    timeReflectFun (x + y) = timeReflectFun x + timeReflectFun y := by
  funext i
  by_cases hi : i = 0
  · subst hi
    simp [timeReflectFun, PiLp.add_apply]
    ring
  · simp [timeReflectFun, hi, PiLp.add_apply]

/-- **Time-reflection commutes with scalar multiplication**. -/
lemma timeReflectFun_smul (c : ℝ) (x : EuclideanSpace ℝ (Fin 4)) :
    timeReflectFun (c • x) = c • timeReflectFun x := by
  funext i
  by_cases hi : i = 0
  · subst hi
    simp [timeReflectFun, PiLp.smul_apply, mul_neg]
  · simp [timeReflectFun, hi, PiLp.smul_apply]

/-- **Time-reflection as a `LinearMap`** on `EuclideanSpace ℝ (Fin 4)`. -/
def timeReflectLinearMap :
    EuclideanSpace ℝ (Fin 4) →ₗ[ℝ] EuclideanSpace ℝ (Fin 4) where
  toFun := timeReflectFun
  map_add' := timeReflectFun_add
  map_smul' := timeReflectFun_smul

@[simp] lemma timeReflectLinearMap_apply (x : EuclideanSpace ℝ (Fin 4)) :
    timeReflectLinearMap x = timeReflectFun x := rfl

/-- **Time-reflection as a self-inverse `LinearEquiv`**. -/
def timeReflectLinearEquiv :
    EuclideanSpace ℝ (Fin 4) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 4) where
  toFun := timeReflectFun
  invFun := timeReflectFun
  left_inv := timeReflectFun_involution
  right_inv := timeReflectFun_involution
  map_add' := timeReflectFun_add
  map_smul' := timeReflectFun_smul

@[simp] lemma timeReflectLinearEquiv_apply (x : EuclideanSpace ℝ (Fin 4)) :
    timeReflectLinearEquiv x = timeReflectFun x := rfl

@[simp] lemma timeReflectLinearEquiv_symm_apply
    (x : EuclideanSpace ℝ (Fin 4)) :
    timeReflectLinearEquiv.symm x = timeReflectFun x := rfl

/-- **Time-reflection as a `ContinuousLinearEquiv`** on
    `EuclideanSpace ℝ (Fin 4)` — finite-dimensionality of the carrier
    makes the underlying `LinearEquiv` automatically continuous. -/
noncomputable def schwartzTimeReflectionEquiv :
    EuclideanSpace ℝ (Fin 4) ≃L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  timeReflectLinearEquiv.toContinuousLinearEquiv

@[simp] lemma schwartzTimeReflectionEquiv_apply
    (x : EuclideanSpace ℝ (Fin 4)) :
    schwartzTimeReflectionEquiv x = timeReflectFun x := rfl

/-! ## §2 — The Schwartz time-reflection CLM

We pull back along `schwartzTimeReflectionEquiv` via
`SchwartzMap.compCLMOfContinuousLinearEquiv`, obtaining
`τ̂ : 𝓢(ℝ⁴, ℝ) →L[ℝ] 𝓢(ℝ⁴, ℝ)` with
`(τ̂ f) x = f (timeReflectFun x)`. -/

/-- **The Schwartz time-reflection CLM** — pull-back of Schwartz
    functions along the time-axis negation
    `τ : (t, x⃗) ↦ (-t, x⃗)`. -/
noncomputable def schwartzTimeReflectionCLM :
    SchwartzSpaceR4 →L[ℝ] SchwartzSpaceR4 :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ schwartzTimeReflectionEquiv

/-- **The Schwartz time-reflection acts pointwise by
    `f ↦ f ∘ timeReflectFun`**. -/
lemma schwartzTimeReflectionCLM_apply_eq
    (f : SchwartzSpaceR4) (x : EuclideanSpace ℝ (Fin 4)) :
    schwartzTimeReflectionCLM f x = f (timeReflectFun x) := by
  simp [schwartzTimeReflectionCLM,
        SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
        schwartzTimeReflectionEquiv_apply]

/-- **The Schwartz time-reflection is an involution at the underlying-
    function level** — `(τ̂ ∘ τ̂) f x = f x` for every `f` and `x`. -/
theorem schwartzTimeReflectionCLM_involution_apply
    (f : SchwartzSpaceR4) (x : EuclideanSpace ℝ (Fin 4)) :
    (schwartzTimeReflectionCLM (schwartzTimeReflectionCLM f)) x = f x := by
  rw [schwartzTimeReflectionCLM_apply_eq,
      schwartzTimeReflectionCLM_apply_eq,
      timeReflectFun_involution]

/-! ## §3 — Strengthened typed predicate

The strengthened predicate adds two structural constraints beyond the
Wave 57 typed form:

  (a) The pull-back map's underlying action coincides with the time-
      axis negation `timeReflectFun` (NOT the full-space negation).
  (b) The reflection FIXES every spatial index `i ≠ 0`. -/

/-- **Strengthened (G2) typed predicate** — existence of a continuous
    linear involution on `𝓢(ℝ⁴, ℝ)` whose underlying point map is the
    time-axis negation `τ : (t, x⃗) ↦ (-t, x⃗)`. -/
def SchwartzReflectionConcreteTypedStatement : Prop :=
  ∃ (θ : SchwartzSpaceR4 →L[ℝ] SchwartzSpaceR4),
    (∀ (f : SchwartzSpaceR4) (x : EuclideanSpace ℝ (Fin 4)),
        θ f x = f (timeReflectFun x)) ∧
    (∀ (f : SchwartzSpaceR4) (x : EuclideanSpace ℝ (Fin 4)),
        (θ (θ f)) x = f x)

/-- **The Schwartz time-reflection CLM inhabits the strengthened
    predicate** — concrete witness with time-axis negation point map
    and involution. The full-space `-id` witness `schwartzReflectionCLM`
    of Wave 57 CANNOT inhabit this strengthened form (its underlying
    point map negates spatial coordinates as well). -/
theorem schwartzReflection_concrete_timeReflection_witness :
    SchwartzReflectionConcreteTypedStatement :=
  ⟨schwartzTimeReflectionCLM,
   schwartzTimeReflectionCLM_apply_eq,
   schwartzTimeReflectionCLM_involution_apply⟩

/-! ## §4 — Cascade to the Wave 57 typed form -/

/-- **Strengthened concrete ⇒ Wave 57 typed
    `SchwartzReflectionTypedStatement`**. The strengthened form
    contains an involution witness as its second conjunct. -/
theorem schwartzReflection_concrete_implies_wave57_typed
    (h : SchwartzReflectionConcreteTypedStatement) :
    SchwartzReflectionTypedStatement := by
  obtain ⟨θ, _hθ_apply, hθ_inv⟩ := h
  exact ⟨θ, hθ_inv⟩

/-- **Strengthened concrete ⇒ Wave 56 `True`-shaped original** Prop. -/
theorem schwartzReflection_concrete_implies_original
    (h : SchwartzReflectionConcreteTypedStatement) :
    SchwartzReflectionStructure :=
  schwartzReflection_typed_implies_original
    (schwartzReflection_concrete_implies_wave57_typed h)

/-! ## §5 — Spatial-fixing structural lemma

Refinement clarifying that the time-reflection FIXES every spatial
index `i ≠ 0` — a property the Wave 57 full-space witness lacks. -/

/-- **The time-reflection FIXES every spatial coordinate.** -/
theorem schwartzTimeReflectionCLM_fixes_spatial
    (x : EuclideanSpace ℝ (Fin 4))
    (i : Fin 4) (hi : i ≠ 0) :
    timeReflectFun x i = x i := by
  simp [timeReflectFun, hi]

/-- **The time-reflection NEGATES the time coordinate.** -/
theorem schwartzTimeReflectionCLM_negates_time
    (x : EuclideanSpace ℝ (Fin 4)) :
    timeReflectFun x 0 = -(x 0) := by
  simp [timeReflectFun]

/-! ## §6 — Honest-scope marker -/

/-- **Honest-scope marker** — the concrete witness strengthens the
    Wave 57 typed (G2) Prop in two ways:

    (a) The reflection's point map is the literal OS-axiom 4 time-axis
        negation `(t, x⃗) ↦ (-t, x⃗)`, NOT the full-space negation
        `x ↦ -x` of the Wave 57 witness.

    (b) The reflection FIXES every spatial coordinate `i ∈ {1, 2, 3}`
        while NEGATING only the time coordinate `i = 0`.

    HOWEVER: the OS reflection-positivity content — positivity of
    `⟨f, θ f⟩` under the time-reflection pairing against the
    Schwinger measure — is NOT proved here. -/
def SchwartzReflectionConcreteWitnessHonestScope : Prop :=
  -- (1) Strengthened typed predicate is inhabited by the time reflection.
  SchwartzReflectionConcreteTypedStatement ∧
  -- (2) Strengthened concrete ⇒ Wave 57 typed.
  (SchwartzReflectionConcreteTypedStatement →
      SchwartzReflectionTypedStatement) ∧
  -- (3) Strengthened concrete ⇒ Wave 56 `True`-shaped original.
  (SchwartzReflectionConcreteTypedStatement →
      SchwartzReflectionStructure) ∧
  -- (4) Spatial coordinates are fixed.
  (∀ (x : EuclideanSpace ℝ (Fin 4)) (i : Fin 4),
      i ≠ 0 → timeReflectFun x i = x i) ∧
  -- (5) Time coordinate is negated.
  (∀ (x : EuclideanSpace ℝ (Fin 4)), timeReflectFun x 0 = -(x 0))

/-- The honest-scope marker holds unconditionally. -/
theorem schwartzReflection_concrete_witness_honestScope_holds :
    SchwartzReflectionConcreteWitnessHonestScope :=
  ⟨schwartzReflection_concrete_timeReflection_witness,
   schwartzReflection_concrete_implies_wave57_typed,
   schwartzReflection_concrete_implies_original,
   schwartzTimeReflectionCLM_fixes_spatial,
   schwartzTimeReflectionCLM_negates_time⟩

/-! ## §7 — Capstone -/

/-- ★★★ **CAPSTONE — Schwartz Time-Reflection Concrete Witness** ★★★
    (Wave 58 STRENGTHENING, 2026-06-02)

    STRENGTHENING of the (G2) Schwartz-reflection typed Prop from
    `YM_WightmanContinuumGapsTypedUpgrade` via a concrete time-
    reflection witness `τ : (t, x⃗) ↦ (-t, x⃗)` on
    `EuclideanSpace ℝ (Fin 4)`.

    **Seven structural clauses**:

    (1) Strengthened typed predicate
        `SchwartzReflectionConcreteTypedStatement` — continuous linear
        involution on `𝓢(ℝ⁴, ℝ)` whose underlying point map is the
        time-axis negation (rules out the Wave 57 full-space witness).
    (2) Concrete witness via `SchwartzMap.compCLMOfContinuousLinearEquiv`
        applied to the time-reflection `ContinuousLinearEquiv`.
    (3) Underlying-function action `(τ̂ f) x = f (timeReflectFun x)`.
    (4) Involution at the underlying-function level.
    (5) Spatial coordinates fixed, time coordinate negated.
    (6) Cascade strengthened ⇒ Wave 57 typed ⇒ Wave 56 original.
    (7) Honest-scope marker.

    **Honest scope**: NOT a Clay discharge. The OS reflection-
    positivity content of axiom 4 is NOT addressed; only the
    structural point-map content of the reflection involution is
    formalised.

    Axiom-free; `#print axioms` returns only
    `[propext, Classical.choice, Quot.sound]`. -/
theorem schwartzReflection_concrete_witness_capstone :
    SchwartzReflectionConcreteTypedStatement ∧
    (∀ (f : SchwartzSpaceR4) (x : EuclideanSpace ℝ (Fin 4)),
        schwartzTimeReflectionCLM f x = f (timeReflectFun x)) ∧
    (∀ (f : SchwartzSpaceR4) (x : EuclideanSpace ℝ (Fin 4)),
        (schwartzTimeReflectionCLM (schwartzTimeReflectionCLM f)) x
          = f x) ∧
    (∀ (x : EuclideanSpace ℝ (Fin 4)) (i : Fin 4),
        i ≠ 0 → timeReflectFun x i = x i) ∧
    (∀ (x : EuclideanSpace ℝ (Fin 4)),
        timeReflectFun x 0 = -(x 0)) ∧
    (SchwartzReflectionConcreteTypedStatement →
        SchwartzReflectionTypedStatement) ∧
    (SchwartzReflectionConcreteTypedStatement →
        SchwartzReflectionStructure) ∧
    SchwartzReflectionConcreteWitnessHonestScope :=
  ⟨schwartzReflection_concrete_timeReflection_witness,
   schwartzTimeReflectionCLM_apply_eq,
   schwartzTimeReflectionCLM_involution_apply,
   schwartzTimeReflectionCLM_fixes_spatial,
   schwartzTimeReflectionCLM_negates_time,
   schwartzReflection_concrete_implies_wave57_typed,
   schwartzReflection_concrete_implies_original,
   schwartzReflection_concrete_witness_honestScope_holds⟩

/-! ## §8 — Axiom-freeness verification -/

#print axioms timeReflectFun_involution
#print axioms timeReflectLinearMap
#print axioms timeReflectLinearEquiv
#print axioms schwartzTimeReflectionEquiv
#print axioms schwartzTimeReflectionCLM
#print axioms schwartzTimeReflectionCLM_apply_eq
#print axioms schwartzTimeReflectionCLM_involution_apply
#print axioms schwartzReflection_concrete_timeReflection_witness
#print axioms schwartzReflection_concrete_implies_wave57_typed
#print axioms schwartzReflection_concrete_implies_original
#print axioms schwartzTimeReflectionCLM_fixes_spatial
#print axioms schwartzTimeReflectionCLM_negates_time
#print axioms schwartzReflection_concrete_witness_honestScope_holds
#print axioms schwartzReflection_concrete_witness_capstone

end YM_SchwartzReflectionConcreteWitness
end PrincipiaTractalis
