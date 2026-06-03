/-
# Bochner-Minlos — Multi-Dimensional Gaussian Witness on ℝ⁴ (Wave 58 STRENGTHENING²)

★ 2026-06-02 — STRENGTHENING² of `BochnerMinlosConcreteTypedStatement`
from `PF/YM_BochnerMinlosConcreteWitness.lean` (Wave 58 STRENGTHENING).

The Wave 58 1-dim form
  `∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ NoAtoms μ`
is satisfied by `gaussianReal 0 1`, but is still 1-dim. The literal
Bochner-Minlos target lives on the topological dual of a nuclear space
`𝓢'(ℝ⁴, ℝ)`. The next concrete strengthening past 1-dim is the
*standard Gaussian on ℝ⁴*, i.e. the product measure of four independent
standard Gaussians, sitting on the four-dimensional real inner-product
space `EuclideanSpace ℝ (Fin 4) = PiLp 2 (fun _ : Fin 4 => ℝ)`
(the underlying measurable structure agrees with `Fin 4 → ℝ` carrying
the product measure `MeasureTheory.Measure.pi (fun _ => gaussianReal 0 1)`).

This file provides:

  (1) A STRENGTHENED² typed Prop `BochnerMinlosR4TypedStatement`
      requiring an atomless probability measure on `Fin 4 → ℝ` (the
      underlying measurable carrier of `EuclideanSpace ℝ (Fin 4)`).

  (2) A CONCRETE WITNESS on `Fin 4 → ℝ` via
      `MeasureTheory.Measure.pi (fun _ : Fin 4 => gaussianReal 0 1)`:
      a standard 4-dim Gaussian product measure, both a probability
      measure and atomless.

  (3) The cascade
        4-dim Gaussian
          ⇒ Wave 58 1-dim concrete `BochnerMinlosConcreteTypedStatement`
          ⇒ Wave 57 typed `BochnerMinlosTypedStatement`
          ⇒ Wave 56 `True`-shaped `BochnerMinlosOnNuclearSpaces`.

## Honest scope

  1. The carrier `Fin 4 → ℝ` (≃ `EuclideanSpace ℝ (Fin 4)`) is FOUR-dim
     and *finite* dimensional. The literal Bochner-Minlos statement
     requires the topological dual of a *nuclear* space
     `𝓢'(ℝ⁴, ℝ)`, which is infinite-dimensional.

  2. Ruled out by this strengthening²: BOTH the Dirac-on-`Unit`
     witness of Wave 57 AND the 1-dim `gaussianReal` witness of
     Wave 58. The dimension-of-spacetime "4" appears literally.

  3. NOT a Clay discharge.

## Build

ZERO project axioms. ZERO sorries.

Author: Wave 58 STRENGTHENING² (Bochner-Minlos R^4 concrete), 2026-06-02.
-/

import PF.YM_BochnerMinlosConcreteWitness
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

set_option autoImplicit false

namespace PrincipiaTractalis
namespace YM_BochnerMinlosR4Witness

open MeasureTheory ProbabilityTheory Complex
open PrincipiaTractalis
open PrincipiaTractalis.YM_Wave56ContinuumLiftAttempt
open PrincipiaTractalis.YM_WightmanContinuumGapsTypedUpgrade
open PrincipiaTractalis.YM_BochnerMinlosConcreteWitness

/-! ## §1 — Strengthened² typed predicate on `Fin 4 → ℝ`

The strengthened² predicate names the genuine product structure on
`Fin 4 → ℝ`, which carries the natural measurable space of
`EuclideanSpace ℝ (Fin 4) = PiLp 2 (fun _ : Fin 4 => ℝ)`. The PiLp
type is a `MeasurableSpace`-equivalent reinforcement carrying the
`ℓ²` inner-product structure on top of the same underlying type.
-/

/-- **Strengthened² (G1) typed predicate on ℝ⁴** — existence of an
    atomless probability measure on `Fin 4 → ℝ`.

    The Dirac-on-`Unit` witness of Wave 57 and the 1-dim `gaussianReal`
    witness of Wave 58 CANNOT inhabit this strengthened² form: the
    carrier is forced to be `Fin 4 → ℝ`. -/
def BochnerMinlosR4TypedStatement : Prop :=
  ∃ μ : Measure (Fin 4 → ℝ), IsProbabilityMeasure μ ∧ NoAtoms μ

/-! ## §2 — Concrete standard Gaussian on `Fin 4 → ℝ`

We build the standard Gaussian on `ℝ⁴` as the product of four
independent standard Gaussians using mathlib's `MeasureTheory.Measure.pi`.

  * `MeasureTheory.Measure.pi` produces a product measure on
    `∀ i, α i`. Specialised to constant family `(fun _ : Fin 4 => ℝ)`
    we obtain a measure on `Fin 4 → ℝ`.

  * `pi.instIsProbabilityMeasure` (Mathlib/MeasureTheory/Constructions/Pi.lean
    line 303) shows the product of probability measures is a
    probability measure.

  * `pi_noAtoms'` (Mathlib/MeasureTheory/Constructions/Pi.lean
    line 531) shows the product of atomless measures is atomless
    when the index type is `Nonempty`.

The standard Gaussians on each coordinate are `gaussianReal 0 1`,
which is a probability measure (`instIsProbabilityMeasureGaussianReal`)
and atomless (`noAtoms_gaussianReal` with `v = 1 ≠ 0`).
-/

/-- The standard 4-dim Gaussian product measure on `Fin 4 → ℝ`. -/
noncomputable def standardGaussianR4 : Measure (Fin 4 → ℝ) :=
  MeasureTheory.Measure.pi (fun _ : Fin 4 => gaussianReal 0 1)

/-- The standard 4-dim Gaussian on `Fin 4 → ℝ` is a probability measure.

    Each coordinate is `gaussianReal 0 1`, a probability measure by
    `instIsProbabilityMeasureGaussianReal`. The product measure
    inherits `IsProbabilityMeasure` via `pi.instIsProbabilityMeasure`. -/
theorem standardGaussianR4_isProbabilityMeasure :
    IsProbabilityMeasure standardGaussianR4 := by
  unfold standardGaussianR4
  haveI : ∀ _ : Fin 4, IsProbabilityMeasure (gaussianReal 0 1) :=
    fun _ => inferInstance
  infer_instance

/-- The standard 4-dim Gaussian on `Fin 4 → ℝ` has no atoms.

    Each coordinate `gaussianReal 0 1` has no atoms by
    `noAtoms_gaussianReal` (since variance `v = 1 ≠ 0`). The
    product inherits `NoAtoms` via `pi_noAtoms'` (`Fin 4` is
    `Nonempty`). -/
theorem standardGaussianR4_noAtoms :
    NoAtoms standardGaussianR4 := by
  unfold standardGaussianR4
  haveI : ∀ _ : Fin 4, NoAtoms (gaussianReal (0 : ℝ) (1 : NNReal)) :=
    fun _ => noAtoms_gaussianReal (by exact one_ne_zero)
  -- `Fin 4` is `Nonempty` via `⟨0⟩`.
  haveI : Nonempty (Fin 4) := ⟨0⟩
  infer_instance

/-- **★ The standard 4-dim Gaussian inhabits the strengthened²
    Bochner-Minlos typed predicate on ℝ⁴ ★** — concrete witness with
    an atomless probability measure on the four-dimensional carrier
    `Fin 4 → ℝ`. -/
theorem bochnerMinlos_R4_gaussian_witness :
    BochnerMinlosR4TypedStatement :=
  ⟨standardGaussianR4,
   standardGaussianR4_isProbabilityMeasure,
   standardGaussianR4_noAtoms⟩

/-! ## §3 — Cascade to Wave 58 (1-dim) → Wave 57 typed → Wave 56 -/

/-- **Strengthened² ⇒ Wave 58 strengthened (1-dim)
    `BochnerMinlosConcreteTypedStatement`**. The 4-dim Gaussian
    witness supplies the 1-dim Gaussian witness on `ℝ` directly via
    `gaussianReal 0 1` — independent of the input. -/
theorem bochnerMinlos_R4_implies_wave58_concrete
    (_h : BochnerMinlosR4TypedStatement) :
    BochnerMinlosConcreteTypedStatement :=
  bochnerMinlos_concrete_gaussianReal_witness

/-- **Strengthened² ⇒ Wave 57 typed `BochnerMinlosTypedStatement`**.

    The 4-dim Gaussian witness on `Fin 4 → ℝ` supplies a
    `ProbabilityMeasure` on a measurable carrier directly, without
    routing through the 1-dim form. -/
theorem bochnerMinlos_R4_implies_wave57_typed
    (h : BochnerMinlosR4TypedStatement) :
    BochnerMinlosTypedStatement := by
  obtain ⟨μ, hμ_prob, _hμ_noAtoms⟩ := h
  exact ⟨Fin 4 → ℝ, inferInstance, ⟨⟨μ, hμ_prob⟩⟩⟩

/-- **Strengthened² ⇒ Wave 56 `True`-shaped original `BochnerMinlosOnNuclearSpaces`**. -/
theorem bochnerMinlos_R4_implies_original
    (h : BochnerMinlosR4TypedStatement) :
    BochnerMinlosOnNuclearSpaces :=
  bochnerMinlos_typed_implies_original
    (bochnerMinlos_R4_implies_wave57_typed h)

/-! ## §4 — Honest-scope marker -/

/-- **Honest-scope marker** — the strengthened² witness improves on the
    Wave 58 1-dim concrete witness in three ways:

    (a) The carrier is `Fin 4 → ℝ` (a four-dim real space, the
        underlying type of `EuclideanSpace ℝ (Fin 4) =
        PiLp 2 (fun _ : Fin 4 => ℝ)`), not `ℝ`.
    (b) The probability measure is the standard 4-dim Gaussian
        product measure
        `MeasureTheory.Measure.pi (fun _ : Fin 4 => gaussianReal 0 1)`,
        atomless and a probability measure.
    (c) The cascade to Wave 58/57/56 is concrete and unconditional.

    HOWEVER: the carrier `Fin 4 → ℝ` is FOUR-dim and FINITE-dim, not
    the topological dual `𝓢'(ℝ⁴, ℝ)` of the Schwartz space on `ℝ⁴`
    which is infinite-dim. The infinite-dim Minlos extension is NOT
    proved. -/
def BochnerMinlosR4WitnessHonestScope : Prop :=
  -- (1) Strengthened² typed predicate is inhabited by the 4-dim
  --     standard Gaussian product measure.
  BochnerMinlosR4TypedStatement ∧
  -- (2) Cascade to Wave 58 1-dim concrete.
  (BochnerMinlosR4TypedStatement → BochnerMinlosConcreteTypedStatement) ∧
  -- (3) Cascade to Wave 57 typed.
  (BochnerMinlosR4TypedStatement → BochnerMinlosTypedStatement) ∧
  -- (4) Cascade to Wave 56 `True`-shaped original.
  (BochnerMinlosR4TypedStatement → BochnerMinlosOnNuclearSpaces)

/-- The honest-scope marker holds unconditionally. -/
theorem bochnerMinlos_R4_witness_honestScope_holds :
    BochnerMinlosR4WitnessHonestScope :=
  ⟨bochnerMinlos_R4_gaussian_witness,
   bochnerMinlos_R4_implies_wave58_concrete,
   bochnerMinlos_R4_implies_wave57_typed,
   bochnerMinlos_R4_implies_original⟩

/-! ## §5 — Capstone -/

/-- ★★★ **CAPSTONE — Bochner-Minlos R^4 Concrete Gaussian Witness** ★★★
    (Wave 58 STRENGTHENING², 2026-06-02)

    STRENGTHENING² of the Wave 58 strengthened (G1) Bochner-Minlos
    Prop from `YM_BochnerMinlosConcreteWitness` via a concrete
    standard Gaussian product measure on `Fin 4 → ℝ` — the underlying
    measurable carrier of `EuclideanSpace ℝ (Fin 4)`.

    **Seven structural clauses**:

    (1) Strengthened² typed predicate
        `BochnerMinlosR4TypedStatement` — atomless probability
        measure on `Fin 4 → ℝ` (rules out Dirac-on-`Unit`
        of Wave 57 AND 1-dim `gaussianReal` of Wave 58).
    (2) Concrete 4-dim Gaussian inhabits the strengthened² predicate.
    (3) `standardGaussianR4` is a probability measure.
    (4) `standardGaussianR4` has no atoms.
    (5) Cascade strengthened² ⇒ Wave 58 strengthened (1-dim).
    (6) Cascade strengthened² ⇒ Wave 57 typed ⇒ Wave 56 original.
    (7) Honest-scope marker.

    **Honest scope**: NOT a Clay discharge. Carrier `Fin 4 → ℝ` is
    finite-dim; the literal Bochner-Minlos statement requires the
    topological dual `𝓢'(ℝ⁴, ℝ)` of a nuclear space, which is
    infinite-dim. The dimension `4` of the carrier matches the
    dimension of spacetime in QFT but does NOT match the dimension
    of the Schwartz dual.

    Axiom-free; `#print axioms` returns only
    `[propext, Classical.choice, Quot.sound]`. -/
theorem bochnerMinlos_R4_witness_capstone :
    BochnerMinlosR4TypedStatement ∧
    IsProbabilityMeasure standardGaussianR4 ∧
    NoAtoms standardGaussianR4 ∧
    (BochnerMinlosR4TypedStatement → BochnerMinlosConcreteTypedStatement) ∧
    (BochnerMinlosR4TypedStatement → BochnerMinlosTypedStatement) ∧
    (BochnerMinlosR4TypedStatement → BochnerMinlosOnNuclearSpaces) ∧
    BochnerMinlosR4WitnessHonestScope :=
  ⟨bochnerMinlos_R4_gaussian_witness,
   standardGaussianR4_isProbabilityMeasure,
   standardGaussianR4_noAtoms,
   bochnerMinlos_R4_implies_wave58_concrete,
   bochnerMinlos_R4_implies_wave57_typed,
   bochnerMinlos_R4_implies_original,
   bochnerMinlos_R4_witness_honestScope_holds⟩

/-! ## §6 — Axiom-freeness verification -/

#print axioms standardGaussianR4_isProbabilityMeasure
#print axioms standardGaussianR4_noAtoms
#print axioms bochnerMinlos_R4_gaussian_witness
#print axioms bochnerMinlos_R4_implies_wave58_concrete
#print axioms bochnerMinlos_R4_implies_wave57_typed
#print axioms bochnerMinlos_R4_implies_original
#print axioms bochnerMinlos_R4_witness_honestScope_holds
#print axioms bochnerMinlos_R4_witness_capstone

end YM_BochnerMinlosR4Witness
end PrincipiaTractalis
